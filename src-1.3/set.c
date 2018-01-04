/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE set.c - *SAT 1.3 */
/*  Memoizing with sets of sets */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "set.h"

/* Memoizing */
static memo_t *SET_memo_ptr;

/* Utility to access fields */
#define Get_field(hash_flag, field) \
(hash_flag ? ((int_memo_hash_t*)(SET_memo_ptr->memo_of_level[SET_memo_ptr->level]->memo_sat))->field : ((int_memo_sat_bm_t*)(SET_memo_ptr->memo_of_level[SET_memo_ptr->level]->memo_sat))->field)

#define Set_field(hash_flag, field, val) \
(hash_flag ? (((int_memo_hash_t*)(SET_memo_ptr->memo_of_level[SET_memo_ptr->level]->memo_sat))->field  = val) : (((int_memo_sat_bm_t*)(SET_memo_ptr->memo_of_level[SET_memo_ptr->level]->memo_sat))->field = val))
 

/* *********************************************************************** */
/* Initialize and clear memoizing */
/* *********************************************************************** */

/* Prototypes ------------------------------------------------------------ */
int_memo_t       *Int_init_memoS(int level);            /* Init current level cache */
char             *Int_init_sat_bm_memoS(int level);     /* Init sat cache via bit matrix */
char             *Int_init_unsat_bm_memoS(int level);   /* Init unsat cache via bit matrix */
char             *Int_init_hash_memoS(int level);       /* Init cache with a hash table */  
int_memo_betas_t *Int_init_betas_memoS();               /* Init dyn. irrelevant betas */
void             Int_clear_memoS(int_memo_t *memo_ptr, int dim); /* Clears a single level cache */
int              Find_next_prime(int n);                /* Returns the first prime number bigger than n */
int              Var_set_hash(char *key, int modulus);  /* Hash function for sets */

/* Interface ------------------------------------------------------------- */

/* Barely allocate the "shell" of the structure */
/* Mainly for referencing the statistics */
void Alloc_memoS(int dim, statistics_t *statistics_ptr)
{
  int i;
  SET_memo_ptr = ALLOC(memo_t, 1);
  /* Initialize array of cache references */
  for (i = 0; i < MAX_DEPTH; i++) 
    SET_memo_ptr->memo_of_level[i] = NIL(int_memo_t);

  /* Record the dimensions */
  SET_memo_ptr->dim = dim;

  /* All flags disabled */
  for (i = 0; i < MAX_FLAGS; i++)  
    SET_memo_ptr->flags[i] = 0;

  /* All stats & times are empty */
  for (i = 0; i < MAX_STATS; i++) {
    SET_memo_ptr->stats[i] = 0;
    SET_memo_ptr->timings[i] = 0;
  }

  /* Reference to statistics */
  SET_memo_ptr->statistics_ptr = statistics_ptr;

  /* Default level is 0 */
  SET_memo_ptr->level = 0;

  return;
}

void Init_memoS() 
{
  /* Initializes level 0 cache */
  SET_memo_ptr->memo_of_level[0] = Int_init_memoS(0);

  return;
}

void Clear_memoS()
{
  int i = 0;
  /* Clean every allocated cache */
  while (SET_memo_ptr->memo_of_level[i] != NIL(int_memo_t)) {
    Int_clear_memoS(SET_memo_ptr->memo_of_level[i], SET_memo_ptr->dim);
    ++i;
  }
  FREE(SET_memo_ptr);
  return;
}

void Force_no_memoS()
{
  SET_memo_ptr = NIL(memo_t);
  return;
}

/* Private functions ------------------------------------------------------ */

/* This function returns a pointer to a single modal level cache */
int_memo_t *Int_init_memoS(int level)
{
  int_memo_t          *memo_ptr;

  /* Initialize level and sat cache */
  memo_ptr = ALLOC(int_memo_t, 1);
  if (Getf_memoS(GET_MODELS)) 
    memo_ptr->memo_sat = 
      (Getf_memoS(HASH_STORAGE) ? Int_init_hash_memoS(level) : Int_init_sat_bm_memoS(level));

  /* Initialize dependencies */
  if (Getf_memoS(GET_DEPENDENCIES))
    memo_ptr->memo_unsat = 
      (Getf_memoS(HASH_STORAGE) ? Int_init_hash_memoS(level) : Int_init_unsat_bm_memoS(level));

  /* Initialize static FAST (possibly is already there!) */
  if (Getf_memoS(STATIC_FAST)) {
    if (!Getf_memoS(Getf_memoS(HASH_STORAGE)) && Getf_memoS(GET_DEPENDENCIES))
      memo_ptr->memo_static_fast = (int_memo_unsat_bm_t*)(memo_ptr->memo_unsat);
    else 
      memo_ptr->memo_static_fast = (int_memo_unsat_bm_t*)Int_init_unsat_bm_memoS(level);
  }

  /* Initialize dynamic FAST */
  if (Getf_memoS(DYNAMIC_FAST))
    memo_ptr->memo_dynamic_fast = Int_init_betas_memoS();

  /* Compute the memory allocated here (bytes) */
  SET_memo_ptr->stats[MEMORY] += sizeof(int_memo_t); /* The structure */

  return memo_ptr;
}

/* This function allocates a sat cache with a bit matrix */
char *Int_init_sat_bm_memoS(int level)
{
  int               dim, i, real_dim;
  statistics_t      *statistics_ptr;
  int_memo_sat_bm_t *memo_ptr;
  
  dim = SET_memo_ptr->dim;
  real_dim =  2 * (dim + 1);
  statistics_ptr = SET_memo_ptr->statistics_ptr;
  memo_ptr = ALLOC(int_memo_sat_bm_t,1);
  
  /* Initialize sets */
  memo_ptr->memo_array = ALLOC(var_set_t*, real_dim);
  /* If cache is by level then exploit information */
  if (Getf_memoS(LEVEL_CACHE)) {
    for (i = 0; i < real_dim; i++) {
      if (Test_atom_at(statistics_ptr, (i <=dim ? i : (i - (dim + 1))), level))
	memo_ptr->memo_array[i] = var_set_new(WINDOW_SIZE);
      else
	memo_ptr->memo_array[i] = NIL(var_set_t);
    }
  } else {
    for (i = 0; i < real_dim; i++)
      memo_ptr->memo_array[i] = var_set_new(WINDOW_SIZE);
  }
  memo_ptr->cur_set   = -1;
  
  /* Fast growth and no compaction */
  memo_ptr->growth = 0;
  memo_ptr->compact = 0;
  
  /* Trashing is not started yet */
  memo_ptr->trashing_sets = 0;
  
  /* Compute allocated memory (bytes) */
  if (Getf_memoS(LEVEL_CACHE))
    SET_memo_ptr->stats[MEMORY] += 
      2 * Count_atoms_at(statistics_ptr, level)  * 
       (sizeof(var_set_t) + WINDOW_SIZE / sizeof(int));
  else
    SET_memo_ptr->stats[MEMORY] += 
      (2 * dim * (sizeof(var_set_t) + WINDOW_SIZE / sizeof(int)));
  SET_memo_ptr->stats[MEMORY] += sizeof(int_memo_sat_bm_t);

  return (char*)memo_ptr;
}

/* This function allocates an unsat cache with a bit matrix */
char *Int_init_unsat_bm_memoS(int level)
{
  int                 dim, i, real_dim;
  statistics_t        *statistics_ptr;
  int_memo_unsat_bm_t *memo_ptr;
  
  dim = SET_memo_ptr->dim;
  real_dim = dim + 1;
  statistics_ptr = SET_memo_ptr->statistics_ptr;
  memo_ptr = ALLOC(int_memo_unsat_bm_t,1);  

  /* Initialize dependencies sets */
  memo_ptr->dep_array = ALLOC(var_set_t*, real_dim);
  memo_ptr->dep_beta = ALLOC(int, (WINDOW_SIZE / DEP_FACTOR));       
  /* If cache is by level then exploit information */
  if (Getf_memoS(LEVEL_CACHE)) {
    for (i = 0; i < real_dim; i++) {
      if (Test_atom_at(statistics_ptr, i, level)) 
	memo_ptr->dep_array[i] = var_set_new(WINDOW_SIZE / DEP_FACTOR);
      else
	memo_ptr->dep_array[i] = NIL(var_set_t);
    }
  } else {
    for (i = 0; i < real_dim; i++) 
      memo_ptr->dep_array[i] = var_set_new(WINDOW_SIZE / DEP_FACTOR);
  }
  memo_ptr->cur_dep   = -1;

  /* Trashing is not started yet */
  memo_ptr->trashing_deps = 0;

  /* Compute allocated memory (bytes) */
  if (Getf_memoS(LEVEL_CACHE))
    SET_memo_ptr->stats[MEMORY] += 
      (Count_atoms_at(statistics_ptr, level) *              /* Static dependencies */
       (sizeof(var_set_t) + (WINDOW_SIZE / DEP_FACTOR) / sizeof(int))) +
      sizeof(int) * (WINDOW_SIZE / DEP_FACTOR);             /* Static dependency labels */ 
  else
    SET_memo_ptr->stats[MEMORY] += 
      dim * (sizeof(var_set_t) + (WINDOW_SIZE / DEP_FACTOR) / sizeof(int)) +
      sizeof(int) * (WINDOW_SIZE / DEP_FACTOR);             
  SET_memo_ptr->stats[MEMORY] += sizeof(int_memo_unsat_bm_t);

  return (char*)memo_ptr;
}

/* Initiliazing a hash table */
char *Int_init_hash_memoS(int level)
{
  int             dim;
  statistics_t    *statistics_ptr;
  int_memo_hash_t *memo_ptr;
  int             bins;
  
  dim = SET_memo_ptr->dim;
  statistics_ptr = SET_memo_ptr->statistics_ptr;
  memo_ptr = ALLOC(int_memo_hash_t,1);
  
  /* If cache is by level then exploit information */
  if (Getf_memoS(LEVEL_CACHE)) {
    /* The number of bins is the prime number next 
       to the number of modal atoms in the level */
/*      bins = Find_next_prime(Count_atoms_at(statistics_ptr, level));
 */
    bins = Find_next_prime(dim);
    memo_ptr->memo_hash = 
      st_init_table_with_params(var_set_cmp, Var_set_hash, bins, INT_MAX,
				1.0, ST_DEFAULT_REORDER_FLAG);
  } else {
    /* The number of bins is the prime number next 
       to the number of modal atoms in the formula */
    bins = Find_next_prime(dim);
    memo_ptr->memo_hash = 
      st_init_table_with_params(var_set_cmp, Var_set_hash, bins, INT_MAX,
				1.0, ST_DEFAULT_REORDER_FLAG);
  }

  /* No current set of betas, no compaction */
  memo_ptr->cur_beta_set = NIL(var_set_t);
  memo_ptr->compact = 0;
  
  /* Compute allocated memory (bytes) */
  SET_memo_ptr->stats[MEMORY] += 
    sizeof(int_memo_hash_t) + sizeof(st_table); 

  return (char*)memo_ptr;
}

/* Initializes dynamic dependencies cache */
int_memo_betas_t *Int_init_betas_memoS()
{
  int              dim, i, real_dim;
  int_memo_betas_t *memo_ptr;
  
  dim = SET_memo_ptr->dim;
  memo_ptr = ALLOC(int_memo_betas_t,1);    
  real_dim = dim + 1;
  
  /* Initialize dynamic dependencies index */
  memo_ptr->dfast_array = ALLOC(int, real_dim);
  memo_ptr->dfast_stack = ALLOC(int*, real_dim);
  for (i = 0; i <= dim; i++) {
    memo_ptr->dfast_array[i] = 0;
    memo_ptr->dfast_stack[i] = NIL(int);
  }
  memo_ptr->dfast_idx = -1;

  /* Compute allocated memory (bytes) */
  SET_memo_ptr->stats[MEMORY] += 
    sizeof(int) * SET_memo_ptr->dim +      /* Dynamic dependency labels */
    sizeof(int*) * SET_memo_ptr->dim;      /* Dynamic dependency stack */

  return memo_ptr;
}

/* Clears everything (still a fake!!!) */
void Int_clear_memoS(int_memo_t *memo_ptr, int dim)
{
  return;
}

/* Finds the next prime p > n */
int Find_next_prime(int n)
{
  int i;
  int j;

  if ((n % 2) == 0) ++n;
  for (i = n; i < (2 * n); i += 2) {
    for (j = 3; j < i; j += 2)
      if ((i % j) == 0) break;
    if (j >= i) break;
  }

  return i;
}

/* *********************************************************************** */
/* Accessing the structure */
/* *********************************************************************** */

/* Prototypes ------------------------------------------------------------ */
lsList   *Int_test_bm_memoS(int_memo_sat_bm_t *memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr);
lsList   *Int_test_hash_memoS(int_memo_hash_t *memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr);
void     Int_store_bm_memoS(int_memo_sat_bm_t *memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr);
void     Int_store_hash_memoS(int_memo_hash_t *memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr);
vertex_t *Int_test_bm_depS(int_memo_unsat_bm_t *memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr);
vertex_t *Int_test_hash_depS(int_memo_hash_t *memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr);
void     Int_store_bm_depS(int_memo_unsat_bm_t *memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr);
void     Int_store_hash_depS(int_memo_hash_t *memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr);
int      Trash_subsets(int_memo_sat_bm_t *memo_ptr, int cur_set);

/* Interface ------------------------------------------------------------- */

int Use_memoS()
{
  return (SET_memo_ptr != NIL(memo_t));
}

void Setf_memoS(int flag)
{
  if (flag == COMPACT_STORAGE) 
    Set_field(Getf_memoS(HASH_STORAGE), compact, 1);
  else 
    SET_memo_ptr->flags[flag] = 1;
  return;
}

void Clearf_memoS(int flag)
{
  if (flag == COMPACT_STORAGE) 
    Set_field(Getf_memoS(HASH_STORAGE), compact, 0);
  else
    SET_memo_ptr->flags[flag] = 0;
  return;
}

int Getf_memoS(int flag)
{
  if (flag == COMPACT_STORAGE) 
    return Get_field(Getf_memoS(HASH_STORAGE), compact);
  else
    return SET_memo_ptr->flags[flag];
}

int Time_memoS(int flag)
{
  return SET_memo_ptr->timings[flag];
}

int Stats_memoS(int stat)
{
  return SET_memo_ptr->stats[stat];
}

void Inc_level_memoS()
{
  ++(SET_memo_ptr->level);
}

void Dec_level_memoS()
{
  --(SET_memo_ptr->level);
}

int Get_level_memoS()
{
  return SET_memo_ptr->level;
}

/* Search for satisfiable subtests */
lsList *Test_memoS(lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr)
{
  int_memo_t *memo_ptr;

  /* First check if the cache for the current level is there 
     and if it is not there then create it */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  if (memo_ptr == NIL(int_memo_t)) {
    SET_memo_ptr->memo_of_level[SET_memo_ptr->level] = 
      Int_init_memoS(SET_memo_ptr->level);
    memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  }

  if (Getf_memoS(HASH_STORAGE))
    return Int_test_hash_memoS((int_memo_hash_t*)memo_ptr->memo_sat,alpha_lsList_ptr, beta_lsList_ptr);
  else
    return Int_test_bm_memoS((int_memo_sat_bm_t*)memo_ptr->memo_sat,alpha_lsList_ptr, beta_lsList_ptr);
}

/* Store satisfiable subtests */
void Store_memoS(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  int_memo_t *memo_ptr;

  /* Set current cache */
  /* It must be there since testing occurs always before of storing
     and testing takes care of allocating new caches */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];

  if (Getf_memoS(HASH_STORAGE))
    Int_store_hash_memoS((int_memo_hash_t*)memo_ptr->memo_sat,alpha_lsList_ptr, beta_vertex_ptr);
  else
    Int_store_bm_memoS((int_memo_sat_bm_t*)memo_ptr->memo_sat,alpha_lsList_ptr, beta_vertex_ptr);

  return;

}

/* Search for unsatisfiable subtests */
vertex_t *Test_depS(lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr)
{
  int_memo_t *memo_ptr;

  /* First check if the cache for the current level is there 
     and if it is not there then create it */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  if (memo_ptr == NIL(int_memo_t)) {
    SET_memo_ptr->memo_of_level[SET_memo_ptr->level] = 
      Int_init_memoS(SET_memo_ptr->level);
    memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  }

  if (Getf_memoS(HASH_STORAGE))
    return Int_test_hash_depS((int_memo_hash_t*)memo_ptr->memo_unsat, alpha_lsList_ptr, beta_lsList_ptr);
  else
    return Int_test_bm_depS((int_memo_unsat_bm_t*)memo_ptr->memo_unsat, alpha_lsList_ptr, beta_lsList_ptr);
}    

/* Search for static dependencies */
lsList *Test_sfastS(lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr,
		    vertex_t **rbeta_vertex_ptr_ptr)
{
  var_set_t  *witness_var_set_ptr;
  var_set_t  *alphas_var_set_ptr, *betas_var_set_ptr;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  lsStatus   list_status;
  int        atom_value, i, j;
  int_memo_t *memo_ptr;
  int_memo_unsat_bm_t *bm_memo_ptr;
  int        win_size;
  int        *purged_alphas, purged_alpha_idx;
  int        lap_time, flag_record;

  *rbeta_vertex_ptr_ptr = NIL(vertex_t);

  /* First check if the cache for the current level is there 
     and if it is not there then create it */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  if (memo_ptr == NIL(int_memo_t)) {
    SET_memo_ptr->memo_of_level[SET_memo_ptr->level] = 
      Int_init_memoS(SET_memo_ptr->level);
    memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  }

  /* Set the reduced window size */
  win_size = WINDOW_SIZE / DEP_FACTOR;
  bm_memo_ptr = memo_ptr->memo_static_fast;

  if (bm_memo_ptr->cur_dep != -1) {
    /* Monitoring access time (if dependencies are not hashed
       this is also an access to dependencies) */
    if (!Getf_memoS(HASH_STORAGE)) ++(SET_memo_ptr->stats[DEP_ACCESS]);
    ++(SET_memo_ptr->stats[SFAST_ACCESS]);
    lap_time = util_cpu_time();

    /* Create a witness, fill it with all the elements */
    witness_var_set_ptr = var_set_new(win_size);
    for (i = 0; i < win_size; i++) 
      var_set_set_elt(witness_var_set_ptr, i);
    
    alphas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    betas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    /* Put the alpha and beta lists into sets */
    lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(alphas_var_set_ptr, atom_value);
    }
    lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(betas_var_set_ptr, atom_value);
    }
    /* Filter the witness through the complement of the alphas */
    /* (seeking for cached subsets of the current set of alphas) */
    if (Get_level_memoS(LEVEL_CACHE)) {
      /* Cache by level makes things slightly different */
      for (i = 0; i <= SET_memo_ptr->dim; i++) 
	if ((bm_memo_ptr->dep_array[i] != NIL(var_set_t)) &&
	    !var_set_get_elt(alphas_var_set_ptr, i)) {
	  var_set_and(witness_var_set_ptr, 
		      witness_var_set_ptr, bm_memo_ptr->dep_array[i]);
	}
    } else {
      for (i = 0; i <= SET_memo_ptr->dim; i++) 
	if (!var_set_get_elt(alphas_var_set_ptr, i)) {
	  var_set_and(witness_var_set_ptr, 
		      witness_var_set_ptr, bm_memo_ptr->dep_array[i]);
	}
    }

    /* If at least one element of the witness is set, go on 
       otherwise fail */
    if (var_set_is_empty(witness_var_set_ptr)) {
      var_set_free(alphas_var_set_ptr);
      var_set_free(betas_var_set_ptr);
      var_set_free(witness_var_set_ptr);
      /* Monitoring access time (if dependencies are not hashed
       this is also an access to dependencies) */
      SET_memo_ptr->timings[SFAST_TIME] += util_cpu_time() - lap_time;
      if (!Getf_memoS(HASH_STORAGE)) SET_memo_ptr->timings[DEP_SEARCH_TIME] += util_cpu_time() - lap_time;
      return alpha_lsList_ptr;
    }

    /* We must keep track of purged alphas */
    purged_alpha_idx = 0;
    purged_alphas = ALLOC(int, (SET_memo_ptr->dim + 1));
    /* We want to record only the first successful access */
    flag_record = 1;
    
    /* Now try to discard as many alphas as possible */
    for (i = 0; i < win_size; i++) 
      if (var_set_get_elt(witness_var_set_ptr, i)) {

	/* The set i contains already purged alphas? */
	j = 0;
	while (j < purged_alpha_idx) {
	  if (!var_set_get_elt(bm_memo_ptr->dep_array[purged_alphas[j]],i)) break;
	  ++j;
	}
	/* If so,  it is no more a subset of current alphas */ 
	if (j < purged_alpha_idx) continue;  

	/* Two cases matter: (i) the beta label is contained in the current list
           of alphas or (ii) the beta label is contained in the current list of betas */
	if (var_set_get_elt(alphas_var_set_ptr, bm_memo_ptr->dep_beta[i])) {
	  /* case (i) applies: the alpha corresponding to the beta label is redundant */
	  if (flag_record) {++(SET_memo_ptr->stats[SFAST_SUCCESS]); flag_record = 0;}
	  var_set_clear_elt(alphas_var_set_ptr, bm_memo_ptr->dep_beta[i]);
	  purged_alphas[purged_alpha_idx++] = bm_memo_ptr->dep_beta[i];
	} else if (var_set_get_elt(betas_var_set_ptr, bm_memo_ptr->dep_beta[i])) {
	  if (!Getf_memoS(HASH_STORAGE)) ++(SET_memo_ptr->stats[DEP_SUCCESS]);
	  /* case (ii) applies: the current test is unconsistent */
	  break;
	}
      }

    /* Monitoring access time (if dependencies are not hashed
       this is also an access to dependencies) */
    SET_memo_ptr->timings[SFAST_TIME] += util_cpu_time() - lap_time;
    if (!Getf_memoS(HASH_STORAGE)) SET_memo_ptr->timings[DEP_SEARCH_TIME] += util_cpu_time() - lap_time;

    /* Clear array of purged alphas */
    FREE(purged_alphas);

    if (i < win_size) {
      /* If the loop ended before reaching winsize an inconsistency was found */
      lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
	atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
	if (atom_value ==  bm_memo_ptr->dep_beta[i]) {
	  *rbeta_vertex_ptr_ptr = UNCAST_VERTEX_ITEM(vertex_lsGeneric);
	  break;
	}
      }
      /* The loop ALWAYS breaks */
      list_status = lsFinish(t_lsGen);
    } else {
      /* Otherwise, just discard alphas from the list */
      lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
	atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
	if (!var_set_get_elt(alphas_var_set_ptr, atom_value)) 
	  list_status = lsDelBefore(t_lsGen, &vertex_lsGeneric);
      }
    }
    
    /* Destroy temporary allocations */
    var_set_free(alphas_var_set_ptr);
    var_set_free(betas_var_set_ptr);
    var_set_free(witness_var_set_ptr);
  }
  
  return alpha_lsList_ptr;
}

/* Store a dependency with a bit matrix */
void Store_sfastS(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  int        i, alpha_value;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  int        win_size;
  int        lap_time;
  int_memo_t *memo_ptr;
  int_memo_unsat_bm_t *bm_memo_ptr;

  /* Set current cache */
  /* It must be there since testing occurs always before than storing
     and testing takes care of allocating new caches */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  bm_memo_ptr = memo_ptr->memo_static_fast;

  win_size = WINDOW_SIZE / DEP_FACTOR;
  ++(SET_memo_ptr->stats[DEP_STORAGE]);
  ++(SET_memo_ptr->stats[DEP_STORE_ACC]);

  /* Monitoring storage time */
  lap_time = util_cpu_time();

  /* Increment the current set modulo win_size */
  (bm_memo_ptr->cur_dep)++;
  if (bm_memo_ptr->cur_dep == win_size) {
    bm_memo_ptr->cur_dep = 0;
    bm_memo_ptr->trashing_deps = 1;
  }

  if (bm_memo_ptr->trashing_deps)
    ++(SET_memo_ptr->stats[DEP_TRASHING]);

  /* Be sure to clear everything */
  for (i = 0; i <= (SET_memo_ptr->dim); i++) 
    var_set_set_elt(bm_memo_ptr->dep_array[i],bm_memo_ptr->cur_dep);
  
  /* Set alphas properly 
     (the complement of the set of alphas is stored) */
  lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
    alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
    var_set_clear_elt(bm_memo_ptr->dep_array[alpha_value],
		      bm_memo_ptr->cur_dep);
  }
  /* Label the dependency set with the beta */
  bm_memo_ptr->dep_beta[bm_memo_ptr->cur_dep] = V_value(beta_vertex_ptr);

  /* Monitoring storage time */
  SET_memo_ptr->timings[DEP_STORE_TIME] += util_cpu_time() - lap_time;

  return;
}

/* Store unsatisfiable subtests */
void Store_depS(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  int_memo_t *memo_ptr;

  /* Set current cache */
  /* It must be there since testing occurs always before than storing
     and testing takes care of allocating new caches */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];

  if (Getf_memoS(HASH_STORAGE))
    Int_store_hash_depS((int_memo_hash_t*)memo_ptr->memo_unsat, alpha_lsList_ptr, beta_vertex_ptr);
  else
    Int_store_bm_depS((int_memo_unsat_bm_t*)memo_ptr->memo_unsat, alpha_lsList_ptr, beta_vertex_ptr);

  return;
}
  
/* Search for dynamic dependencies */
lsList *Test_dfastS(lsList *beta_lsList_ptr) 
{
  int_memo_t *memo_ptr;
  int_memo_betas_t *sm_memo_ptr;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  lsStatus   list_status;
  int        record_flag;
  int        atom_value;
  int        lap_time;

  /* Dynamic FAST cannot be used at any level without cache by levels */
  /* If cache by level is not active and the level is different from 0 
     return without doing nothing */
  if (!Getf_memoS(LEVEL_CACHE) && (SET_memo_ptr->level != 0))
    return beta_lsList_ptr;

  /* First check if the cache for the current level is there 
     and if it is not there then create it */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  if (memo_ptr == NIL(int_memo_t)) {
    SET_memo_ptr->memo_of_level[SET_memo_ptr->level] = 
      Int_init_memoS(SET_memo_ptr->level);
    memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  }

  sm_memo_ptr = memo_ptr->memo_dynamic_fast;
  if (sm_memo_ptr->dfast_idx != -1) {
    /* Monitoring access time */
    ++(SET_memo_ptr->stats[DFAST_ACCESS]);
    lap_time = util_cpu_time();

    /* We want to record the first success only */
    record_flag = 1;

    /* Check if some of the betas is dinamically irrelevant */
    lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      if (sm_memo_ptr->dfast_array[atom_value] != 0) {
	/* The beta was declared dynamically irrelevant, remove it */
	if (record_flag) {++(SET_memo_ptr->stats[DFAST_SUCCESS]); record_flag=0;}
	list_status = lsDelBefore(t_lsGen, &vertex_lsGeneric);
      }
    }

    /* Monitoring access time */
    SET_memo_ptr->timings[DFAST_TIME] += util_cpu_time() - lap_time;
  }

  return beta_lsList_ptr;
}


/* Store dynamic dependencies */
void Store_dfastS(vertex_t *beta_vertex_ptr, int cur_stack_idx)
{
  
  int_memo_t       *memo_ptr;
  int_memo_betas_t *sm_memo_ptr;

  /* Dynamic FAST cannot be used at any level without cache by levels */
  /* If cache by level is not active and the level is different from 0 
     return without doing nothing */
  if (!Getf_memoS(LEVEL_CACHE) && (SET_memo_ptr->level != 0)) return;

  /* First check if the cache for the current level is there 
     and if it is not there then create it */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  if (memo_ptr == NIL(int_memo_t)) {
    SET_memo_ptr->memo_of_level[SET_memo_ptr->level] = 
      Int_init_memoS(SET_memo_ptr->level);
    memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  }

  sm_memo_ptr = memo_ptr->memo_dynamic_fast;
  ++(SET_memo_ptr->stats[DFAST_STORAGE]);

  /* Mark the dynamically irrelevant beta with the current stack index */
  sm_memo_ptr->dfast_array[V_value(beta_vertex_ptr)] = cur_stack_idx; 
  /* Also update the dynamic FAST stack */
  (sm_memo_ptr->dfast_idx)++;
  sm_memo_ptr->dfast_stack[sm_memo_ptr->dfast_idx] =  
    &(sm_memo_ptr->dfast_array[V_value(beta_vertex_ptr)]); 
  
  return;
}

/* Reallign dynamic dependencies */
void Update_dfastS(int cur_stack_idx)
{
  int              run_dfast_idx;
  int_memo_t       *memo_ptr;
  int_memo_betas_t *sm_memo_ptr;

  /* Dynamic FAST cannot be used at any level without cache by levels */
  /* If cache by level is not active and the level is different from 0 
     return without doing nothing */
  if (!Getf_memoS(LEVEL_CACHE) && (SET_memo_ptr->level != 0)) return;

  /* First check if the cache for the current level is there 
     and if it is not then there is nothing to udpate */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  if (memo_ptr == NIL(int_memo_t)) return;

  sm_memo_ptr = memo_ptr->memo_dynamic_fast;
  /* Unmark all the betas that were marked irrelevant on deeper branches */
  for (run_dfast_idx = sm_memo_ptr->dfast_idx; 
       *(sm_memo_ptr->dfast_stack[run_dfast_idx]) > cur_stack_idx;
       *(sm_memo_ptr->dfast_stack[run_dfast_idx]) = 0, run_dfast_idx--);
  
  sm_memo_ptr->dfast_idx = run_dfast_idx;

  return;
}

/* Clear all dynamic dependencies */
void Clear_dfastS()
{
  int        run_dfast_idx;
  int_memo_t *memo_ptr;
  int_memo_betas_t *sm_memo_ptr;

  /* Dynamic FAST cannot be used at any level without cache by levels */
  /* If cache by level is not active and the level is different from 0 
     return without doing nothing */
  if (!Getf_memoS(LEVEL_CACHE) && (SET_memo_ptr->level != 0)) return;

  /* First check if the cache for the current level is there 
     and if it is not then there is nothing to clear */
  memo_ptr = SET_memo_ptr->memo_of_level[SET_memo_ptr->level];
  if (memo_ptr == NIL(int_memo_t)) return;

  sm_memo_ptr = memo_ptr->memo_dynamic_fast;
  /* Sweeps all the marked betas and unmarks them */
  for (run_dfast_idx = sm_memo_ptr->dfast_idx; 
       run_dfast_idx > -1;
       *(sm_memo_ptr->dfast_stack[run_dfast_idx]) = 0, run_dfast_idx--);
  
  sm_memo_ptr->dfast_idx = run_dfast_idx;

  return;
}

/* Private functions ------------------------------------------------------ */

/* Internal test for satisfiability results with a bit matrix */
lsList* Int_test_bm_memoS(int_memo_sat_bm_t *memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr)
{
  var_set_t  *witness_var_set_ptr;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  lsStatus   list_status;
  int        alpha_value, beta_value, i;
  int        lap_time, real_dim;
  int        *match_table, match_idx;
  
  if (memo_ptr->cur_set != -1) {
    /* Monitoring access time */
    lap_time = util_cpu_time();
    ++(SET_memo_ptr->stats[MEMO_ACCESS]);
    real_dim = SET_memo_ptr->dim + 1;
    
    /* Create a witness, fill it with all the elements */
    witness_var_set_ptr = var_set_new(WINDOW_SIZE);
    for (i = 0; i < WINDOW_SIZE; i++) 
      var_set_set_elt(witness_var_set_ptr, i);
    
    /* Filter the witness through the alphas */
    lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_and(witness_var_set_ptr, 
		  witness_var_set_ptr, memo_ptr->memo_array[alpha_value]);
    }
    
    /* If at least one element of the witness is set, go on 
       otherwise fail */
    if (var_set_is_empty(witness_var_set_ptr)) {
      var_set_free(witness_var_set_ptr);
      /* Monitoring access time */
      SET_memo_ptr->timings[MEMO_SEARCH_TIME] += util_cpu_time() - lap_time;
      return beta_lsList_ptr;
    }
    
    /* Something was found! */
    ++(SET_memo_ptr->stats[MEMO_SUCCESS]);
    match_table = ALLOC(int, WINDOW_SIZE);
    match_idx = 0;
    
    /* Get indexes of every matching set */
    i = 0;
    while ((i < WINDOW_SIZE) && !var_set_is_empty(witness_var_set_ptr)) {
      if (var_set_get_elt(witness_var_set_ptr, i)) {
	match_table[match_idx++] = i;
	var_set_clear_elt(witness_var_set_ptr, i);
      }
      ++i;
    }

    /* Now try to discard as many betas as possible */
    lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      beta_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      for (i = 0; i < match_idx; i++)
	if (var_set_get_elt(memo_ptr->memo_array[beta_value + real_dim], match_table[i])) break;
      if (i < match_idx)
	list_status = lsDelBefore(t_lsGen, &vertex_lsGeneric);
    }

    /* Monitoring access time */
    SET_memo_ptr->timings[MEMO_SEARCH_TIME] += util_cpu_time() - lap_time;
    
    /* Destroy temporary allocation */
    var_set_free(witness_var_set_ptr);
    FREE(match_table);
    
  }
  
  return beta_lsList_ptr;
}

/* Internal test for a result with a hash table */
lsList* Int_test_hash_memoS(int_memo_hash_t *memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr)
{
  var_set_t  *alphas_var_set_ptr;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  lsStatus   list_status;
  int        alpha_value, beta_value;
  int        lap_time;
  char       *betas_char_ptr;
  
  if (st_count(memo_ptr->memo_hash) != 0) {
    /* Monitoring access time */
    lap_time = util_cpu_time();
    ++(SET_memo_ptr->stats[MEMO_ACCESS]);
    
    /* Create the set corresponding to the list of alphas */
    alphas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(alphas_var_set_ptr, alpha_value);
    }

    if (st_lookup(memo_ptr->memo_hash, (char*)(alphas_var_set_ptr), &betas_char_ptr)) {
      /* Something was found! */
      ++(SET_memo_ptr->stats[MEMO_SUCCESS]);

      /* Now try to discard as many betas as possible */
      lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
	beta_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
	if (var_set_get_elt((var_set_t*)betas_char_ptr, beta_value))
	  list_status = lsDelBefore(t_lsGen, &vertex_lsGeneric);
      }
    }

    /* Monitoring access time */
    SET_memo_ptr->timings[MEMO_SEARCH_TIME] += util_cpu_time() - lap_time;

    /* Destroy temporary allocation */
    var_set_free(alphas_var_set_ptr);
  }

  return beta_lsList_ptr;

}
    
/* Internal storage in a bit matrix (satisfiability)*/
void Int_store_bm_memoS(int_memo_sat_bm_t* memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  int        alpha_value, beta_value, i, cur_set;
  int        lap_time;

  /* Monitoring storage time */
  lap_time = util_cpu_time();
  ++(SET_memo_ptr->stats[MEMO_STORE_ACC]);

  if (!Getf_memoS(COMPACT_STORAGE)) {
    ++(SET_memo_ptr->stats[MEMO_STORAGE]);

    /* Increment the current set modulo WINDOW_SIZE */
    (memo_ptr->cur_set)++;
    if (memo_ptr->cur_set == WINDOW_SIZE) {
      memo_ptr->cur_set = 0;
      /* Growth is now slow */
      if (Getf_memoS(TRASH_SUBSETS)) 
	memo_ptr->growth = 1;
      /* Trashing of sets starts */
      memo_ptr->trashing_sets = 1;
    }
    
    /* If slow growth and TRASH_SUBSETS are set then 
       try to trash subsets only */
    if ((Getf_memoS(TRASH_SUBSETS) && (memo_ptr->growth))) {
      cur_set = Trash_subsets(memo_ptr, memo_ptr->cur_set);
      /* If no subset to trash was found... */
      if (cur_set == WINDOW_SIZE) 
	/* ...return to fast growth */
	memo_ptr->growth = 0;
      else 
	/* ... else update the current set */
	memo_ptr->cur_set = cur_set;
    } 

    if ((memo_ptr->trashing_sets) && (!(memo_ptr->growth)))
      ++(SET_memo_ptr->stats[MEMO_TRASHING]);

    /* Be sure to clear everything before setting */
    for (i = 0; i < (2 * (SET_memo_ptr->dim + 1)); i++) 
      if (memo_ptr->memo_array[i] != NIL(var_set_t))
	var_set_clear_elt(memo_ptr->memo_array[i],memo_ptr->cur_set);
    
    /* Set alphas properly */
    lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(memo_ptr->memo_array[alpha_value],
		      memo_ptr->cur_set);
    }

  } 
  
  /* Set the beta properly (either for a new entry or for an old one) */
  beta_value = V_value(beta_vertex_ptr) + (SET_memo_ptr->dim + 1);
  var_set_set_elt(memo_ptr->memo_array[beta_value], memo_ptr->cur_set);

  /* Monitoring storage time */
  SET_memo_ptr->timings[MEMO_STORE_TIME] += util_cpu_time() - lap_time;

  return;
}

/* Internal storage in a hash table (satisfiability) */
void Int_store_hash_memoS(int_memo_hash_t* memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  int        alpha_value;
  int        lap_time;
  var_set_t  *alphas_var_set_ptr, *betas_var_set_ptr;
  int        table_status;
  char       **value_stGeneric_ptr_ptr;

  /* Monitoring storage time */
  lap_time = util_cpu_time();
  ++(SET_memo_ptr->stats[MEMO_STORE_ACC]);

  if (!Getf_memoS(COMPACT_STORAGE)) {

    /* Transfer the list of alphas to a set */
    alphas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(alphas_var_set_ptr, alpha_value);
    }

    /* Add the new entry in the table or find one if it already exists */
    table_status = st_find_or_add(memo_ptr->memo_hash, (char*)(alphas_var_set_ptr), &value_stGeneric_ptr_ptr);

    if (table_status) 
      /* Retrieve set of betas */
      betas_var_set_ptr = (var_set_t*)(*value_stGeneric_ptr_ptr);
    else {
      /* Build a new set of betas */
      ++(SET_memo_ptr->stats[MEMO_STORAGE]);
      betas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
      *value_stGeneric_ptr_ptr = (char*)betas_var_set_ptr;
      SET_memo_ptr->stats[MEMORY] += (SET_memo_ptr->dim + 1) / sizeof(int);
    }
    /* Keep track of the current set of betas */
    memo_ptr->cur_beta_set = betas_var_set_ptr;

  }
   
  /* Set the beta properly (either for a new entry or for an old one) */
  var_set_set_elt(memo_ptr->cur_beta_set, V_value(beta_vertex_ptr));

  /* Monitoring storage time */
  SET_memo_ptr->timings[MEMO_STORE_TIME] += util_cpu_time() - lap_time;

  return;
}

/* Internal test for dependency with a bit matrix */
vertex_t *Int_test_bm_depS(int_memo_unsat_bm_t *memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr)
{
  var_set_t  *witness_var_set_ptr;
  var_set_t  *alphas_var_set_ptr, *betas_var_set_ptr;
  vertex_t   *rbeta_vertex_ptr;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  lsStatus   list_status;
  int        atom_value, i;
  int        win_size;
  int        lap_time;

  rbeta_vertex_ptr = NIL(vertex_t);

  /* Set the reduced window size */
  win_size = WINDOW_SIZE / DEP_FACTOR;

  if (memo_ptr->cur_dep != -1) {
    /* Monitoring access time */
    ++(SET_memo_ptr->stats[DEP_ACCESS]);
    lap_time = util_cpu_time();

    /* Create a witness, fill it with all the elements */
    witness_var_set_ptr = var_set_new(win_size);
    for (i = 0; i < win_size; i++) 
      var_set_set_elt(witness_var_set_ptr, i);
    
    alphas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    betas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    /* Put the alpha and beta lists into sets */
    lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(alphas_var_set_ptr, atom_value);
    }
    lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(betas_var_set_ptr, atom_value);
    }
    /* Filter the witness through the complement of the alphas */
    /* (seeking for cached subsets of the current set of alphas) */
    for (i = 0; i <= SET_memo_ptr->dim; i++) 
      if ((memo_ptr->dep_array[i] != NIL(var_set_t)) &&
	  (!var_set_get_elt(alphas_var_set_ptr, i))) 
	var_set_and(witness_var_set_ptr, 
		    witness_var_set_ptr, memo_ptr->dep_array[i]);

    /* If at least one element of the witness is set, go on 
       otherwise fail */
    if (var_set_is_empty(witness_var_set_ptr)) {
      var_set_free(alphas_var_set_ptr);
      var_set_free(betas_var_set_ptr);
      var_set_free(witness_var_set_ptr);
      /* Monitoring access time */
      SET_memo_ptr->timings[DEP_SEARCH_TIME] += util_cpu_time() - lap_time;
      return rbeta_vertex_ptr;
    }

    /* Now try to find an inconsistent beta */
    for (i = 0; i < win_size; i++) 
      if (var_set_get_elt(witness_var_set_ptr, i)) {
	/* Is the beta label contained in the current list of betas? */
	if (var_set_get_elt(betas_var_set_ptr, memo_ptr->dep_beta[i])) {
	  ++(SET_memo_ptr->stats[DEP_SUCCESS]);
	  /* case (ii) applies: the current test is uncosistent */
	  break;
	}
      }

    /* Monitoring access time */
    SET_memo_ptr->timings[DEP_SEARCH_TIME] += util_cpu_time() - lap_time;

    if (i < win_size) {
      /* If the loop ended before reaching winsize an inconsistency was found */
      alpha_lsList_ptr = NIL(lsList);
      lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
	atom_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
	if (atom_value ==  memo_ptr->dep_beta[i]) {
	  rbeta_vertex_ptr = UNCAST_VERTEX_ITEM(vertex_lsGeneric);
	  break;
	}
      }
      /* The loop ALWAYS breaks */
      list_status = lsFinish(t_lsGen);
    } 

    /* Destroy temporary allocations */
    var_set_free(alphas_var_set_ptr);
    var_set_free(betas_var_set_ptr);
    var_set_free(witness_var_set_ptr);
  }

  return rbeta_vertex_ptr;
}

/* Internal test for dependency with a hash table */
vertex_t *Int_test_hash_depS(int_memo_hash_t* memo_ptr, lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr)
{
  var_set_t  *alphas_var_set_ptr;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  vertex_t   *rbeta_vertex_ptr;
  int        alpha_value, beta_value, found;
  int        lap_time;
  char       *betas_char_ptr;

  rbeta_vertex_ptr = NIL(vertex_t);

  if (st_count(memo_ptr->memo_hash) != 0) {
    /* Monitoring access time */
    lap_time = util_cpu_time();
    ++(SET_memo_ptr->stats[DEP_ACCESS]);
    found = 0;
    
    /* Create the set corresponding to the list of alphas */
    alphas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
      alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
      var_set_set_elt(alphas_var_set_ptr, alpha_value);
    }

    if (st_lookup(memo_ptr->memo_hash, (char*)(alphas_var_set_ptr), &betas_char_ptr)) {
      /* Something was found! */
      ++(SET_memo_ptr->stats[MEMO_SUCCESS]);

      /* Now look for an inconsistent beta */
      lsForEachItem(*beta_lsList_ptr, t_lsGen, vertex_lsGeneric) {
	beta_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
	if (var_set_get_elt((var_set_t*)betas_char_ptr, beta_value)) {
	  break; found = 1;
	}
      }

      /* The loop was broken? */
      if (found) {
	lsFinish(t_lsGen);
	rbeta_vertex_ptr = (vertex_t*)vertex_lsGeneric;
      }
    }

    /* Monitoring access time */
    SET_memo_ptr->timings[MEMO_SEARCH_TIME] += util_cpu_time() - lap_time;

    /* Destroy temporary allocation */
    var_set_free(alphas_var_set_ptr);
  }
    
  return rbeta_vertex_ptr;
}

/* Store a dependency with a bit matrix */
void Int_store_bm_depS(int_memo_unsat_bm_t *memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  int        i, alpha_value;
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  int        win_size;
  int        lap_time;


  win_size = WINDOW_SIZE / DEP_FACTOR;
  ++(SET_memo_ptr->stats[DEP_STORAGE]);
  ++(SET_memo_ptr->stats[DEP_STORE_ACC]);

  /* Monitoring storage time */
  lap_time = util_cpu_time();

  /* Increment the current set modulo win_size */
  (memo_ptr->cur_dep)++;
  if (memo_ptr->cur_dep == win_size) {
    memo_ptr->cur_dep = 0;
    memo_ptr->trashing_deps = 1;
  }

  if (memo_ptr->trashing_deps)
    ++(SET_memo_ptr->stats[DEP_TRASHING]);

  /* Be sure to clear everything */
  for (i = 0; i <= (SET_memo_ptr->dim); i++) 
    if (memo_ptr->dep_array[i] != NIL(var_set_t))
      var_set_set_elt(memo_ptr->dep_array[i],memo_ptr->cur_dep);
  
  /* Set alphas properly 
     (the complement of the set of alphas is stored) */
  lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
    alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
    var_set_clear_elt(memo_ptr->dep_array[alpha_value],
		      memo_ptr->cur_dep);
  }
  /* Label the dependency set with the beta */
  memo_ptr->dep_beta[memo_ptr->cur_dep] = V_value(beta_vertex_ptr);

  /* Monitoring storage time */
  SET_memo_ptr->timings[DEP_STORE_TIME] += util_cpu_time() - lap_time;

  return;
}

/* Internal storage in a hash table (unsatisfiability) */
void Int_store_hash_depS(int_memo_hash_t *memo_ptr, lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  lsGen      t_lsGen;
  lsGeneric  vertex_lsGeneric;
  int        alpha_value;
  int        lap_time;
  var_set_t  *alphas_var_set_ptr, *betas_var_set_ptr;
  int        table_status;
  char       **value_stGeneric_ptr_ptr;

  /* Monitoring storage time */
  lap_time = util_cpu_time();
  ++(SET_memo_ptr->stats[DEP_STORE_ACC]);

  /* Transfer the list of alphas to a set */
  alphas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
  lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
    alpha_value = V_value(UNCAST_VERTEX_ITEM(vertex_lsGeneric));
    var_set_set_elt(alphas_var_set_ptr, alpha_value);
  }

  /* Add the new entry in the table or find one if it already exists */
  table_status = st_find_or_add(memo_ptr->memo_hash, (char*)(alphas_var_set_ptr), &value_stGeneric_ptr_ptr);

  if (table_status) 
    /* Retrieve set of betas */
    betas_var_set_ptr = (var_set_t*)(*value_stGeneric_ptr_ptr);
  else {
    /* Build a new set of betas */
    ++(SET_memo_ptr->stats[DEP_STORAGE]);
    betas_var_set_ptr = var_set_new(SET_memo_ptr->dim + 1);
    *value_stGeneric_ptr_ptr = (char*)betas_var_set_ptr;
  }
   
  /* Set the beta properly */
  var_set_set_elt(betas_var_set_ptr, V_value(beta_vertex_ptr));

  /* Monitoring storage time */
  SET_memo_ptr->timings[DEP_STORE_TIME] += util_cpu_time() - lap_time;

  return;
}

/* Interface to var_set_hash */
int Var_set_hash(char *key, int modulus)
{
  return (int)(var_set_hash((var_set_t*)(key)) % (unsigned int)modulus);
}

/* Trashing of subsets */
int Trash_subsets(int_memo_sat_bm_t *memo_ptr, int cur_set)
{
  var_set_t  *witness_var_set_ptr;
  int        *modal_atoms;
  int        max_atoms, i, run_set;
   
   modal_atoms = ALLOC(int, (2 * SET_memo_ptr->dim + 1));
  run_set = cur_set;
  while (run_set < WINDOW_SIZE) {
    max_atoms = 0;
    /* Collect all the atoms of run_set */
    for (i = 0; i <= (2 * SET_memo_ptr->dim); i++) 
      if (var_set_get_elt(memo_ptr->memo_array[i], run_set)) 
	modal_atoms[max_atoms++] = i;

    /* Create a witness, fill it with all the elements but the current */
    witness_var_set_ptr = var_set_new(WINDOW_SIZE);
    for (i = 0; i < WINDOW_SIZE; i++) 
      if (i != run_set) var_set_set_elt(witness_var_set_ptr, i);

    /* Now look for possible supersets in the structure 
       (other than run_set itself!)*/
    for (i = 0; i < max_atoms; i++) 
      var_set_and(witness_var_set_ptr, 
		  witness_var_set_ptr, memo_ptr->memo_array[modal_atoms[i]]);

    /* If the resulting set is not empty, supersets were found
       so run_set can be trashed */
    if (!var_set_is_empty(witness_var_set_ptr)) {
      var_set_free(witness_var_set_ptr);
      break;
    }
	
    /* No supersets found, try with the next set */
    var_set_free(witness_var_set_ptr);
    ++run_set;
  }
      
  FREE(modal_atoms);
  return run_set;
}
