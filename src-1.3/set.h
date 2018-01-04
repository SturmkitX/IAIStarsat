/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE set.h - *SAT 1.3 */
/*  Caching for sets of atoms */

/*  *********************************************************************** */
/*  *********************************************************************** */
   
/*  There are two main data structures:
       - a hash table providing exact matching retrieval
       - a bit matrix providing subset (superset) queries
    plus a side data structure for dynamic dependencies.   
    The following storage functionalities are provided: 
       - cache for satisfiability results 
       - cache for unsatisfiability results (static dependencies) 
       - cache for dynamic dependencies
    together with the following test functionalities: 
       - test for satisfiability/unsatisfiability results 
       - test for modal relevance (FAST):              
               * based on static dependencies, if A & B -> C 
	         then A & B & C <-> A & B (prunes the number of alphas)
	       * based on dynamic dependencies, if backtrack occurred on a 
	         []phi assigned to true, there is an open world where -phi,
		 So -[]phi is irrelevant on the descendant branches (prunes 
		 the number of betas)
*/

#include "limits.h"
#include "math.h"

/* GLU modules */
#include "util.h"
#include "var_set.h"
#include "st.h"

/* *SAT modules */
#include "dp_sat.h"
#include "statistics.h"

#ifndef MEMO
#define MEMO

/* Constants for the data structure 
*/
#define MAX_FLAGS  10      /* No more than 10 flags */
#define MAX_STATS  20      /* No more than 20 statistics */

/* Flags */
#define HASH_STORAGE       0 /* Use the hash table if 1, the bit matrix if 0 */

#define GET_MODELS         1 /* Test for satisfiable worlds */
#define GET_DEPENDENCIES   2 /* Test for dependencies */
#define STATIC_FAST        3 /* Test for static modal relevance */
#define DYNAMIC_FAST       4 /* Test for dynamic modal relevance */  
#define LEVEL_CACHE        5 /* Cache every modal "level" independently */
#define COMPACT_STORAGE    6 /* Try to factorize storage */
#define TRASH_SUBSETS      7 /* Try to trash subsets only */

/* Statistics */
#define MEMO_ACCESS     0  /* # of searches for satisfiable subtests in cache */
#define MEMO_SUCCESS    1  /* # of satisfiable subtests found in cache */
#define DEP_ACCESS      2  /* # of searches for dependencies */
#define DEP_SUCCESS     4  /* # of unsatisfiable subtests found in cache */
#define SFAST_ACCESS    5  /* # of accesses trying to prune alphas */
#define SFAST_SUCCESS   6  /* # of successes in pruning alphas */
#define DFAST_ACCESS    7  /* # of accesses trying to prune betas */
#define DFAST_SUCCESS   8  /* # of successes in pruning betas */
#define MEMORY          9  /* Bytes allocated */
#define MEMO_STORAGE   10  /* Number of sets stored */
#define MEMO_STORE_ACC 11  /* Number of accesses for storing data */
#define MEMO_TRASHING  12  /*   "    of sets trashed */
#define DEP_STORAGE    13  /*   "    of static dependencies stored */
#define DEP_STORE_ACC  14  /* Number of accesses for storing data */
#define DEP_TRASHING   15  /*   "    of dependencies trashed */
#define DFAST_STORAGE  16  /*   "    of dynamic dependencies stored */

/* Clocks */
#define MEMO_SEARCH_TIME  0 /* Time spent searching for satisfiable results */
#define MEMO_STORE_TIME   1 /*  "     "   storing satisfiable results */
#define DEP_SEARCH_TIME   2 /*  "     "   searching for unsatisfiable results */
#define DEP_STORE_TIME    3 /*  "     "   storing unsatisfiable results */
#define SFAST_TIME        4 /*  "     "   trying to prune alphas */
#define DFAST_TIME        5 /*  "     "   trying to prune betas */

/* Expected ratio sets vs. dependencies */
#define DEP_FACTOR    1

/* The memoizing data structure
 */

/* Caching satisfiable subtests with a bit matrix */
typedef struct int_memo_sat_bm {
  var_set_t **memo_array;   /* the data sets */
  int       cur_set;        /* index to the next data set */
  int       growth;         /* 0 = fast growth, 1 = slow growth */  
  int       compact;        /* 0 = add, 1 = stay compact */
  int       trashing_sets;  /* Sets trashing flag */ 
} int_memo_sat_bm_t;

/* Caching dependencies with a bit matrix */
typedef struct int_memo_unsat_bm {
  var_set_t **dep_array;    /* the dependency sets */
  int       *dep_beta;      /* the dependency labels */
  int       cur_dep;        /* index to the next dependency set */
  int       trashing_deps;  /* Dependencies trashing flag */ 
} int_memo_unsat_bm_t;

/* Caching subtests with a hash table */
typedef struct int_memo_hash {
  st_table  *memo_hash;     /* the data sets */
  var_set_t *cur_beta_set;  /* reference to the current set of beta */
  int       compact;        /* 0 = add, 1 = stay compact */
} int_memo_hash_t;

/* Caching irrelevant betas */
typedef struct int_memo_betas {
  int       *dfast_array;   /* dynamically irrelevant modal atoms (indexed 
			       by atoms) */
  int       **dfast_stack;  /* dynamically irrelevant modal atoms (indexed 
			       chronologically) */
  int       dfast_idx;      /* valid dynamic dependencies (stack index) */
} int_memo_betas_t;

/* A single modal level */
typedef struct int_memo {
  char                 *memo_sat;
  char                 *memo_unsat;
  int_memo_unsat_bm_t  *memo_static_fast;
  int_memo_betas_t     *memo_dynamic_fast;
} int_memo_t;

/* The whole cache */
typedef struct memo {
  int_memo_t   *memo_of_level[MAX_DEPTH]; /* caches in every modal "level" */
  int          level;                     /* current modal "level" */
  int          dim;                       /* maximum number of atoms */ 
  int          flags[MAX_FLAGS];          /* flags */
  int          stats[MAX_STATS];          /* statistics */     
  int          timings[MAX_STATS];        /* timings */
  statistics_t *statistics_ptr;           /* a pointer to formula's statistics */
} memo_t;

/* *********************************************************************** */
/* Initialize and clear memoizing */
/* *********************************************************************** */
void Alloc_memoS(int dim, statistics_t *statistics_ptr);
void Init_memoS();
void Clear_memoS();
void Force_no_memoS();

/* *********************************************************************** */
/* Accessing the structure */
/* *********************************************************************** */
/* Test if the structure is being used; return 1 if so, 0 otherwise */
int Use_memoS();

/* Set & get flags */
void Setf_memoS(int flag);
void Clearf_memoS(int flag);
int  Getf_memoS(int flag);

/* Get stats, times, level */
int Stats_memoS(int stat);
int Time_memoS(int time);
int Get_level_memoS();

/* Increment and decrement modal level */
void Inc_level_memoS();
void Dec_level_memoS();

/* Returns a sublist of beta_lsList_ptr containing betas that are not 
   tested with the current set of alphas yet (supersets are checked if
   caching is with a bit matrix). beta_lsList is destructively updated. 
*/
lsList *Test_memoS(lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr);

/* Stores a list of alphas that were tested with the corresponding
   beta.  If COMPACT_STORAGE is set, the routine assumes that the beta
   should be added in the current set of alphas: alphas ARE NOT
   CHECKED!!!  If TRASH_SUBSETS is set and caching is with a bit matrix,
   the routine alternates a "fast" (destructive) growth mode and a "slow"
   (conservative) growth mode. */
void Store_memoS(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr);

/* If at least one of the betas was tested inconsistent with the
   current set (or any subset if caching is with a bit matrix) of the
   alphas the return value is the pointer to the vertex that gave the
   inconsistency, else the return value is NIL(vertex_t). */
vertex_t *Test_depS(lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr);

/* Remembers that the list of alphas implies the beta, i.e. it
   stores a dependency (always fast growth) */
void Store_depS(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr); 

/* Returns a sublist of alpha_lsList_ptr containing dependency-free alphas. 
   If at least one of the betas was tested inconsistent with the
   current set (or any subset) of the alphas then
   alpha_lsList_ptr is unchanged and rbeta_vertex_ptr_ptr points to a non-NIL
   value */
lsList *Test_sfastS(lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr,
		    vertex_t **rbeta_vertex_ptr_ptr);

/* Stores a static dependency */
void Store_sfastS(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr); 


/* Returns a sublist of beta_lsList_ptr containing relevant betas only. */
lsList *Test_dfastS(lsList *beta_lsList_ptr);

/* Stores an irrelevant beta and stamps it with the current stack index */
void Store_dfastS(vertex_t *beta_vertex_ptr, int cur_stack_idx);

/* Updates the cache for dynamic fast: entries that were recorded with a
   stack index higher than the current are invalidated */
void Update_dfastS(int cur_stack_idx);

/* Clears the cache for dynamic fast: every entry is invalidated */
void Clear_dfastS();

#endif






