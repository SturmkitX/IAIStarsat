/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE kdp.c - *SAT 1.3 */
/*  Consistency check in logic K */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "kdp.h"

/* Return types for internal consistency check */

#define REC_CONSISTENT   0  /* Consistency   proved by recursive test */
#define REC_UNCONSISTENT 1  /* Unconsistency   "        "         "   */
#define MEM_CONSISTENT   2  /* Consistency   proved by cache access */
#define MEM_UNCONSISTENT 3  /* Unconsistency   "        "       "   */

/* *********************************************************************** */
/* The functions for testing K consistency of an assignment */
/* *********************************************************************** */

/* Prototypes ------------------------------------------------------------ */
int Plain_test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr);
int Jumpy_test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr);

vertex_t *Int_test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr,
				 lsList *rec_alpha_lsList_ptr, lsList *rec_beta_lsList_ptr,
				 lsList *mem_alpha_lsList_ptr, lsList *mem_beta_lsList_ptr,
				 int *cons_res_ptr);

void Set_K_jump_point(image_t *cur_image_ptr, dag_t *dag_ptr, 
		      lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr);

/* Interface -------------------------------------------------------------- */
int Test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr)
{
  if (EARLY_JUMPING) 
    return Jumpy_test_K_consistency(cur_image_ptr, dag_ptr);
  else
    return Plain_test_K_consistency(cur_image_ptr, dag_ptr);  
}

/* Private functions ------------------------------------------------------ */

/* Plain consistency check: eventually fires backjumping on inconsistency */
int Plain_test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr)
{
  int          cons_res;
  st_table     *agents_st_table_ptr;
  lsList       *alpha_lsList_ptr, *beta_lsList_ptr;
  lsList       *mem_alpha_lsList_ptr, *mem_beta_lsList_ptr;
  lsList       *rec_alpha_lsList_ptr, *rec_beta_lsList_ptr;
  st_generator *at_st_generator;
  stGeneric    ak_stGeneric, av_stGeneric;
  vertex_t     *beta_vertex_ptr;

  /* This is the classification for agents */
  agents_st_table_ptr = st_init_table(st_numcmp, st_numhash);
  /* First of all classify alphas and betas for agents */
  Classify_agents(cur_image_ptr, dag_ptr, agents_st_table_ptr);
  
  /* Now iterate over agents */
  beta_vertex_ptr = NIL(vertex_t);
  st_foreach_item(agents_st_table_ptr, at_st_generator, &ak_stGeneric, &av_stGeneric) {
    /* These are the current agent alphas and betas */
    alpha_lsList_ptr = Alpha_lsList_ptr(UNCAST_AGENT(av_stGeneric));
    beta_lsList_ptr = Beta_lsList_ptr(UNCAST_AGENT(av_stGeneric));
 
    if (PFAST) {

      /* Propositional FAST is active */
      switch (CACHE_AND_FAST) {
      case 0:
	/* There is no need to separate lists: both are purged of irrelevants  */
	mem_alpha_lsList_ptr = rec_alpha_lsList_ptr = Keep_relevant_atoms(cur_image_ptr, alpha_lsList_ptr);
	mem_beta_lsList_ptr = rec_beta_lsList_ptr = Keep_relevant_atoms(cur_image_ptr, beta_lsList_ptr);
	break;
      case 1:
	/* mem_alpha and mem_beta are copies containing only relevant atoms */
	mem_alpha_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, alpha_lsList_ptr);
	rec_alpha_lsList_ptr = alpha_lsList_ptr;
	mem_beta_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, beta_lsList_ptr);
	rec_beta_lsList_ptr = beta_lsList_ptr;	
	break;
      case 2:
	/* rec_alpha and rec_beta are copies containint only relevant atoms */
	rec_alpha_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, alpha_lsList_ptr);
	mem_alpha_lsList_ptr = alpha_lsList_ptr;
	rec_beta_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, beta_lsList_ptr);
	mem_beta_lsList_ptr = beta_lsList_ptr;	
	break;
      }
    
    } else {

      /* Propositional FAST is not active */
      if ((CACHE_AND_FAST != 0) && MFAST) {
	/* Since modal FAST is active separate copies are needed */
	mem_alpha_lsList_ptr = alpha_lsList_ptr;
	rec_alpha_lsList_ptr = ALLOC(lsList,1);
	*rec_alpha_lsList_ptr = lsCopy(*alpha_lsList_ptr, NULL);
	mem_beta_lsList_ptr = beta_lsList_ptr;
	rec_beta_lsList_ptr = ALLOC(lsList,1);
	*rec_beta_lsList_ptr = lsCopy(*beta_lsList_ptr, NULL);
      } else {
	/* There is no need to separate lists */
	mem_alpha_lsList_ptr = rec_alpha_lsList_ptr = alpha_lsList_ptr;
	mem_beta_lsList_ptr = rec_beta_lsList_ptr = beta_lsList_ptr;
      }

    }
      
    /* If non NIL(vertex_t), beta_vertex_ptr generated an unconsistency */
    beta_vertex_ptr = Int_test_K_consistency(cur_image_ptr, dag_ptr, 
					     mem_alpha_lsList_ptr, mem_beta_lsList_ptr,
					     rec_alpha_lsList_ptr, rec_beta_lsList_ptr,
					     &cons_res);

    /* Unconsistent? */
    if (beta_vertex_ptr != NIL(vertex_t)) {

      if (BACK_JUMPING) {
	/* Use the check that turned out to be inconsistent 
	   to backjump in propositional search tree */
	Inc_param(Image_monitor_ptr(cur_image_ptr), BJ_CALLS);
	if (cons_res == REC_UNCONSISTENT) 
	  Set_K_jump_point(cur_image_ptr, dag_ptr, rec_alpha_lsList_ptr, beta_vertex_ptr);
	else
	  Set_K_jump_point(cur_image_ptr, dag_ptr, mem_alpha_lsList_ptr, beta_vertex_ptr);
      }

      /* clean the generator for the agents */
      st_free_gen(at_st_generator);
    }

    /* Cleaning up additional copies */
    if (PFAST) {
      switch (CACHE_AND_FAST) {
      case 0:
	/* Lists will be purged by Clean_agent */
	break;
      case 1:
	/* mem_alpha and mem_beta are copies and must be destroyed */
	lsDestroy(*mem_alpha_lsList_ptr, NULL); FREE(mem_alpha_lsList_ptr);
	lsDestroy(*mem_beta_lsList_ptr, NULL); FREE(mem_beta_lsList_ptr);
	break;
      case 2:
	/* rec_alpha and rec_beta are copies and must be destroyed */
	lsDestroy(*rec_alpha_lsList_ptr, NULL); FREE(rec_alpha_lsList_ptr);
	lsDestroy(*rec_beta_lsList_ptr, NULL); FREE(rec_beta_lsList_ptr);
	break;
      }
      
    } else {
      
      /* Propositional FAST is not active */
      if ((CACHE_AND_FAST != 0) && MFAST) {
	/* rec_alpha and rec_beta are copies and must be destroyed */
	lsDestroy(*rec_alpha_lsList_ptr, NULL); FREE(rec_alpha_lsList_ptr);
	lsDestroy(*rec_beta_lsList_ptr, NULL); FREE(rec_beta_lsList_ptr);
      }
    }

    if (beta_vertex_ptr != NIL(vertex_t)) break;

  } /* end of the loop on agents */

  /* Cleaning up the agents table */
  st_foreach_item(agents_st_table_ptr, at_st_generator, &ak_stGeneric, &av_stGeneric) {
    Clear_agent(av_stGeneric);
  }
  st_free_table(agents_st_table_ptr);    
  
  return (beta_vertex_ptr == NIL(vertex_t));
}

/* Perform a smart early pruning (the minimum number of tests is done) */
int Jumpy_test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr)
{
  int          first_modal_atom, last_modal_atom;
  int          i, cur_atom, ag_num;
  int          result;
  lsList       *beta_lsList_ptr, *alpha_lsList_ptr;
  lsList       *new_alpha_lsList_ptr, *new_beta_lsList_ptr;
  lsList       *mem_alpha_lsList_ptr, *mem_beta_lsList_ptr;
  lsList       *rec_alpha_lsList_ptr, *rec_beta_lsList_ptr;
  vertex_t     *cur_vertex_ptr, *beta_vertex_ptr;
  st_table     *agents_st_table_ptr;
  st_generator *at_st_generator;
  stGeneric    ak_stGeneric, av_stGeneric;
  int          cons_res;

  first_modal_atom = SPREAD(Lpa(dag_ptr) + 1);
  last_modal_atom = SPREAD(Lma(dag_ptr));
  beta_vertex_ptr = NIL(vertex_t);

  /* This is the classification for agents */
  agents_st_table_ptr = st_init_table(st_numcmp, st_numhash);
  Classify_agents_light(cur_image_ptr, dag_ptr, agents_st_table_ptr);

  alpha_lsList_ptr = ALLOC(lsList, 1); beta_lsList_ptr = ALLOC(lsList, 1);
  new_alpha_lsList_ptr = ALLOC(lsList, 1); new_beta_lsList_ptr = ALLOC(lsList, 1);

  /* Iterate over agents */
  result = 1;
  st_foreach_item(agents_st_table_ptr, at_st_generator, &ak_stGeneric, &av_stGeneric) {
    ag_num = UNCAST_KEY(ak_stGeneric);

    /* Create old and new lists for each agent */
    *alpha_lsList_ptr = lsCreate(); *beta_lsList_ptr = lsCreate();
    *new_alpha_lsList_ptr = lsCreate(); *new_beta_lsList_ptr = lsCreate();  

    i = 0;
    /* If jumping already happened, we might want to skip some tests */
    if (Last_stack_idx(cur_image_ptr) > 0) 
      while (i < (Last_stack_idx(cur_image_ptr))) {
	/* Include all the significant alphas and betas into the "old" lists */
	/* Look for a relevant modal atom (must be the same agent) */
	IF_MODAL_ATOM
	  /* Store the atom in the appropriate list */
	  if (Value(cur_image_ptr)[cur_atom] == TT) 
	    lsNewEnd(*alpha_lsList_ptr, CAST_VERTEX_ITEM(cur_vertex_ptr), LS_NH);
	  else 
	    lsNewEnd(*beta_lsList_ptr, CAST_VERTEX_ITEM(cur_vertex_ptr), LS_NH);
	END_IF    
	++i;
      }

    /* Look for an early inconsistency */
    /* Running through the stack (up to the end) */
    while (i < Stack_idx(cur_image_ptr)) {
      /* Get the current atom in the stack */
      /* Look for a relevant modal atom (must be the same agent) */
      IF_MODAL_ATOM
	/* Store the atom in the appropriate list */
	if (Value(cur_image_ptr)[cur_atom] == TT) 
	  lsNewEnd(*new_alpha_lsList_ptr, CAST_VERTEX_ITEM(cur_vertex_ptr), LS_NH);
	else 
	  lsNewEnd(*new_beta_lsList_ptr, CAST_VERTEX_ITEM(cur_vertex_ptr), LS_NH);
      END_IF
      ++i;
    }

    /* See what happened to the lists of alphas and betas */
    /* If there are no new alphas and betas, just go on! */
    if ((lsLength(*new_beta_lsList_ptr) != 0) || 
	(lsLength(*new_alpha_lsList_ptr) != 0)) {

      if (lsLength(*new_beta_lsList_ptr) == 0) {
	if (lsLength(*new_alpha_lsList_ptr) != 0) 
	  /* there were no new betas but some new alphas */
	  Merge_formulae(alpha_lsList_ptr, new_alpha_lsList_ptr);
      } else {
	if (lsLength(*new_alpha_lsList_ptr) == 0) 
	  /* There were some betas but no alphas: do not test the old betas again */
	  Swap_formulae(&beta_lsList_ptr, &new_beta_lsList_ptr);
	else {
	  /* Everything changed: test everything */
	  Merge_formulae(alpha_lsList_ptr, new_alpha_lsList_ptr);
	  Merge_formulae(beta_lsList_ptr, new_beta_lsList_ptr);
	}
      }
      
      if (PFAST) {
	
	/* Propositional FAST is active */
	switch (CACHE_AND_FAST) {
	case 0:
	  /* There is no need to separate lists: both are purged of irrelevants  */
	  mem_alpha_lsList_ptr = rec_alpha_lsList_ptr = Keep_relevant_atoms(cur_image_ptr, alpha_lsList_ptr);
	  mem_beta_lsList_ptr = rec_beta_lsList_ptr = Keep_relevant_atoms(cur_image_ptr, beta_lsList_ptr);
	  break;
	case 1:
	  /* mem_alpha and mem_beta are copies containing only relevant atoms */
	  mem_alpha_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, alpha_lsList_ptr);
	  rec_alpha_lsList_ptr = alpha_lsList_ptr;
	  mem_beta_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, beta_lsList_ptr);
	  rec_beta_lsList_ptr = beta_lsList_ptr;	
	  break;
	case 2:
	  /* rec_alpha and rec_beta are copies containint only relevant atoms */
	  rec_alpha_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, alpha_lsList_ptr);
	  mem_alpha_lsList_ptr = alpha_lsList_ptr;
	  rec_beta_lsList_ptr = Copy_relevant_atoms(cur_image_ptr, beta_lsList_ptr);
	  mem_beta_lsList_ptr = beta_lsList_ptr;	
	  break;
	}
	
      } else {
	
	/* Propositional FAST is not active */
	if ((CACHE_AND_FAST != 0) && MFAST) {
	  /* Since modal FAST is active separate copies are needed */
	  mem_alpha_lsList_ptr = alpha_lsList_ptr;
	  rec_alpha_lsList_ptr = ALLOC(lsList,1);
	  *rec_alpha_lsList_ptr = lsCopy(*alpha_lsList_ptr, NULL);
	  mem_beta_lsList_ptr = beta_lsList_ptr;
	  rec_beta_lsList_ptr = ALLOC(lsList,1);
	  *rec_beta_lsList_ptr = lsCopy(*beta_lsList_ptr, NULL);
	} else {
	  /* There is no need to separate lists */
	  mem_alpha_lsList_ptr = rec_alpha_lsList_ptr = alpha_lsList_ptr;
	  mem_beta_lsList_ptr = rec_beta_lsList_ptr = beta_lsList_ptr;
	}
	
      }

      /* The consistency check */
      beta_vertex_ptr =
	Int_test_K_consistency(cur_image_ptr, dag_ptr, 
			       mem_alpha_lsList_ptr, mem_beta_lsList_ptr, 
			       rec_alpha_lsList_ptr, rec_beta_lsList_ptr, &cons_res);

      if (beta_vertex_ptr != NIL(vertex_t)) {
	
	if (BACK_JUMPING) {
	  /* Use the check that turned out to be inconsistent 
	     to backjump in propositional search tree */
	  Inc_param(Image_monitor_ptr(cur_image_ptr), BJ_CALLS);
	  if (cons_res == REC_UNCONSISTENT) 
	    Set_K_jump_point(cur_image_ptr, dag_ptr, rec_alpha_lsList_ptr, beta_vertex_ptr);
	  else
	    Set_K_jump_point(cur_image_ptr, dag_ptr, mem_alpha_lsList_ptr, beta_vertex_ptr);
	}
	
	st_free_gen(at_st_generator);
      }

      /* Cleaning up additional copies */
      if (PFAST) {
	switch (CACHE_AND_FAST) {
	case 0:
	  /* Lists will be purged by Clean_agent */
	  break;
	case 1:
	  /* mem_alpha and mem_beta are copies and must be destroyed */
	  lsDestroy(*mem_alpha_lsList_ptr, NULL); FREE(mem_alpha_lsList_ptr);
	  lsDestroy(*mem_beta_lsList_ptr, NULL); FREE(mem_beta_lsList_ptr);
	  break;
	case 2:
	  /* rec_alpha and rec_beta are copies and must be destroyed */
	  lsDestroy(*rec_alpha_lsList_ptr, NULL); FREE(rec_alpha_lsList_ptr);
	  lsDestroy(*rec_beta_lsList_ptr, NULL); FREE(rec_beta_lsList_ptr);
	  break;
	}
	
      } else {
	
	/* Propositional FAST is not active */
	if ((CACHE_AND_FAST != 0) && MFAST) {
	  /* rec_alpha and rec_beta are copies and must be destroyed */
	  lsDestroy(*rec_alpha_lsList_ptr, NULL); FREE(rec_alpha_lsList_ptr);
	  lsDestroy(*rec_beta_lsList_ptr, NULL); FREE(rec_beta_lsList_ptr);
	}
      }

    }

    /* Clean the lists for the next agent */
    lsDestroy(*alpha_lsList_ptr, NULL); lsDestroy(*beta_lsList_ptr, NULL);
    lsDestroy(*new_alpha_lsList_ptr, NULL); lsDestroy(*new_beta_lsList_ptr, NULL);

    if (beta_vertex_ptr != NIL(vertex_t)) break; /* break the loop on agents */

  } /* end of the loop on agents */

  /* Clean the allocations */
  FREE(alpha_lsList_ptr); FREE(new_alpha_lsList_ptr);
  FREE(beta_lsList_ptr); FREE(new_beta_lsList_ptr);
  st_free_table(agents_st_table_ptr);    

  if (beta_vertex_ptr == NIL(vertex_t)) {
    /* Declare consistent the current stack */
    Last_stack_idx(cur_image_ptr) = Stack_idx(cur_image_ptr);
    return 1;
  } else {
    /* Set an immediate jump point, unless backjumping occured */
    if (!BACK_JUMPING) Jump_point(cur_image_ptr) = Backup_idx(cur_image_ptr);
    return 0;
  }
}

/* Core loop */
vertex_t *Int_test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr,
				 lsList *rec_alpha_lsList_ptr, lsList *rec_beta_lsList_ptr,
				 lsList *mem_alpha_lsList_ptr, lsList *mem_beta_lsList_ptr,
				 int *cons_res_ptr)
{
  int          result;
  int          list_status;
  int          max_mem, saved_max;
  lsGen        beta_lsGen;
  lsList       *alphas_formula_lsList_ptr, *to_test_lsList_ptr;
  lsList       *fast_alpha_lsList_ptr, *fast_beta_lsList_ptr;
  lsGeneric    beta_lsGeneric;
  vertex_t     *beta_vertex_ptr;
  image_t      *new_image_ptr;  

  beta_vertex_ptr = NIL(vertex_t);

  if (Use_memoS()) {
    /* Caching is active */

    if (MFAST) {
      /* Modal FAST is active */
      /* What kind of interaction between caching and modal FAST? */
      if ((CACHE_AND_FAST == 1) || 
	  (CACHE_AND_FAST == 2)) {
	/* rec and mem are truly different lists */
	if (CACHE_AND_FAST == 1) {
	  /* Apply modal FAST only for searching in cache */
	  fast_alpha_lsList_ptr = mem_alpha_lsList_ptr;
	  fast_beta_lsList_ptr = mem_alpha_lsList_ptr;
	}
	if (CACHE_AND_FAST == 2) {
	  /* Apply modal FAST only for rec. call and storing */
	  fast_alpha_lsList_ptr = rec_alpha_lsList_ptr;
	  fast_beta_lsList_ptr = rec_alpha_lsList_ptr;
	}
      } else {
	/* rec and mem are the same list */
	fast_alpha_lsList_ptr = rec_alpha_lsList_ptr;
	fast_beta_lsList_ptr = rec_alpha_lsList_ptr;
      }
      /* What modal FAST should be performed? */
      if (Getf_memoS(STATIC_FAST)) {
	/* Static fast */
	fast_alpha_lsList_ptr = Test_sfastS(fast_alpha_lsList_ptr, fast_beta_lsList_ptr,
					  &beta_vertex_ptr);
	if (Getf_memoS(GET_DEPENDENCIES) && (beta_vertex_ptr != NIL(vertex_t)))
	  /* An inconsistency was found!! */
	  *cons_res_ptr = MEM_UNCONSISTENT;
	  return beta_vertex_ptr;
      }
      if (Getf_memoS(DYNAMIC_FAST))
	/* Dynamic fast */
	fast_beta_lsList_ptr = Test_dfastS(fast_beta_lsList_ptr);
    }
      
    /* Find out if the formula is unconsistent (static FAST subsumes this testing) */
    if (Getf_memoS(GET_DEPENDENCIES) && !Getf_memoS(STATIC_FAST)) {
      beta_vertex_ptr  = Test_depS(mem_alpha_lsList_ptr, mem_beta_lsList_ptr);
      /* An inconsistency was found!! */
      if (beta_vertex_ptr != NIL(vertex_t)) {
	*cons_res_ptr = MEM_UNCONSISTENT;
	return beta_vertex_ptr;
      }
    }

    /* Eventually filter the list of betas through the memozing structure */
    if (Getf_memoS(GET_MODELS))
      mem_beta_lsList_ptr = Test_memoS(mem_alpha_lsList_ptr, mem_beta_lsList_ptr);
    /* Nothing to check!! */
    if (lsLength(*mem_beta_lsList_ptr) == 0) {
      *cons_res_ptr = MEM_CONSISTENT;
      return beta_vertex_ptr;
    }

  } 

  /* Monitor */
  saved_max = Get_param(Image_monitor_ptr(cur_image_ptr), MAX_SATO_MEMORY);
  Get_param(Image_monitor_ptr(cur_image_ptr), MAX_SATO_MEMORY) = 0;
  max_mem = 0;
  
  /* The conjunction of all the alphas is formed */
  alphas_formula_lsList_ptr = Make_cnf_conj(dag_ptr, rec_alpha_lsList_ptr); 
  /* Now testing the conjunction of the alphas with each beta */
  result = 1;
  lsForEachItem(*rec_beta_lsList_ptr, beta_lsGen, beta_lsGeneric) {
    beta_vertex_ptr = UNCAST_VERTEX_ITEM(beta_lsGeneric);

    /* KSAT(/\_i alpha_i & -beta_j) */
    /* This creates to_test_lsList_ptr */
#ifdef OPTIMIZE
    to_test_lsList_ptr = Merge_formulae_to_new(Make_cnf(dag_ptr, beta_vertex_ptr, NEG_CNF),
					       alphas_formula_lsList_ptr);
#else
    to_test_lsList_ptr = Merge_formulae_to_new(alphas_formula_lsList_ptr,
					       Make_cnf(dag_ptr, beta_vertex_ptr, NEG_CNF));
#endif
    
    /* We need a new image for SATO */
    new_image_ptr = Init_cnf_sat_rec(dag_ptr, to_test_lsList_ptr);
    /* Passing the reference to the monitor structure */
    Image_monitor_ptr(new_image_ptr) = Image_monitor_ptr(cur_image_ptr); 
    Inc_param(Image_monitor_ptr(cur_image_ptr), REC_CALLS); 
    /* Possibly changing the cache level */
    if (Use_memoS() && (Getf_memoS(LEVEL_CACHE))) Inc_level_memoS(); 
    result = Test_dp_sat_rec(new_image_ptr, dag_ptr, to_test_lsList_ptr,  
			     Test_K_consistency);
    /* Possibly restoring the cache level */
    if (Use_memoS() && (Getf_memoS(LEVEL_CACHE))) Dec_level_memoS(); 
    /* Get memory allocation data */
    if ((Get_param(Image_monitor_ptr(cur_image_ptr), MAX_SATO_MEMORY) +  
	 Memory_count(new_image_ptr)) > max_mem) 
      max_mem =  
	Get_param(Image_monitor_ptr(cur_image_ptr), MAX_SATO_MEMORY) +  
	Memory_count(new_image_ptr); 
    
    Clear_image(new_image_ptr); 
    
    /* Cleaning up temporary allocations */
    list_status = lsDestroy(*to_test_lsList_ptr, NULL);
    FREE(to_test_lsList_ptr);
    
    /* Memoizing */
    /* Store a satisfiability result */
    if (Use_memoS() && result && Getf_memoS(GET_MODELS)) {
      Store_memoS(rec_alpha_lsList_ptr, beta_vertex_ptr);
      /* After the first storage, try to be compact */
      Setf_memoS(COMPACT_STORAGE);
    }
    /* Eventually store a dependency */
    if (Use_memoS() && !result) {
      if (Getf_memoS(GET_DEPENDENCIES)) 
	Store_depS(rec_alpha_lsList_ptr, beta_vertex_ptr);
      if (Getf_memoS(STATIC_FAST) && (!Getf_memoS(GET_DEPENDENCIES) || Getf_memoS(HASH_STORAGE)))
	/* Dependency must be stored also for static FAST */
	Store_sfastS(rec_alpha_lsList_ptr, beta_vertex_ptr);
    }

    /* Unconsistent? */
    if (!result) {
      /* Monitor */
      Inc_param(Image_monitor_ptr(cur_image_ptr), MODFAIL_NUM); 
      lsFinish(beta_lsGen);
      break; /* break the loop on betas */
    }
  } /* end of the loop on betas */
  
  /* Cleaning up temporary allocations */
  list_status = lsDestroy(*alphas_formula_lsList_ptr, NULL);
  FREE(alphas_formula_lsList_ptr);

  /* Memoizing */
  /* Allow memoizing to create new entries */
  if (Use_memoS() && Getf_memoS(GET_MODELS)) Clearf_memoS(COMPACT_STORAGE);
  
  /* Monitor */
  if (max_mem > saved_max) 
    Get_param(Image_monitor_ptr(cur_image_ptr), MAX_SATO_MEMORY) = max_mem; 
  else
    Get_param(Image_monitor_ptr(cur_image_ptr), MAX_SATO_MEMORY) = saved_max; 

  /* Consistent? */
  if (result) {
    *cons_res_ptr = REC_CONSISTENT;
    return NIL(vertex_t);
  } else {
    *cons_res_ptr = REC_UNCONSISTENT;
    return beta_vertex_ptr;
  }
}


/* Backjumping: comes into play at the end of the 
   search knowing that the final consistency check generated an inconsistency */
void Set_K_jump_point(image_t *cur_image_ptr, dag_t *dag_ptr, 
		      lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  vertex_t   *alpha_vertex_ptr;
  lsGeneric  t_lsGeneric;
  int i, cur_atom;

  lsLastItem(*alpha_lsList_ptr, &t_lsGeneric, LS_NH);
  alpha_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);

  /* Look back through the stack to find backjump point */
  i = Stack_idx(cur_image_ptr) - 1;
  while (i >= 0) {
    cur_atom = UNVALUATE(Stack(cur_image_ptr)[i].v);
    if ((V_value(alpha_vertex_ptr) == UNSPREAD(cur_atom)) ||
	(V_value(beta_vertex_ptr) == UNSPREAD(cur_atom)))
      break;
    else --i;
  }
  if (i < (Stack_idx(cur_image_ptr) - 1)) 
    Inc_param(Image_monitor_ptr(cur_image_ptr), BJFAIL_NUM);
  /* Set the jump point */
  for (i = 0; ;i++) 
    if (cur_atom == UNVALUATE(Backup(cur_image_ptr)[i])) break;
  Jump_point(cur_image_ptr) = i + 1;

  return;
}
  

