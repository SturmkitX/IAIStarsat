/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE edp.c - *SAT 1.3 */
/*  Consistency check in logic E */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "edp.h"

#ifdef NEW_CHECK
/* *********************************************************************** */
/* The core function for testing E consistency */
/* *********************************************************************** */
vertex_t *Int_test_E_consistency(image_t *cur_image_ptr, dag_t *dag_ptr, 
				 lsList *alpha_lsList_ptr, lsList *beta_lsList_ptr)
{
  int          result, test_ab, test_ba;
  lsStatus     list_status;
  lsList       *to_test_lsList_ptr;
  lsGen        alpha_lsGen, beta_lsGen;
  lsGeneric    alpha_lsGeneric;
  lsGeneric    beta_lsGeneric;
  vertex_t     *alpha_vertex_ptr, *beta_vertex_ptr;
  image_t      *new_image_ptr;

  /* Iterate over betas */
  lsForEachItem(*beta_lsList_ptr, beta_lsGen, beta_lsGeneric) {
    beta_vertex_ptr = UNCAST_VERTEX_ITEM(beta_lsGeneric);

    /* Now iterate over alphas */
    lsForEachItem(*alpha_lsList_ptr, alpha_lsGen, alpha_lsGeneric) {
      alpha_vertex_ptr = UNCAST_VERTEX_ITEM(alpha_lsGeneric);

      /* Should be either ESAT(alpha_i & -beta_j) or ESAT(-alpha_i & beta_j) */
      /* Try to skip both tests */
      if (Use_memoT()) {
	/* trying to retrieve result for ESAT(alpha_i & -beta_j) */
	result = Test_memoT(V_value(alpha_vertex_ptr), V_value(beta_vertex_ptr)); 
	if (result == TEST_SAT) {
	  result = 1; test_ab = 0; test_ba = 0;  /* ESAT(alpha_i & -beta_j) no more testing! */
	} else {
	  if (result == TEST_UNSAT) {
	    result = 0; test_ab = 0;             /* -ESAT(alpha_i & -beta_j) so skip this test */
	  } else {
	    result = 1; test_ab = 1;             /* do test ESAT(alpha_i & -beta_j) */
	  }
	  /* trying to retrieve result for ESAT(-alpha_i & beta_j) */
	  result = Test_memoT(V_value(beta_vertex_ptr), V_value(alpha_vertex_ptr));
	  if (result == TEST_SAT) {
	    result = 1; test_ab = 0; test_ba = 0; /* ESAT(-alpha_i & beta_j) no more testing! */
	    
	  } else {
	    if (result == TEST_UNSAT) {
	      result = 0; test_ba = 0;            /* -ESAT(-alpha_i & beta_j) so skip this test */
	    } else { 
	      result = 1; test_ba = 1;            /* do test ESAT(-alpha_i & beta_j) */
	    }
	  }
	}
      }
      
      /* Should test ESAT(alpha_i & -beta_j)? */
      if (test_ab) {
	/* This creates to_test_lsList_ptr */
	to_test_lsList_ptr = 
	  Merge_formulae_to_new(Make_cnf(dag_ptr, alpha_vertex_ptr, POS_CNF),
				Make_cnf(dag_ptr, beta_vertex_ptr, NEG_CNF));
#ifdef TRACE_CONS
	Print_simple_call(alpha_vertex_ptr, beta_vertex_ptr, to_test_lsList_ptr);
#endif
	/* We need a new image for SATO */
	new_image_ptr = Init_cnf_sat_rec(dag_ptr, to_test_lsList_ptr);
	/* Passing the reference to the monitor structure */
	Inc_param(Image_monitor_ptr(cur_image_ptr), REC_CALLS); 
	Image_monitor_ptr(new_image_ptr) = Image_monitor_ptr(cur_image_ptr); 
	result = Test_dp_sat_rec(new_image_ptr, dag_ptr, to_test_lsList_ptr, 
				 Test_E_consistency);
	  
	/* Store the result for future use */
	if (Use_memoT()) {
	  Store_memoT(V_value(alpha_vertex_ptr), V_value(beta_vertex_ptr), result);
	}
	
	/* If the test was ok, no further test is required */
	if (result) test_ba = 0;
	
	/* Cleaning up temporary allocations */
	list_status = lsDestroy(*to_test_lsList_ptr, NULL);
	FREE(to_test_lsList_ptr);
	Clear_image(new_image_ptr);
#ifdef TRACE_CONS
	printf("Which is %s\n\n\n", (result ? "consistent" : "unconsistent"));
#endif
      }
      
      /* Should test ESAT(-alpha_i & beta_j)? */
      if (test_ba) {
	/* This creates to_test_lsList_ptr */
	to_test_lsList_ptr = 
	  Merge_formulae_to_new(Make_cnf(dag_ptr, alpha_vertex_ptr, POS_CNF),
				Make_cnf(dag_ptr, beta_vertex_ptr, NEG_CNF));
#ifdef TRACE_CONS
	Print_simple_call(beta_vertex_ptr, alpha_vertex_ptr, to_test_lsList_ptr);
#endif
	/* We need a new image for SATO */
	new_image_ptr = Init_cnf_sat_rec(dag_ptr, to_test_lsList_ptr);
	/* Passing the reference to the monitor structure */
	Inc_param(Image_monitor_ptr(cur_image_ptr), REC_CALLS); 
	Image_monitor_ptr(new_image_ptr) = Image_monitor_ptr(cur_image_ptr); 
	result = Test_dp_sat_rec(new_image_ptr, dag_ptr, to_test_lsList_ptr, 
				   Test_E_consistency);
	
	/* Store the result for future use */
	if (Use_memoT()) {
	  Store_memoT(V_value(beta_vertex_ptr), V_value(alpha_vertex_ptr), result);
	}
	
	/* Cleaning up temporary allocations */
	list_status = lsDestroy(*to_test_lsList_ptr, NULL);
	FREE(to_test_lsList_ptr);
	Clear_image(new_image_ptr);
#ifdef TRACE_CONS
	printf("Which is %s\n\n\n", (result ? "consistent" : "unconsistent"));
#endif
      }
      
      /* Unconsistent? */
      if (!result) {
	lsFinish(alpha_lsGen);
	break; /* break the loop on alphas */
      } 
    } /* end of the loop on alphas */
      
    /* Unconsistent? */
    if (!result) {
      lsFinish(beta_lsGen);
      break; /* break the loop on betas */
    }
  } /* end of the loop on betas */

  if (result) return NIL(vertex_t); 
  else return beta_vertex_ptr;

}

/* *********************************************************************** */
/* The function for testing E consistency of an assignment 
   (it uses stack pointer) */
/* *********************************************************************** */
int Test_E_consistency(image_t *cur_image_ptr, dag_t *dag_ptr)
{
  int          ag_num;
  int          result, i;
  int          cur_atom, first_modal_atom, last_modal_atom;
  st_table     *agents_st_table_ptr;
  lsList       *old_alpha_lsList_ptr, *old_beta_lsList_ptr;
  lsList       *new_alpha_lsList_ptr, *new_beta_lsList_ptr;
  st_generator *at_st_generator;
  stGeneric    ak_stGeneric, av_stGeneric;
  vertex_t     *cur_vertex_ptr;

  first_modal_atom = SPREAD(Lpa(dag_ptr) + 1);
  last_modal_atom = SPREAD(Lma(dag_ptr));

  /* This is the classification for agents */
  agents_st_table_ptr = st_init_table(st_numcmp, st_numhash);
  Classify_agents_light(cur_image_ptr, dag_ptr, agents_st_table_ptr);

  old_alpha_lsList_ptr = ALLOC(lsList, 1); old_beta_lsList_ptr = ALLOC(lsList, 1);
  new_alpha_lsList_ptr = ALLOC(lsList, 1); new_beta_lsList_ptr = ALLOC(lsList, 1);

  /* Now iterate over agents */
  result = 1; 
  st_foreach_item(agents_st_table_ptr, at_st_generator, &ak_stGeneric, &av_stGeneric) {
    ag_num = UNCAST_KEY(ak_stGeneric);

    /* Create old and new lists for each agent */
    *old_alpha_lsList_ptr = lsCreate(); *old_beta_lsList_ptr = lsCreate();
    *new_alpha_lsList_ptr = lsCreate(); *new_beta_lsList_ptr = lsCreate();  

    i = 0;
    /* If jumping already happened, we might want to skip some tests */
    if (Last_stack_idx(cur_image_ptr) > 0) 
      while (i < (Last_stack_idx(cur_image_ptr))) {
	/* Include all the significant alphas and betas into the "old" lists */
	/* Look for a relevant modal atom (must be the same agent) */
	IF_RELEVANT_MODAL_ATOM
	  /* Store the atom in the appropriate list */
	  if (Value(cur_image_ptr)[cur_atom] == TT) 
	    lsNewEnd(*old_alpha_lsList_ptr, CAST_VERTEX_ITEM(cur_vertex_ptr), LS_NH);
	  else 
	    lsNewEnd(*old_beta_lsList_ptr, CAST_VERTEX_ITEM(cur_vertex_ptr), LS_NH);
	END_IF    
	++i;
      }

    /* Look for an early inconsistency */
    /* Running through the stack (up to the end) */
    while (i < Stack_idx(cur_image_ptr)) {
      /* Get the current atom in the stack */
      /* Look for a relevant modal atom (must be the same agent) */
      IF_RELEVANT_MODAL_ATOM
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
	  /* there were no new betas but some new alphas: do not test old alphas again */
	  result =
	    (Int_test_E_consistency(cur_image_ptr, dag_ptr, 
				    new_alpha_lsList_ptr, old_beta_lsList_ptr) == NIL(vertex_t));
      } else {
	if (lsLength(*new_alpha_lsList_ptr) == 0) 
	  /* There were some betas but no alphas: do not test the old betas again */
	  result =
	    (Int_test_E_consistency(cur_image_ptr, dag_ptr, 
				    old_alpha_lsList_ptr, new_beta_lsList_ptr) == NIL(vertex_t));
	else {
	  /* Everything changed: test everything but old alphas vs. old betas*/
	  result =
	    ((Int_test_E_consistency(cur_image_ptr, dag_ptr, 
				     new_alpha_lsList_ptr, old_beta_lsList_ptr) == NIL(vertex_t)) &&
	     (Int_test_E_consistency(cur_image_ptr, dag_ptr, 
				     old_alpha_lsList_ptr, new_beta_lsList_ptr) == NIL(vertex_t)) &&
	     (Int_test_E_consistency(cur_image_ptr, dag_ptr, 
				     new_alpha_lsList_ptr, new_beta_lsList_ptr) == NIL(vertex_t)));
	}
      }
    }


    /* Clean the lists for the next agent */
    lsDestroy(*old_alpha_lsList_ptr, NULL); lsDestroy(*old_beta_lsList_ptr, NULL);
    lsDestroy(*new_alpha_lsList_ptr, NULL); lsDestroy(*new_beta_lsList_ptr, NULL);

    if (!result) {
      st_free_gen(at_st_generator);
      break; /* break the loop on agents */
    }
  } /* end of the loop on agents */

  /* Clean the allocations */
  FREE(old_alpha_lsList_ptr); FREE(new_alpha_lsList_ptr);
  FREE(old_beta_lsList_ptr); FREE(new_beta_lsList_ptr);
  st_free_table(agents_st_table_ptr);    

  if (result)
    /* Declare consistent the current stack */
    Last_stack_idx(cur_image_ptr) = Stack_idx(cur_image_ptr);
  else
    /* Set an immediate jump point */
    Jump_point(cur_image_ptr) = Backup_idx(cur_image_ptr);

  return result;
}

#else

/* *********************************************************************** */
/* The function for testing E consistency of an assignment 
   (it does not use stack pointer) */
/* *********************************************************************** */
int Test_E_consistency(image_t *cur_image_ptr, dag_t *dag_ptr)
{
  int          result, test_ab, test_ba;
  lsStatus     list_status;
  st_table     *agents_st_table_ptr;
  lsList       *alpha_lsList_ptr, *beta_lsList_ptr;
  lsList       *to_test_lsList_ptr;
  st_generator *at_st_generator;
  lsGen        alpha_lsGen, beta_lsGen;
  stGeneric    ak_stGeneric, av_stGeneric;
  lsGeneric    alpha_lsGeneric;
  lsGeneric    beta_lsGeneric;
  vertex_t     *alpha_vertex_ptr, *beta_vertex_ptr;
  image_t      *new_image_ptr;

#ifdef TRACE_CONS
  printf("------------------------------");
  printf("Considering the model:\n");
  print_model_complete(cur_image_ptr);
  printf("\n");
#endif
  /* This is the classification for agents */
  agents_st_table_ptr = st_init_table(st_numcmp, st_numhash);
  /* First of all classify alphas and betas for agents */
  Classify_agents(cur_image_ptr, dag_ptr, agents_st_table_ptr);
#ifdef TRACE_CONS
  if (st_count(agents_st_table_ptr) == 0) {
    printf("------------------------------The model is propositional\n\n");
  }
#endif  
  /* Now iterate over agents */
  result = 1; test_ab = 1; test_ba = 1; 
  st_foreach_item(agents_st_table_ptr, at_st_generator, &ak_stGeneric, &av_stGeneric) {
    /* These are the current agent alphas and betas */
    alpha_lsList_ptr = Alpha_lsList_ptr(UNCAST_AGENT(av_stGeneric));
    beta_lsList_ptr = Beta_lsList_ptr(UNCAST_AGENT(av_stGeneric));
#ifdef TRACE_CONS
    if (lsLength(*alpha_lsList_ptr) == 0) {
      printf("------------------------------There is no []alpha in the assigment\n\n");
    } else if (lsLength(*beta_lsList_ptr) == 0) {
      printf("------------------------------There is no -[]beta in the assigment\n\n");
    }
#endif
    /* Iterate over betas */
    lsForEachItem(*beta_lsList_ptr, beta_lsGen, beta_lsGeneric) {
      beta_vertex_ptr = UNCAST_VERTEX_ITEM(beta_lsGeneric);

      /* Now iterate over alphas */
      lsForEachItem(*alpha_lsList_ptr, alpha_lsGen, alpha_lsGeneric) {
	alpha_vertex_ptr = UNCAST_VERTEX_ITEM(alpha_lsGeneric);

	/* Should be either ESAT(alpha_i & -beta_j) or ESAT(-alpha_i & beta_j) */
	/* Try to skip both tests */
	if (Use_memoT()) {
	  /* trying to retrieve result for ESAT(alpha_i & -beta_j) */
/*            Inc_param(Image_monitor_ptr(cur_image_ptr), CACHE_ACCESS);                        */
	  result = Test_memoT(V_value(alpha_vertex_ptr), V_value(beta_vertex_ptr)); 
	  if (result == TEST_SAT) {
/*              Inc_param(Image_monitor_ptr(cur_image_ptr), CACHE_SUCCESS);  */
	    result = 1; test_ab = 0; test_ba = 0;  /* ESAT(alpha_i & -beta_j) no more testing! */
	  } else {
	    if (result == TEST_UNSAT) {
/*                Inc_param(Image_monitor_ptr(cur_image_ptr), CACHE_SUCCESS);  */
	      result = 0; test_ab = 0;             /* -ESAT(alpha_i & -beta_j) so skip this test */
	    } else {
	      result = 1; test_ab = 1;             /* do test ESAT(alpha_i & -beta_j) */
	    }
	    /* trying to retrieve result for ESAT(-alpha_i & beta_j) */
	    result = Test_memoT(V_value(beta_vertex_ptr), V_value(alpha_vertex_ptr));
/*              Inc_param(Image_monitor_ptr(cur_image_ptr), CACHE_ACCESS);  */
	    if (result == TEST_SAT) {
/*                Inc_param(Image_monitor_ptr(cur_image_ptr), CACHE_SUCCESS);  */
	      result = 1; test_ab = 0; test_ba = 0; /* ESAT(-alpha_i & beta_j) no more testing! */

	    } else {
	      if (result == TEST_UNSAT) {
/*                  Inc_param(Image_monitor_ptr(cur_image_ptr), CACHE_SUCCESS);        */
		result = 0; test_ba = 0;            /* -ESAT(-alpha_i & beta_j) so skip this test */
	      } else { 
		result = 1; test_ba = 1;            /* do test ESAT(-alpha_i & beta_j) */
	      }
	    }
	  }
	}

	/* Should test ESAT(alpha_i & -beta_j)? */
	if (test_ab) {
	  /* This creates to_test_lsList_ptr */
	  to_test_lsList_ptr = 
	    Merge_formulae_to_new(Make_cnf(dag_ptr, alpha_vertex_ptr, POS_CNF),
				  Make_cnf(dag_ptr, beta_vertex_ptr, NEG_CNF));
#ifdef TRACE_CONS
	  Print_simple_call(alpha_vertex_ptr, beta_vertex_ptr, to_test_lsList_ptr);
#endif
	  /* We need a new image for SATO */
	  new_image_ptr = Init_cnf_sat_rec(dag_ptr, to_test_lsList_ptr);
	  /* Passing the reference to the monitor structure */
	  Inc_param(Image_monitor_ptr(cur_image_ptr), REC_CALLS); 
	  Image_monitor_ptr(new_image_ptr) = Image_monitor_ptr(cur_image_ptr); 
	  result = Test_dp_sat_rec(new_image_ptr, dag_ptr, to_test_lsList_ptr, 
				   Test_E_consistency);
	  
	  /* Store the result for future use */
	  if (Use_memoT()) {
	    Store_memoT(V_value(alpha_vertex_ptr), V_value(beta_vertex_ptr), result);
	  }
	  
	  /* If the test was ok, no further test is required */
	  if (result) test_ba = 0;
	  
	  /* Cleaning up temporary allocations */
	  list_status = lsDestroy(*to_test_lsList_ptr, NULL);
	  FREE(to_test_lsList_ptr);
	  Clear_image(new_image_ptr);
#ifdef TRACE_CONS
	  printf("Which is %s\n\n\n", (result ? "consistent" : "unconsistent"));
#endif
	}

	/* Should test ESAT(-alpha_i & beta_j)? */
	if (test_ba) {
	  /* This creates to_test_lsList_ptr */
	  to_test_lsList_ptr = 
	    Merge_formulae_to_new(Make_cnf(dag_ptr, alpha_vertex_ptr, POS_CNF),
				  Make_cnf(dag_ptr, beta_vertex_ptr, NEG_CNF));
#ifdef TRACE_CONS
	  Print_simple_call(beta_vertex_ptr, alpha_vertex_ptr, to_test_lsList_ptr);
#endif
	  /* We need a new image for SATO */
	  new_image_ptr = Init_cnf_sat_rec(dag_ptr, to_test_lsList_ptr);
	  /* Passing the reference to the monitor structure */
	  Inc_param(Image_monitor_ptr(cur_image_ptr), REC_CALLS); 
	  Image_monitor_ptr(new_image_ptr) = Image_monitor_ptr(cur_image_ptr); 
	  result = Test_dp_sat_rec(new_image_ptr, dag_ptr, to_test_lsList_ptr, 
				   Test_E_consistency);
	  
	  /* Store the result for future use */
	  if (Use_memoT()) {
	    Store_memoT(V_value(beta_vertex_ptr), V_value(alpha_vertex_ptr), result);
	  }
	  
	  /* Cleaning up temporary allocations */
	  list_status = lsDestroy(*to_test_lsList_ptr, NULL);
	  FREE(to_test_lsList_ptr);
	  Clear_image(new_image_ptr);
#ifdef TRACE_CONS
	  printf("Which is %s\n\n\n", (result ? "consistent" : "unconsistent"));
#endif
	}
	
	/* Unconsistent? */
	if (!result) {
	  lsFinish(alpha_lsGen);
	  break; /* break the loop on alphas */
	} 
      } /* end of the loop on alphas */
      
      /* Unconsistent? */
      if (!result) {
	lsFinish(beta_lsGen);
	break; /* break the loop on betas */
      }
    } /* end of the loop on betas */
    
    /* Unconsistent? */
    if (!result) {
      st_free_gen(at_st_generator);
      break; /* break the loop on agents */
    }
  } /* end of the loop on agents */
  
  /* Cleaning up the agents table */
  st_foreach_item(agents_st_table_ptr, at_st_generator, &ak_stGeneric, &av_stGeneric) {
    Clear_agent(av_stGeneric);
  }
  st_free_table(agents_st_table_ptr);    
#ifdef TRACE_CONS
  if (result)
    printf("------------------------------The model is consistent in K\n\n");
  else
    printf("------------------------------The model is not consistent in K\n\n");
#endif

  if (!result)
    /* Set an immediate jump point */
    Jump_point(cur_image_ptr) = Backup_idx(cur_image_ptr);
  
  return result;
}

#endif
