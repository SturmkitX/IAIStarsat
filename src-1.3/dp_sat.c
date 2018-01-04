/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE dp_sat.c - *SAT 1.3 */
/*  SAT-based modal satisfiability */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "dp_sat.h"

image_t *Init_cnf_sat(dag_t *dag_ptr, int flag_conv)
{
  vertex_t *ma_vertex_ptr;
  lsList   *dummy_lsList_ptr;
  int      cnt;
  image_t  *t_image_ptr;
  int      max_atom, max_indep;
 
  dummy_lsList_ptr = Make_cnf(dag_ptr, dag_ptr->root_vertex_ptr, POS_CNF);
  /* The number of atoms is the maximum number of atoms (the last added atom)
     the number of clauses is the number of entries in the top-level list */
  max_atom = max_indep = Lpa(dag_ptr);
  if (Lma(dag_ptr) > max_atom) max_atom = max_indep = Lma(dag_ptr);
  if (Laa(dag_ptr) > max_atom) max_atom = Laa(dag_ptr);
  t_image_ptr = sato_init(SPREAD(max_atom), lsLength(*dummy_lsList_ptr), SPREAD(max_indep), 1);

  if (flag_conv) {
    For_each_modal_xref_item(dag_ptr, cnt, ma_vertex_ptr) {                
      dummy_lsList_ptr = 
	Make_cnf(dag_ptr, ma_vertex_ptr, POS_CNF);
      dummy_lsList_ptr = 
	Make_cnf(dag_ptr, ma_vertex_ptr, NEG_CNF);
    }
  }

  return t_image_ptr;
}

image_t *Init_cnf_sat_rec(dag_t *dag_ptr, lsList *to_test_lsList_ptr)
{
  image_t  *t_image_ptr;
  int      max_atom, max_indep;
 
  /* The number of atoms is the maximum number of atoms (the last added atom)
     the number of clauses is the number of entries in the top-level list */
  max_atom = max_indep = Lpa(dag_ptr);
  if (Lma(dag_ptr) > max_atom) max_atom = max_indep = Lma(dag_ptr);
  if (Laa(dag_ptr) > max_atom) max_atom = Laa(dag_ptr);
  t_image_ptr = sato_init(++max_atom, lsLength(*to_test_lsList_ptr), ++max_indep, 0);

  return t_image_ptr;
}

/* *********************************************************************** */
/* Translation of dags into cnfs */
/* *********************************************************************** */
lsList *Make_empty_clause()
{

  lsList   *t_clause_lsList_ptr;

  t_clause_lsList_ptr = ALLOC(lsList,1);
  *t_clause_lsList_ptr = lsCreate();

  return t_clause_lsList_ptr;
}

lsList *Make_unit_clause(int value, int sign)
{

  lsList   *t_clause_lsList_ptr;
  lsStatus list_status;

  t_clause_lsList_ptr = ALLOC(lsList,1);
  *t_clause_lsList_ptr = lsCreate();
  list_status = 
    lsNewBegin(*t_clause_lsList_ptr, CAST_LITERAL_ITEM(VALUATE(value,sign)), LS_NH);

  return t_clause_lsList_ptr;
}

void Add_clause(lsList *formula_lsList_ptr, lsList *clause_lsList_ptr)
{
  lsStatus list_status;

  list_status = lsNewEnd(*formula_lsList_ptr,
			 CAST_CLAUSE_ITEM(clause_lsList_ptr), LS_NH);

  return;
}

void Add_literal(lsList *clause_lsList_ptr, int value, int sign)
{
  lsStatus list_status;

  list_status = lsNewEnd(*clause_lsList_ptr,
			 CAST_LITERAL_ITEM(VALUATE(value,sign)), LS_NH);

  return;
}

void Merge_formulae(lsList *formula_lsList_ptr, lsList *added_lsList_ptr) 
{ 
  lsGen     t_lsGen; 
  lsGeneric t_lsGeneric; 
  lsStatus  list_status; 
  
  lsForEachItem(*added_lsList_ptr, t_lsGen, t_lsGeneric) { 
    list_status = lsNewEnd(*formula_lsList_ptr, t_lsGeneric, LS_NH); 
  } 

  return;
} 

void Swap_formulae(lsList **first_lsList_ptr_ptr, lsList **second_lsList_ptr_ptr) 
{ 
  lsList  *t_lsList_ptr;
  
  t_lsList_ptr = *first_lsList_ptr_ptr;
  *first_lsList_ptr_ptr = *second_lsList_ptr_ptr;
  *second_lsList_ptr_ptr = t_lsList_ptr;

  return;
} 

void Negate_formula(lsList *formula_lsList_ptr)
{
  lsGeneric clause_lsGeneric, lit_lsGeneric; 
  lsStatus  list_status; 

  list_status = lsDelEnd(*formula_lsList_ptr, &clause_lsGeneric);
  list_status = lsFirstItem(*UNCAST_CLAUSE_ITEM(clause_lsGeneric), &lit_lsGeneric, LS_NH);
  Add_clause(formula_lsList_ptr, Make_unit_clause(UNCAST_LITERAL_ITEM(lit_lsGeneric),-1));

  return;
}

lsList* Add_dependent_neg(lsList *formula_lsList_ptr, lsList sons_literals_lsList, 
			   int b, int op_code)
{
  lsGen     t_lsGen;
  lsGeneric t_lsGeneric;
  lsStatus  list_status;
  lsList    *t_clause_lsList_ptr, *b_clause_lsList_ptr, *added_lsList_ptr;
  int       s[2][3] = { {1,1,1}, {1,-1,-1} };
  int       first_lit, second_lit;
  int       i;

  added_lsList_ptr = ALLOC(lsList,1);
  *added_lsList_ptr = lsCreate();  

  if (op_code == iff_code) {
    list_status = lsFirstItem(sons_literals_lsList, &t_lsGeneric, LS_NH);
    first_lit = UNCAST_LITERAL_ITEM(t_lsGeneric);
    list_status = lsLastItem(sons_literals_lsList, &t_lsGeneric, LS_NH);
    second_lit = UNCAST_LITERAL_ITEM(t_lsGeneric);

    for (i = 0; i < 2; i++) {
      b_clause_lsList_ptr = Make_unit_clause(b, s[i][0]);
      Add_literal(b_clause_lsList_ptr, first_lit, s[i][1]);
      Add_literal(b_clause_lsList_ptr, second_lit, s[i][2]);
      Add_clause(formula_lsList_ptr, b_clause_lsList_ptr);
      Add_clause(added_lsList_ptr, b_clause_lsList_ptr);
    }
    
  } else if (op_code == and_code) {
   
    t_clause_lsList_ptr = ALLOC(lsList,1);
    *t_clause_lsList_ptr = lsCreate();  
    lsForEachItem(sons_literals_lsList, t_lsGen, t_lsGeneric) {
      Add_literal(t_clause_lsList_ptr, UNCAST_LITERAL_ITEM(t_lsGeneric), -1);
    }
    Add_literal(t_clause_lsList_ptr, b, 1);
    Add_clause(added_lsList_ptr, t_clause_lsList_ptr);
    Add_clause(formula_lsList_ptr, t_clause_lsList_ptr);

  } else { /*  (op_code == or_code) */
    
    lsForEachItem(sons_literals_lsList, t_lsGen, t_lsGeneric) {
      b_clause_lsList_ptr = Make_unit_clause(b, 1);
      Add_literal(b_clause_lsList_ptr, UNCAST_LITERAL_ITEM(t_lsGeneric), -1);
      Add_clause(formula_lsList_ptr, b_clause_lsList_ptr);
      Add_clause(added_lsList_ptr, b_clause_lsList_ptr);
    }
    
  }

  return added_lsList_ptr;
}

lsList* Add_dependent_pos(lsList *formula_lsList_ptr, lsList sons_literals_lsList, 
			    int b, int op_code)
{
  lsGen     t_lsGen;
  lsGeneric t_lsGeneric;
  lsStatus  list_status;
  lsList    *t_clause_lsList_ptr, *b_clause_lsList_ptr, *added_lsList_ptr;
  int       s[2][3] = { {-1,1,-1}, {-1,-1,1} };
  int       first_lit, second_lit;
  int       i;

  added_lsList_ptr = ALLOC(lsList,1);
  *added_lsList_ptr = lsCreate();  

  if (op_code == iff_code) {
    list_status = lsFirstItem(sons_literals_lsList, &t_lsGeneric, LS_NH);
    first_lit = UNCAST_LITERAL_ITEM(t_lsGeneric);
    list_status = lsLastItem(sons_literals_lsList, &t_lsGeneric, LS_NH);
    second_lit = UNCAST_LITERAL_ITEM(t_lsGeneric);

    for (i = 0; i < 2; i++) {
      b_clause_lsList_ptr = Make_unit_clause(b, s[i][0]);
      Add_literal(b_clause_lsList_ptr, first_lit, s[i][1]);
      Add_literal(b_clause_lsList_ptr, second_lit, s[i][2]);
      Add_clause(formula_lsList_ptr, b_clause_lsList_ptr);
      Add_clause(added_lsList_ptr, b_clause_lsList_ptr);
    }
    
  } else if (op_code == or_code) {

    t_clause_lsList_ptr = ALLOC(lsList,1);
    *t_clause_lsList_ptr = lsCreate();  
    lsForEachItem(sons_literals_lsList, t_lsGen, t_lsGeneric) 
      Add_literal(t_clause_lsList_ptr, UNCAST_LITERAL_ITEM(t_lsGeneric), 1);
    Add_literal(t_clause_lsList_ptr, b, -1);
    Add_clause(added_lsList_ptr, t_clause_lsList_ptr);
    Add_clause(formula_lsList_ptr, t_clause_lsList_ptr);

  } else { /* op_code == and_code */

    lsForEachItem(sons_literals_lsList, t_lsGen, t_lsGeneric) {
      b_clause_lsList_ptr = Make_unit_clause(b, -1);
      Add_literal(b_clause_lsList_ptr, UNCAST_LITERAL_ITEM(t_lsGeneric), 1);
      Add_clause(formula_lsList_ptr, b_clause_lsList_ptr);
      Add_clause(added_lsList_ptr, b_clause_lsList_ptr);
    }
  
  }

  return added_lsList_ptr;
}

void Simple_cnf_conversion(lsList *formula_lsList_ptr, vertex_t *f_vertex_ptr, int sign)
{
  lsList    sons_literals_lsList, sons_vertices_lsList;
  lsList    *t_clause_lsList_ptr;
  int       code;
  lsGen     t_lsGen;
  lsStatus  list_status;
  lsGeneric t_lsGeneric;
  int       t_res;
  vertex_t  *t_vertex_ptr;

  sons_literals_lsList = lsCreate();
  sons_vertices_lsList = Get_vertex_sons(f_vertex_ptr);
  lsForEachItem(sons_vertices_lsList, t_lsGen, t_lsGeneric) {
    t_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);
    t_res = ((V_op_code(t_vertex_ptr) == atom_code) ?
	     (sign * SPREAD(V_value(t_vertex_ptr))) :
	     (-1 * sign * SPREAD(V_value(Get_vertex_son(t_vertex_ptr)))));
    list_status = lsNewEnd(sons_literals_lsList, CAST_LITERAL_ITEM(t_res), LS_NH);
  }
  
  code = V_op_code(f_vertex_ptr);
  if ((sign < 0) && (V_op_code(f_vertex_ptr) == and_code)) code = or_code;
  if ((sign < 0) && (V_op_code(f_vertex_ptr) == or_code)) code = and_code;

  if (code == and_code) {
    lsForEachItem(sons_literals_lsList, t_lsGen, t_lsGeneric) {
      Add_clause(formula_lsList_ptr, 
		 Make_unit_clause(UNCAST_LITERAL_ITEM(t_lsGeneric), 1));
    }
  } else {
    t_clause_lsList_ptr = Make_empty_clause();
    lsForEachItem(sons_literals_lsList, t_lsGen, t_lsGeneric) {
      Add_literal(t_clause_lsList_ptr, 
		  UNCAST_LITERAL_ITEM(t_lsGeneric),1);
    }
    Add_clause(formula_lsList_ptr, t_clause_lsList_ptr);
  }

  list_status = lsDestroy(sons_vertices_lsList, NULL);
  list_status = lsDestroy(sons_literals_lsList, NULL);

  return;
}

void Cnf_cnf_conversion(lsList *formula_lsList_ptr, vertex_t *f_vertex_ptr)
{
  lsList    or_sons_vertices_lsList, lit_sons_vertices_lsList;
  lsList    *t_clause_lsList_ptr;
  lsGen     or_lsGen, lit_lsGen;
  lsStatus  list_status;
  lsGeneric or_lsGeneric, lit_lsGeneric;
  int       t_res;
  vertex_t  *or_vertex_ptr, *lit_vertex_ptr;
  

  or_sons_vertices_lsList = Get_vertex_sons(f_vertex_ptr);
  lsForEachItem(or_sons_vertices_lsList, or_lsGen, or_lsGeneric) {
    or_vertex_ptr = UNCAST_VERTEX_ITEM(or_lsGeneric);
    lit_sons_vertices_lsList = Get_vertex_sons(or_vertex_ptr);
    t_clause_lsList_ptr = Make_empty_clause();
    lsForEachItem(lit_sons_vertices_lsList, lit_lsGen, lit_lsGeneric) {
      lit_vertex_ptr = UNCAST_VERTEX_ITEM(lit_lsGeneric);
      t_res = ((V_op_code(lit_vertex_ptr) == atom_code) ?
	       (SPREAD(V_value(lit_vertex_ptr))) :
	       (-1 * SPREAD(V_value(Get_vertex_son(lit_vertex_ptr)))));
      Add_literal(t_clause_lsList_ptr, t_res, 1);
    }
    Add_clause(formula_lsList_ptr, t_clause_lsList_ptr);
    list_status = lsDestroy(lit_sons_vertices_lsList, NULL);
  }
  list_status = lsDestroy(or_sons_vertices_lsList, NULL);

  return;
}


int Make_cnf_rec(dag_t *dag_ptr, vertex_t *f_vertex_ptr, 
		 lsList *formula_lsList_ptr, st_table *visited_st_table_ptr, int polarity)
{
  int        polarity_down;
  lsList     sons_vertices_lsList, sons_literals_lsList;
  lsGen      t_lsGen;
  lsGeneric  t_lsGeneric;
  lsStatus   list_status;
  stGeneric  *value_stGeneric_ptr;
  int        b_res, t_res;
  cnf_info_t *t_cnf_info_ptr;
  
  assert((V_op_code(f_vertex_ptr) != imp_code) &&
	 (V_op_code(f_vertex_ptr) != box_code) &&
	 (V_op_code(f_vertex_ptr) != dia_code));

  switch (V_op_code(f_vertex_ptr))
    {
    case atom_code:
      b_res = SPREAD(V_value(f_vertex_ptr));
      break;
    case not_code:
      /* Polarity is reverted unless both polarities are to be propagated */
      /* Atoms make a special case */
      polarity_down = 
	((polarity == BOTH_CNF) ? polarity : ((polarity == POS_CNF) ? NEG_CNF : POS_CNF));
      b_res = Make_cnf_rec(dag_ptr, Get_vertex_son(f_vertex_ptr),
			   formula_lsList_ptr, visited_st_table_ptr, polarity_down);
      b_res = -1 * b_res;
      break;
    case and_code:
    case or_code:
    case iff_code:
      /* Both polarities are propagated when reaching an iff */
      polarity_down = ((V_op_code(f_vertex_ptr) == iff_code) ? BOTH_CNF : polarity);

      t_cnf_info_ptr = V_AUX(f_vertex_ptr);
      sons_literals_lsList = lsCreate();
      sons_vertices_lsList = Get_vertex_sons(f_vertex_ptr);

      if (!st_find_or_add(visited_st_table_ptr, CAST_TKEY(f_vertex_ptr), 
			  &value_stGeneric_ptr)) {
	/* This subformula was not visited during this conversion:
	   we need to propagate it down and add the corresponding 
	   clauses. */
	*value_stGeneric_ptr = DUMMY_VALUE;
	/* Propagate the conversion to the arguments */
	lsForEachItem(sons_vertices_lsList, t_lsGen, t_lsGeneric) {
	  t_res = Make_cnf_rec(dag_ptr, UNCAST_VERTEX_ITEM(t_lsGeneric),
			       formula_lsList_ptr, visited_st_table_ptr, polarity_down);
	  list_status = lsNewEnd(sons_literals_lsList, CAST_LITERAL_ITEM(t_res), LS_NH);
	}
	if (t_cnf_info_ptr) {
	  /* An optimization: if the subformula was visited before, possibly
	     during another conversion, the correspondant atom and added clauses
	     might be stored in the aux vertex pointer */
	  b_res = SPREAD(b_value(t_cnf_info_ptr));
	  /* Now check for polarities */
	  if ((polarity == POS_CNF) || (polarity == BOTH_CNF)) {
	    if (pos_added_lsList_ptr(t_cnf_info_ptr) != NIL(lsList))
	      Merge_formulae(formula_lsList_ptr, pos_added_lsList_ptr(t_cnf_info_ptr));
	    else
	      pos_added_lsList_ptr(t_cnf_info_ptr) =
		Add_dependent_pos(formula_lsList_ptr, sons_literals_lsList,
				    b_res, V_op_code(f_vertex_ptr));
	  }
	  if ((polarity == NEG_CNF) || (polarity == BOTH_CNF)) {
	    if (neg_added_lsList_ptr(t_cnf_info_ptr) != NIL(lsList))
	      Merge_formulae(formula_lsList_ptr, neg_added_lsList_ptr(t_cnf_info_ptr));
	    else
	      neg_added_lsList_ptr(t_cnf_info_ptr) =
		Add_dependent_neg(formula_lsList_ptr, sons_literals_lsList,
				   b_res, V_op_code(f_vertex_ptr));
	  }
	} else {
	  /* Adding a new atom and definition clauses. Add_dependent returns
	     the list consisting of added clauses for storage purposes only.
	     Added clauses are appended to formula_lsList_ptr inside Add_dependent */
	  b_res = ++Laa(dag_ptr);
	  t_cnf_info_ptr = New_cnf_info(b_res);
	  b_res = SPREAD(b_res);
	  /* Now check for polarities */
	  if ((polarity == POS_CNF) || (polarity == BOTH_CNF)) {
	      pos_added_lsList_ptr(t_cnf_info_ptr) =
		Add_dependent_pos(formula_lsList_ptr, sons_literals_lsList,
				    b_res, V_op_code(f_vertex_ptr));
	  }
	  if ((polarity == NEG_CNF) || (polarity == BOTH_CNF)) {
	      neg_added_lsList_ptr(t_cnf_info_ptr) =
		Add_dependent_neg(formula_lsList_ptr, sons_literals_lsList,
				   b_res, V_op_code(f_vertex_ptr));
	  }
	  V_aux(f_vertex_ptr) = (char*)t_cnf_info_ptr;
	}
      } else {
	/* This subformula was visited during this conversion: no need
	   to get a new atom, no need to add clauses provided that the 
	   polarity is the same */
	b_res = SPREAD(b_value(t_cnf_info_ptr));
	if ((polarity == POS_CNF) || (polarity == BOTH_CNF)) {
	  if (pos_added_lsList_ptr(t_cnf_info_ptr) == NIL(lsList)) {
	    /* Get the literals (they are already computed!) */
	    lsForEachItem(sons_vertices_lsList, t_lsGen, t_lsGeneric) {
	      t_res = SPREAD(b_value(V_AUX(UNCAST_VERTEX_ITEM(t_lsGeneric))));
	      list_status = lsNewEnd(sons_literals_lsList, CAST_LITERAL_ITEM(t_res), LS_NH);
	    }
	    /* Add the clauses */
	    pos_added_lsList_ptr(t_cnf_info_ptr) =
	      Add_dependent_pos(formula_lsList_ptr, sons_literals_lsList,
				b_res, V_op_code(f_vertex_ptr));
	  }
	}
	if ((polarity == NEG_CNF) || (polarity == BOTH_CNF)) {
	  if (neg_added_lsList_ptr(t_cnf_info_ptr) == NIL(lsList)) {
	    /* If not extracted above, get the literals */
	    lsForEachItem(sons_vertices_lsList, t_lsGen, t_lsGeneric) {
	      t_res = SPREAD(b_value(V_AUX(UNCAST_VERTEX_ITEM(t_lsGeneric))));
	      list_status = lsNewEnd(sons_literals_lsList, CAST_LITERAL_ITEM(t_res), LS_NH);
	    }
	    neg_added_lsList_ptr(t_cnf_info_ptr) =
	      Add_dependent_neg(formula_lsList_ptr, sons_literals_lsList,
				 b_res, V_op_code(f_vertex_ptr));
	  }
	}
      }
      
      list_status = lsDestroy(sons_vertices_lsList, NULL);
      list_status = lsDestroy(sons_literals_lsList, NULL);
      break;
    default:
      b_res = 0;
    }

  assert(b_res != 0);
  return b_res;
}

void Clear_clause(lsGeneric t_lsGeneric)
{
  int    list_status;
  lsList *clause_lsList_ptr = UNCAST_CLAUSE_ITEM(t_lsGeneric);

  list_status = lsDestroy(*clause_lsList_ptr,NULL);
  FREE(clause_lsList_ptr);

  return;
}

lsList *Make_cnf(dag_t *dag_ptr, vertex_t *a_vertex_ptr, int sign)
{
  vertex_t *f_vertex_ptr;
  lsList   *formula_lsList_ptr;
  st_table *visited_st_table_ptr;
  int      b;
  int      is_cnf;
  int      polarity;

  /* If the requested cnf is already there return it */
  if ((sign == POS_CNF) && V_pos_lsList_ptr(a_vertex_ptr)) 
    return V_pos_lsList_ptr(a_vertex_ptr);
  if ((sign == NEG_CNF) && V_neg_lsList_ptr(a_vertex_ptr))
    return V_neg_lsList_ptr(a_vertex_ptr);

  /* Skip [] */
  f_vertex_ptr = Get_vertex_son(V_ini_vertex_ptr(a_vertex_ptr));
  
  /* Holds resulting clauses */
  formula_lsList_ptr = ALLOC(lsList,1);
  *formula_lsList_ptr = lsCreate();    

  /* Dealing with cases: */

  /* T */
  if (f_vertex_ptr == dag_top(dag_ptr)) {
    if (sign == POS_CNF)
      V_pos_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr;
    else {
      Add_clause(formula_lsList_ptr, Make_empty_clause());
      V_neg_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr;
    }
    return formula_lsList_ptr;
  }

  /* F */
  if (f_vertex_ptr == dag_bot(dag_ptr)) {
    if (sign == POS_CNF) {
      Add_clause(formula_lsList_ptr, Make_empty_clause());
      V_pos_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr;
    } else
      V_neg_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr;
    return formula_lsList_ptr;
  }

  /* Simple conjunction, simple disjunction */
  if (Is_simple_vertex(f_vertex_ptr)) {
    Simple_cnf_conversion(formula_lsList_ptr, f_vertex_ptr, sign);
    ((sign == POS_CNF) ?
     (V_pos_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr) :
     (V_neg_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr));
    return formula_lsList_ptr;
  }

  /* Cnf */
  is_cnf = Is_cnf_vertex(f_vertex_ptr);

  if (is_cnf && (sign == POS_CNF)) {
    Cnf_cnf_conversion(formula_lsList_ptr, f_vertex_ptr);
    V_pos_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr;
    return formula_lsList_ptr;
  } 

  /* Anything else */
  /* An optimization step: if the negation of the requested formula is
     already there, then just flip the literal representing the whole
     formula. DON'T do that if:
      - it is the negation of a cnf that is actually requested 
      - the cnf translation is optimized (polarities change!) */

  if (!is_cnf && (Cnf_conversion(dag_ptr) == STD_CONVERSION) &&
      V_pos_lsList_ptr(a_vertex_ptr) && (sign == NEG_CNF)) {
    Merge_formulae(formula_lsList_ptr, V_pos_lsList_ptr(a_vertex_ptr));
    Negate_formula(formula_lsList_ptr);
    V_neg_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr;
    return formula_lsList_ptr;
  }

  if (!is_cnf && (Cnf_conversion(dag_ptr) == STD_CONVERSION) &&
      V_neg_lsList_ptr(a_vertex_ptr) && (sign == POS_CNF)) {
    Merge_formulae(formula_lsList_ptr, V_neg_lsList_ptr(a_vertex_ptr));
    Negate_formula(formula_lsList_ptr);
    V_pos_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr;
    return formula_lsList_ptr;
  }

  visited_st_table_ptr = st_init_table(st_ptrcmp, st_ptrhash);
  /* Choose polarity: both polarities for standard conversion, 
     requested polarity for optimized conversion */
  polarity = ((Cnf_conversion(dag_ptr) == STD_CONVERSION) ? BOTH_CNF : sign);
  b = Make_cnf_rec(dag_ptr, f_vertex_ptr, formula_lsList_ptr,
		   visited_st_table_ptr, polarity);
  st_free_table(visited_st_table_ptr);
  /* Add the unit clause that stands for the formula */
  Add_clause(formula_lsList_ptr, Make_unit_clause(b,sign));
  ((sign == POS_CNF) ?
     (V_pos_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr) :
     (V_neg_lsList_ptr(a_vertex_ptr) = formula_lsList_ptr));

  return formula_lsList_ptr;
}


/* *********************************************************************** */
/* Main decision procedure */
/* *********************************************************************** */
int Clause_compare(lsGeneric item1, lsGeneric item2)
{
  return (lsLength(*UNCAST_CLAUSE_ITEM(item1)) - lsLength(*UNCAST_CLAUSE_ITEM(item2)));
}

int Test_dp_sat_rec(image_t *image_ptr, dag_t *dag_ptr,
		    lsList *formula_lsList_ptr,
		    Cons_func_ptr_t Test_star_consistency)
{
  lsStatus list_status;
  int      result;

  /* An optimization for making SATO run faster */
  /* SATO likes shortest clauses first, so the formula is
     sorted in ascending order using the clause length as key */
#ifdef SORT_CLAUSES
   list_status = lsSort(*formula_lsList_ptr, Clause_compare);  
#else
   list_status = LS_OK;
#endif

  /* Referencing the formula as the current main formula */
  Main_formula_lsList_ptr(image_ptr) = formula_lsList_ptr;

  /* Running SATO on the formula */
  result = sato(image_ptr, dag_ptr, Test_star_consistency, formula_lsList_ptr);

  /* Don't trust SATO result immediately: a propositional model might 
     be modally inconsistent! So if the last consistency checking was 
     false, return 0 instead of 1. Otherwise trust SATO */
  if (!Last_cons_res(image_ptr)) result = 0;

  return result;
}

int Test_dp_sat(image_t *image_ptr, dag_t *dag_ptr,
		 Cons_func_ptr_t Test_star_consistency)
{
  vertex_t *t_vertex_ptr;
  int      result;

  t_vertex_ptr = Root_vertex_ptr(dag_ptr);
  result = Test_dp_sat_rec(image_ptr, dag_ptr,
			   V_pos_lsList_ptr(t_vertex_ptr),
			   Test_star_consistency);

 return result;
}

/* *********************************************************************** */
/* Utilities for consistency checking */
/* *********************************************************************** */

lsList *Merge_formulae_to_new(lsList *first_lsList_ptr, lsList *second_lsList_ptr) 
{ 
  lsGen     t_lsGen; 
  lsGeneric t_lsGeneric; 
  lsStatus  list_status; 
  lsList    *t_lsList_ptr;
  
  t_lsList_ptr = ALLOC(lsList, 1);
  *t_lsList_ptr = lsCreate();
  lsForEachItem(*first_lsList_ptr, t_lsGen, t_lsGeneric) { 
    list_status = lsNewEnd(*t_lsList_ptr, t_lsGeneric, LS_NH); 
  } 
  lsForEachItem(*second_lsList_ptr, t_lsGen, t_lsGeneric) { 
    list_status = lsNewEnd(*t_lsList_ptr, t_lsGeneric, LS_NH); 
  } 

  return t_lsList_ptr;
} 

lsList *Make_cnf_conj(dag_t *dag_ptr, lsList *alpha_lsList_ptr)
{
  lsList       *t_lsList_ptr;
  lsGen        t_lsGen;
  lsGeneric    vertex_lsGeneric;
  vertex_t     *alpha_vertex_ptr;
  
  t_lsList_ptr = ALLOC(lsList, 1);
  *t_lsList_ptr = lsCreate();
  lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
    alpha_vertex_ptr = UNCAST_VERTEX_ITEM(vertex_lsGeneric);
    Merge_formulae(t_lsList_ptr, Make_cnf(dag_ptr, alpha_vertex_ptr, POS_CNF));
  }

  return t_lsList_ptr;
}

lsList *Make_implication(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr)
{
  lsList    *t_clause_ptr;
  lsGen     t_lsGen;
  lsGeneric vertex_lsGeneric;
  vertex_t  *alpha_vertex_ptr;

  t_clause_ptr = Make_empty_clause();
  /* Add the negation of each alpha */
  lsForEachItem(*alpha_lsList_ptr, t_lsGen, vertex_lsGeneric) {
    alpha_vertex_ptr = UNCAST_VERTEX_ITEM(vertex_lsGeneric);
    Add_literal(t_clause_ptr, SPREAD(V_value(alpha_vertex_ptr)), -1);
  }
  /* Add the beta */
  Add_literal(t_clause_ptr, SPREAD(V_value(beta_vertex_ptr)), 1);

  return t_clause_ptr;
}

/* *********************************************************************** */
/* Output routines */
/* *********************************************************************** */

void Print_cnf(lsList *formula_lsList_ptr)
{
  lsList    *clause_lsList_ptr;
  lsGen     clause_lsGen, lit_lsGen;
  lsGeneric clause_lsGeneric, lit_lsGeneric;
  int       lit;

  lsForEachItem(*formula_lsList_ptr, clause_lsGen, clause_lsGeneric) {
    clause_lsList_ptr = UNCAST_CLAUSE_ITEM(clause_lsGeneric);
    printf("( ");
    lsForEachItem(*clause_lsList_ptr, lit_lsGen, lit_lsGeneric) {
      lit = UNCAST_LITERAL_ITEM(lit_lsGeneric);
      printf("%d ",lit);
    }
    printf(")\n");
  }

  return;
}

void Print_single_call(vertex_t *beta_vertex_ptr, lsList *to_test_lsList_ptr)
{
  printf("Testing ");
  printf("-%d\n",SPREAD(V_value(beta_vertex_ptr)));
  
  printf("(Corresponding to xref item ");
  printf("%d)\n\n",V_value(beta_vertex_ptr));
  
  printf("Gives the formula\n");
  Print_cnf(to_test_lsList_ptr);
  printf("\n");

  return;
}

void Print_simple_call(vertex_t *alpha_vertex_ptr, vertex_t *beta_vertex_ptr,
		lsList *to_test_lsList_ptr)
{
  printf("Testing ");
  printf("%d ", SPREAD(V_value(alpha_vertex_ptr)));
  printf("-%d\n",SPREAD(V_value(beta_vertex_ptr)));
  
  printf("(Corresponding to xref items ");
  printf("%d ", V_value(alpha_vertex_ptr));
  printf("and %d)\n\n",V_value(beta_vertex_ptr));
  
  printf("Gives the formula\n");
  Print_cnf(to_test_lsList_ptr);
  printf("\n");

  return;
}

void Print_complex_call(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr, 
		lsList *to_test_lsList_ptr)
{
  lsGen      d_lsGen;
  lsGeneric  d_lsGeneric;

  printf("Testing ");
  lsForEachItem(*alpha_lsList_ptr, d_lsGen, d_lsGeneric) {
    printf("%d ", SPREAD(V_value(UNCAST_VERTEX_ITEM(d_lsGeneric))));
  }
  printf("-%d\n",SPREAD(V_value(beta_vertex_ptr)));
  
  printf("(Corresponding to xref items ");
  lsForEachItem(*alpha_lsList_ptr, d_lsGen, d_lsGeneric) {
    printf("%d ", V_value(UNCAST_VERTEX_ITEM(d_lsGeneric)));
  }
  printf("and %d)\n\n",V_value(beta_vertex_ptr));
  
  printf("Gives the formula\n");
  Print_cnf(to_test_lsList_ptr);
  printf("\n");

  return;
}

void Print_alpha_beta(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr) 
{
  lsGen      d_lsGen;
  lsGeneric  d_lsGeneric;

  lsForEachItem(*alpha_lsList_ptr, d_lsGen, d_lsGeneric) {
    printf("%d ", V_value(UNCAST_VERTEX_ITEM(d_lsGeneric)));
  }
  printf("and %d ",V_value(beta_vertex_ptr));
 
  return;
}

void Print_alpha(lsList *alpha_lsList_ptr) 
{
  lsGen      d_lsGen;
  lsGeneric  d_lsGeneric;

  lsForEachItem(*alpha_lsList_ptr, d_lsGen, d_lsGeneric) {
    printf("%d ", V_value(UNCAST_VERTEX_ITEM(d_lsGeneric)));
  }
  return;
}


/* *********************************************************************** */
/* Utilities about cnf_info */
/* *********************************************************************** */
cnf_info_t *New_cnf_info(int b_value)
{
  cnf_info_t *t_cnf_info_ptr;

  t_cnf_info_ptr = ALLOC(cnf_info_t, 1);
  t_cnf_info_ptr->b_value = b_value;
  t_cnf_info_ptr->pos_added_lsList_ptr = NIL(lsList);
  t_cnf_info_ptr->neg_added_lsList_ptr = NIL(lsList);

  return t_cnf_info_ptr;
}

/* *********************************************************************** */
/* Agents management */
/* *********************************************************************** */
agent_t *New_agent()
{
  agent_t *t_agent_ptr;

  t_agent_ptr = ALLOC(agent_t,1);
  Alpha_lsList_ptr(t_agent_ptr) = ALLOC(lsList,1);
  *Alpha_lsList_ptr(t_agent_ptr) = lsCreate();
  Beta_lsList_ptr(t_agent_ptr) = ALLOC(lsList,1);
  *Beta_lsList_ptr(t_agent_ptr) = lsCreate();

  return t_agent_ptr;
}

void Clear_agent(stGeneric t_stGeneric)
{
  agent_t  *t_agent_ptr;
  lsStatus list_status;

  t_agent_ptr = UNCAST_AGENT(t_stGeneric);
  list_status = lsDestroy(*Alpha_lsList_ptr(t_agent_ptr), NULL);
  list_status = lsDestroy(*Beta_lsList_ptr(t_agent_ptr), NULL);
  FREE(Alpha_lsList_ptr(t_agent_ptr));
  FREE(Beta_lsList_ptr(t_agent_ptr));
  FREE(t_agent_ptr);

  return;
}

/* With this routine, alpha and beta lists are ordered 
   according to the SATO stack. */
void Classify_agents(image_t *image_ptr, dag_t *dag_ptr,
		     st_table *agents_st_table_ptr)
{
  int       i;
  int       first_modal_atom;
  int       last_modal_atom;
  int       ag_num, cur_atom;
  vertex_t  *atom_vertex_ptr;
  stGeneric *ag_stGeneric_ptr;
  lsList    *switch_lsList_ptr;
  lsStatus  list_status;
  int       t_status;
  agent_t   *agent_ptr;

  first_modal_atom = SPREAD(Lpa(dag_ptr) + 1);
  last_modal_atom = SPREAD(Lma(dag_ptr));

  for (i = 0; i < Stack_idx(image_ptr); i++) {
    cur_atom = UNVALUATE(Stack(image_ptr)[i].v);
    if ((cur_atom >= first_modal_atom) && (cur_atom <= last_modal_atom)) {
      atom_vertex_ptr = Xref_vertex_ptr_table(dag_ptr)[UNSPREAD(cur_atom)];
      ag_num = V_value(V_ini_vertex_ptr(atom_vertex_ptr));
      t_status = st_find_or_add(agents_st_table_ptr, CAST_KEY(ag_num), &ag_stGeneric_ptr);
      if (!t_status) {
	/* The agent was never listed before */
	agent_ptr = New_agent();
	*ag_stGeneric_ptr = CAST_AGENT(agent_ptr);
      }

      /* Decide if it is a beta or an alpha modal atom */
      if (Value(image_ptr)[cur_atom] == FF) 
	switch_lsList_ptr = Beta_lsList_ptr(UNCAST_AGENT(*ag_stGeneric_ptr));
      else 
	switch_lsList_ptr = Alpha_lsList_ptr(UNCAST_AGENT(*ag_stGeneric_ptr));

      /* Add a pointer to the modal atom in the appropriate list for the agent */
      list_status = lsNewEnd(*switch_lsList_ptr, CAST_VERTEX_ITEM(atom_vertex_ptr), LS_NH);
    }
  }
  
  return;
}
 
/* With this routine, agents are classified according to the SATO stack. */
/* Alpha and beta lists are not attached to the agent */
void Classify_agents_light(image_t *image_ptr, dag_t *dag_ptr,
			   st_table *agents_st_table_ptr)
{
  int       i;
  int       first_modal_atom;
  int       last_modal_atom;
  int       ag_num, cur_atom;
  vertex_t  *atom_vertex_ptr;
  stGeneric *ag_stGeneric_ptr;
  int       t_status;
  agent_t   *agent_ptr;

  first_modal_atom = SPREAD(Lpa(dag_ptr) + 1);
  last_modal_atom = SPREAD(Lma(dag_ptr));

  for (i = 0; i < Stack_idx(image_ptr); i++) {
    cur_atom = UNVALUATE(Stack(image_ptr)[i].v);
    if ((cur_atom >= first_modal_atom) && (cur_atom <= last_modal_atom)) {
      atom_vertex_ptr = Xref_vertex_ptr_table(dag_ptr)[UNSPREAD(cur_atom)];
      ag_num = V_value(V_ini_vertex_ptr(atom_vertex_ptr));
      t_status = st_find_or_add(agents_st_table_ptr, CAST_KEY(ag_num), &ag_stGeneric_ptr);
      /* Always put a dummy agent data structure */
      if (!t_status) {
	agent_ptr = NIL(agent_t);
	*ag_stGeneric_ptr = CAST_AGENT(agent_ptr);
      }
    }
  }
  
  return;
}

lsList *Copy_relevant_atoms(image_t *image_ptr, lsList *source_lsList_ptr)
{
  lsGen     t_lsGen;
  lsGeneric t_lsGeneric;
  lsStatus  list_status;
  lsList    *dest_lsList_ptr;
  int       i = 0;

  dest_lsList_ptr = ALLOC(lsList,1);
  *dest_lsList_ptr = lsCreate();

  lsForEachItem(*source_lsList_ptr, t_lsGen, t_lsGeneric) {
    while (UNSPREAD(UNVALUATE(Stack(image_ptr)[i].v)) != V_value(UNCAST_VERTEX_ITEM(t_lsGeneric))) ++i;
    if (Test_relevance(Stack(image_ptr), Value(image_ptr), i))
        list_status = lsNewEnd(*dest_lsList_ptr, t_lsGeneric, LS_NH);
  }

  return dest_lsList_ptr;
}

lsList *Keep_relevant_atoms(image_t *image_ptr, lsList *source_lsList_ptr)
{
  lsGen     t_lsGen;
  lsGeneric t_lsGeneric;
  lsStatus  list_status;
  int       i = 0;

  lsForEachItem(*source_lsList_ptr, t_lsGen, t_lsGeneric) {
    while (UNSPREAD(UNVALUATE(Stack(image_ptr)[i].v)) != V_value(UNCAST_VERTEX_ITEM(t_lsGeneric))) ++i;
    if (!Test_relevance(Stack(image_ptr), Value(image_ptr), i))
        list_status = lsDelBefore(t_lsGen, &t_lsGeneric);
  }

  return source_lsList_ptr;
}

 
/* *********************************************************************** */
/* Evaluation of cnfs */
/* *********************************************************************** */
int Eval_cnf(lsList *formula_lsList_ptr, st_table *mu_st_table_ptr)
{
  lsGen     or_lsGen, lit_lsGen;
  lsStatus  list_status;
  lsGeneric or_lsGeneric, lit_lsGeneric;
  lsList    *t_clause_lsList_ptr;
  int       del_clause, bot_clause;
  int       lit,j;
  int       table_status;
  stGeneric value_stGeneric;

  j = 2;
  lsForEachItem(*formula_lsList_ptr, or_lsGen, or_lsGeneric) {
    t_clause_lsList_ptr = UNCAST_CLAUSE_ITEM(or_lsGeneric);
    del_clause = 0; bot_clause = 1;
    lsForEachItem(*t_clause_lsList_ptr, lit_lsGen, lit_lsGeneric) {
      lit = UNCAST_LITERAL_ITEM(lit_lsGeneric);
      table_status = st_lookup(mu_st_table_ptr, CAST_KEY(UNVALUATE(lit)), &value_stGeneric);
      if (table_status) {
	if ((UNCAST_TVALUE(value_stGeneric) * lit) > 0) {
	  del_clause = 1; bot_clause = 0; break;
	} 
      } else bot_clause = 0;
    }
    if (bot_clause) {
      printf("The clause:\n");
      lsForEachItem(*t_clause_lsList_ptr, lit_lsGen, lit_lsGeneric) {
	lit = UNCAST_LITERAL_ITEM(lit_lsGeneric);
	printf("%d ",lit);
      }
      printf("\n on line %d was contradicted\n", j);
      return 0;
    }
    if (del_clause) list_status = lsFinish(lit_lsGen);
    if (!del_clause) return -1;
    del_clause = 0;
    ++j;
  }

  return 1;
}

lsList *Assign_cnf(lsList *formula_lsList_ptr, int *mu_table_ptr)
{
  lsGen     or_lsGen, lit_lsGen;
  lsStatus  list_status;
  lsGeneric or_lsGeneric, lit_lsGeneric;
  lsList    *t_clause_lsList_ptr, *s_formula_lsList_ptr, *s_clause_lsList_ptr; 
  int       del_clause, bot_clause;
  int       lit,ato,sign;
  
  s_formula_lsList_ptr = ALLOC(lsList, 1);
  *s_formula_lsList_ptr = lsCreate();
  bot_clause = 0;

  lsForEachItem(*formula_lsList_ptr, or_lsGen, or_lsGeneric) {
    t_clause_lsList_ptr = UNCAST_CLAUSE_ITEM(or_lsGeneric);
    /* Preparing a new clause */
    s_clause_lsList_ptr = Make_empty_clause();
    del_clause = 0; bot_clause = 1;
    lsForEachItem(*t_clause_lsList_ptr, lit_lsGen, lit_lsGeneric) {
      lit = UNCAST_LITERAL_ITEM(lit_lsGeneric);
      ato = UNVALUATE(lit);

      if (mu_table_ptr[ato] == 1)           /* TT true */
	sign = 1;
      else if (mu_table_ptr[ato] == 0)      /* FF false */
	sign = -1;
      else 
	sign = 0;                           /* DC Don't care */

      if ((sign * lit) > 0) {
	del_clause = 1; bot_clause = 0; break;
      } else if ((sign * lit) == 0) {
	Add_literal(s_clause_lsList_ptr, lit, 1);
	bot_clause = 0;
      }
    }

    if (del_clause) {
      lsDestroy(*s_clause_lsList_ptr, NULL);
      FREE(s_clause_lsList_ptr);
      list_status = lsFinish(lit_lsGen);
    } else
      Add_clause(s_formula_lsList_ptr, s_clause_lsList_ptr);
    
    if (bot_clause) break;
  }

  if (bot_clause) lsFinish(or_lsGen);
  return s_formula_lsList_ptr;
}

lsList *Assign_cnf2(lsList *formula_lsList_ptr, st_table *mu_st_table_ptr)
{
  lsGen     or_lsGen, lit_lsGen;
  lsStatus  list_status;
  lsGeneric or_lsGeneric, lit_lsGeneric;
  lsList    *t_clause_lsList_ptr, *s_formula_lsList_ptr, *s_clause_lsList_ptr; 
  int       del_clause, bot_clause;
  int       lit,ato,sign;
  int       table_status;
  stGeneric value_stGeneric;
  
  s_formula_lsList_ptr = ALLOC(lsList, 1);
  *s_formula_lsList_ptr = lsCreate();
  bot_clause = 0;

  lsForEachItem(*formula_lsList_ptr, or_lsGen, or_lsGeneric) {
    t_clause_lsList_ptr = UNCAST_CLAUSE_ITEM(or_lsGeneric);
    /* Preparing a new clause */
    s_clause_lsList_ptr = Make_empty_clause();
    del_clause = 0; bot_clause = 1;
    lsForEachItem(*t_clause_lsList_ptr, lit_lsGen, lit_lsGeneric) {
      lit = UNCAST_LITERAL_ITEM(lit_lsGeneric);
      ato = UNVALUATE(lit);

      table_status = st_lookup(mu_st_table_ptr, CAST_KEY(ato), &value_stGeneric);

      if (table_status) {
	if ((UNCAST_TVALUE(value_stGeneric) *lit) > 0)           /* TT true */
	  sign = 1;
	else                                                     /* FF false */
	  sign = -1;
      } else 
	sign = 0;                                                /* DC Don't care */

      if (sign > 0) {
	del_clause = 1; bot_clause = 0; break;
      } else if (sign == 0) {
	Add_literal(s_clause_lsList_ptr, lit, 1);
	bot_clause = 0;
      }
    }

    if (del_clause) {
      lsDestroy(*s_clause_lsList_ptr, NULL);
      FREE(s_clause_lsList_ptr);
      list_status = lsFinish(lit_lsGen);
    } else
      Add_clause(s_formula_lsList_ptr, s_clause_lsList_ptr);
    
    if (bot_clause) break;
  }

  if (bot_clause) lsFinish(or_lsGen);
  return s_formula_lsList_ptr;
}

void Free_cnf(lsList *formula_lsList_ptr)
{
  lsGen     or_lsGen;
  lsGeneric or_lsGeneric;
  lsList    *t_clause_lsList_ptr;

  lsForEachItem(*formula_lsList_ptr, or_lsGen, or_lsGeneric) {
    t_clause_lsList_ptr = UNCAST_CLAUSE_ITEM(or_lsGeneric);
    lsDestroy(*t_clause_lsList_ptr, NULL);
    FREE(t_clause_lsList_ptr);
  }
  lsDestroy(*formula_lsList_ptr, NULL);
  FREE(formula_lsList_ptr);
}

st_table *Parse_model(FILE *model_file)
{
  int      lit;
  st_table *mu_st_table_ptr;
  int      table_status;

  mu_st_table_ptr = st_init_table(st_numcmp, st_numhash);
  while (fscanf(model_file, "%d", &lit) != EOF) {
/*      printf("%d ", lit);  */
    table_status = st_insert(mu_st_table_ptr, 
			     CAST_KEY(UNVALUATE(lit)), CAST_VALUE((lit > 0) ? 1 : -1));
  }    

  return mu_st_table_ptr;
}

lsList *Parse_clause(char *buffer_char_ptr)
{
  char   *lit_char_ptr;
  lsList *t_clause_lsList_ptr;
  int    i,j,lit; 

  lit_char_ptr = ALLOC(char,10);
  t_clause_lsList_ptr = Make_empty_clause();
  i = 0; 
  while (buffer_char_ptr[i] != '\0') {
    j = 0;
    while (buffer_char_ptr[i]) {
      lit_char_ptr[j] = buffer_char_ptr[i++];
      if (lit_char_ptr[j] == ' ') {
	lit_char_ptr[j] = '\0'; break;
      } else ++j;
    }
    sscanf(lit_char_ptr, "%d", &lit);
    if (lit != 0)
      Add_literal(t_clause_lsList_ptr, lit, 1);
  }
  FREE(lit_char_ptr);

  return t_clause_lsList_ptr;
}

lsList *Parse_cnf(FILE *cnf_file)
{
  char     *buffer_char_ptr;
  lsList   *formula_lsList_ptr;

  formula_lsList_ptr = ALLOC(lsList,1);
  *formula_lsList_ptr = lsCreate();
  
  buffer_char_ptr = ALLOC(char, BUFDIM);
  if (fgets(buffer_char_ptr, BUFDIM, cnf_file) != NULL) 
    while (fgets(buffer_char_ptr, BUFDIM, cnf_file))
      Add_clause(formula_lsList_ptr, Parse_clause(buffer_char_ptr));

   FREE(buffer_char_ptr);

   return formula_lsList_ptr;
}
   
