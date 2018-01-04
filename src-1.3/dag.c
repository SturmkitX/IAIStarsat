/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE dag.c - *SAT 1.3 */
/*  Formula as a dag */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "dag.h"

#ifdef DEBUG_DAG
void Print_vertex_rec(vertex_t *a_vertex_ptr);
#endif

#ifdef DEBUG_GCOLLECT
void Print_vertex_rec(vertex_t *a_vertex_ptr);
#endif

/* *********************************************************************** */
/* Unique table handling (internal use only!) */
/* *********************************************************************** */

void Add_to_table(st_table *u_uni_st_table_ptr, vertex_t *a_vertex_ptr)
{
  stGeneric     *value_stGeneric_ptr;
  lsList        *vertices_lsList_ptr;
  lsStatus      list_status;
  int           table_status;
  
  table_status = st_find_or_add(u_uni_st_table_ptr, 
				CAST_KEY(V_hash_key(a_vertex_ptr)), 
				&value_stGeneric_ptr);
  if (!table_status) {
    /* The key was not already there... */
    vertices_lsList_ptr = ALLOC(lsList, 1);
    *vertices_lsList_ptr = lsCreate();
  } else 
    vertices_lsList_ptr = UNCAST_VALUE(*value_stGeneric_ptr);
  /* The key was already there... */
  
  list_status = lsNewBegin(*vertices_lsList_ptr, CAST_VERTEX_ITEM(a_vertex_ptr), LS_NH);
  *value_stGeneric_ptr = CAST_VALUE(vertices_lsList_ptr);

  return;
}

void Remove_from_table(st_table *u_uni_st_table_ptr, vertex_t *a_vertex_ptr)
{
  stGeneric     value_stGeneric, key_stGeneric;
  lsList        *vertices_lsList_ptr;
  lsStatus      list_status;
  lsGen         t_lsGen;
  lsGeneric     t_lsGeneric;
  int           table_status;
  
  table_status = st_lookup(u_uni_st_table_ptr, 
			   CAST_KEY(V_hash_key(a_vertex_ptr)), 
			   &value_stGeneric);
  if (!table_status) {
    /* The key was not there... */
    return;
  }
  /* The key was there... */
  vertices_lsList_ptr = UNCAST_VALUE(value_stGeneric);
  if (lsLength(*vertices_lsList_ptr) == 1) {
    /* The list had only one element */
    key_stGeneric = CAST_KEY(V_hash_key(a_vertex_ptr));
    table_status = st_delete(u_uni_st_table_ptr, &key_stGeneric, &value_stGeneric);
    list_status = lsDestroy(*UNCAST_VALUE(value_stGeneric), NULL);
    FREE(value_stGeneric);
  } else {
    /* The list has more than one element */
    lsForEachItem(*vertices_lsList_ptr, t_lsGen, t_lsGeneric) {
      if (UNCAST_VERTEX_ITEM(t_lsGeneric) == a_vertex_ptr) {
	list_status = lsDelBefore(t_lsGen, &t_lsGeneric);
	break;
      }
    }
    /* The loop ALWAYS breaks! */
    list_status = lsFinish(t_lsGen);
  }

  return;
}

vertex_t *Add_unique(st_table *uni_st_table_ptr, vertex_t *t_vertex_ptr)
{
  vertex_t      *cur_vertex_ptr = NIL(vertex_t);
  stGeneric     *value_stGeneric_ptr;
  lsList        *vertices_lsList_ptr;
  lsGen         list_generator;
  lsStatus      list_status;
  lsGeneric     t_lsGeneric;
  int           table_status, broken;

#ifdef DEBUG_DAG
  printf("Considering to uniquely add: ");
  Print_vertex_rec(t_vertex_ptr);
  printf("\n  hash code: %d", V_hash_key(t_vertex_ptr));
  printf("\n\n");
  fflush(stdout);
#endif

  /* Initializations */
  broken = 0;

  /* Hash lookup: trying to insert straightly <key, value>.
     If something is already there then worry about it */
  table_status = st_find_or_add(uni_st_table_ptr, 
				CAST_KEY(V_hash_key(t_vertex_ptr)), 
				&value_stGeneric_ptr);
  if (!table_status) {
    /* The key was not already there... */
    vertices_lsList_ptr = ALLOC(lsList, 1);
    *vertices_lsList_ptr = lsCreate();
    list_status = lsNewBegin(*vertices_lsList_ptr, CAST_VERTEX_ITEM(t_vertex_ptr), LS_NH);
    *value_stGeneric_ptr = CAST_VALUE(vertices_lsList_ptr);
  } else {
    /* The key was there. Is the formula a duplicate? */
    vertices_lsList_ptr = UNCAST_VALUE(*value_stGeneric_ptr);
    lsForEachItem(*vertices_lsList_ptr, list_generator, t_lsGeneric) {
      cur_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);
      if (Are_dag_vtx_equal(t_vertex_ptr,cur_vertex_ptr)) {
	broken = 1; 
	break;
      }
    }
    if (broken) {
      /* The formula is a duplicate */
      list_status = lsFinish(list_generator);
      g_delete_vertex(t_vertex_ptr, Clear_vertex_info_soft, NULL);
      t_vertex_ptr = cur_vertex_ptr;
    } else {
      /* The formula has the same key but it is not in the list */
      list_status = lsNewBegin(*vertices_lsList_ptr, CAST_VERTEX_ITEM(t_vertex_ptr), LS_NH);
      *value_stGeneric_ptr = CAST_VALUE(vertices_lsList_ptr);
    }
  }

  assert(t_vertex_ptr != NIL(vertex_t));
  return (t_vertex_ptr);
}


/* *********************************************************************** */
/* Constructors */
/* *********************************************************************** */

typedef vertex_t *vertex_ptr_t;

dag_t *Init_dag()
{
  dag_t *dag_ptr;
  int   i;

  dag_ptr = ALLOC(dag_t,1);

  /* Making tables: unique hash table, garbage hash table, xref table */
  dag_ptr->uni_st_table_ptr = st_init_table(st_numcmp, st_numhash);
  dag_ptr->trash_st_table_ptr = st_init_table(st_ptrcmp, st_ptrhash);
  dag_ptr->xref_vertex_ptr_table = ALLOC(vertex_ptr_t,MAXATOM);
  for (i = 0; i < MAXATOM; i++)
    dag_ptr->xref_vertex_ptr_table[i] = NIL(vertex_t);

  /* Initializing inner graph */
  dag_ptr->inner_graph_ptr = g_alloc();

  /* Setting up default vertices: root, top, bottom */
  dag_ptr->root_vertex_ptr = NIL(vertex_t);
  dag_ptr->top_vertex_ptr = 
    New_vertex(dag_ptr->inner_graph_ptr, top_code, empty_code, top_code);
  dag_ptr->bot_vertex_ptr = 
    New_vertex(dag_ptr->inner_graph_ptr, bot_code, empty_code, bot_code);

  /* Setting up default values: last propositional, last modal, last added atoms */
  (dag_ptr->lpa) = (dag_ptr->lma) = (dag_ptr->laa) = -1;

  /* Default value for modal simplification is 0 (no simplification) */
  (dag_ptr->box_simplify) = 0;

  /* Default value for cnf conversion is STD_CONVERSION */
  (dag_ptr->cnf_conversion) = STD_CONVERSION;

  assert(dag_ptr != NIL(dag_t));
  return dag_ptr;
}

vertex_t *Add_atom(dag_t *dag_ptr, fnode_t *atom_fnode_ptr) 
{ 
  vertex_t *t_vertex_ptr;
  int      value;

  /* Preconditions */
  if (dag_ptr == NIL(dag_t)) return NIL(vertex_t);
  if (!Is_atom(atom_fnode_ptr)) return NIL(vertex_t); 
  value = Valuex(atom_fnode_ptr); 
  if (value > MAXATOM) return NIL(vertex_t); 

  /* Atoms are NOT hashed. Uniqueness is ensured by the
     very same xref_vertex_ptr_table */
  if (dag_ptr->xref_vertex_ptr_table[value] == NIL(vertex_t)) { 
    t_vertex_ptr = g_add_vertex(dag_ptr->inner_graph_ptr);
    Vertex_info(t_vertex_ptr) = 
      CAST_VERTEX_INFO(New_vertex_info(Copy_fnode(atom_fnode_ptr), HASH_ATOM(value)));
    dag_ptr->xref_vertex_ptr_table[value] = t_vertex_ptr;
    if (value > Lpa(dag_ptr)) dag_ptr->lpa = value; 
    dag_ptr->root_vertex_ptr = t_vertex_ptr;
  } else 
    t_vertex_ptr = dag_ptr->xref_vertex_ptr_table[value];
  
  assert(t_vertex_ptr != NIL(vertex_t));
  return (t_vertex_ptr);
} 

vertex_t *Add_unary_op(dag_t *dag_ptr, vertex_t *a_vertex_ptr, 
		       fnode_t *op_fnode_ptr)
{
  vertex_t      *t_vertex_ptr;
  edge_t        *t_edge_ptr;
  int           hash_key;
  int           trash_status;

#ifdef DEBUG_DAG
  printf("Considering to add operator %d to: ", Op_code(op_fnode_ptr));
  Print_vertex_rec(a_vertex_ptr);
  printf("\n\n");
  fflush(stdout);
#endif

  /* Preconditions */
  if (!Is_unary(op_fnode_ptr)) return NIL(vertex_t); 
  if (dag_ptr == NIL(dag_t)) return NIL(vertex_t);
  if (a_vertex_ptr == NIL(vertex_t)) return NIL(vertex_t);

  /* Dealing with -T and -F */
  if (Op_code(op_fnode_ptr) == not_code) {
    if (a_vertex_ptr == dag_top(dag_ptr)) return dag_bot(dag_ptr);
      
    if (a_vertex_ptr == dag_bot(dag_ptr)) return dag_top(dag_ptr);
  }

  /* Propositional simplification */
  /* Rules:
     --A => A     
  */

  /* Optional modal simplification */
  /* Rules:
     []T => T
     <>F => F */

  t_vertex_ptr = NIL(vertex_t);

  switch (Op_code(op_fnode_ptr))
    {
    case not_code:
      if (V_op_code(a_vertex_ptr) == not_code) 
	t_vertex_ptr = Get_vertex_son(a_vertex_ptr);
      break;
    case box_code:
      if (Box_simplify(dag_ptr)) 
	if (a_vertex_ptr == dag_top(dag_ptr)) t_vertex_ptr = dag_top(dag_ptr);
      break;
    case dia_code:
      if (Box_simplify(dag_ptr))
	if (a_vertex_ptr == dag_bot(dag_ptr)) t_vertex_ptr = dag_bot(dag_ptr);
      break;
      }

  /* Any simplification occured? */
  if (t_vertex_ptr != NIL(vertex_t)) {
    trash_status = Check_and_trash_vertex(dag_ptr, a_vertex_ptr);
    return t_vertex_ptr;
  }

  /* Hash key calculation: we want different agents to be different
     atoms so they get different hash keys */
  hash_key = HASH_OP(Op_code(op_fnode_ptr), V_hash_key(a_vertex_ptr));
  if ((Op_code(op_fnode_ptr) == box_code) ||
      (Op_code(op_fnode_ptr) == dia_code))
    hash_key = HASH_OP(Valuex(op_fnode_ptr), hash_key);

  /* Adding the node (temporarily!) as a father of a_vertex_ptr */
  t_vertex_ptr = g_add_vertex(dag_ptr->inner_graph_ptr);
  Vertex_info(t_vertex_ptr) = 
    CAST_VERTEX_INFO(New_vertex_info(Copy_fnode(op_fnode_ptr), hash_key));
  t_edge_ptr = g_add_edge(t_vertex_ptr, a_vertex_ptr);

  /* Try to uniquely add the formula. */
  t_vertex_ptr = Add_unique(dag_ptr->uni_st_table_ptr, t_vertex_ptr);
  dag_ptr->root_vertex_ptr = t_vertex_ptr;

  assert(t_vertex_ptr != NIL(vertex_t));
  return (t_vertex_ptr);
}

vertex_t *Add_binary_op(dag_t *dag_ptr, 
			vertex_t *a_vertex_ptr, vertex_t *b_vertex_ptr, 
			fnode_t *op_fnode_ptr)
{
  vertex_t      *t_vertex_ptr, *s_vertex_ptr;
  edge_t        *t_edge_ptr;
  fnode_t       *t_op_fnode_ptr;
  int           hash_key;
  int           compl_pair;
  int           trash_a, trash_b;
  int           trash_status;

#ifdef DEBUG_DAG
  printf("Considering to conjoin: ");
  Print_vertex_rec(a_vertex_ptr);
  printf("\n");
  printf("using operator %d with: ", Op_code(op_fnode_ptr));
  Print_vertex_rec(b_vertex_ptr);
  printf("\n\n");
  fflush(stdout);
#endif

  /* Preconditions */
  if (Is_binary(op_fnode_ptr)==0) return NIL(vertex_t);
  if (dag_ptr == NIL(dag_t)) return NIL(vertex_t);
  if (a_vertex_ptr == NIL(vertex_t)) return NIL(vertex_t);
  if (b_vertex_ptr == NIL(vertex_t)) return NIL(vertex_t);

  /* Dealing with duplicated operands */
  if (a_vertex_ptr == b_vertex_ptr) 
    switch (Op_code(op_fnode_ptr))
      {
      case or_code: case and_code:
      case iff_code:
	return a_vertex_ptr;
      case imp_code:
	trash_status = Check_and_trash_vertex(dag_ptr, a_vertex_ptr);
	return dag_top(dag_ptr);
      }
  
  /* Propositional simplification */
  /* All simplifications are symmetric, except -> */
  /* Rules:
     A  v  -A => T   A v   T => T   A v   F => A 
     A  &  -A => F   A &   T => A   A &   F => F

     A  -> -A => -A  A ->  T => T   A ->  F => -A
     -A ->  A => A   T ->  A => A   F ->  A => T  

     A <-> -A => F   T <-> A => A   F <-> A => -A */

  t_vertex_ptr = NIL(vertex_t);
  trash_a = trash_b = 0;

  compl_pair = Are_dag_vtx_compl_eq(a_vertex_ptr, b_vertex_ptr);
  switch (Op_code(op_fnode_ptr))
    {
    case or_code:
      if (compl_pair) { 
	t_vertex_ptr = dag_top(dag_ptr); 
	trash_a = (compl_pair < 0);       /* Just trash -A */
	trash_b = (compl_pair > 0); break; }
      if ((a_vertex_ptr == dag_top(dag_ptr)) ||
	  (b_vertex_ptr == dag_top(dag_ptr))) {
	if (!Is_constant(dag_ptr, b_vertex_ptr)) trash_b = 1;
	if (!Is_constant(dag_ptr, a_vertex_ptr)) trash_a = 1;
	t_vertex_ptr = dag_top(dag_ptr); break; }
      if (a_vertex_ptr == dag_bot(dag_ptr)) {
	t_vertex_ptr = b_vertex_ptr; break; }
      if (b_vertex_ptr == dag_bot(dag_ptr)) 
	t_vertex_ptr = a_vertex_ptr; 
      break;
    case and_code:
      if (compl_pair) {
	t_vertex_ptr = dag_bot(dag_ptr);
	trash_a = (compl_pair < 0);       /* Just trash -A */
	trash_b = (compl_pair > 0); break; }
      if ((a_vertex_ptr == dag_bot(dag_ptr)) ||
	  (b_vertex_ptr == dag_bot(dag_ptr))) {
	if (!Is_constant(dag_ptr, b_vertex_ptr)) trash_b = 1;
	if (!Is_constant(dag_ptr, a_vertex_ptr)) trash_a = 1;
	t_vertex_ptr = dag_bot(dag_ptr); break; }
      if (a_vertex_ptr == dag_top(dag_ptr)) {
	t_vertex_ptr = b_vertex_ptr; break; }
      if (b_vertex_ptr == dag_top(dag_ptr)) 
	t_vertex_ptr = a_vertex_ptr; 
      break;
    case imp_code:
      if (compl_pair) {
	t_vertex_ptr = b_vertex_ptr; break; }
      if (b_vertex_ptr == dag_top(dag_ptr)) {
	trash_a = 1;
	t_vertex_ptr = dag_top(dag_ptr); break; }
      if (b_vertex_ptr == dag_bot(dag_ptr)) {
	t_op_fnode_ptr = Make_formula_nary(not_code, empty_code, Make_empty());
	t_vertex_ptr = Add_unary_op(dag_ptr, a_vertex_ptr, t_op_fnode_ptr);
	Clear_fnode(t_op_fnode_ptr, NULL); break; }
      if (a_vertex_ptr == dag_top(dag_ptr)) {
	t_vertex_ptr = b_vertex_ptr; break; }
      if (a_vertex_ptr == dag_bot(dag_ptr)) {
	trash_b = 1;
	t_vertex_ptr = dag_top(dag_ptr); }
      break;
    case iff_code:
      if (compl_pair) {
	trash_a = (compl_pair < 0);       /* Just trash -A */
	trash_b = (compl_pair > 0); 
	t_vertex_ptr = dag_bot(dag_ptr); break; }

      if ((a_vertex_ptr == dag_bot(dag_ptr)) || 
	  (b_vertex_ptr == dag_bot(dag_ptr))) {
	s_vertex_ptr = (a_vertex_ptr == dag_bot(dag_ptr) ?
			b_vertex_ptr : a_vertex_ptr);
	t_op_fnode_ptr = Make_formula_nary(not_code, empty_code, Make_empty());
	t_vertex_ptr = 
	  Add_unary_op(dag_ptr, s_vertex_ptr, t_op_fnode_ptr);
	Clear_fnode(t_op_fnode_ptr, NULL); break; }

      if ((a_vertex_ptr == dag_top(dag_ptr)) ||
	  (b_vertex_ptr == dag_top(dag_ptr))) 
	t_vertex_ptr = (a_vertex_ptr == dag_top(dag_ptr) ?
			b_vertex_ptr : a_vertex_ptr);
    }
  
  /* Any simplification occured? */
  if (t_vertex_ptr != NIL(vertex_t)) {
    if (trash_a) Check_and_trash_vertex(dag_ptr, a_vertex_ptr);
    if (trash_b) Check_and_trash_vertex(dag_ptr, b_vertex_ptr);
    return t_vertex_ptr;
  }

  /* Ordering between vertices; DO NOT CHANGE ORDER FOR IMPLICATION!  */
  if (Op_code(op_fnode_ptr) != imp_code)
    if (V_hash_key(a_vertex_ptr) > V_hash_key(b_vertex_ptr)) 
      Swap_vertex_ptr(&a_vertex_ptr, &b_vertex_ptr);
  
  /* Hash key calculation */
  hash_key = HASH_OP(Op_code(op_fnode_ptr),V_hash_key(a_vertex_ptr));
  hash_key = HASH_OP(V_hash_key(b_vertex_ptr),hash_key);

  /* Adding the node (temporarily!) as a father of a_vertex_ptr and b_vertex_ptr */
  t_vertex_ptr = g_add_vertex(dag_ptr->inner_graph_ptr);
  Vertex_info(t_vertex_ptr) = CAST_VERTEX_INFO(New_vertex_info(Copy_fnode(op_fnode_ptr), hash_key));
  t_edge_ptr = g_add_edge(t_vertex_ptr, a_vertex_ptr);
  t_edge_ptr = g_add_edge(t_vertex_ptr, b_vertex_ptr);
  
  /* Try to uniquely add the formula. */
  t_vertex_ptr = Add_unique(dag_ptr->uni_st_table_ptr, t_vertex_ptr);
  dag_ptr->root_vertex_ptr = t_vertex_ptr;
  
  assert(t_vertex_ptr != NIL(vertex_t));
  return (t_vertex_ptr);
}


vertex_t *Add_nary_op(dag_t *dag_ptr, 
		      lsList *vertices_lsList_ptr, 
		      fnode_t *op_fnode_ptr)
{
  vertex_t      *t_vertex_ptr, *cur_vertex_ptr;
  vertex_t      *ext_vertex_ptr, *int_vertex_ptr;
  edge_t        *t_edge_ptr;
  int           hash_key;
  lsGen         list_generator, ext_gen, int_gen;
  lsStatus      list_status;
  lsGeneric     t_lsGeneric, ext_lsGeneric, int_lsGeneric;
  int           compl_found, dismiss;
  
#ifdef DEBUG_DAG
  printf("Considering to conjoin:\n");
  lsForEachItem(*vertices_lsList_ptr, list_generator, t_lsGeneric) {
    Print_vertex_rec(UNCAST_VERTEX_ITEM(t_lsGeneric));
    printf ("\n");
  }
  printf("using operator %d", Op_code(op_fnode_ptr));
  printf("\n\n");
  fflush(stdout);
#endif

  /* Preconditions */
  if (Is_nary(op_fnode_ptr)==0) return NIL(vertex_t);
  if (dag_ptr == NIL(dag_t)) return NIL(vertex_t);
  if (vertices_lsList_ptr == NIL(lsList)) return NIL(vertex_t);
  if (lsLength(*vertices_lsList_ptr) == 0) return NIL(vertex_t);  

  /* Dealing with duplicated operands: sorting is on pointers. */
  list_status = lsSort(*vertices_lsList_ptr, Generic_comp);
  list_status = lsUniq(*vertices_lsList_ptr, Generic_comp, NULL);
  /* Trying to give just one operand? */
  if (lsLength(*vertices_lsList_ptr) == 1) {
    list_status = lsFirstItem(*vertices_lsList_ptr, &t_lsGeneric, LS_NH);
    return UNCAST_VERTEX_ITEM(t_lsGeneric);
  }

  /* Simplification */
  /* Rules:
     ... A v -A ... => T
     ... A & -A ... => F
     A v T v B => T       A v F v B => A v B 
     A & T & B => A & B   A & F & B => F     */
  
  /* Sweeping trough the list looking for complementary pairs,
     constant true or constant false */
  compl_found = 0;                                                      
  dismiss = 0;
  lsForEachItem(*vertices_lsList_ptr, ext_gen, ext_lsGeneric) {
    ext_vertex_ptr = UNCAST_VERTEX_ITEM(ext_lsGeneric);
    if (ext_vertex_ptr == dag_top(dag_ptr)) 
      switch (Op_code(op_fnode_ptr)) 
	{
	case and_code: dismiss = 1; break;
	case or_code: compl_found = 1; break;
	}
    if (ext_vertex_ptr == dag_bot(dag_ptr))
      switch (Op_code(op_fnode_ptr)) 
	{
	case and_code: compl_found = 1; break;
	case or_code: dismiss = 1; break;
	}
    if (dismiss) {
      list_status = lsDelBefore(ext_gen, &t_lsGeneric);
      dismiss = 0;
      continue;
    }      
    if (!compl_found) {
      lsForEachItemRev(*vertices_lsList_ptr, int_gen, int_lsGeneric) {
	int_vertex_ptr = UNCAST_VERTEX_ITEM(int_lsGeneric);
	if (ext_vertex_ptr == int_vertex_ptr) break;
	if (Are_dag_vtx_compl_eq(ext_vertex_ptr, int_vertex_ptr) != 0) {
	  compl_found = 1; break;
	}
      }
      list_status = lsFinish(int_gen); /* The innermost loop ALWAYS breaks! */
    }
    
    if (compl_found) break;
  }
  
  if (compl_found) {
    list_status = lsFinish(ext_gen);
    Check_and_trash_vertices(dag_ptr, *vertices_lsList_ptr);
    switch (Op_code(op_fnode_ptr))
      {
      case and_code: return dag_bot(dag_ptr);
      case or_code: return dag_top(dag_ptr);
      }
  }
  
  if (lsLength(*vertices_lsList_ptr) == 0) {
    switch (Op_code(op_fnode_ptr))
      {
      case and_code: return dag_top(dag_ptr);
      case or_code: return dag_bot(dag_ptr);
      }
  }
  
  if (lsLength(*vertices_lsList_ptr) == 1) {
    list_status = lsFirstItem(*vertices_lsList_ptr, &t_lsGeneric, LS_NH);
    return UNCAST_VERTEX_ITEM(t_lsGeneric);
  }


  /* Sorting the list of vertices using hash keys
     This speeds up equality testing */
  list_status = lsSort(*vertices_lsList_ptr, Hash_key_comp);

  /* Hash key calculation */
  hash_key = 0;
  lsForEachItem(*vertices_lsList_ptr, list_generator, t_lsGeneric) {
    cur_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);
    hash_key = HASH_OP(V_hash_key(cur_vertex_ptr), hash_key);
  }
  hash_key = HASH_OP(Op_code(op_fnode_ptr), hash_key);

  /* Adding the node (temporarily!) */
  t_vertex_ptr = g_add_vertex(dag_ptr->inner_graph_ptr);
  Vertex_info(t_vertex_ptr) = CAST_VERTEX_INFO(New_vertex_info(Copy_fnode(op_fnode_ptr), hash_key));
  lsForEachItem(*vertices_lsList_ptr, list_generator, t_lsGeneric) {
    cur_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);
    t_edge_ptr = g_add_edge(t_vertex_ptr, cur_vertex_ptr);
  }
  
  /* Try to uniquely add the formula. */
  t_vertex_ptr = Add_unique(dag_ptr->uni_st_table_ptr, t_vertex_ptr);
  dag_ptr->root_vertex_ptr = t_vertex_ptr;
  
  assert(t_vertex_ptr != NIL(vertex_t));
  return (t_vertex_ptr);
}


/* *********************************************************************** */
/* Interface with fnode_t structures */
/* *********************************************************************** */
vertex_t *Make_vertex_rec(dag_t *dag_ptr, fnode_t *a_fnode_ptr, int l_simplify)
{
  vertex_t *t_vertex_ptr, *t1_vertex_ptr, *op_vertex_ptr;
  vertex_t *first_vertex_ptr, *second_vertex_ptr;
  lsList   op_vertices_lsList;
  lsStatus list_status;
  fnode_t  *cur_op_fnode_ptr;
  fnode_t  *t_fnode_ptr;
  

  switch (Op_code(a_fnode_ptr))
    {
    case top_code:
      t_vertex_ptr = dag_top(dag_ptr);
      break;
    case bot_code:
      t_vertex_ptr = dag_bot(dag_ptr);
      break;
    case atom_code:
      t_vertex_ptr = Add_atom(dag_ptr, a_fnode_ptr);
      break;
    case not_code:
    case box_code: case dia_code:
      first_vertex_ptr = Make_vertex_rec(dag_ptr, Op_fnode_ptr(a_fnode_ptr),l_simplify);
      t_vertex_ptr = Add_unary_op(dag_ptr, first_vertex_ptr, a_fnode_ptr);
      break;
    case imp_code:
    case iff_code:
      first_vertex_ptr = Make_vertex_rec(dag_ptr, Op_fnode_ptr(a_fnode_ptr),l_simplify);
      second_vertex_ptr = 
	Make_vertex_rec(dag_ptr, 
			Next_fnode_ptr(Op_fnode_ptr(a_fnode_ptr)), l_simplify);
      if (l_simplify == NCDEI) {
	t_vertex_ptr = 
	  Add_binary_op(dag_ptr, first_vertex_ptr, second_vertex_ptr, a_fnode_ptr);
      } else {
	if ((Op_code(a_fnode_ptr) == iff_code) && (l_simplify == NCDE)) {
	  t_vertex_ptr = 
	    Add_binary_op(dag_ptr, first_vertex_ptr, second_vertex_ptr, a_fnode_ptr);
	} else {
	  t_fnode_ptr = Make_formula_nary(not_code, empty_code, Make_empty());
	  t_vertex_ptr = 
	    Add_unary_op(dag_ptr, first_vertex_ptr, t_fnode_ptr);
	  Op_code(t_fnode_ptr) = or_code;
	  t_vertex_ptr = 
	    Add_binary_op(dag_ptr, t_vertex_ptr, second_vertex_ptr, 
			  t_fnode_ptr);

	  if (Op_code(a_fnode_ptr) == iff_code) {
	    Op_code(t_fnode_ptr) = not_code;
	    t1_vertex_ptr = 
	      Add_unary_op(dag_ptr, second_vertex_ptr, t_fnode_ptr);
	    Op_code(t_fnode_ptr) = or_code;
	    t1_vertex_ptr = 
	      Add_binary_op(dag_ptr, t1_vertex_ptr, first_vertex_ptr, t_fnode_ptr);
	    Op_code(t_fnode_ptr) = and_code;
	    t_vertex_ptr = 
	      Add_binary_op(dag_ptr, t1_vertex_ptr, t_vertex_ptr, t_fnode_ptr);
	    Clear_fnode(t_fnode_ptr, NULL);
	  }
	}
      }
      break;
    case and_code:
    case or_code:
      cur_op_fnode_ptr = Op_fnode_ptr(a_fnode_ptr);
      op_vertices_lsList = lsCreate();
      {
	int i;
	i = 1;
      while (cur_op_fnode_ptr) {
	op_vertex_ptr = Make_vertex_rec(dag_ptr, cur_op_fnode_ptr, l_simplify);
	list_status = lsNewEnd(op_vertices_lsList, CAST_VERTEX_ITEM(op_vertex_ptr), LS_NH);
	cur_op_fnode_ptr = Next_fnode_ptr(cur_op_fnode_ptr);
	i++;
      }
      }
      t_vertex_ptr = Add_nary_op(dag_ptr, &op_vertices_lsList, a_fnode_ptr);
      list_status = lsDestroy(op_vertices_lsList, NULL);
      break;
    default:
      t_vertex_ptr = NIL(vertex_t);
    }
  
  assert(t_vertex_ptr != NIL(vertex_t));
  return (t_vertex_ptr);
}

dag_t *Make_dag(fnode_t *ntree_fnode_ptr, 
		int box_simplify, int l_simplify, int cnf_conversion)
{
  dag_t    *dag_ptr;
  
  /* Preconditions */
  if (ntree_fnode_ptr == NIL(fnode_t)) return NIL(dag_t);

  /* Initializing DAG and setting flags */
  dag_ptr = Init_dag();
  Box_simplify(dag_ptr) = box_simplify;
  Cnf_conversion(dag_ptr) = cnf_conversion;

  /* The heart of the procedure! */
  dag_ptr->root_vertex_ptr = Make_vertex_rec(dag_ptr, ntree_fnode_ptr, l_simplify);

  /* Getting rid of garbage */
#ifdef GCOLLECT
  Garbage_collect(dag_ptr);
#endif

  assert(dag_ptr != NIL(dag_t));
  return (dag_ptr);
}

/* *********************************************************************** */
/* Decision procedure routines */
/* *********************************************************************** */
int Replace_boxes_rec(dag_t *dag_ptr, vertex_t *a_vertex_ptr,
		      st_table *new_uni_st_table_ptr,
		      st_table *visited_st_table_ptr)
{
  lsList        sons_vertices_lsList, out_edges_lsList;
  int           new_hash_key, son_hash_key;
  vertex_t      *son_vertex_ptr, *new_box_vertex_ptr;
  lsGen         list_generator;
  lsStatus      list_status;
  lsGeneric     t_lsGeneric;
  vertex_info_t *t_vertex_info_ptr;
  fnode_t       *new_atom_fnode_ptr;
  edge_t        *t_edge_ptr;
  stGeneric     *value_stGeneric_ptr;


  /* You cannot do this with diamonds */
  assert(V_op_code(a_vertex_ptr) != dia_code); 

  new_hash_key = V_hash_key(a_vertex_ptr);

  /* Check if the vertex was visited yet */
  if (!st_find_or_add(visited_st_table_ptr, CAST_TKEY(a_vertex_ptr), 
		      &value_stGeneric_ptr)) {
    *value_stGeneric_ptr = DUMMY_VALUE;
    
    switch (V_op_code(a_vertex_ptr))
      { 
      case atom_code:
      case bot_code:
      case top_code:
	new_hash_key = V_hash_key(a_vertex_ptr);
	break;
      case not_code:
      case and_code:
      case or_code:           
      case imp_code: 	 
      case iff_code:
	sons_vertices_lsList = Get_vertex_sons(a_vertex_ptr);  /* This CREATES THE LIST! */
	new_hash_key = V_op_code(a_vertex_ptr);
	lsForEachItem(sons_vertices_lsList, list_generator, t_lsGeneric) {
	  son_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);
	  son_hash_key = Replace_boxes_rec(dag_ptr, son_vertex_ptr,
					   new_uni_st_table_ptr,
					   visited_st_table_ptr);
	  new_hash_key = HASH_OP(son_hash_key, new_hash_key);
	}
	V_hash_key(a_vertex_ptr) = new_hash_key;
	/* Rearrainging sons to respect ordering (implication is already "ordered")*/
	if (V_op_code(a_vertex_ptr) != imp_code) {
	  list_status = lsSort(sons_vertices_lsList, Hash_key_comp);
	  out_edges_lsList = g_get_out_edges(a_vertex_ptr);
	  lsForEachItem(out_edges_lsList, list_generator, t_lsGeneric) {
	    g_delete_edge(UNCAST_EDGE_ITEM(t_lsGeneric), NULL);
	  }
	  lsForEachItem(sons_vertices_lsList, list_generator, t_lsGeneric) {
	    g_add_edge(a_vertex_ptr, UNCAST_VERTEX_ITEM(t_lsGeneric));
	  }
	}
	list_status = lsDestroy(sons_vertices_lsList, NULL); /* This DESTROYS THE LIST! */
	/* Reforming the unique table */
	Add_to_table(new_uni_st_table_ptr, a_vertex_ptr);
	break;
      case box_code:
	son_vertex_ptr = Get_vertex_son(a_vertex_ptr);
	son_hash_key = Replace_boxes_rec(dag_ptr, son_vertex_ptr,
					 new_uni_st_table_ptr,
					 visited_st_table_ptr);
	new_hash_key = HASH_OP(son_hash_key, V_op_code(a_vertex_ptr));
	
	/* First: build a new [] vertex that saves a_vertex_ptr information.
	   The former son of a_vertex_ptr is attached to the new vertex */
	t_vertex_info_ptr = 
	  New_vertex_info(Copy_fnode(V_ini_fnode_ptr(a_vertex_ptr)), new_hash_key);
	new_box_vertex_ptr = g_add_vertex(dag_ptr->inner_graph_ptr);
	Vertex_info(new_box_vertex_ptr) = CAST_VERTEX_INFO(t_vertex_info_ptr);
	t_edge_ptr = g_add_edge(new_box_vertex_ptr, son_vertex_ptr);
	
	
	/* Second: reform unique table using the new [] vertex */
	/* The former [] vertex is becoming an atom, thus is not hashed */
	Add_to_table(new_uni_st_table_ptr, new_box_vertex_ptr);
	
	/* Third: make a new atom of the current vertex. Fathers
	   do not loose their former modal child! The vertex is linked to
	   the cross reference table. */
	++(dag_ptr->lma); 
	new_atom_fnode_ptr = Make_formula_nary(atom_code, dag_ptr->lma, Make_empty());
	new_hash_key = HASH_ATOM(dag_ptr->lma);
	V_ini_fnode_ptr(a_vertex_ptr) = new_atom_fnode_ptr;
	V_hash_key(a_vertex_ptr) = new_hash_key;
	dag_ptr->xref_vertex_ptr_table[dag_ptr->lma] = a_vertex_ptr;
	
	/* Fourth: create xref_info for the new atom and attach the [] vertex to
	   it so we can access the [] subdag through the newly added atom */
	V_xref_info_ptr(a_vertex_ptr) = New_xref_info(new_box_vertex_ptr);
	
	break;
      }
  }
  
  return (new_hash_key);
}

void Replace_boxes(dag_t *dag_ptr)
{
  int      dummy_key;
  vertex_t *ref_vertex_ptr;
  edge_t   *t_edge_ptr;
  st_table *visited_st_table_ptr;

  /* Initialize lma value and clear the old unique table.
     Initialize the visited table. Replace boxes gives a new unique table.
     At the end visited table is freed */
  dag_ptr->lma = dag_ptr->lpa;
  st_free_table(dag_ptr->uni_st_table_ptr);
  dag_ptr->uni_st_table_ptr = st_init_table(st_numcmp, st_numhash);
  visited_st_table_ptr = st_init_table(st_ptrcmp, st_ptrhash);
  
  dummy_key = Replace_boxes_rec(dag_ptr, dag_ptr->root_vertex_ptr,
				dag_ptr->uni_st_table_ptr,
				visited_st_table_ptr);

  st_free_table(visited_st_table_ptr);

  /* Initialize laa value */
  dag_ptr->laa = dag_ptr->lma;

  /* Add an xref node to the main formula in order to handle top-level
     reasoning; if it is not a modal atom then we need a dummy node to skip
     when building bdds or cnfs (uniformity with modal atoms) */
  if ((V_op_code(dag_ptr->root_vertex_ptr) != atom_code) ||
      (V_value(dag_ptr->root_vertex_ptr) <= Lpa(dag_ptr))) {
    ref_vertex_ptr = g_add_vertex(dag_ptr->inner_graph_ptr);
    t_edge_ptr = g_add_edge(ref_vertex_ptr, dag_ptr->root_vertex_ptr);
    Vertex_info(ref_vertex_ptr) = 
      CAST_VERTEX_INFO(New_vertex_info(Make_formula_nary(box_code, empty_code, Make_empty()), box_code));
    V_xref_info_ptr(dag_ptr->root_vertex_ptr) = New_xref_info(ref_vertex_ptr);
  }   
  
  return;
}


/* *********************************************************************** */
/* Tests */
/* *********************************************************************** */
int Are_dag_vtx_equal(vertex_t *a_vertex_ptr, vertex_t *b_vertex_ptr)
{
  vertex_t *a_son_vertex_ptr, *b_son_vertex_ptr;
  lsList    a_sons_lsList, b_sons_lsList;
  lsGen     a_lsGen, b_lsGen;
  lsStatus  list_status;
  lsGeneric a_lsGeneric, b_lsGeneric;
  int       broken;

#ifdef DEBUG_DAG
  printf("\tNow comparing:\n");
  printf("\t"); Print_vertex_rec(a_vertex_ptr);
  printf("\n\t"); Print_vertex_rec(b_vertex_ptr);
  printf("\n\n");
#endif

  /* Atoms, top and bottom will not survive this check! */
  if (a_vertex_ptr == b_vertex_ptr) return (1); 
  if (V_hash_key(a_vertex_ptr) != V_hash_key(b_vertex_ptr))
    return (0);
  if (V_op_code(a_vertex_ptr) != V_op_code(b_vertex_ptr))
    return (0);

  /* Let's look at the other operators */
  switch (V_op_code(a_vertex_ptr))
    {
    case not_code: case and_code:
    case iff_code: case imp_code:
    case or_code:
      if (V_op_code(a_vertex_ptr) != V_op_code(b_vertex_ptr))
	return (0);
      break;
    case box_code: case dia_code:
      if ((V_op_code(a_vertex_ptr) != V_op_code(b_vertex_ptr)) ||
	  (V_value(a_vertex_ptr) != V_value(b_vertex_ptr)))
	return (0);
    }
      
  a_sons_lsList = Get_vertex_sons(a_vertex_ptr); /* This CREATES A NEW LIST! */
  b_sons_lsList = Get_vertex_sons(b_vertex_ptr); /* This CREATES A NEW LIST! */
  if (lsLength(a_sons_lsList) != lsLength(b_sons_lsList))
    return 0;
  broken = 0;
  b_lsGen = lsStart(b_sons_lsList);
  lsForEachItem(a_sons_lsList, a_lsGen, a_lsGeneric) {
    list_status = lsNext(b_lsGen, &b_lsGeneric, LS_NH);
    a_son_vertex_ptr = UNCAST_VERTEX_ITEM(a_lsGeneric);
    b_son_vertex_ptr = UNCAST_VERTEX_ITEM(b_lsGeneric);    
    if (!Are_dag_vtx_equal(a_son_vertex_ptr, b_son_vertex_ptr)) {
      broken = 1;
      break;
    }
  }
  if (broken) list_status = lsFinish(a_lsGen);
  list_status = lsFinish(b_lsGen);
  list_status = lsDestroy(a_sons_lsList, NULL);
  list_status = lsDestroy(b_sons_lsList, NULL);

  return (!broken);
}

int Are_dag_vtx_compl_eq(vertex_t *a_vertex_ptr, vertex_t *b_vertex_ptr)
{
  int sign;

  sign = 0;
  if (V_op_code(a_vertex_ptr) == not_code)
    sign = -1;
  if ((V_op_code(b_vertex_ptr) == not_code) && !sign)
    sign = 1;
  if ((sign == -1) &&
      (Get_vertex_son(a_vertex_ptr) != b_vertex_ptr)) sign = 0;
  if ((sign == 1) &&
      (Get_vertex_son(b_vertex_ptr) != a_vertex_ptr)) sign = 0;
  
  return sign;
}
      
int Is_orphan(dag_t *dag_ptr, vertex_t *a_vertex_ptr)
{
  lsList   t_fathers_lsList;
  lsStatus list_status;
  int      answer;
  
  /* The root vertex is never an orphan, by definition! */
  if (a_vertex_ptr == Root_vertex_ptr(dag_ptr)) return 0;
  t_fathers_lsList = Get_vertex_fathers(a_vertex_ptr); /* This CREATES THE LIST! */
  answer = (lsLength(t_fathers_lsList) == 0);
  list_status = lsDestroy(t_fathers_lsList, NULL);

  return answer;
}

int Is_simple_vertex(vertex_t *a_vertex_ptr)
{
  int       res;
  lsGen     t_lsGen;
  lsStatus  list_status;
  lsGeneric t_lsGeneric;
  lsList    sons_lsList;

  if ((V_op_code(a_vertex_ptr) != and_code) &&
      (V_op_code(a_vertex_ptr) != or_code))
    return (0);
  res = 1;
  sons_lsList = Get_vertex_sons(a_vertex_ptr);
  lsForEachItem(sons_lsList, t_lsGen, t_lsGeneric) {
    if (!Is_literal_vertex(UNCAST_VERTEX_ITEM(t_lsGeneric))) {
      res = 0;
      break;
    }
  }
  if (!res) list_status = lsFinish(t_lsGen);
  list_status = lsDestroy(sons_lsList, NULL);

  return res;
}

int Is_cnf_vertex(vertex_t *a_vertex_ptr)
{
  int       res;
  lsGen     t_lsGen;
  lsStatus  list_status;
  lsGeneric t_lsGeneric;
  lsList    sons_lsList;

  if (V_op_code(a_vertex_ptr) != and_code) return 0;
  res = 1;
  sons_lsList = Get_vertex_sons(a_vertex_ptr);
  lsForEachItem(sons_lsList, t_lsGen, t_lsGeneric) {
    if (V_op_code(UNCAST_VERTEX_ITEM(t_lsGeneric)) != or_code) {
      res = 0; break;
    }
    if (!Is_simple_vertex(UNCAST_VERTEX_ITEM(t_lsGeneric))) {
      res = 0; break;
    }
  }
  if (!res) list_status = lsFinish(t_lsGen);
  list_status = lsDestroy(sons_lsList, NULL);

  return res;
}

int Generic_comp(lsGeneric a_gen, lsGeneric b_gen)
{
  return (a_gen - b_gen);
}


int Hash_key_comp(lsGeneric a_gen, lsGeneric b_gen)
{
  vertex_t *a_vertex_ptr, *b_vertex_ptr;
  
  a_vertex_ptr = UNCAST_VERTEX_ITEM(a_gen);
  b_vertex_ptr = UNCAST_VERTEX_ITEM(b_gen);
  
  return (V_hash_key(a_vertex_ptr) - V_hash_key(b_vertex_ptr));
}
  
/* *********************************************************************** */
/* Utilities about vertex_info  */
/* *********************************************************************** */
vertex_info_t *New_vertex_info(fnode_t *ini_fnode_ptr,
			        int hash_key)
{
  vertex_info_t *t_vertex_info_ptr;
  
  t_vertex_info_ptr = ALLOC(vertex_info_t,1);
  (t_vertex_info_ptr->ini_fnode_ptr) = ini_fnode_ptr;
  (t_vertex_info_ptr->hash_key) = hash_key;
  
  return (t_vertex_info_ptr);
}

void Clear_vertex_info_esile(gGeneric gen)
{
  vertex_info_t *t_vertex_info_ptr;

  t_vertex_info_ptr = UNCAST_VERTEX_INFO(gen);
  Clear_fnode(t_vertex_info_ptr->ini_fnode_ptr, NULL);   /* This WAS A COPY! */

  FREE(t_vertex_info_ptr);
}


void Clear_vertex_info_soft(gGeneric gen)
{
  vertex_info_t *t_vertex_info_ptr;

  t_vertex_info_ptr = UNCAST_VERTEX_INFO(gen);
  if (t_vertex_info_ptr->ini_fnode_ptr)
    Clear_fnode(t_vertex_info_ptr->ini_fnode_ptr, NULL);   
  if (t_vertex_info_ptr->xref_info_ptr)
    Clear_xref_info(t_vertex_info_ptr->xref_info_ptr);

  FREE(t_vertex_info_ptr);
}
 
void Clear_vertex_info_hard(gGeneric gen, nGeneric_func_ptr_t Clear_aux_func)
{
  vertex_info_t *t_vertex_info_ptr;

  t_vertex_info_ptr = UNCAST_VERTEX_INFO(gen);
  if (t_vertex_info_ptr->ini_fnode_ptr)
    Clear_fnode(t_vertex_info_ptr->ini_fnode_ptr, Clear_aux_func);
  if (t_vertex_info_ptr->xref_info_ptr)
    Clear_xref_info(t_vertex_info_ptr->xref_info_ptr);
}
 

/* *********************************************************************** */
/* Utilities about xref_info */
/* *********************************************************************** */
xref_info_t *New_xref_info(vertex_t *ini_vertex_ptr)
{
  xref_info_t *t_xref_info_ptr;

  t_xref_info_ptr = ALLOC(xref_info_t, 1);

  Ini_vertex_ptr(t_xref_info_ptr) = ini_vertex_ptr;
  Pos_lsList_ptr(t_xref_info_ptr) = Neg_lsList_ptr(t_xref_info_ptr) = NIL(lsList);

  return t_xref_info_ptr;
}


void Clear_xref_info(xref_info_t  *xref_data)
{ }

/* *********************************************************************** */
/* Utilities about dag vertices */
/* *********************************************************************** */
void Swap_vertex_ptr(vertex_t **a_vertex_ptr_ptr,
		     vertex_t **b_vertex_ptr_ptr)
{
  vertex_t *t_vertex_ptr;

  t_vertex_ptr = *a_vertex_ptr_ptr;
  *a_vertex_ptr_ptr = *b_vertex_ptr_ptr;
  *b_vertex_ptr_ptr = t_vertex_ptr;
}

vertex_t *New_vertex(graph_t *graph_ptr, int op_code, int value, int hash_key)
{
  vertex_info_t *t_vertex_info_ptr;
  vertex_t      *t_vertex_ptr;
  
  t_vertex_info_ptr = 
    New_vertex_info(Make_formula_nary(op_code, value, Make_empty()), hash_key);
  t_vertex_ptr = g_add_vertex(graph_ptr);
  Vertex_info(t_vertex_ptr) = CAST_VERTEX_INFO(t_vertex_info_ptr);

  return t_vertex_ptr;
}

vertex_t *Copy_vertex(graph_t *graph_ptr, vertex_t *source_vertex_ptr)
{
  vertex_t      *t_vertex_ptr;

  t_vertex_ptr = New_vertex(graph_ptr, V_op_code(source_vertex_ptr),
			    V_value(source_vertex_ptr), V_hash_key(source_vertex_ptr));
  if (V_xref_info_ptr(source_vertex_ptr)) 
    V_xref_info_ptr(t_vertex_ptr) = V_xref_info_ptr(source_vertex_ptr);

  return t_vertex_ptr;
}

vertex_t *Get_vertex_son(vertex_t *uop_vertex_ptr)
{
  lsList    out_edge_lsList;
  lsStatus  list_status;
  lsGeneric t_lsGeneric;
  vertex_t  *t_vertex_ptr;

  if (V_op_code(uop_vertex_ptr) == atom_code) return NIL(vertex_t);
  out_edge_lsList = g_get_out_edges(uop_vertex_ptr);
  list_status =  lsFirstItem(out_edge_lsList, &t_lsGeneric, LS_NH); 
  t_vertex_ptr = g_e_dest(UNCAST_EDGE_ITEM(t_lsGeneric)); 

  assert(t_vertex_ptr != NIL(vertex_t));
  return t_vertex_ptr;
} 

/* Behaves badly on the second argument: FIX! */
vertex_t *Get_vertex_ith_son(vertex_t *nop_vertex_ptr, int i)
{
  lsList    out_edge_lsList;
  lsStatus  list_status;
  lsGeneric t_lsGeneric;
  lsGen     list_generator;
  vertex_t* t_vertex_ptr;

  if (V_op_code(nop_vertex_ptr) == atom_code) return NIL(vertex_t);
  out_edge_lsList = g_get_out_edges(nop_vertex_ptr); 
  if (i > lsLength(out_edge_lsList)) return NIL(vertex_t);
  list_generator = lsStart(out_edge_lsList);
  while (i > 0) {
    list_status = lsNext(list_generator, &t_lsGeneric, LS_NH);
    --i;
  }
  t_vertex_ptr = g_e_dest(UNCAST_EDGE_ITEM(t_lsGeneric)); 
  list_status = lsFinish(out_edge_lsList);

  assert(t_vertex_ptr != NIL(vertex_t));
  return t_vertex_ptr;
}

lsList Get_vertex_sons(vertex_t *nop_vertex_ptr)
{
  edge_t    *t_edge_ptr;
  vertex_t  *a_son_vertex_ptr;
  lsList    sons_lsList;
  lsStatus  list_status;
  lsGen     edges_lsGen;

  if (V_op_code(nop_vertex_ptr) == atom_code) return LS_NIL;
  sons_lsList = lsCreate();
  foreach_out_edge(nop_vertex_ptr, edges_lsGen, t_edge_ptr) {
    a_son_vertex_ptr = g_e_dest(t_edge_ptr); 
    assert(a_son_vertex_ptr != NIL(vertex_t));    
    list_status = lsNewEnd(sons_lsList, CAST_VERTEX_ITEM(a_son_vertex_ptr), LS_NH);
  }

  assert(sons_lsList != LS_NIL);
  return sons_lsList;
}

lsList Get_vertex_fathers(vertex_t *a_vertex_ptr)
{
  edge_t    *t_edge_ptr;
  vertex_t  *a_father_vertex_ptr;
  lsList    fathers_lsList;
  lsStatus  list_status;
  lsGen     edges_lsGen;

  fathers_lsList = lsCreate();
  foreach_in_edge(a_vertex_ptr, edges_lsGen, t_edge_ptr) {
    a_father_vertex_ptr = g_e_source(t_edge_ptr); 
    assert(a_father_vertex_ptr != NIL(vertex_t));    
    list_status = lsNewEnd(fathers_lsList, CAST_VERTEX_ITEM(a_father_vertex_ptr), LS_NH);
  }

  return fathers_lsList;
} 


/* *********************************************************************** */
/* Garbage handling */
/* *********************************************************************** */
int Check_and_trash_vertex(dag_t *dag_ptr, vertex_t *a_vertex_ptr)
{
  if (!Is_constant(dag_ptr, a_vertex_ptr))
    return st_insert(dag_ptr->trash_st_table_ptr, CAST_TKEY(a_vertex_ptr), DUMMY_VALUE);
  else
    return (-1);
}

int Check_and_trash_vertices(dag_t *dag_ptr, lsList vertices_lsList)
{
  lsGen     list_generator;
  lsGeneric t_lsGeneric;
  vertex_t  *trashee_vertex_ptr;
  int       table_status;

  table_status = 0;
  lsForEachItem(vertices_lsList, list_generator, t_lsGeneric) {
    trashee_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);
    if (!Is_constant(dag_ptr, trashee_vertex_ptr)) 
      table_status = (table_status ||
	st_insert(dag_ptr->trash_st_table_ptr, 
		  CAST_TKEY(trashee_vertex_ptr), DUMMY_VALUE));
  }

  return table_status;
}
  
void Garbage_collect_rec(dag_t *dag_ptr, 
			 st_table *new_trash_st_table_ptr,
			 st_table *old_trash_st_table_ptr,
			 vertex_t *a_vertex_ptr)
{
  int       value;
  vertex_t  *t_vertex_ptr;
  lsList    a_sons_lsList;
  lsGeneric t_lsGeneric;
  lsGen     list_generator;
  lsStatus  list_status;

#ifdef DEBUG_GCOLLECT
  if (Is_orphan(dag_ptr, a_vertex_ptr)) {
    printf("This is an orphan: ");
    Print_vertex_rec(a_vertex_ptr);
    printf("\n\n");
  } else {
    if (a_vertex_ptr != Root_vertex_ptr(dag_ptr)) {
      printf("This is not an orphan: ");
      Print_vertex_rec(a_vertex_ptr);
      printf("\nHis fathers are:\n "); 
      a_sons_lsList = Get_vertex_fathers(a_vertex_ptr);  
      lsForEachItem(a_sons_lsList, list_generator, t_lsGeneric) {  
	Print_vertex_rec(UNCAST_VERTEX_ITEM(t_lsGeneric));  
	printf("\n");  
      }  
      list_status = lsDestroy(a_sons_lsList, NULL);  
    }
  }
#endif

  if (Is_constant(dag_ptr, a_vertex_ptr)) return;

  if ((Is_orphan(dag_ptr, a_vertex_ptr)) &&
      (!st_is_member(new_trash_st_table_ptr, CAST_TKEY(a_vertex_ptr))))
    {
      /* The node is orphan and it is not marked for deletion
	 in the new table it must be disposed 
	 together with its orphan descendants (if any) */
      if (V_op_code(a_vertex_ptr) == atom_code)
	{
	  /* An orphan atom must be removed from the cross-reference table */
	  value = V_value(a_vertex_ptr);
	  g_delete_vertex(a_vertex_ptr, Clear_vertex_info_soft, NULL);
	  dag_ptr->xref_vertex_ptr_table[value] = NIL(vertex_t); 
	} else {
	  /* An orphan operator must be disposed and 
	     his (possibly orphan) sons are marked for deletion. 
	     Do not mark sons for deletion if they are constants 
	     Also, a disposed operator is removed from the uique table. */
	  a_sons_lsList = Get_vertex_sons(a_vertex_ptr); /* This CREATES THE LIST! */
#ifdef DEBUG_GCOLLECT
	  printf("There are %d items in the unique table.\n\n", st_count(dag_ptr->uni_st_table_ptr));
#endif
	  Remove_from_table(dag_ptr->uni_st_table_ptr, a_vertex_ptr);
#ifdef DEBUG_GCOLLECT
	  printf("There are %d items in the unique table.\n\n", st_count(dag_ptr->uni_st_table_ptr));
#endif
	  g_delete_vertex(a_vertex_ptr, Clear_vertex_info_soft, NULL);
	  lsForEachItem(a_sons_lsList, list_generator, t_lsGeneric) {
	    t_vertex_ptr = UNCAST_VERTEX_ITEM(t_lsGeneric);
	    if (Is_orphan(dag_ptr, t_vertex_ptr) &&
		(!Is_constant(dag_ptr, t_vertex_ptr)))
	      st_insert(new_trash_st_table_ptr, CAST_TKEY(t_vertex_ptr), DUMMY_VALUE);
	  }
	  list_status = lsDestroy(a_sons_lsList, NULL);
	}
    }

  return;
}
      
void Small_garbage_collect(dag_t *dag_ptr, st_table *trash_st_table_ptr)
{
  stGeneric    k_stGeneric_ptr;
  stGeneric    v_stGeneric_ptr;
  st_generator *table_generator;
  st_table     *old_st_table_ptr, *new_st_table_ptr;
  vertex_t     *t_vertex_ptr;

#ifdef DEBUG_GCOLLECT
  printf("Trying to collect:\n");
  st_foreach_item(trash_st_table_ptr, table_generator,
		  &k_stGeneric_ptr, &v_stGeneric_ptr) {
    t_vertex_ptr = UNCAST_TKEY(k_stGeneric_ptr);
    Print_vertex_rec(t_vertex_ptr);
    printf("\n");
  }
#endif

  old_st_table_ptr = trash_st_table_ptr;
  while (st_count(old_st_table_ptr)) {
    new_st_table_ptr = st_init_table(st_ptrcmp, st_ptrhash);
    st_foreach_item(old_st_table_ptr, table_generator,
		    &k_stGeneric_ptr, &v_stGeneric_ptr) {
      t_vertex_ptr = UNCAST_TKEY(k_stGeneric_ptr);
      Garbage_collect_rec(dag_ptr, new_st_table_ptr, old_st_table_ptr, t_vertex_ptr);
    }
    st_free_table(old_st_table_ptr);
    old_st_table_ptr = new_st_table_ptr;
  }
}

void Garbage_collect(dag_t *dag_ptr)
{
   int i;

   Small_garbage_collect(dag_ptr, dag_ptr->trash_st_table_ptr);
   /* Realign lpa value */
   if ((dag_ptr->xref_vertex_ptr_table[dag_ptr->lpa]) == NIL(vertex_t)) {
     for (i = (dag_ptr->lpa); i >= 0; i--)
       if (dag_ptr->xref_vertex_ptr_table[i] != NIL(vertex_t)) break;
     (dag_ptr->lpa) = i; 
   }

   return;
}

/* *********************************************************************** */
/* Output routines */
/* *********************************************************************** */
void Print_vertex_rec(vertex_t *a_vertex_ptr)
{
  lsList    a_sons_lsList;
  lsGen     a_sons_lsGen;
  lsGeneric son_lsGeneric;
  lsStatus  list_status; 
  int       paren_count;

  paren_count = 1;
  switch (V_op_code(a_vertex_ptr))
    { 
    case and_code: 	 
      printf("(AND "); break; 
    case or_code:           
      printf("(OR "); break; 
    case imp_code: 	 
      printf("(IMP "); break; 
    case iff_code:           
      printf("(IFF "); break;    
    case not_code:
      printf("(NOT "); break;    
      
    case box_code:
      printf("(ALL R%d ", V_value(a_vertex_ptr)); break;    
      
    case dia_code:
      printf("(SOME R%d ", V_value(a_vertex_ptr)); break;    
      
    case atom_code:
      printf("C%d ", V_value(a_vertex_ptr)); paren_count--; break;
      
    case top_code:  
      printf("T "); paren_count--; break; 
    case bot_code:     
      printf("F "); paren_count--; break; 
    } 
  
  if (paren_count) { 
    a_sons_lsList = Get_vertex_sons(a_vertex_ptr);   /* This CREATES THE LIST! */
    lsForEachItem(a_sons_lsList, a_sons_lsGen, son_lsGeneric) {
      Print_vertex_rec(UNCAST_VERTEX_ITEM(son_lsGeneric));
    }
    list_status = lsDestroy(a_sons_lsList, NULL);    /* This DESTROYS THE LIST! */
    printf(")"); 
  } 
} 

void Print_vertex_prolog(vertex_t *a_vertex_ptr)
{
  lsList    a_sons_lsList;
  lsGen     a_sons_lsGen;
  lsGeneric son_lsGeneric;
  lsStatus  list_status; 
  int       paren_count;

  paren_count = 1;
  switch (V_op_code(a_vertex_ptr))
    { 
    case and_code: 	 
      printf("and([ "); paren_count++; break; 
    case or_code:           
      printf("or([ "); paren_count++; break; 

    case not_code:
      printf("not( "); break;    
    case box_code:
      printf("all(r%d, ", V_value(a_vertex_ptr)); break;    
    case dia_code:
      printf("some(r%d, ", V_value(a_vertex_ptr)); break;    
      
    case atom_code:
      printf("c%d ", V_value(a_vertex_ptr)); paren_count--; break;
    case top_code:  
      printf("and([c1, not(c1)]) "); paren_count--; break; 
    case bot_code:     
      printf("or([c1, not(c1)]) "); paren_count--; break; 
    } 
  
  if (paren_count) { 
    a_sons_lsList = Get_vertex_sons(a_vertex_ptr);   /* This CREATES THE LIST! */
    a_sons_lsGen = lsStart(a_sons_lsList);
    if (lsNext(a_sons_lsGen, &son_lsGeneric, LS_NH) == LS_OK) 
      while (1) {
	Print_vertex_prolog(UNCAST_VERTEX_ITEM(son_lsGeneric));
	if (lsNext(a_sons_lsGen, &son_lsGeneric, LS_NH) == LS_OK) 
	  printf(",");
	else
	  break;
      }
    lsFinish(a_sons_lsGen);
    list_status = lsDestroy(a_sons_lsList, NULL);    /* This DESTROYS THE LIST! */
    if (paren_count > 1) printf("])"); else printf(")");
  } 
} 


void Print_dag_lisp(dag_t *dag_ptr)
{
  Print_vertex_rec(dag_ptr->root_vertex_ptr);
}

void Print_dag_prolog(dag_t *dag_ptr)
{
  Print_vertex_prolog(dag_ptr->root_vertex_ptr);
  printf(".\n");
}


int Depth_eval_rec(vertex_t *a_vertex_ptr, int d)
{
  lsList    a_sons_lsList;
  lsGen     a_sons_lsGen;
  lsGeneric son_lsGeneric;
  lsStatus  list_status; 
  int       cur_d,max_d;

  switch (V_op_code(a_vertex_ptr))
    { 
    case box_code:
    case dia_code:
      ++d;
      break;
      
    case atom_code:
    case top_code:  
    case bot_code:     
      return d;
    } 
  
  a_sons_lsList = Get_vertex_sons(a_vertex_ptr);   /* This CREATES THE LIST! */
  max_d = 0;
  lsForEachItem(a_sons_lsList, a_sons_lsGen, son_lsGeneric) {
      cur_d = Depth_eval_rec(UNCAST_VERTEX_ITEM(son_lsGeneric), d);
      if (cur_d > max_d) max_d = cur_d;
  }
  list_status = lsDestroy(a_sons_lsList, NULL);    /* This DESTROYS THE LIST! */
  
  return max_d;
} 

int Depth_eval(dag_t *dag_ptr)
{
  return Depth_eval_rec(dag_ptr->root_vertex_ptr, 0);
}

void Print_cnf_int(lsList *formula_lsList_ptr)
{
  lsList    *clause_lsList_ptr;
  lsGen     clause_lsGen, lit_lsGen;
  lsGeneric clause_lsGeneric, lit_lsGeneric;
  int       lit;

  lsForEachItem(*formula_lsList_ptr, clause_lsGen, clause_lsGeneric) {
    clause_lsList_ptr = (lsList*)(clause_lsGeneric);
    printf("( ");
    lsForEachItem(*clause_lsList_ptr, lit_lsGen, lit_lsGeneric) {
      lit = (int)(lit_lsGeneric);
      printf("%d ",lit);
    }
    printf(")\n");
  }

  return;
}


void Print_dag_info(dag_t *dag_ptr)
{ 
  int i;
  vertex_t      *item_vertex_ptr;

  printf("****************************************\n");
  printf("ORIGINAL FORMULA (propositional)\n");
  printf("****************************************\n\n");
  Print_vertex_rec(dag_ptr->root_vertex_ptr);

  if (V_xref_info_ptr(dag_ptr->root_vertex_ptr)) 
    if (V_pos_lsList_ptr(dag_ptr->root_vertex_ptr)) { 
      printf("\n------------------------------\n"); 
      Print_cnf_int(V_pos_lsList_ptr(dag_ptr->root_vertex_ptr)); 
    } 
      
#ifdef DEBUG_UNIQUE
  {
      lsGen         list_generator;
      lsStatus      list_status;
      lsGeneric     t_lsGeneric;
      stGeneric     k_stGeneric, v_stGeneric;
      st_generator *t_st_generator;

      printf("\n\n****************************************\n");
      printf("UNIQUE TABLE CONTENTS <key,formula-list>\n");
      printf("****************************************\n\n");
      printf("There are %d items in the unique table.\n\n", st_count(dag_ptr->uni_st_table_ptr));
      st_foreach_item(dag_ptr->uni_st_table_ptr, t_st_generator, &k_stGeneric, &v_stGeneric) {
	printf("%d - ", UNCAST_KEY(k_stGeneric));
	lsForEachItem(*UNCAST_VALUE(v_stGeneric), list_generator, t_lsGeneric) {
	  Print_vertex_rec(UNCAST_VERTEX_ITEM(t_lsGeneric));
	  printf(", ");
	}
	printf("\n------------------------------\n");
      }
  }
#endif
  if (Lpa(dag_ptr) > -1) {
    printf("\n****************************************\n");
    printf("PROPOSITIONAL VARIABLES\n");
    printf("****************************************\n\n");
    For_each_prop_xref_item(dag_ptr, i, item_vertex_ptr) {
      if (item_vertex_ptr != NIL(vertex_t))
	printf("C%d, ",i);
    }
  }
  printf("\n");
  if (Lma(dag_ptr) > -1) {
    printf("\n****************************************\n");
    printf("MODAL XREF ITEMS\n");
    printf("****************************************\n\n");
    For_each_modal_xref_item(dag_ptr, i, item_vertex_ptr) {
      printf("[%d] ",i);
      Print_vertex_rec(V_ini_vertex_ptr(item_vertex_ptr));
      if (V_pos_lsList_ptr(item_vertex_ptr)) { 
	printf("\n--positive CNF\n"); 
  	Print_cnf_int(V_pos_lsList_ptr(item_vertex_ptr)); 
      } 
      if (V_neg_lsList_ptr(item_vertex_ptr)) { 
	printf("\n--negative CNF\n"); 
  	Print_cnf_int(V_neg_lsList_ptr(item_vertex_ptr)); 
      } 
      printf("\n------------------------------\n");
    }
    printf("****************************************\n\n");
  }

  return;
}


