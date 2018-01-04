/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE fnode.c - *SAT 1.3 */
/*  Formula as tree */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "fnode.h"


/* *********************************************************************** */
/* Constructors */
/* *********************************************************************** */

fnode_t *Make_empty(void)
{
  return NIL(fnode_t);
}

fnode_t *Make_fnode(void)
{
  fnode_t *t_fnode_ptr;

  t_fnode_ptr = ALLOC(fnode_t,1);
  Op_code(t_fnode_ptr) = nul_code;
  Valuex(t_fnode_ptr) = 0;
  Aux(t_fnode_ptr) = NIL(char);
  Left_fnode_ptr(t_fnode_ptr) = 
    Right_fnode_ptr(t_fnode_ptr) = NIL(fnode_t);

  return t_fnode_ptr;
}

fnode_t *Make_formula_nary( int op_code, 
			    int value,
			   fnode_t *op_fnode_ptr)
{
  fnode_t *t_fnode_ptr;

  t_fnode_ptr = Make_fnode();
  Op_code(t_fnode_ptr) = op_code;
  Valuex(t_fnode_ptr) = value;
  Op_fnode_ptr(t_fnode_ptr) = op_fnode_ptr;

  return t_fnode_ptr;
}

fnode_t *Make_operand_nary(fnode_t *head_fnode_ptr, fnode_t *tail_fnode_ptr)
{
  Next_fnode_ptr(head_fnode_ptr) = tail_fnode_ptr;

  return head_fnode_ptr;
}
  
fnode_t *Make_formula_binary(fnode_t *left_fnode_ptr, 
			      int op_code, 
			      int value,
			     fnode_t *right_fnode_ptr)
{
  fnode_t *t_fnode_ptr;

  t_fnode_ptr = Make_fnode();
  
  Op_code(t_fnode_ptr) = op_code;
  Valuex(t_fnode_ptr) = value;
  Left_fnode_ptr(t_fnode_ptr) = left_fnode_ptr;
  Right_fnode_ptr(t_fnode_ptr)= right_fnode_ptr;

  return t_fnode_ptr;
}


fnode_t *Copy_fnode(fnode_t *a_fnode_ptr)
{
  fnode_t *t_fnode_ptr;
  
  t_fnode_ptr = Make_fnode();
  Op_code(t_fnode_ptr) = Op_code(a_fnode_ptr);
  Valuex(t_fnode_ptr) = Valuex(a_fnode_ptr);
  Op_fnode_ptr(t_fnode_ptr) = Op_fnode_ptr(a_fnode_ptr);
  Next_fnode_ptr(t_fnode_ptr) = Next_fnode_ptr(a_fnode_ptr);

  return t_fnode_ptr;
}

/* *********************************************************************** */
/* Deconstructors */
/* *********************************************************************** */

void Clear_fnode(fnode_t *fnode_ptr, nGeneric_func_ptr_t Clear_aux_func)
{
  if (fnode_ptr) {
    if (Clear_aux_func) (*Clear_aux_func)(Aux(fnode_ptr));
    FREE(fnode_ptr);
  }
}

void Clear_rec_fnode(fnode_t *fnode_ptr, nGeneric_func_ptr_t Clear_aux_func)
{
  if (Left_fnode_ptr(fnode_ptr))
    Clear_rec_fnode(Left_fnode_ptr(fnode_ptr), Clear_aux_func);
  if (Right_fnode_ptr(fnode_ptr)) 
    Clear_rec_fnode(Right_fnode_ptr(fnode_ptr), Clear_aux_func);

  Clear_fnode(fnode_ptr,Clear_aux_func);
}

/* *********************************************************************** */
/* Preprocessing */
/* *********************************************************************** */

fnode_t *Convert_rec(fnode_t *cur_fnode_ptr, fnode_t *next_fnode_ptr) 
{ 
  if (cur_fnode_ptr->right_fnode_ptr)  
    cur_fnode_ptr->right_fnode_ptr =  
      Convert_rec(cur_fnode_ptr->right_fnode_ptr, NIL(fnode_t)); 
  if (cur_fnode_ptr->left_fnode_ptr)  
    cur_fnode_ptr->left_fnode_ptr =  
       Convert_rec(cur_fnode_ptr->left_fnode_ptr, cur_fnode_ptr->right_fnode_ptr); 
  cur_fnode_ptr->right_fnode_ptr = next_fnode_ptr; 
  
  return cur_fnode_ptr; 
} 

fnode_t *Convert_binary2nary(fnode_t *btree_fnode_ptr) 
{ 
  return Convert_rec(btree_fnode_ptr, NIL(fnode_t)); 
} 

void Flatten_bounds(fnode_t *tree_fnode_ptr, 
		    fnode_t **h_fnode_ptr_ptr, fnode_t **t_fnode_ptr_ptr)
{
  fnode_t      *op_fnode_ptr;
   int upper_code;
  fnode_t      *head_fnode_ptr, *tail_fnode_ptr;
  fnode_t      **to_hook_fnode_ptr_ptr;
  fnode_t      *d_fnode_ptr;
  int          dismiss;

  head_fnode_ptr = tail_fnode_ptr = NIL(fnode_t);
  (*h_fnode_ptr_ptr) = 
    (*t_fnode_ptr_ptr) = NIL(fnode_t);

  op_fnode_ptr = (tree_fnode_ptr->left_fnode_ptr);
  switch (Op_code(tree_fnode_ptr))
    {
    case atom_code:
      break;
    case imp_code: case iff_code:
    case not_code: case box_code:
    case dia_code:
      while (op_fnode_ptr) {
	Flatten_bounds(op_fnode_ptr, &head_fnode_ptr, &tail_fnode_ptr);
	op_fnode_ptr = Next_fnode_ptr(op_fnode_ptr);
      }
      break;
    case or_code:
    case and_code:
      upper_code = Op_code(tree_fnode_ptr);
      to_hook_fnode_ptr_ptr = 
	&(tree_fnode_ptr->left_fnode_ptr);
      while (op_fnode_ptr) {
	dismiss = 0;
	d_fnode_ptr = NIL(fnode_t);
	Flatten_bounds(op_fnode_ptr, &head_fnode_ptr, &tail_fnode_ptr);
	if (Op_code(op_fnode_ptr) == upper_code) {
	  *to_hook_fnode_ptr_ptr = head_fnode_ptr;
	  to_hook_fnode_ptr_ptr = &(Next_fnode_ptr(tail_fnode_ptr));
	  dismiss = 1;
	} else {
	  *to_hook_fnode_ptr_ptr = op_fnode_ptr;
	  to_hook_fnode_ptr_ptr = &(Next_fnode_ptr(op_fnode_ptr));
	}
	if ((Next_fnode_ptr(op_fnode_ptr) == NIL(fnode_t))
	    && (!dismiss))
	  *t_fnode_ptr_ptr = op_fnode_ptr;
	else
	  *t_fnode_ptr_ptr = tail_fnode_ptr;
	if (dismiss) d_fnode_ptr = op_fnode_ptr; 
 	op_fnode_ptr = Next_fnode_ptr(op_fnode_ptr);
 	Clear_fnode(d_fnode_ptr, NULL); 
      }
      *h_fnode_ptr_ptr = Op_fnode_ptr(tree_fnode_ptr);
    }
}  

void Flatten_and_or(fnode_t *ntree_fnode_ptr)
{
  fnode_t *dummy_head_fnode_ptr,*dummy_tail_fnode_ptr;

  dummy_head_fnode_ptr = 
    dummy_tail_fnode_ptr = NIL(fnode_t);
  Flatten_bounds(ntree_fnode_ptr, 
		 &dummy_head_fnode_ptr, 
		 &dummy_tail_fnode_ptr);
}

void Flatten_double_not(fnode_t *ntree_fnode_ptr)
{
  fnode_t *op_fnode_ptr, *d_fnode_ptr;

  if ((Op_code(ntree_fnode_ptr) == not_code) &&
      (Op_code(ntree_fnode_ptr->left_fnode_ptr) == not_code)) {
    Op_code(ntree_fnode_ptr) =
		Op_code(ntree_fnode_ptr->left_fnode_ptr->left_fnode_ptr);
    Valuex(ntree_fnode_ptr) = 
	      Valuex(ntree_fnode_ptr->left_fnode_ptr->left_fnode_ptr);
    d_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
    Op_fnode_ptr(ntree_fnode_ptr) =
		 Op_fnode_ptr(ntree_fnode_ptr->left_fnode_ptr->left_fnode_ptr);
    Clear_fnode(Op_fnode_ptr(d_fnode_ptr), NULL);
    Clear_fnode(d_fnode_ptr, NULL);
  }
  if (!Is_atom(ntree_fnode_ptr)) {
    op_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
    while (op_fnode_ptr) {
      Flatten_double_not(op_fnode_ptr);
      op_fnode_ptr = Next_fnode_ptr(op_fnode_ptr);
    }
  }
}

void Convert_dia2box(fnode_t *ntree_fnode_ptr)
{
  fnode_t *keep_fnode_ptr, *op_fnode_ptr;
   int v_keep;

  if (Op_code(ntree_fnode_ptr) == dia_code) {
    keep_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
    v_keep = Valuex(ntree_fnode_ptr);
    Op_code(ntree_fnode_ptr) = not_code;
    Valuex(ntree_fnode_ptr) = empty_code;
    Op_fnode_ptr(ntree_fnode_ptr) =
		 Make_formula_nary(box_code, v_keep, 
				   Make_formula_nary(not_code, empty_code, keep_fnode_ptr));
    Convert_dia2box(keep_fnode_ptr);
  } else {
    if (!Is_atom(ntree_fnode_ptr)) {
      op_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
      while (op_fnode_ptr) {
	Convert_dia2box(op_fnode_ptr);
	op_fnode_ptr = Next_fnode_ptr(op_fnode_ptr);
      }
    }
  }

  return;
}

/*  void Convert_NNF(fnode_t *btree_fnode_ptr, int flag_nnf) */
/*  { */
/*    fnode_t *t_fnode_ptr; */

/*    switch (Op_code(btree_fnode_ptr))  */
/*      { */
/*      case atom_code: */
/*        if (flag_nnf) { */
/*  	Op_code(btree_fnode_ptr) = not_code; */
/*  	btree_fnode_ptr->left_fnode_ptr =  */
/*  	  Make_formula_binary(Make_empty(), atom_code, Valuex(btree_fnode_ptr), Make_empty()); */
/*  	Valuex(btree_fnode_ptr) = empty_code; */
/*        } */
/*        break; */
/*      case top_code: */
/*        if (flag_nnf) Op_code(btree_fnode_ptr) = bot_code; */
/*        break; */
/*      case bot_code: */
/*        if (flag_nnf) Op_code(btree_fnode_ptr) = top_code; */
/*        break; */
/*      case box_code: */
/*        Convert_NNF(Left_fnode_ptr(btree_fnode_ptr), 0); */
/*        if (flag_nnf) { */
/*  	Op_code(btree_fnode_ptr) = not_code; */
/*  	btree_fnode_ptr->left_fnode_ptr =  */
/*  	  Make_formula_binary(Left_fnode_ptr(btree_fnode_ptr), box_code, empty_code, Make_empty()); */
/*        } */
/*        break; */
/*      case dia_code: */
/*        t_fnode_ptr = Left_fnode_ptr(btree_fnode_ptr); */
/*        if (!flag_nnf) { */
/*  	Op_code(btree_fnode_ptr) = not_code; */
/*  	Left_fnode_ptr(btree_fnode_ptr) = Make_formula_binary(t_fnode_ptr, */
/*  							      box_code, empty_code, */
/*  							      Make_empty()); */
/*        } else  */
/*  	Op_code(btree_fnode_ptr) = box_code; */
/*        Convert_NNF(t_fnode_ptr,1); */
/*        break; */
/*      case not_code: */
/*        if (flag_nnf) */
/*  	Convert_NNF(Left_fnode_ptr(btree_fnode_ptr),0); */
/*        else */
/*  	Convert_NNF(Left_fnode_ptr(btree_fnode_ptr),1); */
      
/*        t_fnode_ptr = Left_fnode_ptr(btree_fnode_ptr); */
/*        Left_fnode_ptr(btree_fnode_ptr) = Left_fnode_ptr(t_fnode_ptr); */
/*        Right_fnode_ptr(btree_fnode_ptr) = Right_fnode_ptr(t_fnode_ptr); */
/*        Op_code(btree_fnode_ptr) = Op_code(t_fnode_ptr); */
/*        Valuex(btree_fnode_ptr) = Valuex(t_fnode_ptr); */
/*        Clear_fnode(t_fnode_ptr, NULL); */

/*        break; */

/*      case or_code: */
/*        if (flag_nnf) Op_code(btree_fnode_ptr) = and_code; */
/*        Convert_NNF(Left_fnode_ptr(btree_fnode_ptr), flag_nnf); */
/*        Convert_NNF(Right_fnode_ptr(btree_fnode_ptr), flag_nnf); */
/*        break; */

/*      case and_code: */
/*        if (flag_nnf) Op_code(btree_fnode_ptr) = or_code; */
/*        Convert_NNF(Left_fnode_ptr(btree_fnode_ptr), flag_nnf); */
/*        Convert_NNF(Right_fnode_ptr(btree_fnode_ptr), flag_nnf); */
/*        break; */

/*      case imp_code: */
/*        if (flag_nnf) { */
/*  	Op_code(btree_fnode_ptr) = and_code; */
/*  	Convert_NNF(Left_fnode_ptr(btree_fnode_ptr), 0); */
/*  	Convert_NNF(Right_fnode_ptr(btree_fnode_ptr), 1); */
/*        } else { */
/*  	Op_code(btree_fnode_ptr) = or_code; */
/*  	Convert_NNF(Left_fnode_ptr(btree_fnode_ptr), 1); */
/*  	Convert_NNF(Right_fnode_ptr(btree_fnode_ptr), 0); */
/*        } */
/*        break; */

/*      case iff_code: */
/*        if (flag_nnf) { */
/*  	Convert_NNF(Left_fnode_ptr(btree_fnode_ptr), 0); */
/*  	Convert_NNF(Right_fnode_ptr(btree_fnode_ptr), 1); */
/*        } else { */
/*  	Convert_NNF(Left_fnode_ptr(btree_fnode_ptr), 0); */
/*  	Convert_NNF(Right_fnode_ptr(btree_fnode_ptr), 0); */
/*        } */
/*        break; */
/*      } */

/*    return; */
/*  }  */

void Convert_NNF(fnode_t *ntree_fnode_ptr, int flag_nnf)
{
  fnode_t *t_fnode_ptr;

  switch (Op_code(ntree_fnode_ptr)) 
    {
    case atom_code:
      if (flag_nnf) {
	Op_code(ntree_fnode_ptr) = not_code;
	Op_fnode_ptr(ntree_fnode_ptr) = 
	  Make_formula_nary(atom_code, Valuex(ntree_fnode_ptr), Make_empty());
	Valuex(ntree_fnode_ptr) = empty_code;
      }
      break;
    case top_code:
      if (flag_nnf) Op_code(ntree_fnode_ptr) = bot_code;
      break;
    case bot_code:
      if (flag_nnf) Op_code(ntree_fnode_ptr) = top_code;
      break;
    case box_code:
      /* Propagate the conversion inside the box */
      Convert_NNF(Op_fnode_ptr(ntree_fnode_ptr), 0);
      if (flag_nnf) {
	Op_code(ntree_fnode_ptr) = not_code;
	Op_fnode_ptr(ntree_fnode_ptr) = 
	  Make_formula_nary(box_code, Valuex(ntree_fnode_ptr), Op_fnode_ptr(ntree_fnode_ptr));
	Valuex(ntree_fnode_ptr) = empty_code;
      }
      break;
    case dia_code:
      t_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
      if (!flag_nnf) {
	Op_code(ntree_fnode_ptr) = not_code;
	Op_fnode_ptr(ntree_fnode_ptr) = Make_formula_nary(box_code, Valuex(ntree_fnode_ptr), t_fnode_ptr);
	Valuex(ntree_fnode_ptr) = empty_code;
      } else 
	Op_code(ntree_fnode_ptr) = box_code;
      Convert_NNF(t_fnode_ptr,1);
      break;
    case not_code:
      if (flag_nnf)
	Convert_NNF(Op_fnode_ptr(ntree_fnode_ptr),0);
      else
	Convert_NNF(Op_fnode_ptr(ntree_fnode_ptr),1);
      
      t_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
      Op_fnode_ptr(ntree_fnode_ptr) = Op_fnode_ptr(t_fnode_ptr);
      Op_code(ntree_fnode_ptr) = Op_code(t_fnode_ptr);
      Valuex(ntree_fnode_ptr) = Valuex(t_fnode_ptr);
      Clear_fnode(t_fnode_ptr, NULL);

      break;

    case or_code:
      if (flag_nnf) Op_code(ntree_fnode_ptr) = and_code;
      t_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
      while (t_fnode_ptr != NIL(fnode_t)) {
	Convert_NNF(t_fnode_ptr, flag_nnf);
	t_fnode_ptr = Next_fnode_ptr(t_fnode_ptr);
      }
      break;

    case and_code:
      if (flag_nnf) Op_code(ntree_fnode_ptr) = or_code;
      t_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
      while (t_fnode_ptr != NIL(fnode_t)) {
	Convert_NNF(t_fnode_ptr, flag_nnf);
	t_fnode_ptr = Next_fnode_ptr(t_fnode_ptr);
      }
      break;

    case imp_code:
      if (flag_nnf) {
	Op_code(ntree_fnode_ptr) = and_code;
	Convert_NNF(Op_fnode_ptr(ntree_fnode_ptr), 0);
	Convert_NNF(Next_fnode_ptr(Op_fnode_ptr(ntree_fnode_ptr)), 1);
      } else {
	Op_code(ntree_fnode_ptr) = or_code;
	Convert_NNF(Op_fnode_ptr(ntree_fnode_ptr), 1);
	Convert_NNF(Next_fnode_ptr(Op_fnode_ptr(ntree_fnode_ptr)), 0);
      }
      break;

    case iff_code:
      if (flag_nnf) {
	Convert_NNF(Op_fnode_ptr(ntree_fnode_ptr), 0);
	Convert_NNF(Next_fnode_ptr(Op_fnode_ptr(ntree_fnode_ptr)), 1);
      } else {
	Convert_NNF(Op_fnode_ptr(ntree_fnode_ptr), 0);
	Convert_NNF(Next_fnode_ptr(Op_fnode_ptr(ntree_fnode_ptr)), 0);
      }
      break;
    }

  return;
}



/* *********************************************************************** */
/* Translations */
/* *********************************************************************** */
void Translate_from_E_to_K(fnode_t *ntree_fnode_ptr)
{
  fnode_t *keep_fnode_ptr, *op_fnode_ptr;

  /* Boldly no diamonds here! */
  assert(Op_code(ntree_fnode_ptr) != dia_code);
  if (Op_code(ntree_fnode_ptr) == box_code) {
    /* Boldly single agent logic! */
    assert(Valuex(ntree_fnode_ptr) == 0);
    /* Translation from E to K(0,1): t([]F) -> -[0]-( [1]t(F) /\ [0]-t(F)) */
    Op_code(ntree_fnode_ptr) = not_code;
    keep_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
    Op_fnode_ptr(ntree_fnode_ptr) = 
      Make_formula_nary(box_code, 0, 
        Make_formula_nary(not_code, empty_code,
          Make_formula_nary(and_code, empty_code, 
			    Make_operand_nary(Make_formula_nary(box_code, 1, keep_fnode_ptr),
					      Make_formula_nary(box_code, 0,
								Make_formula_nary(not_code, empty_code,
										  keep_fnode_ptr))))));
    Translate_from_E_to_K(keep_fnode_ptr);
  } else {
    if (!Is_atom(ntree_fnode_ptr)) {
      op_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
      while (op_fnode_ptr) {
	Translate_from_E_to_K(op_fnode_ptr);
	op_fnode_ptr = Next_fnode_ptr(op_fnode_ptr);
      }
    }
  }

  return;
}

void Translate_from_EM_to_K(fnode_t *ntree_fnode_ptr)
{
  fnode_t *keep_fnode_ptr, *op_fnode_ptr;

  /* Boldly no diamonds here! */
  assert(Op_code(ntree_fnode_ptr) != dia_code);
  if (Op_code(ntree_fnode_ptr) == box_code) {
    /* Boldly single agent logic! */
    assert(Valuex(ntree_fnode_ptr) == 0);
    /* Translation from EM to K: t([]F) -> -[0]-([0]t(F)) */
    Op_code(ntree_fnode_ptr) = not_code;
    keep_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
    Op_fnode_ptr(ntree_fnode_ptr) = 
      Make_formula_nary(box_code, 0, 
        Make_formula_nary(not_code, empty_code,
          Make_formula_nary(box_code, 0, keep_fnode_ptr)));
    Translate_from_EM_to_K(keep_fnode_ptr);
  } else {
    if (!Is_atom(ntree_fnode_ptr)) {
      op_fnode_ptr = Op_fnode_ptr(ntree_fnode_ptr);
      while (op_fnode_ptr) {
	Translate_from_E_to_K(op_fnode_ptr);
	op_fnode_ptr = Next_fnode_ptr(op_fnode_ptr);
      }
    }
  }

  return;
}

/* *********************************************************************** */
/* Tests */
/* *********************************************************************** */
int Is_simple(fnode_t *fnode_ptr)
{
  fnode_t *op_fnode_ptr;

  if (Is_atom(fnode_ptr)) return (0);
  op_fnode_ptr = Op_fnode_ptr(fnode_ptr);
  while (op_fnode_ptr) {
    if (!Is_atom(op_fnode_ptr)) return (0);
    op_fnode_ptr = Next_fnode_ptr(op_fnode_ptr);
  }

  return (1);
}

/* *********************************************************************** */
/* Output routines */
/* *********************************************************************** */

void Print_fnode_cnf(fnode_t *fnode_ptr) 
{
  fnode_t *or_fnode_ptr, *lit_fnode_ptr;;
  
  or_fnode_ptr = Op_fnode_ptr(fnode_ptr);
  while (or_fnode_ptr) 
     { 
       lit_fnode_ptr = Op_fnode_ptr(or_fnode_ptr);
       while (lit_fnode_ptr) {
	 if (Op_code(lit_fnode_ptr) == not_code)
	   printf("-%d ",Valuex(Op_fnode_ptr(lit_fnode_ptr)));
	 else
	   printf("%d ",Valuex(lit_fnode_ptr));
	 lit_fnode_ptr = Next_fnode_ptr(lit_fnode_ptr);
       }
       printf("\n");
       or_fnode_ptr = Next_fnode_ptr(or_fnode_ptr);
     }

  return;
}

void Print_fnode_lwb(fnode_t *fnode_ptr)
{
  switch (Op_code(fnode_ptr))
    {
    case and_code: case or_code:           
    case imp_code: case iff_code:        
      printf("(");
      Print_fnode_lwb(Left_fnode_ptr(fnode_ptr));
      switch (Op_code(fnode_ptr))
	{
	case and_code:
	  printf(" & "); break;
	case or_code:
	  printf(" v "); break;
	case imp_code:
	  printf(" -> "); break;
	case iff_code:
	  printf(" <-> "); break; 
	}
      Print_fnode_lwb(Right_fnode_ptr(fnode_ptr));
      printf(")");
      break;
    case box_code:
    case dia_code:
    case not_code:
      printf("(");
      switch (Op_code(fnode_ptr))
	{
	case not_code:
	  printf("~"); break;
	case box_code:
	  printf("box "); break;
	case dia_code:
	  printf("dia "); break;
	}
      Print_fnode_lwb(Left_fnode_ptr(fnode_ptr));
      printf(")");
      break;
    case atom_code:
      printf("p%d",(Valuex(fnode_ptr)));
      break;
    case top_code:
      printf("true");
      break;
    case bot_code:
      printf("false");
      break;
    }
  fflush(stdout);
  return;
}







