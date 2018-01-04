/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE trie.c - *SAT 1.3 */
/*  SATO satisfiability checker */ 

/*  *********************************************************************** */
/*  *********************************************************************** */


/*********************************************************************
; Copyright 1992-97, The University of Iowa (UI).  All rights reserved. 
; By using this software the USER indicates that he or she has read, 
; understood and will comply with the following:
;
; --- UI hereby grants USER nonexclusive permission to use, copy and/or
; modify this software for internal, noncommercial, research purposes only.
; Any distribution, including commercial sale or license, of this software,
; copies of the software, its associated documentation and/or modifications
; of either is strictly prohibited without the prior consent of UI.  Title
; to copyright to this software and its associated documentation shall at
; all times remain with UI.  Appropriate copyright notice shall be placed
; on all software copies, and a complete copy of this notice shall be
; included in all copies of the associated documentation.  No right is
; granted to use in advertising, publicity or otherwise any trademark,
; service mark, or the name of UI.  Software and/or its associated
; documentation identified as "confidential," if any, will be protected
; from unauthorized use/disclosure with the same degree of care USER
; regularly employs to safeguard its own such information.
;
; --- This software and any associated documentation is provided "as is," and
; UI MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS OR IMPLIED, INCLUDING
; THOSE OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE, OR THAT
; USE OF THE SOFTWARE, MODIFICATIONS, OR ASSOCIATED DOCUMENTATION WILL
; NOT INFRINGE ANY PATENTS, COPYRIGHTS, TRADEMARKS OR OTHER INTELLECTUAL
; PROPERTY RIGHTS OF A THIRD PARTY.  UI, the University of Iowa,
; its Regents, officers, and employees shall not be liable under any
; circumstances for any direct, indirect, special, incidental, or
; consequential damages with respect to any claim by USER or any third
; party on account of or arising from the use, or inability to use, this
; software or its associated documentation, even if UI has been advised
; of the possibility of those damages.
*********************************************************************/
#include "satotrie.h"

#define trie_assign_value(image_ptr, i, val)\
  if (Backup_idx(image_ptr)) {\
    V3(image_ptr)[i]->next = Top_var3(image_ptr)->next;\
    Top_var3(image_ptr)->next = V3(image_ptr)[i]; }\
  assign_value(image_ptr,i, val)

#define trie2_assign_value(image_ptr, i, val)\
  if (Backup_idx(image_ptr)) {\
    V2(image_ptr)[i]->next = Top_var2(image_ptr)->next;\
    Top_var2(image_ptr)->next = V2(image_ptr)[i]; }\
  assign_value(image_ptr,i, val)

image_t *Init_image()
{
  image_t *t_image_ptr;

  t_image_ptr = ALLOC(image_t, 1);
  
  Trie_avail(t_image_ptr) = CLAUSE3(t_image_ptr) = 
    Root3(t_image_ptr) = NHtrie(t_image_ptr) = CLtrie(t_image_ptr) = NULL;
  V3(t_image_ptr) =  NULL;
  V2(t_image_ptr) = NULL;
  Trie2_Ucl(t_image_ptr) = NULL;
  Top_var3(t_image_ptr) = NULL;
  Top_var2(t_image_ptr) = NULL;
  Conflict_cl(t_image_ptr) = Nonunit_cls(t_image_ptr) = 
    Old_cls(t_image_ptr) = BItrie(t_image_ptr) = NULL;

  Branch_mark(t_image_ptr) = 1;
  Roots(t_image_ptr) = ALLOC(trie_ptr_t, MAX_ATOM);
  Tdc_idx_end(t_image_ptr) = MAX_ATOM;
  Act_max_atom(t_image_ptr) = 0;

  /* Inizialization of allocated blocks list */
  Cur_block(t_image_ptr) = 0;

  /* Inizialization of modal backjumping points */
  Jump_point(t_image_ptr) = MAX_LIST;
  Last_stack_idx(t_image_ptr) = 0;

  return t_image_ptr;
}

void Clear_image(image_t *image_ptr)
{
  int       i;

  /* Deallocate all the blocks in the tracking list */
  for (i = 0; i < Cur_block(image_ptr); i++) FREE(Ablocks_table(image_ptr)[i]);

  FREE(image_ptr->roots);
  FREE(image_ptr);

  return;
}

void trie_init_once_forall (image_ptr)
     image_t *image_ptr;
{
#ifdef MORETRACE
  if (sizeof(struct trie) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct trie) = %d\n", sizeof(struct trie));
  if (sizeof(struct var2) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct var2) = %d\n", sizeof(struct var2));
  if (sizeof(struct var3) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct var3) = %d\n", sizeof(struct var3));
  if (sizeof(struct cap) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct cap) = %d\n", sizeof(struct cap));
#endif

  V2(image_ptr) = NULL;
  V3(image_ptr) = NULL;
  CLtrie(image_ptr) = NHtrie(image_ptr) = Root3(image_ptr) = NULL;
  Trie_news(image_ptr) = Trie_frees(image_ptr) = Trie_gets(image_ptr) = Trie_avails(image_ptr) = 0;
  Trie_avail(image_ptr) = NULL;
  BItrie(image_ptr) = CLAUSE3(image_ptr) = get_trie(image_ptr);
}

void init_trie (image_ptr)
     image_t *image_ptr;
{
  free_trie(image_ptr,Root3(image_ptr));   /* CHANGED with 3.2 */
  free_trie(image_ptr,NHtrie(image_ptr));  /* CHANGED with 3.2 */
  free_trie(image_ptr,CLtrie(image_ptr));  /* CHANGED with 3.2 */
  Old_cls(image_ptr) = NULL;
  Root3(image_ptr) = CLtrie(image_ptr) = NHtrie(image_ptr) = NULL;
  /* Added */
  NHtrietl(image_ptr) = NULL;
  Backup_idx(image_ptr) = 0;
  /* STACK */
  Stack_idx(image_ptr) = 0;
#ifdef MORETRACE
  if (TRACE == 4) printf("init_trie: stack index is %d\n",Stack_idx(image_ptr));
#endif
  Top_var2(image_ptr) = NULL;
  Top_var3(image_ptr) = NULL;

  NH_num(image_ptr) = Jump_num(image_ptr) = 
    Pure_num(image_ptr) = UIP_num(image_ptr) = Clause_extra_num(image_ptr) = 0;
  Miss_num(image_ptr) = 0;
}

struct trie *trie_create_one_path (image_ptr, arr, signs, count)
     image_t *image_ptr; int arr[], signs[], count;
{
  int sign;
  struct trie *first, *pre, *no;

  first = no = get_trie(image_ptr); 
  no->key = arr[count]; 
  sign = signs[no->key];
  while (--count >= 0) {
    pre = no;
    no = get_trie(image_ptr);
    if (sign) pre->pos = no;
    else pre->neg = no;
    no->key = arr[count]; 
    sign = signs[no->key];
  }
  if (sign)
    no->pos = CLAUSE3(image_ptr);
  else
    no->neg = CLAUSE3(image_ptr);
  return first;
}

int trie_insert_clause ( image_ptr, cl_arr, sign_arr, total )             
     image_t *image_ptr; int cl_arr[], sign_arr[], total;
{

  if (Root3(image_ptr) == CLAUSE3(image_ptr)) return 1;

  if (total > 0) 
    Root3(image_ptr) = trie_insert_literals(image_ptr, Root3(image_ptr), cl_arr, sign_arr, total-1);

  if (total == 0 || Root3(image_ptr) == CLAUSE3(image_ptr)) { /* an empty clause is found */

#ifdef MORETRACE
    if (TRACE > 6)
      printf( "    [C%ld] becomes empty.\n", Clause_num(image_ptr));
#endif

    free_trie(image_ptr,Root3(image_ptr)); /* CHANGED with 3.2 */
    Root3(image_ptr) = CLAUSE3(image_ptr);
    return 1;
  }
  return 0;
}

struct trie *trie_insert_literals (image_ptr, root, arr, signs, count)
     image_t *image_ptr;
     struct trie *root; /* current root of the tree */
     int arr[], signs[]; /* current clause */
     int count; /* the length of the current clause */
     /* int depth; depth(Root3(image_ptr)) = 0, depth(Root3(image_ptr).pos) = 1, etc. */

{
  int key;
  int sign, idx;
  struct trie *no, *bro1, *bro2, *pars[MAX_LENGTH];
  /* Removed and put into image_ptr */
  /*    static struct trie *roots[MAX_ATOM]; */

  if (root == NULL)
    for (idx = 0; idx < Max_atom(image_ptr); idx++) Roots(image_ptr)[idx] = NULL;

  key = arr[count];

  if (Roots(image_ptr)[key] == NULL) {
    if (GRASP && Backup_idx(image_ptr)) {
      for (idx = key-1; idx >= 0; idx--) {
	if (Roots(image_ptr)[idx] != NULL) {
	  return trie2_insert_clause(image_ptr,Roots(image_ptr)[idx], arr, signs, count);
	}
      }
      return trie2_insert_clause(image_ptr,root, arr, signs, count);
    }
    Roots(image_ptr)[key] = no = trie_create_one_path (image_ptr,arr, signs, count);
    for (idx = key-1; idx >= 0; idx--) {
      if (Roots(image_ptr)[idx] != NULL) {
	no->bro = Roots(image_ptr)[idx]->bro;
	Roots(image_ptr)[idx]->bro = no;
	return root;
      }
    }
    no->bro = root;
    return no;
  }

  no = Roots(image_ptr)[key];

  if (GRASP && Backup_idx(image_ptr)) 
    return trie2_insert_clause(image_ptr, no, arr, signs, count);

  idx = 0;
  bro1 = bro2 = NULL;

  while (no != NULL && count >= 0) {
    key = arr[count];
    sign = signs[key]; 
    
    if (key == no->key) {
      if HAS_POS_CL(image_ptr,no) {
	
	if (sign == 1) {
#ifdef MORETRACE
	  print_x_subsume(image_ptr);
#endif
	  Subsume_num(image_ptr)++;
	  return root; /* skip this clause */
	} /* otherwise sign = 0 */

#ifdef MORETRACE
	print_x_skip(image_ptr);
#endif
	
	count--;
	bro1 = no;
	no = no->bro; 

      } else if HAS_NEG_CL(image_ptr,no) {
      
	if (sign == 0) {
#ifdef MORETRACE
	  print_x_subsume(image_ptr);
#endif
	  Subsume_num(image_ptr)++;
	  return root; /* skip this clause */
	} /* otherwise sign == 1 */

#ifdef MORETRACE
	print_x_skip(image_ptr);
#endif
	count--;
	bro1 = no;
	no = no->bro; 
      } else {
	count--;
	pars[idx++] = no;
	bro1 = NULL;
	if (sign) no = no->pos; else no = no->neg;
      }
      
    } else if (key < no->key) {
      bro2 = no;
      no = NULL;
    } else {
      bro1 = no;
      no = bro1->bro;
      while ((no != NULL) && (no->key < key)) {
	bro1 = no;
	no = bro1->bro;
      }
    }
  }

  if (count >= 0) {
    no = trie_create_one_path (image_ptr, arr, signs, count);
    no->bro = bro2;
    if (bro1 == NULL) {
      if (idx--) {
	if (signs[pars[idx]->key])
	  pars[idx]->pos = no;
	else 
	  pars[idx]->neg = no;
	return root;
      } else {
	return no;
      }
    } else {
      bro1->bro = no;
      return root;
    }
  }

  /* count < 0 */
  while (idx--) {
    no = pars[idx];
    sign = signs[no->key];
    if (sign) {
      free_trie(image_ptr,no->pos);
      no->pos = CLAUSE3(image_ptr);
    
      if (no->neg != NULL) {
	no->bro = merge_tries(image_ptr, no->bro, no->neg);
	no->neg = NULL;
      }
    } else {
      free_trie(image_ptr,no->neg);
      no->neg = CLAUSE3(image_ptr);    
    
      if (no->pos != NULL) {
	no->bro = merge_tries(image_ptr, no->bro, no->pos);
	no->pos = NULL;
      }
    }
    
    if (no->bro != CLAUSE3(image_ptr)) return root;
  }
  return CLAUSE3(image_ptr);
}

struct trie *trie_attach_clause (image_ptr, no, sign )
     image_t *image_ptr;
     struct trie *no;
     int sign;
{
  if ( sign == 1 ) {
    
    free_trie(image_ptr,no->pos); /* CHANGED with 3.2 */
    no->pos = CLAUSE3(image_ptr);
    
    if (no->neg != NULL) {
      no->bro = merge_tries(image_ptr, no->bro, no->neg);
      no->neg = NULL;
    }
      
  } else {
      
    free_trie(image_ptr,no->neg); /* CHANGED with 3.2 */
    no->neg = CLAUSE3(image_ptr);    
    
    if (no->pos != NULL) {
      no->bro = merge_tries(image_ptr, no->bro, no->pos);
      no->pos = NULL;
    }
  }
  
  if (no->bro == CLAUSE3(image_ptr)) { /* release no and return no->bro */
    free_trie(image_ptr,no);           /* CHANGED with 3.2 */
    return CLAUSE3(image_ptr);
  } else 
    return no;
}

struct trie *merge_tries(image_ptr, n1, n2)
     image_t *image_ptr;
     struct trie *n1, *n2;  
     /* do lazy clean and complete merge */
{
    if (n2 == NULL) return n1;  
    if (n2 == CLAUSE3(image_ptr)) { free_trie(image_ptr,n1); return n2;} /* CHANGED with 3.2 */
    if (n1 == NULL) return n2;
    if (n1 == CLAUSE3(image_ptr)) { free_trie(image_ptr,n2); return n1;} /* CHANGED with 3.2 */
    
    if (n2->key < n1->key) {
    n2->bro = merge_tries(image_ptr,n1, n2->bro);
    /* CHANGED with 3.2 */
    if (n2->bro == CLAUSE3(image_ptr)) { free_trie(image_ptr,n2); return CLAUSE3(image_ptr); } 
    return n2;
  }

  if (n1->key < n2->key) {
    n1->bro = merge_tries(image_ptr, n1->bro, n2);
    /* CHANGED with 3.2 */
    if (n1->bro == CLAUSE3(image_ptr)) { free_trie(image_ptr,n1); return CLAUSE3(image_ptr); }
    return n1;
  }

  /* now, n1->key == n2->key */
  n1->bro = merge_tries(image_ptr,n1->bro, n2->bro);
  n2->bro = NULL;
  if (n1->bro == CLAUSE3(image_ptr)) {
    free_trie(image_ptr,n1);  /* CHANGED with 3.2 */
    free_trie(image_ptr,n2);  /* CHANGED with 3.2 */
    return CLAUSE3(image_ptr);
  }

  n1->pos = merge_tries(image_ptr,n1->pos, n2->pos);
  n1->neg = merge_tries(image_ptr,n1->neg, n2->neg);
  free_trie_cell(image_ptr, n2);

  if (n1->pos == CLAUSE3(image_ptr)) {
    n1->bro = merge_tries(image_ptr,n1->bro, n1->neg);
    n1->neg = NULL;
  }
  if (n1->neg == CLAUSE3(image_ptr)) {
    n1->bro = merge_tries(image_ptr,n1->bro, n1->pos);
    n1->pos = NULL;
  }

  /* CHANGED with 3.2 */
  if (n1->bro == CLAUSE3(image_ptr)) { free_trie(image_ptr,n1); return CLAUSE3(image_ptr); }
  return n1;
}

/* CHANGED with 3.2 */
/*  struct trie *get_trie_link (image_ptr) */
/*       image_t *image_ptr; */
/*  { */
/*    struct trie *p; */
/*    struct links *l; */

/*    l = ( struct links * ) tp_alloc (image_ptr,  sizeof ( struct links ) ); */
/*    p = ( struct trie * ) tp_alloc (image_ptr,  sizeof ( struct trie ) ); */
/*    if (p == NULL) { */
/*      fprintf ( stderr, "get_trie return NULL.\n"); */
/*      exit(1); */
/*    } */

/*    l->lin = l->back = NULL; */
/*    l->stamp = NULL; */

/*    p->link = l; */
/*    p->pos = p->neg = p->bro = p->par = NULL; */
/*    p->esign = DC; */

/*    return (p); */
/*  }  */

struct trie *get_trie (image_ptr)
     image_t *image_ptr;
{
  struct trie *p;
  struct links *l;

#ifndef OPTIMIZE
  if (Trie_avail(image_ptr) == NULL) {
      l = NULL;
      p = ( struct trie * ) tp_alloc ( image_ptr, sizeof ( struct trie ) );
      if (p == NULL) {
	fprintf ( stderr, "get_trie return NULL.\n");
	exit(1);
      }
      p->link = l;
      Trie_news(image_ptr)++;
  } else {
    Trie_avails(image_ptr)--;
    p = Trie_avail(image_ptr);
    Trie_avail(image_ptr) = Trie_avail(image_ptr)->bro;
  }
#else
  if (Trie_avail(image_ptr)) {
    Trie_avails(image_ptr)--;
    p = Trie_avail(image_ptr);
    Trie_avail(image_ptr) = Trie_avail(image_ptr)->bro;
  } else {
    l = NULL;
    p = ( struct trie * ) tp_alloc ( image_ptr, sizeof ( struct trie ) );
    p->link = l;
    Trie_news(image_ptr)++;
  }
#endif

  Trie_gets(image_ptr)++;
  p->pos = p->neg = p->bro = p->par = NULL;
  p->esign = DC;

  return(p);
} 
 
void free_trie (image_ptr, no)
     image_t *image_ptr;
     struct trie *no;
{
  /* CHANGED with 3.2 */
  struct trie *no2;

  if (no != NULL && no != CLAUSE3(image_ptr)) {
    if (no->pos != NULL && no->pos != CLAUSE3(image_ptr)) free_trie (image_ptr, no->pos );
    if (no->neg != NULL && no->neg != CLAUSE3(image_ptr)) free_trie (image_ptr,  no->neg );
    /* CHANGED with 3.2 */
    no2 = no;
    no = no->bro;
    free_trie_cell(image_ptr, no2);
  }
}

/* CHANGED with 3.2 */
/*  void free_trie2 (image_ptr,no) */
/*       image_t *image_ptr; */
/*       struct trie *no; */
/*  { */
/*    struct trie *no2; */
/*    while (no != NULL && no != CLAUSE3(image_ptr)) { */
/*      if (no->pos != NULL && no->pos != CLAUSE3(image_ptr)) free_trie2 (image_ptr,  no->pos ); */
/*      if (no->neg != NULL && no->neg != CLAUSE3(image_ptr)) free_trie2 (image_ptr,  no->neg ); */
/*      no2 = no; */
/*      no = no->bro; */
/*      free_trie_cell(image_ptr, no2); */
/*    } */
/*  } */

void print_trie (image_ptr, no)
     image_t *image_ptr;
     struct trie *no;
{
  printf( "\nClause Tree:\n");
  if (no == NULL)
    printf( "   nil");
  else if (no == CLAUSE3(image_ptr))
    printf( "   [C]");
  else 
    print_trie_aux(image_ptr, no, 0, "", "", "");
  printf( "\n");
}

void print_trie_aux(image_ptr, no, sign, leader, addition, arrow)
     /* assume no != NULL */
     image_t *image_ptr;
     struct trie *no;
     int sign;
     char *leader, *addition, *arrow;
{
  char leader2[MAX_ATOM];
  int i;
  i = 0;

  printf( "\n%s%s", leader, arrow);

  if (sign == 0)
    printf( " x%d[%d,%d]", no->key, no->esign, no->psign);
  else if (sign == 1 || sign == 2)
    if (no == CLAUSE3(image_ptr))
      printf( "->[C]");
    else 
      printf( "-x%d[%d,%d]", no->key, no->esign, no->psign);
  else 
    printf( " x%d[%d,%d]", no->key, no->esign, no->psign);

  if (no->pos != NULL) i++;
  if (no->neg != NULL) i++;
  if (no->bro != NULL) i++;

  str_cat(leader, addition, leader2);

  if (no->pos != NULL) {
    if (i == 1)
      print_trie_aux(image_ptr, no->pos, 1, leader2, "     ", " `-P-");
    else
      print_trie_aux(image_ptr, no->pos, 1, leader2, " |   ", " |-P-");
    i--;
  }

  if (no->neg != NULL) {
    if (i == 1)
      print_trie_aux(image_ptr, no->neg, 2, leader2, "     ", " `-N-");
    else
      print_trie_aux(image_ptr, no->neg, 2, leader2, " |   ", " |-N-");
    i--;
  }

  if (no->bro != NULL) {
      print_trie_aux(image_ptr, no->bro, 3, leader2, "", "");
    }
}

/***********************************************************/
/** search for a model **/
/***********************************************************/

/* Modified to work with consistency testing */
int trie_search (image_ptr, dag_ptr, Test_star_consistency)
     image_t         *image_ptr;
     dag_t           *dag_ptr;
     Cons_func_ptr_t Test_star_consistency;
{
  int res = 0;

#ifdef MORETRACE
  /*  if (TRACE == 6) print_trie(image_ptr, Root3(image_ptr)); */
  if (TRACE > 6) print_trie(image_ptr, Root3(image_ptr));
#endif

  if (Root3(image_ptr) == NULL) {
    Branch_num(image_ptr) = Branch_succ(image_ptr) = 1;
    if (TRACE) printf( "\nEvery atom has a fixed truth value.\n");
    if (TRACE) print_model(image_ptr, stdout);
    /* We must test this if it is not propositional */
    if (Test_star_consistency != NULL) 
      res = (*Test_star_consistency)(image_ptr, dag_ptr);
    else res = 1;
  } else if (Root3(image_ptr) == CLAUSE3(image_ptr) || trie_create_var_table(image_ptr) == UNSAT) {
    Branch_num(image_ptr) = Branch_fail(image_ptr) = 1;
    if (TRACE) 
      printf( "\nAn empty clause is found from the first %ld clauses.\n", Clause_num(image_ptr));
    res = 0;
  } else {
    Branch_num(image_ptr) = 1;
    Branch_fail(image_ptr) = Branch_succ(image_ptr) = 0;
    res = trie2_search2(image_ptr,dag_ptr,Test_star_consistency); 
  }
  return res;
}

/* DO NOT USE THIS!!! */
int trie_strategy0(image_ptr) 
     image_t *image_ptr; 
     /* the least unsigned variable */ 
{ 
  int i;  
  
  for (i = 1; (i <= Max_atom(image_ptr)); i++)  
      if (Value(image_ptr)[i] == DC) return i; 
  return 0; 
} 

/***************************************************/

void pv(image_ptr, n) 
     image_t *image_ptr;
     int n; 
{ 
  printf("Value[%d] = %d", n, Value(image_ptr)[n]); 
}

void p_trie_info (image_ptr) 
     image_t *image_ptr; 
{ 
  if (TRACE) {
    printf( "\nThere are %ld nodes in use and %ld nodes available.\n", 
	    Trie_gets(image_ptr) - Trie_frees(image_ptr), Trie_avails(image_ptr)); 
    printf( "There are %ld calls to get_node and %ld calls to new_node.\n", 
	    Trie_gets(image_ptr), Trie_news(image_ptr)); 
  }
} 

/********************************************************
  Toplevel Code for SATO with backjumping
********************************************************/

/* Modified to handle pure literal */
int trie_create_var_table(image_ptr)
     image_t *image_ptr;
{
  int pos, neg, i;
  struct var2 *el;
  int extra_space = 0;
  if (GRASP) extra_space = EXTRA_SPACE;
  if (Root3(image_ptr) == CLAUSE3(image_ptr)) return UNSAT;
  if (Root3(image_ptr) == NULL) return SAT;

  init_var2_table (image_ptr);
  Clause_num(image_ptr) = visit_trie2(image_ptr, Root3(image_ptr), NULL, 0, 0, 0);
#ifdef MORETRACE
  if (TRACE) printf("There are %ld clauses in the trie (%d are non-Horn).\n", 
		    Clause_num(image_ptr), NH_num(image_ptr));
#endif

  for (i = 1; i <= Max_atom(image_ptr); i++) {
    el = V2(image_ptr)[i];
    pos = el->pos_count;
    neg = el->neg_count;
    el->pos_count = el->neg_count = 0;
    
    /* We don't want the pure literal rule to be enforced 
       here unless PURE_HEUR = 2 */
    
    if (PURE_HEUR == 2) {
      if (Value(image_ptr)[i] == DC) {
	if (pos == 0 || neg == 0) {
	  if (pos == 0) {
	    Inc_param(Image_monitor_ptr(image_ptr), PURE_NUM);
	    trie2_assign_value(image_ptr,i, FF);
	  } else { 
	    Inc_param(Image_monitor_ptr(image_ptr), PURE_NUM);
	    trie2_assign_value(image_ptr,i, TT);
	  }
	  Pure_num(image_ptr)++;
#ifdef MORETRACE
	  print_x_pure(image_ptr);
#endif
	} 
      }
    }
    
    if (Value(image_ptr)[i] == DC) {
      el->pos_extra = el->neg_extra = extra_space;
      el->pos = get_trie2_array(image_ptr, pos+extra_space);
      el->neg = get_trie2_array(image_ptr, neg+extra_space);
    } else {
      level_of(el) = 0;
      if (pos > 0) el->pos = get_trie2_array(image_ptr, pos);
      if (neg > 0) el->neg = get_trie2_array(image_ptr, neg);
    }
  }
    
  trie2_fill_in_clauses(image_ptr, NHtrie(image_ptr));
  /* No separate data structure unless HORN_HEUR is 1 */
  if (HORN_HEUR)
    trie2_fill_in_clauses(image_ptr, CLtrie(image_ptr));
  
  return SAT;
}

void init_var2_table (image_ptr)
     image_t *image_ptr;
{
  /*  static int old_Max_atom; */
  int i;
  struct var2 *el;

  if (V2(image_ptr) != NULL) {
    for (i=1; i <= Old_max_atom(image_ptr); i++)  {
      el = V2(image_ptr)[i];
      free(el->pos);
      free(el->neg);
    }
    free(V2(image_ptr));
  }

  Old_max_atom(image_ptr) = Max_atom(image_ptr);

  /* Modified! Trapping memory allocation with malloc */
  /* Add the newly created block to the tracking list */
  Ablocks_table(image_ptr)[Cur_block(image_ptr)] = 
    (char*) malloc ( sizeof ( struct var2 *) * (1+Max_atom(image_ptr) ));
  V2(image_ptr) = (struct var2 **) Ablocks_table(image_ptr)[Cur_block(image_ptr)++];

#ifndef OPTMIZE
  Memory_count(image_ptr) += ( sizeof ( struct var2 *) * (1+Max_atom(image_ptr) ));

  if (V2(image_ptr) == NULL) {
    fprintf ( stderr, "var_table returns NULL.\n");
    exit(1);
  }
#endif

  for (i=0; i <= Max_atom(image_ptr); i++)  {  
    V2(image_ptr)[i] = el = (struct var2 *) tp_alloc (image_ptr, sizeof ( struct var2 ) );

    /* basic stuff */
    el->key = i;
    el->next = NULL;
    el->pos = el->neg = NULL;
    el->neg_count = el->pos_count = 0;

    /* related to unit-propagations. */
    el->frozen = NULL;                  /* frozen clauses */
    el->pure = 0;                       /* used also in GRASP */

    /* GRASP techniques */
    el->force = NULL;
    el->level = 0;
    el->pos_extra = el->neg_extra = 0;
  }

  /*check_cl(0, NULL, NULL); */
  Trie2_Ucl(image_ptr) = get_trie2_array(image_ptr, MAX_LIST);
  Trie2_Ucl_idx(image_ptr) = 0;
}

struct trie **get_trie2_array (image_ptr, size)
     image_t *image_ptr;
     int size;
{
  struct trie **p;

  /* Modified! Trapping memory allocation with malloc */
  /* Append the newly created block to the tracking list */
  Ablocks_table(image_ptr)[Cur_block(image_ptr)] = 
    (char*) malloc ( sizeof ( struct trie *) * size );
  p = (struct trie **) Ablocks_table(image_ptr)[Cur_block(image_ptr)++]; 
  
#ifndef OPTIMIZE
  if (p == NULL) {
    fprintf ( stderr, "get_trie2_array return NULL.\n");
    exit(1);
  }
#endif
  Memory_count(image_ptr) += sizeof ( struct trie *) * size;

  return p;
}

long visit_trie2 (image_ptr, tr, par, pflag, count, pcount)
     image_t *image_ptr;
     struct trie *tr, *par;
     int count, pcount;
     /* Visit the whole trie.
	When go down, (a) assign the parent; (b) count the numbers
	of literals and positive literals; (d) if a CLAUSE3(image_ptr) is found, 
	create a clause node.
	When go up, return the number of clauses in the trie.
	*/
{
  if (tr == CLAUSE3(image_ptr)) {
    tr = get_trie(image_ptr);
    tr->par = par;
    count_of_clause(tr) = count;
    tr->psign = pcount;
    
    /* HORN */
    if (pcount > 1) {  
#ifdef TRIE_UNREV
      if (NHtrietl(image_ptr) == NULL) {
	tr->bro = NULL;
	NHtrie(image_ptr) = NHtrietl(image_ptr) = tr;
      } else {
	NHtrietl(image_ptr)->bro = tr;
	NHtrietl(image_ptr) = tr;
      }
#else
      tr->bro = NHtrie(image_ptr);
      NHtrie(image_ptr) = tr;
#endif
      NH_num(image_ptr)++;
    } else { 
      /* No separate data structure unless HORN_HEUR is 1 */
      if (HORN_HEUR) {
	tr->bro = CLtrie(image_ptr); 
	CLtrie(image_ptr) = tr; 
      } else {
#ifdef TRIE_UNREV
	if (NHtrietl(image_ptr) == NULL) {
	  tr->bro = NULL;
	  NHtrie(image_ptr) = NHtrietl(image_ptr) = tr;
	} else {
	  NHtrietl(image_ptr)->bro = tr;
	  NHtrietl(image_ptr) = tr;
	}
#else
	tr->bro = NHtrie(image_ptr);
	NHtrie(image_ptr) = tr;
#endif
      }
    } 

    return 1;

  } else {

    int key = tr->key;
    long x=0, y=0, z=0;

    if (tr->pos != NULL) {
      y = visit_trie2(image_ptr, tr->pos, tr, 1, 1+count, 1+pcount);
      V2(image_ptr)[key]->pos_count += y;
    }

    if (tr->neg != NULL) {
      z = visit_trie2(image_ptr, tr->neg, tr, 0, 1+count, pcount);
      V2(image_ptr)[key]->neg_count += z;
    }


    if (tr->bro != NULL) 
      x = visit_trie2(image_ptr, tr->bro, par, pflag, count, pcount);

    tr->par = par;
    tr->psign = pflag;

    return (x + y + z);
  }
}

void trie2_fill_in_clauses (image_ptr, cl)
     image_t *image_ptr;
     struct trie *cl;
{
  struct trie *tr, *son;
  struct var2 *el;

  while (cl != NULL) {

    tr = cl->par;
    el = V2(image_ptr)[tr->key];
    if (HAS_POS_CL(image_ptr,tr)) {
      el->pos[el->pos_count++] = cl;
    } else {
      el->neg[el->neg_count++] = cl;
    }

    son = tr;
    tr = tr->par;
    while (tr != NULL) {
      el = V2(image_ptr)[tr->key];
      if (son->psign) {
	el->pos[el->pos_count++] = cl;
      } else {
	el->neg[el->neg_count++] = cl;
      }
      son = tr;
      tr = tr->par;
    }

    cl = cl->bro;
  }
}

void var_clauses(image_ptr, i, f )
     image_t *image_ptr;
     int i;
{
  int j, l;

  if (f % 2 && (l = V2(image_ptr)[i]->pos_count) > 0) {
    printf("here are the positive clauses for var %d.\n", i);
    for (j=0; j<l; j++) 
      print_clause_from_leaf(image_ptr, V2(image_ptr)[i]->pos[j]);
  }

  if (f > 1 && (l = V2(image_ptr)[i]->neg_count) > 0) {
    printf("here are the negative clauses for var %d.\n", i);
    for (j=0; j<l; j++) 
      print_clause_from_leaf(image_ptr, V2(image_ptr)[i]->neg[j]);
  }
}

void print_clause_from_leaf (image_ptr, tr)
     image_t *image_ptr;
     struct trie *tr;
{
  struct trie *son;

  printf("%s c=%d ( ", 
	 (active_clause(tr))? " " : "m", count_of_clause(tr));

  tr = tr->par;
  printf("%s%d[%d] ",  HAS_POS_CL(image_ptr,tr)? "" : "-", tr->key, Value(image_ptr)[tr->key]);

  son = tr;
  tr = tr->par;
  while (tr != NULL) {
    printf("%s%d[%d] ",  (son->psign)? "" : "-", tr->key, Value(image_ptr)[tr->key]);
    son = tr; 
    tr = tr->par;
  }
  printf(")\n");
}

/* Modified to work with consistency testing */
/* Modified to work with modal dynamic backtracking */
/* Modified to handle timeout */
int trie2_search2 (image_ptr,dag_ptr,Test_star_consistency)
     image_t         *image_ptr;
     dag_t           *dag_ptr;
     Cons_func_ptr_t Test_star_consistency;
{
  struct var2 *it;
  int i;    
  
  /* Unit propagations: unit clauses are collected 
     into Trie2_Ucl(image_ptr) */
  if (trie2_handle_known_values(image_ptr) == UNSAT) return 0;

  Nonunit_cls(image_ptr) = NHtrie(image_ptr);
  i = trie2_next_key(image_ptr,dag_ptr,Test_star_consistency);
  
  /* the major loop goes here. */
  while (!Stop(image_ptr) && i > 0) {
    Top_var2(image_ptr) = it = V2(image_ptr)[i];

    /* Optional: modal backtracking */
    /* Realligning the pointer to the checked stack */
    if (JUMPING && (Stack_idx(image_ptr) <= Last_stack_idx(image_ptr)))
      Last_stack_idx(image_ptr) = Stack_idx(image_ptr) - 1;

    if (Value(image_ptr)[i] == TT) {
      if (trie2_propagate_true(image_ptr, it,0) != UNSAT)
	/* Optional: modal backtracking */
	/* Pruning the propositional search tree */
	if (JUMPING && (Jump_point(image_ptr) != MAX_LIST)) {
	  if (Backup_idx(image_ptr) > Jump_point(image_ptr))
	    i = trie2_prev_key(image_ptr, 1);
	  else {
	    Jump_point(image_ptr) = MAX_LIST;
	    i = trie2_next_key(image_ptr,dag_ptr,Test_star_consistency);
	  }
	} else 
	  i = trie2_next_key(image_ptr,dag_ptr,Test_star_consistency);
      else {
	i = trie2_prev_key(image_ptr, 0);
      }
    } else { /* Value[i] == FF */
      if (trie2_propagate_false(image_ptr, it,0) != UNSAT) {
	/* Optional: modal backtracking */
	/* Pruning the propositional search tree */
	if (JUMPING && (Jump_point(image_ptr) != MAX_LIST)) {
	  if (Backup_idx(image_ptr) > Jump_point(image_ptr))
	    i = trie2_prev_key(image_ptr, 1);
	  else {
	    Jump_point(image_ptr) = MAX_LIST;
	    i = trie2_next_key(image_ptr,dag_ptr,Test_star_consistency);
	  }
	} else 
	  i = trie2_next_key(image_ptr,dag_ptr,Test_star_consistency);
      } else {
	i = trie2_prev_key(image_ptr, 0);
      }
    }

    /* Timeout checking */
    /*     if (TIMEOUT &&  */
    /*  	(Lap_time(Image_monitor_ptr(image_ptr), DSAT) > (TIMEOUT * 1000))) { */
    /*        Stop(image_ptr) = 1; */
    /*        TIMEOUT = -1; */
    /*      } */
    
  } /* while */

  return ((Branch_succ(image_ptr) > 0)? 1 : (Stop(image_ptr))? 2 : 0);
}

/* Modified to work with consistency checking */
/* Modified to work with modal dynamic backtracking */
int trie2_next_key (image_ptr,dag_ptr,Test_star_consistency)
     image_t         *image_ptr;
     dag_t           *dag_ptr;
     Cons_func_ptr_t Test_star_consistency;
{
  int i;

  if (trie2_handle_unit_clauses(image_ptr, 1) == UNSAT)
    return trie2_prev_key(image_ptr, 1);

  UIP(image_ptr) = HAVE_UIP;
  /* Modified! Now this is a macro */
  trie2_best_key(image_ptr, dag_ptr);

  /* Optional: modal backtracking */
  if (EARLY_JUMPING && i) {
    /* Monitor */
    Inc_param(Image_monitor_ptr(image_ptr), EP_CALLS);
    (*Test_star_consistency)(image_ptr, dag_ptr);
    /* Monitor */
    if (Jump_point(image_ptr) != MAX_LIST)
      Inc_param(Image_monitor_ptr(image_ptr), EPFAIL_NUM);
  }

  if (i == 0) return handle_succ_end(image_ptr,dag_ptr,Test_star_consistency);

  /* Monitor */
  Inc_param(Image_monitor_ptr(image_ptr), SPLIT_NUM); 
  if ((i >= SPREAD(Lpa(dag_ptr))) && (i <= SPREAD(Lma(dag_ptr))))
    Inc_param(Image_monitor_ptr(image_ptr), SPLIT_MOD_NUM); 
  else if (i > SPREAD(Lma(dag_ptr)))
    Inc_param(Image_monitor_ptr(image_ptr), SPLIT_DEP_NUM); 

  Branch_open(image_ptr)++;
  Branch_num(image_ptr)++;
  
  if (Backup_idx(image_ptr) >= MAX_LIST) {
    fprintf ( stderr, "MAX_LIST(%d) is too small in trie2_next_key().\n", 
	      MAX_LIST);
    Stop(image_ptr) = 1;
  }

  Backup(image_ptr)[Backup_idx(image_ptr)++] = i;
  /* STACK */
  if (TRACE == 4)
    printf("next_key: putting %d to stack index %d\n", i, Stack_idx(image_ptr));
  if (V2(image_ptr)[i]->pos_count == 0)
    Stack(image_ptr)[Stack_idx(image_ptr)].f = SPN;
  else if (V2(image_ptr)[i]->neg_count == 0)
    Stack(image_ptr)[Stack_idx(image_ptr)].f = SPP;
  else 
    Stack(image_ptr)[Stack_idx(image_ptr)].f = SP;
  Stack(image_ptr)[Stack_idx(image_ptr)++].v = i;
  level_of(V2(image_ptr)[i]) = Branch_open(image_ptr);
  mark_of(V2(image_ptr)[i]) = NULL;

#ifdef MORETRACE
  print_let_x_have(image_ptr);
#endif

  return i;
}

int trie2_prev_key (image_ptr, clean)
     image_t *image_ptr;
     int clean;
{
  int i;
  
  OLDV(image_ptr) = Trie2_Ucl_idx(image_ptr) = Tdc_idx(image_ptr) = 0;
  Tdc_idx_end(image_ptr) = MAX_ATOM;
  UIP(image_ptr) = 0;

  while (Backup_idx(image_ptr)-- > 0) {
    if ((i = Backup(image_ptr)[Backup_idx(image_ptr)]) < 0) {
      int j;
      
      i = -i; 
      Conflict_cl(image_ptr) = NULL;
      j = Conflict_cl_level(image_ptr);

      if (clean) trie2_clean_dependents(image_ptr, V2(image_ptr)[i], clean-1);
#ifdef MORETRACE
      else print_up_to_x(image_ptr);
#endif
      Value(image_ptr)[i] = DC;
      clean = 2;

      if (GRASP) {
	if (j < Branch_open(image_ptr)) { 
	  int good = 1;
	  Jump_num(image_ptr)++;

#ifdef MORETRACE
	  if (TRACE > 2)
	    printf("    Backjumping from level %d to %d\n", Branch_open(image_ptr), j);
#endif

	  while (good && Backup_idx(image_ptr)) {
	    if ((i = Backup(image_ptr)[--Backup_idx(image_ptr)]) < 0) {
	      trie2_clean_dependents(image_ptr, V2(image_ptr)[-i], clean);
	    } else if (level_of(V2(image_ptr)[i]) > j) {
	      Branch_num(image_ptr)--;
	      Branch_open(image_ptr)--;
	      trie2_clean_dependents(image_ptr, V2(image_ptr)[i], clean);
	    } else { 
	      Backup_idx(image_ptr)++;
	      good = 0;
	    }
	  }
	}
      }
    } else {
      int NEXT_VALUE = NEG(Value(image_ptr)[i]);

      Branch_open(image_ptr)--;

      if (clean) trie2_clean_dependents(image_ptr, V2(image_ptr)[i], clean-1);
#ifdef MORETRACE
      else print_up_to_x(image_ptr);
#endif

      Backup(image_ptr)[Backup_idx(image_ptr)++] = -i;
      /* STACK */
      if (TRACE == 4)
	printf("prev_key: putting %d to stack index %d\n", i, Stack_idx(image_ptr));
      if (V2(image_ptr)[i]->pos_count == 0)
	Stack(image_ptr)[Stack_idx(image_ptr)].f = SPN;
      else if (V2(image_ptr)[i]->neg_count == 0)
	Stack(image_ptr)[Stack_idx(image_ptr)].f = SPP;
      else 
	Stack(image_ptr)[Stack_idx(image_ptr)].f = SP;

      Stack(image_ptr)[Stack_idx(image_ptr)++].v = -i;
      Value(image_ptr)[i] = NEXT_VALUE;
      
      if (GRASP) {
	if (Conflict_cl(image_ptr) == NULL) {
	  mark_of(V2(image_ptr)[i]) = NULL;
	} else {
	  mark_of(V2(image_ptr)[i]) = Conflict_cl(image_ptr);
	  Conflict_cl(image_ptr) = NULL;
	}
	if (Conflict_cl_level(image_ptr) > Branch_open(image_ptr)) Conflict_cl_level(image_ptr) = Branch_open(image_ptr);
	level_of(V2(image_ptr)[i]) = Conflict_cl_level(image_ptr);
      }

#ifdef MORETRACE
      if (GRASP && (TRACE > 8 || TRACE == 3 || TRACE == 4))
	  printf("  [%d]", level_of(V2(image_ptr)[i]));
      print_now_let_x_have(image_ptr);
#endif
      return i;
    }
  }
  return Stop(image_ptr) = 0;
}

int trie2_mom (image_ptr, dag_ptr, total, keys)
     image_t *image_ptr;
     dag_t *dag_ptr;
     int total, keys[];
{
  int s, best_key, best_sign, sign, new, max_weight;
  best_sign = best_key = max_weight = 0;

#ifdef MORETRACE
  if (total && TRACE >= 4) 
    printf("There are %d MOM candidates\n", total);
#endif


  for (s = 0; s < total; s++) {
    new = trie2_compute_mom(image_ptr, dag_ptr, keys[s], &sign);
    if (new > max_weight) {
      best_key = keys[s];
      best_sign = sign;
      max_weight = new;
    }
  }

#ifdef MORETRACE
  if (total && TRACE >= 4) 
    printf("The winner is %d\n", best_key);
#endif

  Value(image_ptr)[best_key] = best_sign;
  return best_key;
}


/* Modified to handle pure literal */
/* Modified to get different heuristics */
int trie2_compute_mom (image_ptr, dag_ptr, i, sign)
     image_t *image_ptr;
     dag_t *dag_ptr;
     int i, *sign;
{
  int j, k, num_cls, pos_count, neg_count;
  int pos_count2, pos_count3;
  int neg_count2, neg_count3;
  struct trie *cl, **cls;

  pos_count = neg_count = 1;
  neg_count2 = neg_count3 = 1;
  pos_count2 = pos_count3 = 1;

  
  j = 0;
  cls = V2(image_ptr)[i]->neg;
  num_cls = V2(image_ptr)[i]->neg_count;
  
  for (k = 0; k < num_cls; k++) if (active_clause((cl=cls[k]))) { 
    j = 1; 
    /* Modified: if BIAS>10 neglects clause lenght */
    if (BIAS == 21) {
      if (count_of_clause(cl) == 2) { 
	neg_count2++;
      } 
      if (count_of_clause(cl) == 3) { 
	neg_count3++;
      } 
    } else if (BIAS > 10) 
      neg_count++;
    else
      if (count_of_clause(cl) == 2) { 
	neg_count++;
      } 
  }
  
  if (PURE_HEUR) {
    /* We don't want pure literal unless PURE_HEUR != 0 */
    if ((j == 0) &&
	((PURE_HEUR==2) || (i > SPREAD(Lma(dag_ptr))))) {
      trie2_pure_delete(image_ptr, i, TT);
      return -1;
    }
  }    
  
  j = 0;
  cls = V2(image_ptr)[i]->pos;
  num_cls = V2(image_ptr)[i]->pos_count;
  
  for (k = 0; k < num_cls; k++) if (active_clause((cl=cls[k]))) { 
    j = 1; 
    /* Modified: if BIAS>10 neglects clause lenght */
    if (BIAS == 21) {
      if (count_of_clause(cl) == 2) { 
	pos_count2++;
      } 
      if (count_of_clause(cl) == 3) { 
	pos_count3++;
      } 
    } else if (BIAS > 10) 
      pos_count++;
    else
      if (count_of_clause(cl) == 2) { 
	pos_count++;
      } 
  }
  
  /* We don't want pure literal unless PURE_HEUR = 1 */
  if (PURE_HEUR) {
    if ((j == 0) &&
	((PURE_HEUR==2) || (i > SPREAD(Lma(dag_ptr))))) {
      trie2_pure_delete(image_ptr, i, FF);
      return -1;
    }
  }
    
#ifdef MORETRACE
  if (TRACE > 4) 
    printf("   key %d:  neg = %d, pos = %d\n", i, neg_count, pos_count);
#endif

  /* Modified! Now this is a macro since different biases can be given */
  trie2_choose_sign(image_ptr);

  /* Modified! Now this is a macro since different weights can be chosen */
  return trie2_choose_weight(image_ptr);

}

/* Modified to avoid splitting on dependant variables */
/* whenever SPLIT_DEP = 0 */
int trie2_strategy1 (image_ptr, dag_ptr)
     image_t *image_ptr;
     dag_t   *dag_ptr;
/* apply MOM to all active variables */
{
  int i, total, keys[MAX_ATOM], start;

  total = 0;
  if ((!SPLIT_DEP) && (Max_atom(image_ptr) > Max_indep(image_ptr))) {
    /* We really need to discriminate */
    for (i = 1; i <= Max_indep(image_ptr); i++)
      if (Value(image_ptr)[i] == DC) keys[total++] = i;
    start = Max_indep(image_ptr) + 1;
  } else {
    /* Every variable is independent or we want to split on any variable */
    start = 1;
  }
  if (total == 0) 
    /* Handle a tail of dependent variables or every variable */
    for (i = start; i <= Max_atom(image_ptr); i++)
      if (Value(image_ptr)[i] == DC) keys[total++] = i;

  return (trie2_mom(image_ptr, dag_ptr, total, keys));
}

/* Modified to avoid splitting on dependant variables */
/* whenever SPLIT_DEP = 0 */
int trie2_strategy2(image_ptr, dag_ptr)
     image_t *image_ptr;
     dag_t *dag_ptr;
     /* apply MOM to all active variables appearing
	in shortest non-Horn clauses */
{
  int i, x, y, min_len, total, keys[MAGIC]; /* Modified!!! */
  struct trie *cl = NHtrie(image_ptr);
  struct trie *cls[MAGIC];                  /* Modified!!! */
  min_len = MAX_ATOM;
  total = 0;
  
  /* at first, collect all the shortnest clauses */
  while (cl != NULL) {
    if (active_clause(cl)) {
      if (count_of_clause(cl) < min_len) {
	min_len = count_of_clause(cl);
	cls[0] = cl;
	total = 1;
      } else if (total < MAGIC && count_of_clause(cl) == min_len) {
	cls[total++] = cl;
      }
    }
    cl = cl->bro;
  }
  
  if (total == 0) return 0; 

  /* then, colect active keys in the shortest clauses */
  y = 0;
  
  if ((!SPLIT_DEP) && (Max_atom(image_ptr) > Max_indep(image_ptr))) {
    /* Try to collect independent variables */
    i = total;
    while  (i && y < MAGIC) {
      cl = cls[--i];
      cl = cl->par;
      while (cl != NULL && y < MAGIC) {
	x = cl->key;
	if (Value(image_ptr)[x] == DC && 
	    V2(image_ptr)[x]->pure != MAX_ATOM &&
	    x <= Max_indep(image_ptr)) {
	  V2(image_ptr)[x]->pure = MAX_ATOM;
	  keys[y++] = x;
	}
	cl = cl->par;
      }
    }
  } 

  if (y == 0) {
    /* No variables were collected */
    i = total; 
    while  (i && y < MAGIC) {
      cl = cls[--i];
      cl = cl->par;
      while (cl != NULL && y < MAGIC) {
	x = cl->key;
	if (Value(image_ptr)[x] == DC && 
	    V2(image_ptr)[x]->pure != MAX_ATOM) {
	  V2(image_ptr)[x]->pure = MAX_ATOM;
	  keys[y++] = x;
	}
	cl = cl->par;
      }
    }
  }

  for (i = 0; i < y; i++) V2(image_ptr)[keys[i]]->pure = 0;
  i = trie2_mom(image_ptr, dag_ptr, y, keys);
  if (i == 0)  /* purecheck blocked the keys */
    return (trie2_strategy2(image_ptr,dag_ptr));
  else 
    return i;
}

/* Modified to avoid splitting on dependant variables */
/* whenever SPLIT_DEP = 0 */
int trie2_strategy3 (image_ptr)
     image_t *image_ptr;
     /* choose the min variable in the first shortest clause */
{
  int i;
  int min_clause_count = MAX_ATOM;
  struct trie *min_clause = NULL;
  struct trie *cl = NHtrie(image_ptr);

  while (cl != NULL) {
    if (active_clause(cl)) {
      i = count_of_clause(cl);
      /* We don't want relaxation to horn clauses unless HORN_HEUR = 1 */
      if (HORN_HEUR) {
	if (i == cl->psign) 
	  if (min_clause_count > i) {
	    min_clause_count = i;
	    min_clause = cl;
	    if (i <= 2) cl = CLAUSE3(image_ptr); 
	  }
      } else {
	if (min_clause_count > i) {
	    min_clause_count = i;
	    min_clause = cl;
	    if (i <= 2) cl = CLAUSE3(image_ptr); 
	  }
      }
    }
    cl = cl->bro;
  }
  
  if (min_clause == NULL) return 0;

#ifdef MORETRACE
  if (TRACE == 4) print_clause_from_leaf(min_clause);
#endif

  i = 0;

  if ((!SPLIT_DEP) && (Max_atom(image_ptr) > Max_indep(image_ptr))) {
    /* Try to collect independent variables */
    cl = min_clause->par;
    while (cl != NULL) {
      if (Value(image_ptr)[cl->key] == DC)  i = cl->key;
      cl = cl->par;
    }
  }

  if (i == 0) {
    /* No variables were collected */
    cl = min_clause->par;
    while (cl != NULL) {
      if (Value(image_ptr)[cl->key] == DC)  i = cl->key;
      cl = cl->par;
    }
  }

  Value(image_ptr)[i] = CHOICE1;
  return i;
}

int trie2_strategy4 (image_ptr)
     image_t *image_ptr;     
  /* choose a variable in a shortest clause;
     using the occurrence as the second criterion */
{
  int i, min_idx, saved_min_idx;
  int min_clause_count = MAX_ATOM;
  struct trie *min_clauses[50], *no;
  struct trie *cl = NHtrie(image_ptr);

  for (i = 1; i <= Max_atom(image_ptr); i++) V2(image_ptr)[i]->pos2 = 0;
  min_idx = 0;

  while (cl != NULL) {
    if (active_clause(cl)) {

      if (min_clause_count > i) {
	min_clause_count = i;
	min_idx = 1;
	min_clauses[0] = cl;
      } else if (min_idx < 50 && min_clause_count == i) {
	min_clauses[min_idx++] = cl;
      }

      no = cl->par;
      while (no != NULL) {
	V2(image_ptr)[no->key]->pos2++;
	no = no->par;
      }
    }
    cl = cl->bro;
  }

  if (min_clause_count == MAX_ATOM) return 0;

  min_clause_count = 0;
  saved_min_idx = min_idx;

  if ((!SPLIT_DEP) && (Max_atom(image_ptr) > Max_indep(image_ptr))) {
    /* Try to collect independent variables */
    while (min_idx) {
      cl = min_clauses[--min_idx]->par;
      while (cl != NULL) {
	if (Value(image_ptr)[cl->key] == DC && 
	    min_clause_count <  V2(image_ptr)[cl->key]->pos2 &&
	    cl->key <= Max_indep(image_ptr)) {
	  min_clause_count = V2(image_ptr)[cl->key]->pos2;
	  i = cl->key;
	  /*printf("key = %d, occ = %d\n", i, min_clause_count); */
	}
	cl = cl->par;
      }
    }
  }

  if (min_clause_count == 0) {
    min_idx = saved_min_idx;
    while (min_idx) {
      cl = min_clauses[--min_idx]->par;
      while (cl != NULL) {
	if (Value(image_ptr)[cl->key] == DC && 
	    min_clause_count <  V2(image_ptr)[cl->key]->pos2) {
	  min_clause_count = V2(image_ptr)[cl->key]->pos2;
	  i = cl->key;
	  /*printf("key = %d, occ = %d\n", i, min_clause_count); */
	}
	cl = cl->par;
      }
    }
  }

  Value(image_ptr)[i] = CHOICE1;
  return i;
}

/* Modified to avoid splitting on dependant variables */
/* whenever SPLIT_DEP = 0 */
int trie2_strategy5 (image_ptr)
     image_t *image_ptr;     
  /* choose a variable with the highest occurrence */
{
  int i, min_idx, min_key, start;
  struct trie *no;
  struct trie *cl = NHtrie(image_ptr);

  for (i = 1; i <= Max_atom(image_ptr); i++) V2(image_ptr)[i]->pos2 = 0;

  while (cl != NULL) {
    if (active_clause(cl)) {
      no = cl->par;
      while (no != NULL) {
	V2(image_ptr)[no->key]->pos2++;
	no = no->par;
      }
    }
    cl = cl->bro;
  }
  
  min_key = min_idx = 0;
  if ((!SPLIT_DEP) && (Max_atom(image_ptr) > Max_indep(image_ptr))) {
    /* We really need to discriminate */
    for (i = 1; i <= Max_indep(image_ptr); i++) 
      if (Value(image_ptr)[i] == DC && V2(image_ptr)[i]->pos2 > min_idx) {
	min_idx = V2(image_ptr)[i]->pos2;
	min_key = i;
      }
    start = Max_indep(image_ptr) + 1;
  } else {
    /* Every variable is independent or we want to split on any variable */
    start = 1;
  }
  if (min_key == 0)
    /* Handle a tail of dependent variables or every variable */
    for (i = start; i <= Max_atom(image_ptr); i++) 
      if (Value(image_ptr)[i] == DC && V2(image_ptr)[i]->pos2 > min_idx) {
	min_idx = V2(image_ptr)[i]->pos2;
	min_key = i;
      }

  Value(image_ptr)[min_key] = CHOICE1;
  return min_key;
}

/* Modified to avoid splitting on dependant variables */
/* whenever SPLIT_DEP = 0 */
int trie2_strategy6 (image_ptr)
     image_t *image_ptr;     
  /* choose a variable with the highest occurrence */
{
  int i, min_wei, min_key, pos_wei, start;
  struct trie *no;
  struct trie *cl = NHtrie(image_ptr);

  for (i = 1; i <= Max_atom(image_ptr); i++) V2(image_ptr)[i]->pos2 = 0;
  min_wei = 0;

  while (cl != NULL) {
    if (active_clause(cl)) {
      no = cl->par;
      while (no != NULL) {
	V2(image_ptr)[no->key]->pos2 += 1;
	no = no->par;
      }
    }
    cl = cl->bro;
  }
  
  min_key = min_wei = 0;
  if ((!SPLIT_DEP) && (Max_atom(image_ptr) > Max_indep(image_ptr))) {
    /* We really need to discriminate */
    for (i = 1; i <= Max_indep(image_ptr); i++) 
      if (Value(image_ptr)[i] == DC && V2(image_ptr)[i]->pos2 > min_wei) {
	min_wei = V2(image_ptr)[i]->pos2;
	min_key = i;
      }
    start = Max_indep(image_ptr) + 1;
  } else {
    /* Every variable is independent or we want to split on any variable */
    start = 1;
  }
  if (min_key == 0) 
    /* Handle a tail of dependent variables or every variable */
    for (i = start; i <= Max_atom(image_ptr); i++) 
      if (Value(image_ptr)[i] == DC && V2(image_ptr)[i]->pos2 > min_wei) {
	min_wei = V2(image_ptr)[i]->pos2;
	min_key = i;
      }

  if (min_key == 0) return 0;

  pos_wei = 0;
  for (i = V2(image_ptr)[min_key]->pos_count-1; i >= 0; i--) 
    if (active_clause(V2(image_ptr)[min_key]->pos[i])) pos_wei++;
  min_wei -= pos_wei;
  Value(image_ptr)[min_key] = (min_wei >= pos_wei)? TT : FF; 
/*    printf("choose %d, [N#=%d, P#=%d]\n", min_key, min_wei, pos_wei); */

  return min_key;
}

void trie2_pure_delete (image_ptr, i, sign)
     image_t *image_ptr;     
     int i, sign;
{
  int j, num_cls;
  struct trie **cls, *frozens, *cl;
  struct var2 *el;

  Value(image_ptr)[i] = sign;
  el = V2(image_ptr)[i];
  el->level = PURECHECK;
  Pure_num(image_ptr)++;
  /* Monitor */
  Inc_param(Image_monitor_ptr(image_ptr), PURE_NUM);

  /* STACK */
  Stack(image_ptr)[Stack_idx(image_ptr)].f = PP;
  Stack(image_ptr)[Stack_idx(image_ptr)++].v = i;

#ifdef MORETRACE
  print_x_pure(image_ptr);
#endif

  el->next = Top_var2(image_ptr)->next;
  Top_var2(image_ptr)->next = el;

  if (sign == TT) {
    cls = el->pos;
    num_cls = el->pos_count;
  } else {
    cls = el->neg;
    num_cls = el->neg_count;
  }

  frozens = CLAUSE3(image_ptr);
  for (j = 0; j < num_cls; j++) if (active_clause((cl=cls[j]))) {
    frozen_lin(cl) = frozens;
    frozens = cl;
  }
  frozen_cls(el) = frozens;
}

void trie2_pure_check (image_ptr)
     image_t *image_ptr;     
     /* implementing pure deletion */
{
  int i, j, k, num_cls;
  struct trie **cls;
  struct var2 *el;

  for (i = 1; i <= Max_atom(image_ptr); i++) if (Value(image_ptr)[i] == DC) {

    j = 0;
    el = V2(image_ptr)[i];
    cls = el->neg;
    num_cls = el->neg_count;
    for (k = 0; k < num_cls; k++) 
      if (active_clause(cls[k])) { k = num_cls; j = 1; }

    if (j == 0) trie2_pure_delete(image_ptr, i, TT);
    else {

      j = 0;
      cls = el->pos;
      num_cls = el->pos_count;
      for (k = 0; k < num_cls; k++) 
	if (active_clause(cls[k])) { k = num_cls; j = 1; }

      if (j == 0) trie2_pure_delete(image_ptr, i, FF);
    }
  }
}

int trie2_propagate_true (image_ptr, el, save)
     image_t *image_ptr;     
     struct var2 *el;
     int save;
{
  int key = el->key;
  int i, j, count, num_cls;
  struct trie **cls, *cl;

  /* decrement the count of clauses in which key appears negatively. */
  cls = el->neg;
  num_cls = el->neg_count;

  for (i = 0; i < num_cls; i++) {
    cl = cls[i];
    if (active_clause(cl)) {
      count = --count_of_clause(cl);
      if (count == 0) { 	
	/* restore what is done so far and then backtrack */
	count_of_clause(cl)++;
	for (j = 0; j < i; j++) {
	  if (active_clause(cls[j])) {
	    count_of_clause(cls[j])++;
	  }
	}
	if (save && GRASP) trie2_record_conflict(image_ptr, cl);
	return handle_fail_end(image_ptr);
      } else if (count == 1) {
	/* store unit clauses in an array */
	Trie2_Ucl(image_ptr)[Trie2_Ucl_idx(image_ptr)++] = cl;
      }
    }
  }

  /* remember the key for freezing its positive clauses */
  Tdc(image_ptr)[--Tdc_idx_end(image_ptr)] = key;

  /* remember the vars for backtracking */
  if (save) {
    el->next = Top_var2(image_ptr)->next;
    Top_var2(image_ptr)->next = el;
  }
  return SAT;
}

int trie2_propagate_false (image_ptr, el, save)
     image_t *image_ptr;     
     struct var2 *el;
     int save;
{
  int key = el->key;
  int i, j, count, num_cls;
  struct trie **cls, *cl;

  /* decrement the count of clauses in which key appears positively. */
  cls = el->pos;
  num_cls = el->pos_count;

  for (i = 0; i < num_cls; i++) {
    cl = cls[i];
    if (active_clause(cl)) {
      count = --count_of_clause(cl);
      if (count == 0) { 	
	/* restore what is done so far and then backtrack */
	count_of_clause(cl)++;
	for (j = 0; j < i; j++) 
	  if (active_clause(cls[j])) {
	    count_of_clause(cls[j])++;
	    cls[j]->psign++;
	  }
	if (save && GRASP) trie2_record_conflict(image_ptr, cl);
	return handle_fail_end(image_ptr);
      } else if (count == 1) {
	/* store unit clauses in an array */
	Trie2_Ucl(image_ptr)[Trie2_Ucl_idx(image_ptr)++] = cl;
      }
      --cl->psign;
    }
  }

  /* remember the key for freezing its negative clauses */
  Tdc(image_ptr)[--Tdc_idx_end(image_ptr)] = key;
    
  /* remember the vars for backtracking */
  if (save) {
    el->next = Top_var2(image_ptr)->next;
    Top_var2(image_ptr)->next = el;
  }
  return SAT;
}

void trie2_clean_dependents (image_ptr, act, defreeze)
     image_t *image_ptr;     
     struct var2 *act; int defreeze;
{
  struct var2 *it, *next;
  struct trie *cl, *cl2;
  
  /* at first, defreeze the clauses */
  if (defreeze) {
    it = act;
    while (it != NULL) {
      cl = frozen_cls(it);
      frozen_cls(it) = NULL;
      while (cl != CLAUSE3(image_ptr)) {
	cl2 = frozen_lin(cl);
	frozen_lin(cl) = NULL;
	cl = cl2;
      }
      it = it->next;
    }
  }

  /* next, increase the counters */
  it = act->next;
  while (it != NULL) {
    trie2_clean_one_var(image_ptr, it);
    next = it->next;
    it->next = NULL;
    it = next;
  }
  trie2_clean_one_var(image_ptr, act);
  act->next = NULL;

  if (Old_cls(image_ptr) != NULL) {
    cl = NHtrie(image_ptr);
    while (cl != Old_cls(image_ptr)) {
      trie2_adjust_counts(image_ptr, cl);
      cl = cl->bro;
    }
    Old_cls(image_ptr) = NULL;
  }
}

void trie2_clean_one_var (image_ptr, it)
     image_t *image_ptr;     
     struct var2 *it; 
{
  int i, j, sign, num_cls;
  struct trie **cls, *cl;

  i = it->key;

#ifdef MORETRACE
  print_up_to_x(image_ptr);
#endif

  sign = Value(image_ptr)[i];

  if (it->level == PURECHECK) {
    it->level = 0;
  } else if (sign) {  
    /* increment the counter of clauses */
    cls = it->neg;
    num_cls = it->neg_count;
    for (j = 0; j < num_cls; j++) 
      if (active_clause((cl=cls[j]))) {
	count_of_clause(cl)++;
      }
  } else {
    cls = it->pos;
    num_cls = it->pos_count;
    for (j = 0; j < num_cls; j++) 
      if (active_clause((cl=cls[j]))) {
	count_of_clause(cl)++;
	cl->psign++;
      }
  }

  Value(image_ptr)[i] = DC;
  /* STACK */
  --Stack_idx(image_ptr); 
  if (TRACE == 4)
    printf("clean_one_var: decrementing stack index to %d\n", Stack_idx(image_ptr));
}

int trie2_handle_known_values (image_ptr)
     image_t *image_ptr;     
     /* search through Clause and collect all the unit clauses 
	into Trie2_Ucl(image_ptr). */
{
  if (Tdc_idx(image_ptr) > MAX_ATOM) {
    fprintf ( stderr, "Tdc_idx (%d) > MAX_ATOM (%d).\n", Tdc_idx(image_ptr), MAX_ATOM);
    exit(1);
  }

  Tdc_idx_end(image_ptr) = MAX_ATOM;
  Top_var2(image_ptr) = V2(image_ptr)[0];
  while (Tdc_idx(image_ptr)--) {
    if (trie2_propagate(image_ptr, V2(image_ptr)[Tdc(image_ptr)[Tdc_idx(image_ptr)]], Value(image_ptr)[Tdc(image_ptr)[Tdc_idx(image_ptr)]], 0) == UNSAT) 
      return UNSAT;
  }
  Tdc_idx(image_ptr) = 0;

  return (trie2_handle_unit_clauses(image_ptr, 0));
}

void trie2_freeze_clauses(image_ptr)
     image_t *image_ptr;     
{
  int i, j, key, num_cls;
  struct var2 *el;
  struct trie **cls, *frozens, *cl;

  if (Tdc_idx_end(image_ptr) < 0) {
    fprintf ( stderr, "Tdc is overflow (Tdc_idx_end(image_ptr) = %d).\n", Tdc_idx_end(image_ptr));
    exit(1);
  }

  /* freeze clauses in which key appears as its value. */
  for (i = Tdc_idx_end(image_ptr); i < MAX_ATOM; i++) {
    el = V2(image_ptr)[Tdc(image_ptr)[i]];
    key = el->key;
    if (Value(image_ptr)[key] == TT) {
      cls = el->pos;
      num_cls = el->pos_count;
    } else {
      cls = el->neg;
      num_cls = el->neg_count;
    }

    frozens = CLAUSE3(image_ptr);
    for (j = 0; j < num_cls; j++) if (active_clause((cl=cls[j]))) {
      frozen_lin(cl) = frozens;
      frozens = cl;
    }
    frozen_cls(el) = frozens;
  }
  Tdc_idx_end(image_ptr) = MAX_ATOM;
}

int trie2_handle_unit_clauses (image_ptr, save)
     image_t *image_ptr;     
     int save;
     /* handle each unit clause one by one ... */
{
  int i;
  struct trie *cl, *tr;
  
  /* At first, collect unit clauses from new clauses */
  if (Nonunit_cls(image_ptr) != NHtrie(image_ptr)) {
    cl = NHtrie(image_ptr); i = 0;
    while (cl != Nonunit_cls(image_ptr)) {
      if (count_of_clause(cl) < 2) {
	i++;
	if (active_clause(cl)) {
	  /*print_clause_from_leaf(cl);*/
	  Trie2_Ucl(image_ptr)[Trie2_Ucl_idx(image_ptr)++] = cl;
	}
      }
      cl = cl->bro;
    }
    if (i == 0) Nonunit_cls(image_ptr) = NHtrie(image_ptr);
  }

  if (Trie2_Ucl_idx(image_ptr) >= MAX_LIST) {
    printf("Trie1_Ucl (%d) overflow!\n", MAX_LIST);
    exit(1);
  }

  while (Trie2_Ucl_idx(image_ptr) > 0) {
    
    cl = Trie2_Ucl(image_ptr)[--Trie2_Ucl_idx(image_ptr)];
    /*printf("-");    print_clause_from_leaf(cl);*/
    
    if (active_clause(cl)) {
      if (count_of_clause(cl) == 0) {
	if (GRASP && Backup_idx(image_ptr)) trie2_record_conflict(image_ptr, cl);
	return handle_fail_end(image_ptr);
      } else {

	/* at first locate the literal which has no value */
	tr = cl->par; 
	i = 0;
	while (tr != NULL && i == 0) {
	  if (Value(image_ptr)[tr->key] == DC) i = tr->key;
	  else tr = tr->par;
	}

	if (i) {
	  struct var2 *el = V2(image_ptr)[i];

	  Value(image_ptr)[i] = (cl->psign)? TT : FF;
	  /* Monitor */
	  Inc_param(Image_monitor_ptr(image_ptr), UNIT_NUM);
	  /* STACK */
	  if (TRACE == 4) 
	    printf("handle_unit_clauses: putting %d in stack index %d\n", i, Stack_idx(image_ptr));
  	  Stack(image_ptr)[Stack_idx(image_ptr)].f = UP; 
	  Stack(image_ptr)[Stack_idx(image_ptr)++].v = i; 

#ifdef MORETRACE
	  print_x_has_to(image_ptr);
#endif

	  if (GRASP) {
	    mark_of(el) = cl;
	    level_of(el) = Branch_open(image_ptr);
	  }

	  if (trie2_propagate(image_ptr, el, Value(image_ptr)[i], save) == UNSAT) {
	
#ifdef MORETRACE
	    print_up_to_x(image_ptr);
#endif
	    /* STACK */
	    --Stack_idx(image_ptr); 
	    if (TRACE == 4)
	      printf("handle_unit_clauses: decrementing stack index to %d\n", Stack_idx(image_ptr));    

	    Value(image_ptr)[i] = DC;
	    return UNSAT;
	  }
	}
      }
    }
  }

  trie2_freeze_clauses(image_ptr);
  /*if (PURECHECK && save) trie2_pure_check();*/

  return SAT;
}

void trie2_record_conflict (image_ptr, cl)
     image_t *image_ptr;     
     struct trie *cl;
{
  int i, j, u, uip, uip_num, total;
  int sign_arr[MAX_ATOM], uips[MAX_LENGTH], cl_arr[MAX_LENGTH];

  sign_arr[0] = 0;
  Conflict_cl(image_ptr) = NULL;
  Old_cls(image_ptr) = NHtrie(image_ptr);

  if (UIP(image_ptr)) {
    Conflict_cl_level(image_ptr) = (Backup(image_ptr)[Backup_idx(image_ptr)-1] > 0)? 0 : Branch_open(image_ptr);
    uip_num = trie2_locate_uips(image_ptr, cl, uips);
  } else {
    Conflict_cl_level(image_ptr) = 0;
    uip = Backup(image_ptr)[Backup_idx(image_ptr)-1];
    if (uip < 0) uip = 0;
    uips[0] = uip;
    uip_num = 1;
  }

  for (u = 0; u < uip_num; u++) {
    total = trie2_collect_parents(image_ptr, cl, 0, cl_arr, uip=uips[u], u, sign_arr);

    for (i = sign_arr[0]; i > 0; i--) V2(image_ptr)[sign_arr[i]]->pure = 0;

    if (total <= 0) {
      if (!UIP(image_ptr)) Conflict_cl_level(image_ptr) = Branch_open(image_ptr);
    } else {

      /* remove level 0 variables */
      /* fix the sign of literals in the new clause */
      for (i = 0; i < total; i++) {
	j = cl_arr[i];
	if (level_of(V2(image_ptr)[j]) == 0) {
	  cl_arr[i--] = cl_arr[--total];
	} else {
	  V2(image_ptr)[j]->pure = 0;
	  if (j != uip) {
	    if (!UIP(image_ptr) && level_of(V2(image_ptr)[j]) > Conflict_cl_level(image_ptr))  
	      Conflict_cl_level(image_ptr) = level_of(V2(image_ptr)[j]);
	  }
	  sign_arr[j] = NEG(Value(image_ptr)[j]);
	}
      }

      if (u) {	
	cl_arr[total++] = j = uips[u-1];
	sign_arr[j] = Value(image_ptr)[j];
	V2(image_ptr)[j]->pure = 0;
      }

#ifdef MORETRACE
      if (TRACE > 1) {
	printf("\nCollected clause [open: %d]:\n   (", 
	       Branch_open(image_ptr));
	for (i = 0; i < total; i++) {
	  j = cl_arr[i];
	  printf(" %s%d[%d]", ((sign_arr[j])? "" : "-"), j, level_of(V2(image_ptr)[j]));
	}
	printf(")\n\n");
      }
#endif

      /*check_cl(total, cl_arr, sign_arr);*/

      if (total <= GRASP) {
	insert_sorter(cl_arr, total);

	/* integrating the new clause into the database */
	for (i = 0; i < total; i++) {
	  j = cl_arr[i];
	  if (sign_arr[j]) {
	    if (V2(image_ptr)[j]->pos_extra <= 0) { 

#ifdef MORETRACE
	      if (TRACE > 2) 
		printf("  x%d has %d occurrences.\n", j, V2(image_ptr)[j]->pos_count);
#endif

	      Miss_num(image_ptr)++; 
	      if (trie2_add_extra_space(image_ptr, V2(image_ptr)[j], TT) == 0) return; 
	    }
	  } else {
	    if (V2(image_ptr)[j]->neg_extra <= 0) { 
	      Miss_num(image_ptr)++; 

#ifdef MORETRACE
	      if (TRACE > 2) 
		printf(" -x%d has %d occurrences.\n", j, V2(image_ptr)[j]->neg_count);
#endif

	      if (trie2_add_extra_space(image_ptr, V2(image_ptr)[j], FF) == 0) return; 
	    }
	  }
	}

	if (total > 0) {
	  cl = trie_insert_literals(image_ptr, Root3(image_ptr), cl_arr, sign_arr, total-1);
	  if (cl != CLAUSE3(image_ptr) && cl != NULL) {
	    trie2_integrate_clause(image_ptr, cl, (u)? uips[u-1] : 0);
	    if (uip_num > 1) Conflict_cl(image_ptr) = NULL;
	  }
	} 
      }
    }
    cl = mark_of(V2(image_ptr)[uip]);
  }
}

int trie2_add_extra_space (image_ptr, it, sign)
     image_t *image_ptr;     
     struct var2 *it;
     int sign;
{
  int i, old_space;
  struct trie **old_arr, **new_arr;

  if (sign) {
    old_space = it->pos_count;
    old_arr = it->pos;
  } else {
    old_space = it->neg_count;
    old_arr = it->neg;
  }

  /* new_arr = get_trie2_array(old_space+EXTRA_SPACE);*/
  /* Modified! Trapping memory allocation with malloc */
  {
    char *t_block_ptr;
    
    t_block_ptr = (char*) malloc( sizeof ( struct trie *) * (old_space+EXTRA_SPACE));
    /* Append the newly created block to the tracking list */
/*      lsNewEnd(*Ablocks_lsList_ptr(image_ptr), (lsGeneric) t_block_ptr, LS_NH); */
    Ablocks_table(image_ptr)[Cur_block(image_ptr)++] = t_block_ptr;
    new_arr = (struct trie **) t_block_ptr;
  }

  if (new_arr == NULL) {
    printf("Warning: ran out space; no more new clauses\n");
    return (GRASP = 0);
  }
  Memory_count(image_ptr) += (EXTRA_SPACE) * sizeof ( struct trie *);

  for (i = 0; i < old_space; i++) new_arr[i] = old_arr[i];
  free(old_arr);

  if (sign) {
    it->pos_extra = EXTRA_SPACE;
    it->pos = new_arr;
  } else {
    it->neg_extra = EXTRA_SPACE;
    it->neg = new_arr;
  }
  return 1;
}

struct trie *trie2_insert_clause (image_ptr,root, arr, signs, count)
     /* return the end of the clause */
     image_t *image_ptr;
     struct trie *root;
     int arr[], signs[], count;
{
  int key;
  int sign;
  struct trie *no, *bro1, *bro2, *parent;

  parent = NULL;
  bro1 = bro2 = NULL;
  no = root;
  key = arr[count];
  sign = signs[key]; 

  while (no != NULL && count >= 0) {
    
    if (key == no->key) {
      if HAS_POS_CL(image_ptr,no) {
	
	if (sign == 1) {

#ifdef MORETRACE
	  print_x_subsume(image_ptr);
#endif

	  return NULL; /* skip this clause */
	} /* otherwise sign = 0 */

#ifdef MORETRACE
	print_x_skip(image_ptr);
#endif

	bro1 = no;
	no = no->bro; 
      } else if HAS_NEG_CL(image_ptr,no) {
      
	if (sign == 0) {

#ifdef MORETRACE
	  print_x_subsume(image_ptr);
#endif

	  return NULL; /* skip this clause */
	} /* otherwise sign == 1 */

#ifdef MORETRACE
	print_x_skip(image_ptr);
#endif

	bro1 = no;
	no = no->bro; 
      } else {
	parent = no;
	bro1 = NULL;
	if (sign) no = no->pos; else no = no->neg;
      }

      if (count-->0) {
	key = arr[count];
	sign = signs[key]; 
      }

    } else if (key < no->key) {
      bro2 = no;
      no = NULL;
    } else {
      bro1 = no;
      no = bro1->bro;
      while ((no != NULL) && (no->key < key)) {
	bro1 = no;
	no = bro1->bro;
      }
    }
  }

  if (count >= 0) {
    no = get_trie(image_ptr); 
    no->key = arr[count]; 
    no->par = parent;
    if (parent != NULL)
      no->psign = signs[no->par->key];
    no->bro = bro2;
    if (bro1 == NULL) {
      if (signs[no->par->key])
	no->par->pos = no;
      else 
	no->par->neg = no;
    } else {
      bro1->bro = no;
    }
    sign = signs[no->key];
    while (--count >= 0) {
      bro1 = no;
      no = get_trie(image_ptr);
      if (sign) bro1->pos = no;
      else bro1->neg = no;
      no->par = bro1;
      no->psign = sign;
      no->key = arr[count]; 
      sign = signs[no->key];
    }
  } else if (parent == NULL) {
    /* an empty clause is found */
    return CLAUSE3(image_ptr);
  } else {
    no = parent;
  }

  if (signs[no->key]) {
    no->pos = CLAUSE3(image_ptr);
    no->neg = NULL;
  } else {
    no->neg = CLAUSE3(image_ptr);
    no->pos = NULL;
  }
  return no;
}

void trie2_integrate_clause (image_ptr, no, uip)
     image_t *image_ptr;     
     struct trie *no;
{
  int psign, i;
  struct trie *cl;
  struct var2 *el;

  cl = get_trie(image_ptr);
  cl->par = no;
  if (uip) {
    count_of_clause(cl) = 1;
    cl->psign = (Value(image_ptr)[uip])? 1 : 0;
    /* printf("You need to mark this clause!"); */
  } else 
    count_of_clause(cl) = cl->psign = 0;

  Conflict_cl(image_ptr) = cl;
  cl->bro = NHtrie(image_ptr);
  NHtrie(image_ptr) = cl;
  Clause_extra_num(image_ptr)++;

  i = no->key;
  el = V2(image_ptr)[i];
  if HAS_POS_CL(image_ptr,no) {
    el->pos_extra--;
    el->pos[el->pos_count++] = cl;
  } else {
    el->neg_extra--;
    el->neg[el->neg_count++] = cl;
  }
  
  psign = no->psign;
  no = no->par;
  while (no != NULL) {
    i = no->key;
    el = V2(image_ptr)[i];
    if (psign) {
      el->pos_extra--;
      el->pos[el->pos_count++] = cl;
    } else {
      el->neg_extra--;
      el->neg[el->neg_count++] = cl;
    }
    psign = no->psign;
    no = no->par;
  }
}

int trie2_collect_parents (image_ptr, cl, total, result, uip, cl_num, nodes)
     image_t *image_ptr;     
     struct trie *cl;
     int total, result[], uip, nodes[];
{
  int i, idx;
  struct trie *stack[MAX_LENGTH];

  stack[0] = cl->par;
  idx = 1;

  while (idx) {
    cl = stack[--idx];
    if (cl->par != NULL) stack[idx++] = cl->par;
    i = cl->key;

    if (V2(image_ptr)[i]->pure <= cl_num) {

      /* quit when the following condition is true */
      if (idx >= MAX_LENGTH || total >= MAX_LENGTH || Value(image_ptr)[i] == DC) { 
	for (i = 0; i < total; i++)  V2(image_ptr)[result[i]]->pure = 0;
	return 0; 
      }

      V2(image_ptr)[i]->pure = cl_num+1;
      if (i != uip && level_of(V2(image_ptr)[i]) >= Branch_open(image_ptr)) {
	if (mark_of(V2(image_ptr)[i]) != NULL) {
	  stack[idx++] = mark_of(V2(image_ptr)[i])->par;
	  nodes[++nodes[0]] = i;
	} else {
	  result[total++] = i;
	}
      } else {
	result[total++] = i;
      }
    }
  }

  return total;
}

int trie2_locate_uips ( image_ptr, cl0, uips )
     image_t *image_ptr;     
     struct trie *cl0;
     int uips[];
{
  int np[MAX_LENGTH], keys[MAX_LENGTH];
  int num, xyz;

  mark_of(V2(image_ptr)[0]) = cl0;

  xyz = trie2_dfs( image_ptr, 0, -1, np, keys );
  if (xyz == 0) return 0;

  num = topo_sort(image_ptr, np, uips, xyz );
  while (xyz>=0) V2(image_ptr)[keys[xyz--]]->pure = 0;

  if (num == 0) { uips[0] = 0; return 1; }
  return num;
}

int trie2_dfs ( image_ptr, key, dfsnum, np, keys )
     image_t *image_ptr;     
     int key, dfsnum, np[], keys[];
{
  int  i;

  dfsnum++;
  if (dfsnum >= MAX_LENGTH) { 
    for (i = 0; i < dfsnum; i++) V2(image_ptr)[keys[i]]->pure = 0; 
    return 0; 
  }
  V2(image_ptr)[key]->pure = -dfsnum;
  np[dfsnum] = 0;
  keys[dfsnum] = key;

  if (mark_of(V2(image_ptr)[key]) != NULL) {
    struct trie *cl;

    cl = mark_of(V2(image_ptr)[key])->par;
    while (cl != NULL) {
      if ((i= cl->key) != key) {
	if (level_of(V2(image_ptr)[i]) >= Branch_open(image_ptr)) {
	  if (V2(image_ptr)[i]->pure >= 0 &&
	      (dfsnum = trie2_dfs( image_ptr, i, dfsnum, np, keys )) == 0) {
	    return 0;
	  }
	  ++np[-V2(image_ptr)[i]->pure];
	} else {
	  if (Conflict_cl_level(image_ptr) < level_of(V2(image_ptr)[i])) 
	    Conflict_cl_level(image_ptr) = level_of(V2(image_ptr)[i]);
	}
      }
      cl = cl->par;
    }
  }
  
  return dfsnum;
}

int topo_sort (image_ptr, np, uips, total )
     image_t *image_ptr;     
     int np[], uips[], total;
{
  int uipnum, i, key, idx, idx2, last_dfsnum;
  int stack[MAX_LENGTH], inlevel[MAX_LENGTH], level[MAX_LENGTH];
  int lvl, dfsnum, d2;
  struct trie *cl;

  /* initialization */
  stack[0] = uipnum = last_dfsnum = 0;
  for (i = 0; i <= total; i++) inlevel[i] = level[i] = 0;
  idx = 1;
  idx2 = MAX_LENGTH;

  while (idx) {

    key = stack[--idx];
    dfsnum = -V2(image_ptr)[key]->pure;
    lvl = level[dfsnum];

    while (idx2 < MAX_LENGTH && np[stack[idx2]] == 0) idx2++;

    if (idx == 0 &&  /* no other roots */
	idx2 >= MAX_LENGTH &&  /* no other paths */
	inlevel[lvl] == 0) {  /* no other paths */
      
      if (last_dfsnum < dfsnum) {
	uips[uipnum++] = key;
	last_dfsnum = dfsnum+1; 
	UIP_num(image_ptr)++;

#ifdef MORETRACE
	if (TRACE > 3) printf("     %d is a UIP(image_ptr)\n", key);
#endif
      }
    }

    inlevel[lvl] = 1;

    if ((cl = mark_of(V2(image_ptr)[key])) != 0) {

#ifdef MORETRACE
      if (TRACE > 3) printf("   Children of %d (level=%d): [", key, lvl);
#endif

      cl = cl->par;
      while (cl != NULL) {
	if ((i= cl->key) != key &&
	    level_of(V2(image_ptr)[i]) >= Branch_open(image_ptr)) {

	  d2 = -V2(image_ptr)[i]->pure;

#ifdef MORETRACE
	  if (TRACE > 3) printf(" %d (level=%d)", i, level[d2]);
#endif	  

	  if (lvl >= level[d2]) {
	    level[d2] = lvl+1;
	  }
	  if (--np[d2] == 0) stack[idx++] = i;
	  else stack[--idx2] = d2;
	  if (idx >= idx2) return 0;
	} 
	cl = cl->par;
      }

#ifdef MORETRACE
      if (TRACE > 3) printf(" ]\n");
#endif
    }
  }

  if (uipnum) {
    if (uips[uipnum-1] != key) 
      uips[uipnum++] = key;
    else
      UIP_num(image_ptr)--;
  }

  return uipnum;
}

int trie2_max_level (image_ptr, cl, key)
     image_t *image_ptr;     
     struct trie *cl;
     int key;
{
  int max = 0;
  cl = cl->par;
  while (cl != NULL) {
    if (cl->key != key &&
	level_of(V2(image_ptr)[cl->key]) > max)
      max = level_of(V2(image_ptr)[cl->key]);
    cl = cl->par;
 }
  return max;
}

void trie2_adjust_counts (image_ptr, cl)
     image_t *image_ptr;     
     struct trie *cl;
{
  struct trie *tr;
  struct trie *son;
  int count, pcount;

  count = pcount = 0;

  tr = cl->par;

  if (Value(image_ptr)[tr->key] == DC) {
    count++;
    if (HAS_POS_CL(image_ptr,tr)) pcount++;
  }

  son = tr; 
  tr = tr->par;
  while (tr != NULL) {
    if (Value(image_ptr)[tr->key] == DC) {
      count++;
      if (son->psign) pcount++;
    }
    son = tr;
    tr = tr->par;
  }

  count_of_clause(cl) = count;
  cl->psign = pcount;
}

void trie2_empty (image_ptr, cl)
     image_t *image_ptr;     
     struct trie *cl;
{
  while (cl != NULL) {
    if (trie2_is_empty(image_ptr, cl)) print_clause_from_leaf(cl);
    cl = cl->bro;
  }
}

int trie2_is_empty (image_ptr, tr)
     image_t *image_ptr;     
     struct trie *tr;
{
  struct trie *son;

  tr = tr->par;
  if (HAS_POS_CL(image_ptr,tr) && Value(image_ptr)[tr->key] != FF) return 0;
  if (HAS_NEG_CL(image_ptr,tr) && Value(image_ptr)[tr->key] == FF) return 0;

  son = tr;
  tr = tr->par;
  while (tr != NULL) {
    if (son->psign && Value(image_ptr)[tr->key] != FF) return 0;
    if (son->psign == 0 && Value(image_ptr)[tr->key] == FF) return 0;
    son = tr; 
    tr = tr->par;
  }
  return 1;
}

void trie2_stats (image_ptr)
     image_t *image_ptr;     
{
  printf("\n");
  if (Clause_extra_num(image_ptr)) 
    printf("The number of created clauses is %d (%d array updates).\n",
	   Clause_extra_num(image_ptr), Miss_num(image_ptr));
  if (UIP_num(image_ptr))
    printf("The number of found UIPs is %d.\n",
	   UIP_num(image_ptr));
  if (Jump_num(image_ptr))
    printf("The number of backjumping is %d.\n",
	   Jump_num(image_ptr));
  if (Pure_num(image_ptr))
    printf("The number of pure deletions is %ld.\n",
	   Pure_num(image_ptr));
}

void print_all_clauses (image_ptr, cl)
     image_t *image_ptr;     
     struct trie *cl;
{
  while (cl != NULL) {
    print_clause_from_leaf(cl);
    cl = cl->bro;
  }

  return;
}

int trie2_insert_one_key (image_ptr, key, key_arr, total)
     image_t *image_ptr;     
     int key, key_arr[], total;
     /* insert a literal into the current clause.
	return 0 if the key is in key_arr.
	otherwise, return the length of the current clause. */
{
  int j;

  for (j = 0; j < total; j++)
    if (key == key_arr[j]) j = MAX_ATOM;

  if (j >= MAX_ATOM) return 0;
  key_arr[total++] = key;
  return total;
}


void trie2_record_keeping (image_ptr)
     image_t *image_ptr;     
{
  int i;

  /* adjust splitting strategies */
  SELECT = 2;
  if (NH_num(image_ptr) > 2) {
    i = (100*Clause_num(image_ptr))/(NH_num(image_ptr)-2);
    /* if NH > 20% select 1. */
    if (i < 350) SELECT = 1;
    else if (i >= 4242) {
      /* if NH < 2% select 3. */
      if (i == 6233 || i == 5187) SELECT = 3;
      i = CHOICE1;
      CHOICE1 = CHOICE2;
      CHOICE2 = i;
    }
  }
  return;

}








