/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE satotrie.h - *SAT 1.3 */
/*  A reentrant version of SATO using tries */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include <stdio.h>

#include "dag.h"
#include "common_sat.h"
#include "monitor.h" 

#ifndef SATOTRIE
#define SATOTRIE

/* Constants ******************************************************************
*/

/* From sato.h */
#define MAX_INT       2147483647   /* 32 bit integer */
#define MAX_SHORT          32767   /* 16 bit integer */
#define MAX_CHAR             255   /*  8 bit integer */
#define MAX_ATOM           10000   /* no bigger than MAX_SHORT */
#define MAX_LIST           10000   /* maximal elements in a list */
#define MAX_LENGTH           250   /* maximal literals in a clause */
#define MAX_STACK             10   /* maximal elements in a stack */
#define MAX_STACK1   MAX_STACK-1
#define MAX_ABG_SIZE         140

#define FF                0             /* false */
#define TT                1             /* true */
#define DC                2             /* Don't-Care value */
#define SAT               3
#define UNSAT             MAX_ATOM
#define NEG(v)           (v == TT? FF : TT)

/* From sato.c */
#define TP_ALLOC_SIZE MAX_SHORT
#define ARG_TYPE unsigned

/* From trie.h */
#define FLOW 1437004800         /* FLOW = 12! x 3 */
#define EXTRA_SPACE (GRASP<<2)
#define HAVE_UIP 1
#define PURECHECK -MAX_ATOM
#define MAGIC 35               /* at most 12*/
#define JUMP 1;                /* never perform jumpy search */

/* Added */
#define CONTRADICTION  -1
#define TAUTOLOGY       1
#define FORMULA_OK      0

/* Global parameters **********************************************************
*/
#ifdef IN_MAIN
#define GLOB         /* empty string if included by main program */
#else
#define GLOB extern  /* extern if included by anything else */
#endif


/* From sato.h */
GLOB int SELECT;     /* the splitting heuristic to be used */
GLOB int LINE;       /* how many atoms per line in a printed model */ 
GLOB int GRASP;      /* the maximum length for the reason */
GLOB int CHOICE1;    /* the first value to be assigned when splitting */
GLOB int CHOICE2;    /* the complement of CHOICE1 */

GLOB int TRACE;      /* Available for future extensions */

/* Added */
GLOB int TIMEOUT;       /* set a timeout (in seconds) on the decision process */

GLOB int BIAS;          /* splitting sign */ 

GLOB int PURE_HEUR;     /* pure literal detection and propagation (default 0)
			   PURE_HEUR = 0  do not propagate
			   PURE_HEUR = 1  propagate in added variables only 
			   PURE_HEUR = 2  always propagate */

GLOB int HORN_HEUR;     /* relaxation to horn clauses (default 0)
			   HORN_HEUR = 0 split on any clause
			   HORN_HEUR = 1 split on non-horn clauses only */

GLOB int SPLIT_DEP;     /* splitting on dependent atoms (default 0)
			   SPLIT_DEP = 1 split on any atom
			   SPLIT_DEP = 0 split on independent atoms only */

GLOB int CNF_CONV;      /* what kind of CNF conversion (if needed) should be performed
			   CNF_CONV = 0 standard (non-optimized) conversion
			   CNF_CONV = 1 optimized conversion
			   (See dag.h) */

GLOB int NNF_CONV;      /* pushing down negations
			   NNF_CONV = 0 negations are not pushed down 
			   NNF_CONV = 1 negations are pushed down */

GLOB int LANGUAGE;      /* the DAG propositional language
			   LANGUAGE = 0 unrestricted language (imp,iff,or,and,not)
			   LANGUAGE = 1 restricted language (iff,or,and,not)
			   LANGUAGE = 2 restricted language (or,and,not) 
			   (See dag.h) */

GLOB int EARLY_JUMPING; /* early pruning */
GLOB int BACK_JUMPING;  /* backjumping strategy */

GLOB int JUMPING;       /* either early pruning or backjumping is enabled (default 0) */

GLOB int CACHE_MEMO;     /* memoizing strategy */
GLOB int WINDOW_SIZE;    /* how many intermediate results can be stored w/o trashing */
GLOB int PFAST;          /* propositional relevance checking */
GLOB int MFAST;          /* modal relevance checking */
GLOB int CACHE_AND_FAST; /* how to combine relevance checking and caching */

GLOB int VERBOSE;       /* enable rich output */ 

/* Types **********************************************************************
*/

/* The trie */
struct trie { /* trie of clauses */
  char psign, esign; 
  short key;
  struct trie *bro;
  struct trie *pos, *neg;
  struct trie *par;
  struct links *link;
};

struct links {
  struct trie *lin;
  struct trie *back;
  struct cap *stamp;
};

struct cap { 
  struct trie *tr;
};

struct var3 { 
  int key;
  struct trie *push, *pull;
  struct trie **pos, **neg;
  struct cap *both, *poss, *negs;
  struct cap *pposs, *pnegs;
  struct var3 *next;
};

struct var2 { 
  short key;
  short pos_extra;
  short neg_extra;
  short level;
  short pos2;
  short neg2;
  int pure;
  int pos_count;
  int neg_count;
  struct trie *frozen, *force;
  struct trie **pos, **neg;
  struct var2 *next;
};

/* The image */

/* STACK */
#define  UP  0  /* Unit propagation */
#define  PP  1  /* Pure propagation */
#define  SP  2  /* Splitting propagation */
#define  SPP 3  /* Splitting propagation on positive pure literal */
#define  SPN 4  /* Splitting propagation on negative pure literal */

typedef struct stack_elem {
  int   v;
  short f; 
} stack_elem_t;

typedef struct trie *trie_ptr_t; 

typedef struct image {
  /* .h variables */
  long unsigned trie_frees, trie_avails, trie_gets, trie_news;
  struct trie *trie_avail;

  struct trie *clause3;
  struct trie *root3;
  struct trie *nhtrie;
  struct trie *cltrie;
  /* Added to handle non-reversing building of trie */
  struct trie *nhtrietl;
  
  struct var3 **v3;
  struct var3 *top_var3;

  struct var2 **v2;
  struct var2 *top_var2;
  
  struct trie **trie2_ucl;
  int trie2_ucl_idx;

  /* .c variables */
  int tdc_idx_end;
  struct trie *conflict_cl, *nonunit_cls, *old_cls, *bitrie;
  int conflict_cl_level;
  long pure_num;
  int uip, uip_num, jump_num, nh_num, miss_num;

  /* some sato.h variables: the variables used in the decision process,
     not the configuration parameters, are included */
  int value[ MAX_ATOM ];
  int old_value[ MAX_LIST ], old_choice[ MAX_LIST ], oldv;
  int max_atom;
  long max_clause;
  long printed_clause;
  long clause_num, subsume_num, unit_num;
  int tdc[MAX_ATOM], tdc_idx; 
  
  unsigned long branch_num;
  long branch_fail;
  unsigned int branch_succ, branch_open, clause_extra_num;
  
  int backup[MAX_LIST];
  int backup_idx;
  
  long memory_count;   
  int stop;
  int lookahead_level;
  
  char          *alloc_block;    /* location returned by most recent malloc */
  char          *alloc_pos;      /* current position in block */
  unsigned long branch_mark;
  
  /* Added to handle splitting on added variables */
  /* If SPLIT_INDEP = 1 the atom i is not
     chosen for splitting, unless i <= max_indep */
  int max_indep;
  /* Added to handle consistency checking */
  int last_cons_res;
  /* Added to handle the current formula */
  lsList *main_formula_lsList_ptr;
  /* Added to handle memory deallocation: keeps a list of pointers
     corresponding to the blocks returned by tp_alloc */
  char *ablocks_table[MAX_SHORT];
  int cur_block;
  /* Added to reference the parameter monitoring structure */
  monitor_t *image_monitor_ptr; 
  /* Added to handle modal backjumping */
  /* This is the index in the stack where SATO should backjump to */
  int jump_point;
  int last_stack_idx;
  /* STACK */
  stack_elem_t stack[MAX_LIST];
  int stack_idx;

  trie_ptr_t *roots;          /* variables that were declared as static into trie.c */
  int        old_max_atom;      
  int        act_max_atom;    /* variable declared into clause.c */
} image_t;

/* Image handling *************************************************************
*/
/* Image initialization and disposal */
image_t *Init_image();
void    Clear_image(image_t *image_ptr);

/* A set of macros that simulates global and static variables */

/* The macros to get former static variables */
#define Roots(image_ptr)         (image_ptr->roots)
#define Old_max_atom(image_ptr)  (image_ptr->old_max_atom)
#define Act_max_atom(image_ptr)  (image_ptr->act_max_atom)

/* Former sato.h global variables */
#define Trie_frees(image_ptr)  (image_ptr->trie_frees)
#define Trie_avails(image_ptr) (image_ptr->trie_avails)
#define Trie_gets(image_ptr)   (image_ptr->trie_gets)
#define Trie_news(image_ptr)   (image_ptr->trie_news)

#define Trie_avail(image_ptr)  (image_ptr->trie_avail)
#define CLAUSE3(image_ptr) (image_ptr->clause3)
#define Root3(image_ptr)   (image_ptr->root3)
#define NHtrie(image_ptr)  (image_ptr->nhtrie)
#define CLtrie(image_ptr)  (image_ptr->cltrie)
/* Added to handle non reversing trie building */
#define NHtrietl(image_ptr)  (image_ptr->nhtrietl)
  
#define V3(image_ptr)        (image_ptr->v3)
#define Top_var3(image_ptr)  (image_ptr->top_var3)
#define V2(image_ptr)        (image_ptr->v2)
#define Top_var2(image_ptr)  (image_ptr->top_var2)
#define Trie2_Ucl(image_ptr) (image_ptr->trie2_ucl)

#define Trie2_Ucl_idx(image_ptr) (image_ptr->trie2_ucl_idx)

/* Former trie.c global variables */
#define Tdc_idx_end(image_ptr)       (image_ptr->tdc_idx_end)
#define Conflict_cl(image_ptr)       (image_ptr->conflict_cl)
#define Nonunit_cls(image_ptr)       (image_ptr->nonunit_cls)
#define Old_cls(image_ptr)           (image_ptr->old_cls)
#define BItrie(image_ptr)            (image_ptr->bitrie)
#define Conflict_cl_level(image_ptr) (image_ptr->conflict_cl_level)
#define Pure_num(image_ptr)          (image_ptr->pure_num)
#define UIP(image_ptr)               (image_ptr->uip)
#define UIP_num(image_ptr)           (image_ptr->uip_num)
#define Jump_num(image_ptr)          (image_ptr->jump_num)
#define NH_num(image_ptr)            (image_ptr->nh_num)
#define Miss_num(image_ptr)          (image_ptr->miss_num) 

/* Former sato.h global variables */
#define Value(image_ptr)           (image_ptr->value) 
#define Old_value(image_ptr)       (image_ptr->old_value) 
#define Old_choice(image_ptr)      (image_ptr->old_choice) 
#define OLDV(image_ptr)            (image_ptr->oldv) 
#define Max_atom(image_ptr)        (image_ptr->max_atom)
#define Max_clause(image_ptr)      (image_ptr->max_clause) 
#define Printed_clause(image_ptr)  (image_ptr->printed_clause) 
#define Clause_num(image_ptr)      (image_ptr->clause_num)
#define Subsume_num(image_ptr)     (image_ptr->subsume_num)
#define Unit_num(image_ptr)        (image_ptr->unit_num)
#define Tdc(image_ptr)             (image_ptr->tdc)
#define Tdc_idx(image_ptr)         (image_ptr->tdc_idx)

#define Branch_num(image_ptr)       (image_ptr->branch_num)
#define Branch_fail(image_ptr)      (image_ptr->branch_fail)
#define Branch_succ(image_ptr)      (image_ptr->branch_succ)
#define Branch_open(image_ptr)      (image_ptr->branch_open)
#define Clause_extra_num(image_ptr) (image_ptr->clause_extra_num)

#define Backup(image_ptr)           (image_ptr->backup)
#define Backup_idx(image_ptr)       (image_ptr->backup_idx)

#define Memory_count(image_ptr)    (image_ptr->memory_count)
#define Stop(image_ptr)            (image_ptr->stop)
#define Lookahead_level(image_ptr) (image_ptr->lookahead_level)

#define Max_indep(image_ptr)               (image_ptr->max_indep)
#define Last_cons_res(image_ptr)           (image_ptr->last_cons_res)
#define Main_formula_lsList_ptr(image_ptr) (image_ptr->main_formula_lsList_ptr)
#define Ablocks_table(image_ptr)           (image_ptr->ablocks_table)
#define Cur_block(image_ptr)               (image_ptr->cur_block)
#define Image_monitor_ptr(image_ptr)       (image_ptr->image_monitor_ptr)
#define Jump_point(image_ptr)              (image_ptr->jump_point) 
#define Last_stack_idx(image_ptr)          (image_ptr->last_stack_idx)
#define Stack(image_ptr)                   (image_ptr->stack)
#define Stack_idx(image_ptr)               (image_ptr->stack_idx)
#define Storage_lsList_ptr(image_ptr)      (image_ptr->storage_lsList_ptr)

/* Former sato.c global variables */
#define Alloc_block(image_ptr) (image_ptr->alloc_block)
#define Alloc_pos(image_ptr)   (image_ptr->alloc_pos)
#define Branch_mark(image_ptr) (image_ptr->branch_mark)

/* Macros *********************************************************************
*/

/* From trie.h */
#define HAS_POS_CL(image_ptr, no) (no->pos == CLAUSE3(image_ptr))
#define HAS_NEG_CL(image_ptr, no) (no->neg == CLAUSE3(image_ptr))

#define trie2_propagate(image_ptr, a,b,c) \
  ((b)? trie2_propagate_true(image_ptr,a,c) : trie2_propagate_false(image_ptr,a,c))

#define count_of_clause(cl) cl->key
#define active_clause(cl) cl->neg == NULL
#define frozen_lin(cl) cl->neg

#define binary_lin(cl) cl->pos
#define unit_lin(cl) cl->link->back

#define level_of(it) it->level
#define mark_of(it) it->force
#define frozen_cls(it) it->frozen

#define free_trie_cell(image_ptr, no) \
  if (no->key == -1) { \
     printf("re-free a cell\n"); bug(4);\
  } else { no->key = -1; \
    no->bro = Trie_avail(image_ptr); \
    Trie_avail(image_ptr) = no;\
    Trie_avails(image_ptr)++; \
  }\
  Trie_frees(image_ptr)++

/* From sato.h */
#define assign_value(image_ptr, i, val)\
  Value(image_ptr)[i] = val;\
  Tdc(image_ptr)[Tdc_idx(image_ptr)++] = i

#define print_let_x_have(image_ptr) \
    if (TRACE == 2) printf("B%ld.", Branch_num(image_ptr)); \
    else if (TRACE > 8 || TRACE == 3 || TRACE == 4)  \
      printf("[%d]  let x%d have value %d.\n", Branch_open(image_ptr), i, Value(image_ptr)[i])

#define print_now_let_x_have(image_ptr) \
    if (TRACE == 2) printf( "B%ld.", Branch_num(image_ptr)); \
    else if (TRACE > 8 || TRACE == 3 || TRACE == 4)  \
      printf( "    now let x%d have value %d.\n", i, Value(image_ptr)[i])

#define print_x_has_to(image_ptr) \
    if (TRACE == 2) printf( "."); \
      else if (TRACE > 8 || TRACE == 4)  \
	printf( "      now x%d has value %d.\n", i, Value(image_ptr)[i])

#define print_x_contradictory \
     if (TRACE > 8 || TRACE == 4) \
	printf( "      x%d has contradictory values.\n", i)

#define print_up_to_x(image_ptr) \
    if (TRACE > 8 || TRACE == 4) \
        printf( "      reset x%d's value %d.\n", i, Value(image_ptr)[i])

#define print_x_pure(image_ptr) \
    if (TRACE > 8 || TRACE == 4) \
      fprintf (stdout, "    x%d is set to %d by pure-literal deletion.\n", \
		 i, Value(image_ptr)[i])

#define print_x_subsume(image_ptr) \
	  if (TRACE > 6) \
	    printf( "      [C%d] is subsumed by another clause.\n", \
		    Clause_num(image_ptr))

#define print_x_skip(image_ptr) \
	if (TRACE > 6) \
	  printf( "    %d in [C%d] is skipped by tail resolution.\n", \
		  key, Clause_num(image_ptr))

/* Following use of TRIE_PUSH_BROTHERS is identical to trie_push_brothers(top_no). 
   struct trie *tr = top_no;
   TRIE_PUSH_BROTHERS
*/
#define TRIE_PUSH_BROTHERS \
  struct trie *bros[MAX_SHORT];\
  struct trie *no;\
  int i;\
  int esign;\
  int vi;\
  int idx;\
  struct var3 *it;\
  idx = 1;\
  bros[0] = tr;\
  while (idx > 0) {\
    tr = bros[--idx];\
    while (tr != NULL) {\
      no = tr;\
      i = no->key;\
      esign = no->esign;\
      vi = Value(image_ptr)[i];\
      it = V3(image_ptr)[i];\
      if (esign == TT) {\
	if (vi == DC) {\
	  trie_assign_value(image_ptr, i, TT);\
	} else if (vi == FF) {\
	  return handle_fail_end();\
	}\
	if (tr->bro != NULL) bros[idx++] = tr->bro;\
	tr = no->neg;\
      } else if (esign == FF) {\
	if (vi == DC) {\
	  trie_assign_value(image_ptr, i, FF);\
	} else if (vi == TT) {\
	  return handle_fail_end();\
	}\
	if (tr->bro != NULL) bros[idx++] = tr->bro;\
	tr = no->pos;\
      } else { /* esign == DC */ \
	if (vi == TT) {\
	  if (tr->bro != NULL) bros[idx++] = tr->bro;\
	  tr = no->neg;\
	} else if (vi == FF) {\
	  if (tr->bro != NULL) bros[idx++] = tr->bro;\
	  tr = no->pos;\
	} else {  /* vi == DC */ \
	  struct cap *cp;\
	  if (no->neg == NULL) {\
	    if (no->pos != NULL) {\
	      cp = it->poss;\
	      no->link->lin = cp->tr;\
	      cp->tr = no;\
	      if (Backup_idx(image_ptr)) {\
		no->link->stamp = cp;\
		no->link->back = Top_var3(image_ptr)->push;\
		Top_var3(image_ptr)->push = no;\
	      }\
	    }\
	  } else if (no->pos == NULL) {\
	    cp = it->negs;\
	    no->link->lin = cp->tr;\
	    cp->tr = no;\
	    if (Backup_idx(image_ptr)) {\
	      no->link->stamp = cp;\
	      no->link->back = Top_var3(image_ptr)->push;\
	      Top_var3(image_ptr)->push = no;\
	    }\
	  } else {\
	    cp = it->both;\
	    no->link->lin = cp->tr;\
	    cp->tr = no;\
	    if (Backup_idx(image_ptr)) {\
	      no->link->stamp = cp;\
	      no->link->back = Top_var3(image_ptr)->push;\
	      Top_var3(image_ptr)->push = no;\
	    }\
	  }\
	  tr = tr->bro;\
	}\
      }\
    }\
  }

/* Added */

#define trie2_best_key(image_ptr,dag_ptr)\
  if (SELECT == 1) {\
    i = trie2_strategy1(image_ptr,dag_ptr);\
  } else if (SELECT == 2) {\
    i = trie2_strategy2(image_ptr,dag_ptr);\
  } else if (SELECT == 3) {\
    i = trie2_strategy3(image_ptr);\
  } else if (SELECT == 4) {\
    i = trie2_strategy4(image_ptr);\
  } else if (SELECT == 5) {\
    i = trie2_strategy5(image_ptr);\
  } else if (SELECT == 6) {\
    i = trie2_strategy6(image_ptr);\
  } else {\
    fprintf ( stderr, "Unknown option: -s%d\n", SELECT);\
    Stop(image_ptr) = 1;\
    i = 0;\
  }

#define trie2_choose_sign(image_ptr)\
  if ((BIAS == 1) || (BIAS == 11)) {\
    *sign = (neg_count > pos_count)? CHOICE2 : CHOICE1;\
  } else if ((BIAS == 2) || (BIAS == 12)) {\
    *sign = FF;\
  } else if ((BIAS == 3) || (BIAS == 13)) {\
    *sign = TT;\
  } else if (BIAS == 21) {\
    *sign = (pos_count > neg_count)? TT : FF;\
  } else {\
    fprintf ( stderr, "Unknown option: -l%d\n", BIAS);\
    Stop(image_ptr) = 1;\
    *sign = FF;\
  }

#define pos_weight_boehm (pos_count2 * 1000 + pos_count3)
#define neg_weight_boehm (neg_count2 * 1000 + neg_count3)

#define trie2_choose_weight(image_ptr)\
  ((BIAS < 21) ? (neg_count * pos_count) : \
   ((pos_weight_boehm > neg_weight_boehm) ? \
    (pos_weight_boehm + 2*neg_weight_boehm) : (2*pos_weight_boehm + neg_weight_boehm)))


/* Prototypes *****************************************************************
*/

/* Added */
image_t *sato_init();                       
void print_model_complete ();
void parse_cmd_line();

/* For sato.c */
int sato ();
int build ();
void p_input_stats();
void p_paras ();
void p_stats ();
void print_model ();
int handle_succ_end ();
int handle_fail_end (); 
void bug ();
char *tp_alloc();
void print_guide_path ();
void output_guide_path ();
int read_guide_path ();
void print_read_guide_path ();

/* For clause.c */
void print_clause ();
void fprint_clause ();
void print_unit_clause ();
int read_one_clause ();
int input_clauses ();
int insert_one_key ();
int read_int();
int skip_chars_until ();
void reverse ();
void insert_sorter ();
int str_int();
void str_cat();
void str_copy();

/* For trie.c */
void trie_init_once_forall ();
void init_trie ();
struct trie *trie_create_one_path ();
struct trie *trie_insert_literals ();
struct trie *trie_attach_clause ();
struct trie *merge_tries();
struct trie *get_trie_link ();
struct trie *get_trie ();
void free_trie ();
void free_trie2 ();
void real_free_trie2();
void print_trie ();
void print_trie_aux();
int trie_strategy0();
int trie_search();

int trie_propagate_values ();
int trie_pull_list ();
int trie_pull_par_up ();
int trie_push_list_pos ();
int trie_push_list_neg ();
int trie_push_brothers ();
int trie_clean_dependents ();
int trie_short_pos_clause();
int trie_short_pos_clause_all();
int trie_insert_clause();

void p_trie_info ();
void init_var3_table ();
int visit_trie ();
int trie_create_var_table();
void init_var2_table ();
struct trie **get_trie2_array ();
long visit_trie2 ();
void trie2_fill_in_clauses ();
void var_clauses();
void print_clause_from_leaf ();
int trie2_search2 ();
int trie2_next_key ();
int trie2_prev_key ();
int trie2_mom ();
void trie2_update_binary ();
void trie2_compute_binary ();
int trie2_compute_mom ();
int trie2_strategy1 ();
int trie2_strategy2 ();
int trie2_strategy3 ();
int trie2_strategy4 ();
int trie2_strategy5 ();
int trie2_strategy6 ();
void trie2_pure_delete ();
void trie2_pure_check ();
int trie2_propagate_true ();
int trie2_propagate_false ();
void trie2_clean_dependents ();
void trie2_clean_one_var ();
void trie2_freeze_clauses();
int trie2_handle_unit_clauses ();
int trie2_handle_known_values ();
int trie2_add_extra_space ();
int trie2_collect_parents ();
void trie2_record_conflict ();
struct trie *trie2_insert_clause ();
void trie2_integrate_clause ();
int trie2_locate_uips ();
int trie2_dfs ();
int topo_sort ();
int trie2_max_level ();
void trie2_adjust_counts ();
void trie2_empty ();
int trie2_is_empty ();
void trie2_stats ();
int trie2_insert_one_key ();
#endif





