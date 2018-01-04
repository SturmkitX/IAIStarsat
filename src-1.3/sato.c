/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE sato.c - *SAT 1.3 */
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

image_t *sato_init(max_atom, max_clause, max_indep, glob)
     int max_atom; long max_clause; int max_indep;
     int glob;
{
  image_t *image_ptr;
  int     i;

  image_ptr = Init_image();

  /* This is new */
  Max_atom(image_ptr) = max_atom;
  Max_clause(image_ptr) = max_clause;
  Max_indep(image_ptr) = max_indep;
  Last_cons_res(image_ptr) = 1;          /* Assuming consistency */
  
  /* The following initializations used to be in command_line_check */
  Memory_count(image_ptr) = 0;
  Lookahead_level(image_ptr) = 0;

  Stop(image_ptr) = 0; 
  OLDV(image_ptr) = 0;

  /* Global variables are initialized only once */
  if (glob) {
    GRASP = 0;             /* Backjumping is disabled */
    TRACE = 0;
    SELECT = 2;         
    LINE = 20;
    CHOICE1 = FF;
    CHOICE2 = TT;
    /* This was added */
    TIMEOUT = 1000;       /* 1000 seconds of CPU time for the decision process */
    BIAS = 1;             /* Original SATO heuristic (when SELECT=1,2) */
    HORN_HEUR = 0;        /* Relaxation to Horn clauses is disabled */
    SPLIT_DEP = 0;        /* Split on independent variables only */  

    EARLY_JUMPING = 1;    /* Early pruning is enabled */
    BACK_JUMPING = 0;       
    JUMPING = 1;
    CACHE_MEMO = 3;      /* Memoizing is for SAT/UNSAT with a bit matrix */
    MFAST = 0;           /* No modal FAST */
    PFAST = 0;           /* No propositional FAST */
    CACHE_AND_FAST = 0;  /* No interaction between caching and FAST */
    WINDOW_SIZE = 512;   /* Default value for memoizing window (if enabled) */
    VERBOSE = 1;         /* Compact output with comments*/
    
  } 

  /* The following initializations used to be in main */
  Alloc_block(image_ptr) = NULL;         /* Added for safety reasons */
  Alloc_pos(image_ptr) = NULL;           /* Added for safety reasons */   
  trie_init_once_forall(image_ptr);

  /* The following initializations used to be in read_one_problem */
  for (i = 1; i <= Max_atom(image_ptr); i++) Value(image_ptr)[i] = DC; 

  return image_ptr;
}

void parse_cmd_line(image_ptr, argc, argv)
     image_t *image_ptr;
     int     argc;
     char    **argv;
{
    int i, temp;

    for(i = 1; i < argc; i++) 
      if (argv[i][0] == '-')  {
	temp = str_int(argv[i], 2);

	if ((argv[i][1] == 'k') ||
	    (argv[i][1] == 'n') ||
	    (argv[i][1] == 'f')) {
	  continue; 
	} else if (argv[i][1] == 's') {
	  SELECT = temp;
	} else if (argv[i][1] == 'l') {
	  BIAS = temp;
	} else if (argv[i][1] == 'v') {
	  CHOICE1 = TT;
	  CHOICE2 = FF;
	} else if (argv[i][1] == 'p') {
	  PURE_HEUR = temp;
	} else if (argv[i][1] == 'g') {
	  GRASP = temp;
	} else if (argv[i][1] == 'h') {
	  HORN_HEUR = 1;
	} else if (argv[i][1] == 'd') {
	  SPLIT_DEP = 1;
	} else if (argv[i][1] == 'e') {
	  EARLY_JUMPING = temp;
	  JUMPING = temp;
	} else if (argv[i][1] == 'b') {
	  BACK_JUMPING = temp;
	  JUMPING = temp;
	} else if (argv[i][1] == 'o') {
	  TIMEOUT = temp;
	} else if (argv[i][1] == 'm') {
	  CACHE_MEMO = temp;
	} else if (argv[i][1] == 'w') {
	  WINDOW_SIZE = temp;
	} else if (argv[i][1] == 'a') {
	  PFAST = temp;
	} else if (argv[i][1] == 'c') {
	  MFAST = temp; 
	} else if (argv[i][1] == 't') {
	  CACHE_AND_FAST = temp;
	} else if (argv[i][1] == 'r') {
	  VERBOSE = temp;
	} else {
	  fprintf(stderr, "%s ignores invalid parameter : %s\n",
		  argv[0], argv[i] );
	}
      } else if (i+1 < argc) {
	fprintf ( stderr, "%s ignores invalid parameter : %s\n",
		  argv [0], argv [i] );
      }

    return;
}


/* the main function of sato: return 1 if satisfiable; 0 otherwise.  */
/* Modified to handle a list of clauses as input instead of a file */
/* Modified to handle empty clauses in the input as well as tautologies */
int sato (image_ptr, dag_ptr, Test_star_consistency, formula_lsList_ptr)
     image_t         *image_ptr;
     dag_t           *dag_ptr;
     Cons_func_ptr_t Test_star_consistency;
     lsList          *formula_lsList_ptr;
{
  int i;

  i = build(image_ptr, formula_lsList_ptr);

  switch (i)
    {
    case FORMULA_OK:
#ifdef MORETRACE
      if (TRACE) printf("Using the trie structure for clauses.\n");
#endif
      i = trie_search(image_ptr,dag_ptr,Test_star_consistency);
      break;
    case CONTRADICTION:
      Branch_num(image_ptr) = Branch_fail(image_ptr) = 1;
      i = 0;
    }

#ifdef MORETRACE  
  if (TRACE) p_stats(image_ptr);
  if ((Branch_succ(image_ptr) && Backup_idx(image_ptr) > 0) && TRACE)
    print_guide_path(image_ptr);
#endif
  
  return i;
}


/* Modified to handle a list of clauses as input instead of a file */
int build (image_ptr, formula_lsList_ptr)
     image_t *image_ptr;
     lsList *formula_lsList_ptr;
{
  int j;

  Alloc_block(image_ptr) = NULL;
  Alloc_pos(image_ptr) = NULL;
  Clause_num(image_ptr) = Subsume_num(image_ptr) = Unit_num(image_ptr) = 0;
  Tdc_idx(image_ptr) = 0;
#ifdef MORETRACE
  if (TRACE > 5) printf( "\nInput clauses are:\n\n");
#endif
  init_trie(image_ptr);

  /* read clauses and build tree */
  j = 0;
  j = input_clauses (image_ptr, formula_lsList_ptr );

#ifdef MORETRACE
  if (TRACE) p_input_stats(image_ptr);
  fflush(stdout);
#endif
  return j;
}

void p_input_stats(image_ptr)
     image_t *image_ptr;
{
  if (Clause_num(image_ptr) == 0) {
    printf( "There are no input clauses.\n\n");
    exit(0);
  } else if ((Clause_num(image_ptr) - Subsume_num(image_ptr)) == 1) {
    printf( "There is only one input clause.\n\n");
    exit(0);
  } else if (Subsume_num(image_ptr) > 0)
    printf( "There are %ld input clauses (%ld unit, %ld subsumed, %ld retained).\n", 
	    Clause_num(image_ptr), 
	    Unit_num(image_ptr), Subsume_num(image_ptr), 
	    Clause_num(image_ptr)+Unit_num(image_ptr)-Subsume_num(image_ptr));
  else 
    printf( "There are %ld input clauses.\n", Clause_num(image_ptr) );
  
  printf( "The maximal index of propositional variables is %d.\n",
	  Max_atom(image_ptr));
  printf( "The mallocated memory is %10.2f Kbytes.\n", Memory_count(image_ptr) / 1024.0);
}

void p_paras (image_ptr )
     image_t *image_ptr;
{
  printf ( "Set the trace level to %d.\n", TRACE );
  printf ( "Print at most %d atoms per line in a model.\n", LINE );
}

void p_stats (image_ptr)
     image_t *image_ptr;
{
  if (Branch_succ(image_ptr) > 0) 
    printf( "\nThe number of found models is %d.\n", Branch_succ(image_ptr));
  else if (Branch_num(image_ptr) == Branch_fail(image_ptr)) 
    printf( "\nThe clause set is unsatisfiable.\n");
  else
    printf( "\nThe search for unsatisfiability is incomplete.\n");

  if (Branch_num(image_ptr) == 1)
    printf( "\nThere is only one branch (%d succeeded, %ld failed).\n", 
	   Branch_succ(image_ptr), Branch_fail(image_ptr));
  else 
    printf( "\nThere are %ld branches (%d succeeded, %ld failed).\n", 
	   Branch_num(image_ptr), Branch_succ(image_ptr), Branch_fail(image_ptr));

  if (TRACE > 2) p_trie_info(image_ptr);
}

void print_model (image_ptr)
     image_t *image_ptr;
{
  int i, col, row;

  printf( "\nModel #%d:", Branch_succ(image_ptr));
  if (TRACE < 5) 
    printf( " (indices of true atoms)\n\n    " );
  else 
    printf( "\n\n    " );
  
  if (LINE <= 1) {
    for (i = 1; i <= Max_atom(image_ptr); i++)
      if (TRACE < 5) {
	if (Value(image_ptr)[i] == TT)
	  printf( "%d  ", i);
      } else printf( "%d  ", (Value(image_ptr)[i] == TT)? 1 : 0);
  } else {
    col = row = 0;
    for (i = 1; i <= Max_atom(image_ptr); i++) {
      if (TRACE < 5) {
	if (Value(image_ptr)[i] == TT) { 
	  printf( "%d  ", i);
	  ++col; 
	}
      } else { 
	printf( "%d  ", (Value(image_ptr)[i] == TT)? 1 : 0); 
	++col; 
      }
      
      if ( col == LINE ) {
	col = 0;  printf( "\n    " );
	if ( ++row == LINE ) { 
	  row = 0; 
	  if (i < Max_atom(image_ptr)) printf( "\n    " ); 
	}
      }
    }
  }
  printf( "\n");
}

/* Displays positive and negative values */
void print_model_complete (image_ptr)
     image_t *image_ptr;
{
  int i, col, row;

  if (LINE <= 1) {
    for (i = 1; i <= Max_atom(image_ptr); i++) {
      if (Value(image_ptr)[i] == TT)
	printf( "%d ", i);
      if (Value(image_ptr)[i] == FF)
	printf( "-%d ", i);
    }
  } else {
    col = row = 0;
    for (i = 1; i <= Max_atom(image_ptr); i++) {
      if (Value(image_ptr)[i] == TT) { 
	printf( "%d ", i);
	++col; 
      }
      if (Value(image_ptr)[i] == FF) { 
	printf( "-%d ", i);
	++col; 
      }
      
      if ( col == LINE ) {
	col = 0;  printf( "\n    " );
	if ( ++row == LINE ) { 
	  row = 0; 
	  if (i < Max_atom(image_ptr)) printf( "\n    " ); 
	}
      }
    }
  }
/*    printf( "\n"); */
  fflush(stdout);
  return; 
}

void print_stack(image_ptr)
     image_t *image_ptr;
{
  int i,a;
  
  if Stack_idx(image_ptr) {
    printf("The search stack is:\n( ");
    for (i = 0; i < Stack_idx(image_ptr); i++) {
      a = Stack(image_ptr)[i].v;
      if (a < 0) a = -1 * a;
      printf("%s%s%s%d ",
	     ((Stack(image_ptr)[i].f == SPP) ? "p" : (Stack(image_ptr)[i].f == SPN) ? "n" : ""),
	     ((Stack(image_ptr)[i].f >= SP) ? ((Stack(image_ptr)[i].v > 0) ? "f" : "s") : "u"), 
	     ((Value(image_ptr)[a] == TT) ? "" : "-"), a);
    }
    printf(" )\n");
  } else
    printf("The search stack is empty.\n");

  return; 
}

/* Modified to work with consistency testing */
/* When consistency checking fails, the search for another model is requested */
int handle_succ_end (image_ptr, dag_ptr, Test_star_consistency)
     image_t         *image_ptr;
     dag_t           *dag_ptr;
     Cons_func_ptr_t Test_star_consistency;
{
  int res;

  /* Monitor */
  Inc_param(Image_monitor_ptr(image_ptr), ASSIGN_NUM);

  Branch_succ(image_ptr)++;
#ifdef MORETRACE
  if (TRACE == 2) printf( "S%d\n", Branch_succ(image_ptr));
  if (TRACE) print_model(image_ptr);
#endif

  /* Test consistency now, unless the consistency test is NULL */
  if (Test_star_consistency != NULL) {
    res = (*Test_star_consistency)(image_ptr, dag_ptr); 
    Last_cons_res(image_ptr) = res;
  } else res = 1;

  return (res ? 0 : trie2_prev_key(image_ptr, 2)); 

}

int handle_fail_end (image_ptr) 
     image_t *image_ptr;
  { 
    /* Monitor */
    Inc_param(Image_monitor_ptr(image_ptr), PROPFAIL_NUM);

    Branch_fail(image_ptr)++; 
    if (Backup_idx(image_ptr) < 3) Lookahead_level(image_ptr) = Backup_idx(image_ptr); 
    else Lookahead_level(image_ptr) = Backup_idx(image_ptr)-3; 

  #ifdef MORETRACE 
    if (TRACE == 2) printf( "F%ld\n", Branch_fail(image_ptr)); 
    else if (TRACE > 8 || TRACE == 3 || TRACE == 4)   
      printf( "      an empty clause is found.\n");  
  #endif 

    return UNSAT; 
  } 

void bug (i)
     int i;
{
#ifdef PRIVATE
  printf("<<<<<<<<<<<<<<<<<<< BUG%d >>>>>>>>>>>>>>>>>>>>\n", i);
#else
  i = 1;
#endif
}

/*************
 *    OTTER's Function:
 *
 *    char *tp_alloc(n)
 *
 *    Allocate n contiguous bytes, aligned on pointer boundry.
 *
 *************/

#define scale sizeof(int *)

/* Adds the allocated block to Ablocks_lsList_ptr */
char *tp_alloc(image_ptr, n)
     image_t *image_ptr;
     int n;
{
  char *return_block;

  /* if n is not a multiple of sizeof(int *), then round up so that it is */
  /*if (n % scale != 0)	n += (scale - (n % scale));*/
  if (Alloc_block(image_ptr) == NULL || Alloc_block(image_ptr) + TP_ALLOC_SIZE - Alloc_pos(image_ptr) < n) {
    /* try to malloc a new block */
#ifndef OPTIMIZE
    if (n > TP_ALLOC_SIZE) {
      fprintf(stderr, "tp_alloc, request too big: %d\n", n);
      exit(0);
    } else {
#endif
      Alloc_pos(image_ptr) = Alloc_block(image_ptr) = (char *) malloc((ARG_TYPE) TP_ALLOC_SIZE);
      /* Modified! Append the newly created block to the tracking list */
      Ablocks_table(image_ptr)[Cur_block(image_ptr)++] = Alloc_block(image_ptr);
      /*        lsNewEnd(*Ablocks_lsList_ptr(image_ptr), (lsGeneric) Alloc_block(image_ptr), LS_NH); */
      /* End */
#ifndef OPTIMIZE
      if (Alloc_pos(image_ptr) == NULL) {
	fprintf(stderr, "ABEND, malloc returns NULL (out of memory).\007\n");
	fprintf(stderr, "%ld K has been mallocated.\007\n", Memory_count(image_ptr)/1042);
	exit(0);
      }
#endif
      Memory_count(image_ptr) += TP_ALLOC_SIZE;
#ifndef OPTIMIZE
    }
#endif
  }

  return_block = Alloc_pos(image_ptr);
  Alloc_pos(image_ptr) += n;
  return(return_block);
}  /* tp_alloc */

void print_guide_path (image_ptr)
     image_t *image_ptr;
{
  if (!Backup_idx(image_ptr)) 
    printf( "\nThe search tree path is empty.\n");
  else {
    printf( "\nThe search tree path is:\n ");
    output_guide_path(image_ptr);
    printf( "\n");
    fflush(stdout);
  }
}

void output_guide_path (image_ptr)
     image_t *image_ptr;
{
  int i, k;

  printf( "( ");

  for (i = 0; i < Backup_idx(image_ptr); i++) {
    k = Backup(image_ptr)[i];
    if (k > 0) { printf( "f"); }
    else { printf( "s"); k = -k; }

    if (Value(image_ptr)[k] == FF) 
      printf( "-%d ", k);
    else 
      printf( "%d ", k);
  }
  printf( ")");
}

/*******************************
 This was originally clause.c
******************************/

void print_clause (image_ptr, arr, sign, total)
     image_t *image_ptr;
     int arr[], sign[], total;
{
  fprint_clause (image_ptr, arr, sign, total);
}

void fprint_clause (image_ptr, arr, sign, total)
     image_t *image_ptr;
     int arr[], sign[], total;
{
  Printed_clause(image_ptr)++;
  total--;
  while ( total >= 0 ) {
    if (sign[arr[total]] == 0) printf("-");
    printf ("%d ", arr[total--] );
  }
  printf("0\n");
}

void print_unit_clause (image_ptr, sign, i)
     image_t *image_ptr;
     int sign, i;
{ 
  Printed_clause(image_ptr)++;
  printf((sign == TT)? "%d 0\n" : "-%d 0\n", i);
}

int insert_clause (image_ptr,  cl_arr, sign_arr, total )             
     image_t *image_ptr;
     int cl_arr[], sign_arr[], total;
{
  int j, i, k;

  if (cl_arr[0] > Max_atom(image_ptr)) bug(10);
  if (TRACE > 8) print_clause(image_ptr, cl_arr, sign_arr, total);

  /* check for literals and clauses subsumed by unit clauses */
  j = 0;
  for (i = 0; i < total; i++) {
    k = cl_arr[i];
    if (Value(image_ptr)[k] == DC) 
      cl_arr[j++] = k;
    else if (Value(image_ptr)[k] == sign_arr[k]) { /* the clause is subsumed */
      Subsume_num(image_ptr)++;

#ifdef MORETRACE
      if (TRACE > 7)
	printf("      [C%ld] is subsumed by unit clause (%d).\n",
		Clause_num(image_ptr), (Value(image_ptr)[k])? k : -k);
#endif
      return FORMULA_OK;

    } else { /* the literal is subsumed */

#ifdef MORETRACE
      if (TRACE > 7)
	printf("    %d in [C%ld] is skipped due to a unit clause.\n",
		k, Clause_num(image_ptr));
#endif
    }
  }
  total = j;

  if (total == 0) {

#ifdef MORETRACE
    if (TRACE > 6)
      printf( "    [C%ld] becomes empty.\n", Clause_num(image_ptr));
#endif

    bug(4);
    return CONTRADICTION;
  }

  if (TRACE > 8)
    print_clause(image_ptr, cl_arr, sign_arr, total);

  if (total == 1) { /* a unit clause is found */

    j = cl_arr[0];
    assign_value(image_ptr, j, sign_arr[j]);
    Unit_num(image_ptr)++;
    /* Monitor */
    Inc_param(Image_monitor_ptr(image_ptr), UNIT_NUM);
    /* STACK */
    if (TRACE == 4) printf("preprocessing: putting %d to stack index %d\n", j, Stack_idx(image_ptr));
    Stack(image_ptr)[Stack_idx(image_ptr)].f = UP; 
    Stack(image_ptr)[Stack_idx(image_ptr)++].v = j; 

#ifdef MORETRACE
    if (TRACE > 7 || TRACE == 4)
      printf ( "    x%d is set to %d by unit clause.\n",
	       j, Value(image_ptr)[j]);
#endif

    return FORMULA_OK;
  }
  
  return trie_insert_clause(image_ptr, cl_arr, sign_arr, total);
}


int read_one_clause ( image_ptr, clause_lsList_ptr, cl_arr, sign_arr, tautology, mark )
     image_t *image_ptr;
     lsList *clause_lsList_ptr; 
     int cl_arr[], sign_arr[], *tautology;
     long mark[];
{
  int       total, sign, i;
  lsGen     t_lsGen;
  lsGeneric t_lsGeneric;
  lsStatus  list_status;
  
  total = 0;
  *tautology = 0;
  lsForEachItem(*clause_lsList_ptr, t_lsGen, t_lsGeneric) {
    i = (int) t_lsGeneric;
    /* If the clause contains the literal 0, sign will be 2
       so the clause will be ignored!! */
    sign = read_int(&i);

    if  (sign != 2) { 
      if (i > Act_max_atom(image_ptr) && (Act_max_atom(image_ptr) = i) > Max_atom(image_ptr)) {
	fprintf ( stderr, "Atom %d > Max_atom(=%d).\n",
		  i, Max_atom(image_ptr));
	exit(0);
      } 
      if (mark == NULL) {
	cl_arr [ total++ ] = i;
	sign_arr [ i ] = sign;
      } else {
	if ((total = insert_one_key(i, sign, cl_arr, sign_arr, total)) == 0) {
	  *tautology = 1;
	}
      } 
      
      if (*tautology) {
	list_status = lsFinish(t_lsGen);
	return 0;
      }
    }
  }
  
  return total;
}

/* Modified to handle a list of clauses as input instead of a file */
int input_clauses ( image_ptr, formula_lsList_ptr )
     image_t *image_ptr;
     /* return 1 if an empty clause is found; otherwise, 0 */
     lsList *formula_lsList_ptr; 
{
  if (formula_lsList_ptr == NIL(lsList)) {
    fprintf(stderr, "no input formula\n");
  } else {
    int        total_lits, i, tautology;
    long       mark[MAX_ATOM];
    lsGen      t_lsGen;
    lsGeneric  t_lsGeneric;
    lsStatus   list_status;
  
    for (i = 0; i <= Max_atom(image_ptr); i++) mark[i] = MAX_ATOM;

    /* Reading the clauses */
   lsForEachItem(*formula_lsList_ptr, t_lsGen, t_lsGeneric) {

      int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

      tautology = 0;
      Clause_num(image_ptr)++;
      total_lits = read_one_clause( image_ptr, (lsList*) t_lsGeneric, 
				    cl_arr, sign_arr, &tautology, mark );

      if (tautology == TAUTOLOGY) {
	Subsume_num(image_ptr)++;
#ifdef MORETRACE
	if (TRACE > 6) 
	  printf("      [C%ld] is a tautology.\n", Clause_num(image_ptr));
#endif
	
      } else 
	if (total_lits > 0) {
	  if (insert_clause ( image_ptr, cl_arr, sign_arr, total_lits) == CONTRADICTION) {
	    Max_atom(image_ptr) = Act_max_atom(image_ptr);
	    list_status = lsFinish(t_lsGen);
	    return CONTRADICTION;
	  }
	} else {
	  /* Emtpy clause means contradiction */
	  return CONTRADICTION;
	}
    }
  }

  Max_atom(image_ptr) = Act_max_atom(image_ptr);
  return FORMULA_OK;
}


int insert_one_key ( key, sign, cl_arr, sign_arr, total)
     int key, sign, cl_arr[], sign_arr[], total;
     /* insert a literal into the current clause.
	return 0 if a tautology is found.
	ignore duplicate literals.
	return the length of the current clause. */
{
  int i, j;

  for (j = 0; j < total; j++)
    if (key > cl_arr[j]) {
      for (i = total; i > j; i--)
	cl_arr[i] = cl_arr[i-1];
      cl_arr[j] = key;
      sign_arr[key] = sign;
      return total+1;
    } else if (key == cl_arr[j]) {
      if (sign == sign_arr[key])
	return total;
      else 
	return 0;
    }
  
  cl_arr[total] = key;
  sign_arr[key] = sign;
  return total+1;
}


/* Modified to handle literals */
int read_int( temp)
     int *temp;
{
  int sign;

  sign = 1;
  if (*temp < 0) {
    sign = 0; 
    (*temp) = (*temp) * -1;
  }
  if (temp == 0) return 2;

  return sign;
}

int skip_chars_until ( f, c )
     FILE *f; 
     char c;
{ 
  int ch;

  while ((ch = getc ( f )) != EOF && ch != c);
  return ch;
}

/******** functions on integer arrays and strings **********/

void reverse (arr, x)
     int arr[], x;
{
  int i = 0;
  int j = x-1;

  while (i < j) {
    x = arr[i];
    arr[i++] = arr[j];
    arr[j--] = x;
  }
}

void insert_sorter (arr, last)
     int arr[], last;
{
  int x, y, i, j;

  for (i = 1; i < last; i++) {
    x = arr[i];
    y = arr[i-1];
    j = i;
    while (y < x) {
      arr[j--] = y;
      y = (j > 0)? arr[j-1] : MAX_SHORT;
    }
    arr[j] = x;
  }
}

int str_int(s, i)
     char s[];
     int i;
{
  int n = 0;
  for( ; s[i] >= '0' && s[i] <= '9'; i++)
    n = n * 10 + s[i] - '0';

  return n;
} 

void str_cat(s1,s2,s3)
     char *s1;
     char *s2;
     char *s3;
{
  int i, j;

  for (i = 0; s1[i] != '\0'; i++)
    s3[i] = s1[i];
  for (j = 0; s2[j] != '\0'; j++, i++)
    s3[i] = s2[j];
  s3[i] = '\0';
}
    
