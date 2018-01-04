/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE main-dp.c - *SAT 1.3 */
/*  Main program */

/*  *********************************************************************** */
/*  *********************************************************************** */
/* This is main! */
#define IN_MAIN

/* Standard modules */
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <signal.h>

/* *SAT modules */
#include "fnode.h"
#include "dag.h"
#include "dp_sat.h"
#include "satotrie.h" 
#include "monitor.h"
#include "statistics.h"
#include "table.h"
#include "set.h"

/* Choose the logic consistency test package */
#ifdef TRANSLATE_TO_K
#include "kdp.h"
#else

#ifdef KSAT
#include "kdp.h"
#endif

#ifdef ESAT
#include "edp.h"
#endif

#endif

/* Main variables */
extern fnode_t  *formula_as_tree;
extern int         yydebug;
dag_t           *dag_ptr;
image_t         *image_ptr;
monitor_t       *monitor_ptr;
statistics_t    *statistics_ptr;
int             res;
Cons_func_ptr_t Test_star_consistency;

/* Prototypes */
extern int      yyparse();
Cons_func_ptr_t Choose_test(); 
void            Translate_to_K(fnode_t *formula_fnode_ptr);
void            Set_preprocessing_flags(int *bary, int *negate);
void            Setup_caching(dag_t *dag_ptr, statistics_t *statistics_ptr);
int             Skip_params(int argc, char **argv); 
void            Help_and_exit(char **argv);
void            Display_results(monitor_t *monitor_ptr);
void            Bare_display_results(monitor_t *monitor_ptr);
void            Bare_display_params(monitor_t *monitor_ptr);
void            Preparse_cmd_line(int argc, char **argv);
void            Purge_comments();
void            Handle_exceptions(int sig);

int main(int argc, char **argv)
{
  int filec;
  int bary, negate;
  struct rlimit rt;

/*    yydebug = 0; */

  /* Initializing the monitor */
  monitor_ptr = Init_monitor();

  /* If no argument is supplied give help and exit starSAT */
  if (argc < 2) Help_and_exit(argv);

  /* Getting the index for the file name in command line */
  filec = Skip_params(argc, argv);

  /* Parsing the input formula------------------------------------------------ */
  if (freopen(argv[filec], "r", stdin) != NULL) { 
#ifdef PURGE_COMMENTS
    Purge_comments();
#endif
    Start_clock(monitor_ptr, PARSE);
    yyparse();
    Stop_clock(monitor_ptr, PARSE);
    /* Recover stdin!!! */
    freopen("/dev/tty", "r", stdin); 
  } else { 
    printf("File %s does not exists\n",argv[1]); 
    exit(-1); 
  } 

  /* Preprocessing------------------------------------------------------------ */
  Start_clock(monitor_ptr, PREPROCESS);
  Set_preprocessing_flags(&bary, &negate);
  Preparse_cmd_line(argc, argv);
  if (bary) {
    /* If the input syntax defines binary trees,
       they are converted to n-ary trees */
    formula_as_tree = Convert_binary2nary(formula_as_tree);
    Flatten_and_or(formula_as_tree);  
  }

  if (NNF_CONV) 
    /* Decide whether to push down negation or not */
    if (negate) Convert_NNF(formula_as_tree, 1); else Convert_NNF(formula_as_tree, 0);
  else {
    /* Just get rid of diamonds from the input syntax */
    Convert_dia2box(formula_as_tree);
  }
  Stop_clock(monitor_ptr, PREPROCESS);

#ifdef TRANSLATE_TO_K
  /* Applying a translational approach for a classical modal logic */
  Start_clock(monitor_ptr, TRANSLATE);
  Translate_to_K(formula_as_tree);
  Stop_clock(monitor_ptr, TRANSLATE);
#endif

  /* Building and Stat ------------------------------------------------------- */
  Start_clock(monitor_ptr, BUILD);
  /* Working either as a validity checker (the input formula is negated) or 
     as a satisfiability checker. */
  if (NNF_CONV || !negate)
    /* Formula was (eventually) negated by NNF conversion */ 
    dag_ptr = Make_dag(formula_as_tree, 0, LANGUAGE, CNF_CONV); 
  else
    /* Formula must be negated here */
    dag_ptr = Make_dag(Make_formula_nary(not_code, empty_code, formula_as_tree), 
		       0, LANGUAGE, CNF_CONV);  
  /* Replacing boxes with modal atoms */
  Replace_boxes(dag_ptr);  
  /* Extracting information from the formula */
  statistics_ptr = Compute_statistics(dag_ptr); 
  /* Initializing the decision algorithm */
  image_ptr = Init_cnf_sat(dag_ptr, GREEDY_CNF_CONV);  
  Stop_clock(monitor_ptr, BUILD);

  /* Eventually, command line parameters change default initialization */
  parse_cmd_line(image_ptr, argc, argv);
  if (VERBOSE == 10) {
    Bare_display_params(monitor_ptr);
    exit(0);
  }

  /* Initializing timeout, memory out and installing exceptions handler */
  getrlimit(RLIMIT_CPU, &rt);
  rt.rlim_cur = TIMEOUT   +   
      ((Get_clock(monitor_ptr, PARSE) +   
        Get_clock(monitor_ptr, PREPROCESS) +
	Get_clock(monitor_ptr, BUILD)) / 1000);   
  setrlimit(RLIMIT_CPU, &rt);

  signal(SIGXCPU, Handle_exceptions);
  signal(SIGSEGV, Handle_exceptions);

#ifdef DEBUG
  Print_dag_info(dag_ptr); 
#endif

  /* Starting the decision algorithm ----------------------------------------- */
  if (Lma(dag_ptr) != Lpa(dag_ptr)) Setup_caching(dag_ptr,statistics_ptr);
  
  Image_monitor_ptr(image_ptr) = monitor_ptr;
  Test_star_consistency = Choose_test();

  Start_clock(monitor_ptr, DSAT); 
  res = Test_dp_sat(image_ptr, dag_ptr, Test_star_consistency);
  Stop_clock(monitor_ptr, DSAT); 

  /* Get memory allocation data and displaying results */
  Inc_param_by(monitor_ptr, MAX_SATO_MEMORY, Memory_count(image_ptr));
  Display_results(monitor_ptr);
  
  /* Clear things away */
  Clear_image(image_ptr);
  Clear_monitor(monitor_ptr);
  
  return (0);
}

void Handle_exceptions(int sig)
{
  switch (sig) 
    {
    case SIGXCPU:
      TIMEOUT = -1;
      Stop_clock(monitor_ptr, DSAT);
      Display_results(monitor_ptr);
    case SIGSEGV:
      TIMEOUT = -2;
      Stop_clock(monitor_ptr, DSAT);
      Display_results(monitor_ptr);
    }

  /* Clear things away */
  Clear_image(image_ptr);
  Clear_monitor(monitor_ptr);

  exit(0);
}

Cons_func_ptr_t Choose_test()
{
#ifdef TRANSLATE_TO_K
  return (Test_K_consistency);
#else

#ifdef KSAT
  return (Test_K_consistency);
#endif

#ifdef ESAT
  return (Test_E_consistency);
#endif

#endif
}

void Setup_caching(dag_t *dag_ptr, statistics_t *statistics_ptr)
{
  Force_no_memoT();
  Force_no_memoS();

#ifdef ESAT
  Init_memoT(Lma(dag_ptr));
#else
  if ((CACHE_MEMO > 0) || (MFAST > 0)) {
    /* Just allocate space for cache (no setup yet) */
    Alloc_memoS(Lma(dag_ptr), statistics_ptr);

    /* Caching is forcefully by level and bit matrices are lossy */
    Setf_memoS(LEVEL_CACHE);
    Clearf_memoS(TRASH_SUBSETS);

    if (CACHE_MEMO) {
      /* Using hash table or bit matrices? */
      if (CACHE_MEMO > 3) Setf_memoS(HASH_STORAGE);

      /* What to cache? */
      if ((CACHE_MEMO == 1) || (CACHE_MEMO == 3) ||
	  (CACHE_MEMO == 4) || (CACHE_MEMO == 6))
	Setf_memoS(GET_MODELS);
      if ((CACHE_MEMO == 2) || (CACHE_MEMO == 3) ||
	  (CACHE_MEMO == 4) || (CACHE_MEMO == 6))
	Setf_memoS(GET_DEPENDENCIES);
    }

    /* Set modal relevance checking parameters */
    if ((MFAST == 1) || (MFAST == 3)) Setf_memoS(STATIC_FAST);
    if ((MFAST == 2) || (MFAST == 3)) Setf_memoS(DYNAMIC_FAST);
    
    /* Setup the structure using the internal flags */
    Init_memoS();
  }

#endif

  return;
}

void Set_preprocessing_flags(int *bary, int *negate)
{
#ifdef BARY
  *bary = 1;
#else
  *bary = 0;
#endif
  
#ifdef NEGATE
  *negate = 1;
#else
  *negate = 0;
#endif
  
  return;
}


void Translate_to_K(fnode_t *formula_fnode_ptr)
{
#ifdef ESAT
  Translate_from_E_to_K(formula_fnode_ptr);
#endif
}

int Skip_params(int argc, char **argv)
{
  int i;
  
  for(i = 1; i < argc; i++) 
    if (argv[i][0] != '-') break;

  return i;
}

void Help_and_exit(char **argv)
{
  printf("Welcome to *SAT, a platform for experimenting with SAT-based procedures!\n");
  printf("Usage: %s [<Options>] <Input_file>\n\n", argv[0]);
  printf("Options are:\n");
  printf("********** SPLITTING **********\n");
  printf("   -s<n>    : choose a different splitting heuristic (n = 1..6):\n");
  printf("               n = 1 MOM strategy to all active variables\n");
  printf("               n = 2 MOM strategy to all active variables in the\n"); 
  printf("                     shortest clauses\n");
  printf("               n = 3 choose the min variable in the first shortest\n");
  printf("                      clause (sign = CHOICE1)\n");
  printf("               n = 4 choose a variable in a shortest clause using\n");
  printf("                     occurrence as the second criterion (sign = CHOICE1)\n");
  printf("               n = 5 choose a variable with the highest occurrence\n");
  printf("                     (sign = CHOICE1)\n");
  printf("               n = 6 choose a variable with the highest occurence\n");
  printf("                     (sign = ?)\n");
  printf("   -l<n>    : choose a different MOM strategy (n = 1..3 - 11..13 - 21):\n");
  printf("               n < 11       original SATO weighting:\n");
  printf("                   n=1 sign =(neg_count>pos_count)? CHOICE1 : CHOICE2;\n");
  printf("                   n=2 sign = FF\n");
  printf("                   n=3 sign = TT\n");
  printf("               11 <= n < 21 clauses lenght does not matter (sign as n - 10)\n");
  printf("               n = 21       Boehm's weight and sign\n");
  printf("   -v       : splitting bias becomes CHOICE1 = TT, CHOICE2 = FF\n\n");

  printf("********** OPTIMIZATIONS (PROPOSITIONAL LOGIC ONLY!!)  **********\n");
  printf("   -p<n>    : enable pure literal detection     \n");
  printf("              n=1 on added variables only       \n");
  printf("              n=2 on any variable               \n");
  printf("   -g<n>    : enable propositional backjumping  \n");        
  printf("   -h       : enable relaxation to horn clauses \n\n");        

  printf("********** INTERNAL CNF CONVERSION **********\n");
  printf("   -k       : choose the conversion type\n");
  printf("              n=0 standard CNF conversion\n");
  printf("              n=1 optimized CNF conversion (also triggers -n, -p1)\n");
  printf("   -n       : pushing down negations\n");
  printf("   -d       : don't prefer splitting on independent variables\n\n");

  printf("********** MODAL LOGICS **********\n");
  printf("   -e<n>    : modal early pruning: 0 disable, 1 enable\n");   	
  printf("   -b<n>    : enable modal backjumping: 0 disable, 1 enable\n");
  printf("   -m<n>    : with n<=3 enable caching with a bit matrix:\n");
  printf("               n=1 enable caching of satisfiable subtests\n");
  printf("               n=2 enable caching of unsatisfiable subtests\n");
  printf("               n=3 enable both kinds of caching (2+1)\n");
  printf("              with n>3 enable caching with a hash table:\n");
  printf("               n=4 enable caching of satisfiable subtests\n");
  printf("               n=5 enable caching of unsatisfiable subtests\n");
  printf("               n=6 enable both kinds of caching\n");
  printf("   -w<n>    : cache memory size for a bit matrix (a multiple of 32 is good!)\n");
/*    printf("   -a<n>    : enable propositional relevance checking (FAST):\n");             */
/*    printf("               n=1                                     / alphas\n"); */
/*    printf("               n=2 discard propositionally irrelevant <  betas\n"); */
/*    printf("               n=3                                     \\ alphas and betas\n"); */
/*    printf("   -c<n>    : enable modal relevance checking (FAST):\n"); */
/*    printf("               n=1                             / alphas\n"); */
/*    printf("               n=2 discard modally irrelevant <  betas\n"); */
/*    printf("               n=3                             \\ alphas and betas\n"); */
/*    printf("   -t<n>    : if both -m and either -a or -c are active determines\n"); 
 */
/*    printf("   -t<n>    : if both -m and -a are active determines\n"); */
/*    printf("              the combination between FAST and consistency check/caching\n"); */
/*    printf("              (default is to use active FAST both for checking and storing):\n"); */
/*    printf("               n=1 use active FAST for searching in cache\n"); */
/*    printf("               n=2 use active FAST for consistency check (and storing)\n"); */

  printf("********** MISCELLANEA **********\n");
  printf("   -r<n>    : determines output level:\n");
  printf("               n=0 single line data without comments\n");
  printf("               n=1    \"     \"  \"   with comments\n");
  printf("               n=2 verbose output\n");
  printf("   -o<sec>  : enable a timeout (disable any timeout if 0)\n\n");

  printf("Defaults are: -s2 -l1 (CHOICE1 = FF, CHOICE2 = TT);\n");
  printf("              -g0, pure literal is on added variables only and\n");
  printf("              relaxation to horn cl. is disabled;\n");
  printf("              splitting on dependent variables is disabled,\n");
  printf("              cnf conversion is -k1, negations are pushed in;\n");
  printf("              early pruning is enabled, backjumping is disabled,\n");
  printf("              caching is -m3, -w512, timeout is -o1000, -r1.\n\n");
  
  exit (0);
}

void Display_results(monitor_t *monitor_ptr)
{
  if (VERBOSE == 2) {

    /* Verbosity level 2 ----------------------------------------------------- */
    printf("The formula was %s\n", (res ? "satisfiable" : "unsatisfiable"));
    printf("--------------------TIMINGS\n");
    printf("Parse time        %s\n", Print_clock(monitor_ptr, PARSE));
    printf("Preprocess time   %s\n", Print_clock(monitor_ptr, PREPROCESS));
    printf("Translate time    %s\n", Print_clock(monitor_ptr, TRANSLATE));
    printf("Build time        %s\n", Print_clock(monitor_ptr, BUILD));
    printf("Decision time     %s\n", Print_clock(monitor_ptr, DSAT));
    printf("--------------------GENERAL\n");
    printf("Consistency checks         %d\n", Get_param(monitor_ptr, REC_CALLS));
    printf("Failed consistency checks  %d\n", Get_param(monitor_ptr, MODFAIL_NUM));
    if (EARLY_JUMPING) {
      printf("Early Pruning (calls)      %d\n", Get_param(monitor_ptr, EP_CALLS));
      printf("Early Pruning (backtracks) %d\n", Get_param(monitor_ptr, EPFAIL_NUM));
    }
    if (BACK_JUMPING) {
      printf("Backjumping (calls)     %d\n", Get_param(monitor_ptr, BJ_CALLS));
      printf("Backjumping (backjumps) %d\n", Get_param(monitor_ptr, BJFAIL_NUM));
    } 
    printf("--------------------DAVIS PUTNAM\n");
    printf("Unit propagations  %d\n", Get_param(monitor_ptr, UNIT_NUM));
    printf("Pure literals      %d\n", Get_param(monitor_ptr, PURE_NUM));
    printf("Splits             %d\n", Get_param(monitor_ptr, SPLIT_NUM));
    printf("  on modal atoms   %d\n", Get_param(monitor_ptr, SPLIT_MOD_NUM));
    printf("  on added var.    %d\n", Get_param(monitor_ptr, SPLIT_DEP_NUM));
    printf("Assignments found  %d\n", Get_param(monitor_ptr, ASSIGN_NUM));
    printf("Bactracks          %d\n", Get_param(monitor_ptr, PROPFAIL_NUM));
    printf("--------------------CNF CONVERSION\n");
    printf("Added variables   %d\n", Laa(dag_ptr) - Lma(dag_ptr));
    if (Use_memoS()) {
      float t_ratio;

      printf("--------------------CACHING\n");
      printf("Cache accesses      %d\n", Stats_memoS(MEMO_ACCESS));
      printf("Cache successes     %d\n", Stats_memoS(MEMO_SUCCESS));
      printf("Total search time   %d (msec)\n", Time_memoS(MEMO_SEARCH_TIME));
      
      if (Stats_memoS(MEMO_STORAGE)) {
        t_ratio = 
          (float)(Stats_memoS(MEMO_TRASHING)) / (float)(Stats_memoS(MEMO_STORAGE));
      } else {
        t_ratio = 0.00; 
      }

      printf("Items stored        %d (trashing ratio %.2f)\n", 
	     Stats_memoS(MEMO_STORAGE), t_ratio);
      printf("Totale store time   %d (msec)\n", Time_memoS(MEMO_STORE_TIME));

      if (Getf_memoS(GET_DEPENDENCIES)) {
	printf("Dependencies tried  %d\n", Stats_memoS(DEP_ACCESS));
	printf("Dependencies found  %d\n", Stats_memoS(DEP_SUCCESS));
	printf("Total search time   %d (msec)\n", Time_memoS(DEP_SEARCH_TIME));

	if (Stats_memoS(DEP_STORAGE)) {
	  t_ratio = 
	    (float)(Stats_memoS(DEP_TRASHING)) / (float)(Stats_memoS(DEP_STORAGE));
	} else {
	  t_ratio = 0.00; 
	}
	printf("Dependecies stored  %d (trashing ratio %.2f)\n", 
	       Stats_memoS(DEP_STORAGE), t_ratio);
	printf("Total store time    %d (msec)\n", Time_memoS(DEP_STORE_TIME));
      }

      if (Getf_memoS(STATIC_FAST)) {
	printf("Attempts to prune alphas %d\n", Stats_memoS(SFAST_ACCESS));
	printf("Success in pruning alphas %d\n", Stats_memoS(SFAST_SUCCESS));
	printf("Time spent for searching %d (msec)\n", Time_memoS(SFAST_TIME));
	
	if (!Getf_memoS(GET_DEPENDENCIES)) {
	  if (Stats_memoS(DEP_STORAGE))
	    t_ratio = 
	      (float)(Stats_memoS(DEP_TRASHING)) / (float)(Stats_memoS(DEP_STORAGE));
	  else
	    t_ratio = 0.00;
	  printf("Static dependencies stored  %d (trashing ratio %.2f)\n", 
		 Stats_memoS(DEP_STORAGE), t_ratio);
	}
      }

      if (Getf_memoS(DYNAMIC_FAST)) {
	printf("Attempts to prune betas %d\n", Stats_memoS(DFAST_ACCESS));
	printf("Success in pruning betas %d\n", Stats_memoS(DFAST_SUCCESS));
	printf("Time spent for searching %d (msec)\n", Time_memoS(DFAST_TIME));

	printf("Dynamic dependencies stored  %d\n", Stats_memoS(DFAST_STORAGE));
      }

    }
    printf("--------------------MEMORY\n");
    printf("Maximum memory allocated by SATO               %d Kb\n", 
	   (Get_param(monitor_ptr, MAX_SATO_MEMORY) /1024));
    if (Use_memoS()) {
      printf("Total memory allocated for caching             %d Kb\n", (Stats_memoS(MEMORY) / 1024));
    }
    if (TIMEOUT == -1) printf("TIMEOUT WAS REACHED!!!!\n");

  } else if (VERBOSE == 1) {

    /* Verbosity level 1 ----------------------------------------------------- */
    Bare_display_params(monitor_ptr);
    Bare_display_results(monitor_ptr);
    
  } else {

    /* Verbosity level 0 ----------------------------------------------------- */
    Bare_display_results(monitor_ptr);

  }

  return;
}

void Bare_display_results(monitor_t *monitor_ptr)

{

  if (TIMEOUT == -1) res = -1;
  printf("%d, %s", res, Print_clock(monitor_ptr, BUILD));
  printf(", %s, %d, %d", Print_clock(monitor_ptr, DSAT),
	 Get_param(monitor_ptr, REC_CALLS), Get_param(monitor_ptr, MODFAIL_NUM));
  if (EARLY_JUMPING) {
    printf(", %d, %d", Get_param(monitor_ptr, EP_CALLS), Get_param(monitor_ptr, EPFAIL_NUM));
  }
  if (BACK_JUMPING) {
    printf(", %d, %d", Get_param(monitor_ptr, BJ_CALLS),  Get_param(monitor_ptr, BJFAIL_NUM));
  } 
  printf(", %d, %d, %d, %d, %d, %d, %d, %d",
	 Get_param(monitor_ptr, UNIT_NUM), Get_param(monitor_ptr, PURE_NUM), Get_param(monitor_ptr, SPLIT_MOD_NUM),
	 Get_param(monitor_ptr, SPLIT_DEP_NUM), Get_param(monitor_ptr, SPLIT_NUM), 
	 Get_param(monitor_ptr, ASSIGN_NUM), Get_param(monitor_ptr, PROPFAIL_NUM), 
	 (Laa(dag_ptr) - Lma(dag_ptr)));
  if (Use_memoS()) {
    float t_ratio;
    printf(", %d, %d", Stats_memoS(MEMO_ACCESS), Stats_memoS(MEMO_SUCCESS));
    printf(", %d", Time_memoS(MEMO_SEARCH_TIME));
    if (Getf_memoS(MEMO_STORAGE)) {
      t_ratio = 
	(float)(Stats_memoS(MEMO_TRASHING)) / (float)(Stats_memoS(MEMO_STORAGE));
    } else {
      t_ratio = 0.00; 
    }
    printf(", %d, %.2f, %d", Stats_memoS(MEMO_STORAGE), t_ratio, Time_memoS(MEMO_STORE_TIME));
    if (Getf_memoS(GET_DEPENDENCIES)) {
      printf(", %d, %d", Stats_memoS(DEP_ACCESS), Stats_memoS(DEP_SUCCESS));
      printf(", %d", Time_memoS(DEP_SEARCH_TIME));
      if (Stats_memoS(DEP_STORAGE)) {
	t_ratio = 
	  (float)(Stats_memoS(DEP_TRASHING)) / (float)(Stats_memoS(DEP_STORAGE));
      } else {
	t_ratio = 0.00; 
      }
      printf(" ,%d, %.2f, %d", Stats_memoS(DEP_STORAGE), t_ratio, Time_memoS(DEP_STORE_TIME));
    }
    if (Getf_memoS(STATIC_FAST)) {
      printf(", %d, %d", Stats_memoS(SFAST_ACCESS), Stats_memoS(SFAST_SUCCESS));
      printf(", %d", Time_memoS(SFAST_TIME));
      if (!Getf_memoS(GET_DEPENDENCIES)) {
	if (Stats_memoS(DEP_STORAGE))
	  if (Stats_memoS(DEP_STORAGE))
	    t_ratio = 
	      (float)(Stats_memoS(DEP_TRASHING)) / (float)(Stats_memoS(DEP_STORAGE));
	  else
	    t_ratio = 0.00;
	printf(" ,%d, %.2f", Stats_memoS(DEP_STORAGE), t_ratio);	
      }
      
    }
    if (Getf_memoS(DYNAMIC_FAST)) {
      printf(" ,%d, %d, %d", Stats_memoS(DFAST_ACCESS), Stats_memoS(DFAST_SUCCESS), Stats_memoS(DFAST_STORAGE));
      printf(", %d", Time_memoS(DFAST_TIME));
      
    }
  }
  printf(", %d", (Get_param(monitor_ptr, MAX_SATO_MEMORY) /1024));
  if (Use_memoS()) {
    printf(", %d", (Stats_memoS(MEMORY) / 1024));
  }
  printf("\n");

  return;
}

void Bare_display_params(monitor_t *monitor_ptr)
{
  printf("Sat, Btime, Dtime, ConsChecks, FConsChecks");
  
  if (EARLY_JUMPING) {
    printf(", EPcalls, EPbackts");
  }
  
  if (BACK_JUMPING) {
    printf(", BJcalls, BJbackts");
  } 
  
  printf(", Unit, Pure, MSplit, DSplit, TSplit, Assign, Backts, AddVar"); 
  
  if (Use_memoS()) {
    
    printf(", Macc, Msucc");
    printf(", MaTime");
    printf(", Mstore, Mtrash, MsTime");
    
    if (Getf_memoS(GET_DEPENDENCIES)) {
      printf(", Dacc, Dsucc");
      printf(", DaTime");
      printf(", Dstore, Dtrash, DsTime");
    }
    
    if (Getf_memoS(STATIC_FAST)) {
      printf(", Sacc, Ssucc");
      printf(", SdaTime");
      
      if (!Getf_memoS(GET_DEPENDENCIES)) {
        printf(", Dstore, Dtrash");
      }
      
    }
    
    if (Getf_memoS(DYNAMIC_FAST)) {
      printf(", Nacc, Nsucc, Nstore");
      printf(", NdaTime");
      
    }
  }
  printf(", MaxMem");
  if (Use_memoS()) {
    printf(", CacheMem");
  }
  printf("\n");
}


/* Setting defaults and parsing modal/preprocessing data only */
void Preparse_cmd_line(int argc, char **argv)
{
    int i, temp;

    CNF_CONV = OPT_CONVERSION;  /* Default is: optimized cnf conversion */

    for(i = 1; i < argc; i++) 
      if (argv[i][0] == '-')  {
	temp = str_int(argv[i], 2);

	if (argv[i][1] == 'k') {
	  CNF_CONV = temp;
	} else if (argv[i][1] == 'n') {
	  NNF_CONV = 1;
	} else if (argv[i][1] == 'f') {
	  LANGUAGE = temp;
	} 
      }

    /* When the optimized conversion is requested... */
    if (CNF_CONV == OPT_CONVERSION) {
      NNF_CONV = 1;                 /* Negations MUST be pushed down */
      LANGUAGE = NCDE;              /* The language MUST allow for equivalences */
      PURE_HEUR = 1;                /* Pure literal is allowed on dependent variables */
    } else {
      PURE_HEUR = 0;                /* Pure literal rule is disabled */
    }

    return;
}

void Purge_comments()
{
  int ch;

  /* Purge lines of comments */
  while ((ch = getc(stdin)) == '%')
    ch = skip_chars_until(stdin, '\n');
  /* Rstore first non-comment character read */
  ch = ungetc(ch,stdin);
  
  return;
}
  
