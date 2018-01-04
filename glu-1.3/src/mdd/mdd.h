#ifndef MDD_DEFINED
#define MDD_DEFINED


#include "util.h"
#include "array.h"
#include "st.h"
#include "var_set.h"

#include "bdd.h" 

/*    #include "bdd_int.h"   */

/************************************************************************/
#define str_len         10
#define MONITOR         0
#define VERBOSE         0
#define SOLUTION        0
#define BDD_SIZE        1
#define USE_ITE         1
#define BYPASS          1
/* code may not be fully debugged for interleaving */
#define INTERLEAVE      0

#define mdd_and bdd_and
#define mdd_cofactor_minterm bdd_cofactor
#define mdd_constant bdd_constant
#define mdd_dup bdd_dup
/* mdd_equal returns 1 if two MDD's are identical */
/* mdd_eq is a totally different function */
/* which returns an MDD instead */
#define mdd_equal bdd_equal
#define mdd_free bdd_free
#define mdd_get_manager bdd_get_manager
#define mdd_is_tautology bdd_is_tautology
#define mdd_ite bdd_ite
/* mdd_lequal checks for implication, */
/* mdd_lequal(f,g,1,0) returns the value of (f => g') */
/* mdd_leq is a totally different function */
#define mdd_lequal bdd_leq
#define mdd_not bdd_not
#define mdd_one bdd_one
#define mdd_or bdd_or
#define mdd_size bdd_size
#define mdd_size_multiple bdd_size_multiple
#define mdd_top_var_id bdd_top_var_id
#define mdd_xor bdd_xor
#define mdd_xnor bdd_xnor
#define mdd_zero bdd_zero
#define mdd_EMPTY bdd_EMPTY

#define mdd_first_solution mdd_first_cube
#define mdd_next_solution mdd_next_cube

#define mdd_eq_c(m,a,b)  	mdd_func1c(m,a,b,eq2)
#define mdd_geq_c(m,a,b) 	mdd_func1c(m,a,b,geq2)
#define mdd_gt_c(m,a,b)  	mdd_func1c(m,a,b,gt2)
#define mdd_leq_c(m,a,b) 	mdd_func1c(m,a,b,leq2)
#define mdd_lt_c(m,a,b)  	mdd_func1c(m,a,b,lt2)
#define mdd_neq_c(m,a,b) 	mdd_func1c(m,a,b,neq2)

#define mdd_eq(m,a,b)  		mdd_func2(m,a,b,eq2)
#define mdd_geq(m,a,b) 		mdd_func2(m,a,b,geq2)
#define mdd_gt(m,a,b)  		mdd_func2(m,a,b,gt2)
#define mdd_leq(m,a,b) 		mdd_func2(m,a,b,leq2)
#define mdd_lt(m,a,b)  		mdd_func2(m,a,b,lt2)
#define mdd_neq(m,a,b) 		mdd_func2(m,a,b,neq2)
#define mdd_unary_minus(m,a,b) 	mdd_func2(m,a,b,unary_minus2)

#define mdd_eq_plus(m,a,b,c)	mdd_func3(m,a,b,c,eq_plus3)
#define mdd_geq_plus(m,a,b,c)	mdd_func3(m,a,b,c,geq_plus3)
#define mdd_gt_plus(m,a,b,c)	mdd_func3(m,a,b,c,gt_plus3)
#define mdd_leq_plus(m,a,b,c)	mdd_func3(m,a,b,c,leq_plus3)
#define mdd_lt_plus(m,a,b,c)	mdd_func3(m,a,b,c,lt_plus3)
#define mdd_neq_plus(m,a,b,c)	mdd_func3(m,a,b,c,neq_plus3)

#define mdd_eq_minus(m,a,b,c)	mdd_func3(m,a,b,c,eq_minus3)
#define mdd_geq_minus(m,a,b,c)	mdd_func3(m,a,b,c,geq_minus3)
#define mdd_gt_minus(m,a,b,c)	mdd_func3(m,a,b,c,gt_minus3)
#define mdd_leq_minus(m,a,b,c)	mdd_func3(m,a,b,c,leq_minus3)
#define mdd_lt_minus(m,a,b,c)	mdd_func3(m,a,b,c,lt_minus3)
#define mdd_neq_minus(m,a,b,c)	mdd_func3(m,a,b,c,neq_minus3)

#define mdd_eq_plus_c(m,a,b,c)	mdd_func2c(m,a,b,c,eq_plus3)
#define mdd_geq_plus_c(m,a,b,c)	mdd_func2c(m,a,b,c,geq_plus3)
#define mdd_gt_plus_c(m,a,b,c)	mdd_func2c(m,a,b,c,gt_plus3)
#define mdd_leq_plus_c(m,a,b,c)	mdd_func2c(m,a,b,c,leq_plus3)
#define mdd_lt_plus_c(m,a,b,c)	mdd_func2c(m,a,b,c,lt_plus3)
#define mdd_neq_plus_c(m,a,b,c)	mdd_func2c(m,a,b,c,neq_plus3)


#define mdd_eq_plus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,eq_plus3mod)
#define mdd_geq_plus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,geq_plus3mod)
#define mdd_gt_plus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,gt_plus3mod)
#define mdd_leq_plus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,leq_plus3mod)
#define mdd_lt_plus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,lt_plus3mod)
#define mdd_neq_plus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,neq_plus3mod)

#define mdd_eq_minus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,eq_minus3mod)
#define mdd_geq_minus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,geq_minus3mod)
#define mdd_gt_minus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,gt_minus3mod)
#define mdd_leq_minus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,leq_minus3mod)
#define mdd_lt_minus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,lt_minus3mod)
#define mdd_neq_minus_c_mod(m,a,b,c)	mdd_func2c_mod(m,a,b,c,neq_minus3mod)

#define mdd_eq_s(m,a,b) 	mdd_ineq_template_s(m,a,b,0,0,1)
#define mdd_geq_s(m,a,b) 	mdd_ineq_template_s(m,a,b,0,1,1)
#define mdd_gt_s(m,a,b)		mdd_ineq_template_s(m,a,b,0,1,0)
#define mdd_neq_s(m,a,b)	mdd_ineq_template_s(m,a,b,1,1,0)
#define mdd_leq_s(m,a,b)	mdd_ineq_template_s(m,a,b,1,0,1)
#define mdd_lt_s(m,a,b)		mdd_ineq_template_s(m,a,b,1,0,0)

/**** for backward compatibility only ****/
#define mdd_eq_g(m,a,b)  	mdd_func2(m,a,b,eq2)
#define mdd_geq_g(m,a,b) 	mdd_func2(m,a,b,geq2)
#define mdd_gt_g(m,a,b)  	mdd_func2(m,a,b,gt2)
#define mdd_leq_g(m,a,b) 	mdd_func2(m,a,b,leq2)
#define mdd_lt_g(m,a,b)  	mdd_func2(m,a,b,lt2)
#define mdd_neq_g(m,a,b) 	mdd_func2(m,a,b,neq2)
#define mdd_init_name(v,n,s) 	mdd_init(v,n,s)

/* mdd_int.h */
#define MDD_NOT(node)           ((bdd_node *) ((int) (node) ^ 01))
#define MDD_REGULAR(node)       ((bdd_node *) ((int) (node) & ~01))
#define MDD_IS_COMPLEMENT(node) ((int) (node) & 01)

#define MDD_ONE(bdd)            (bdd)->one
#define MDD_ZERO(bdd)           (MDD_NOT(MDD_ONE(bdd)))

#ifndef MAX
#define MAX(a,b) (a) > (b) ? (a) : (b)
#endif

#ifndef MIN
#define MIN(a,b) (a) < (b) ? (a) : (b)
#endif

    typedef struct bdd_t mdd_t;
    typedef struct bdd_manager mdd_manager;

typedef enum {
	MDD_ACTIVE,
	MDD_BUNDLED
} mvar_status;

struct mvar_type {
    int mvar_id;		/* mvar id */
    mvar_status status;         /* Whether the mvar is currently being used or 
                                   has been bundled into another mvar */
    char *name;			/* name of mvar */
    int values;			/* no. of values mvar can take */
    int encode_length;		/* no. of binary variables, bvar's, */
				/* needed to encode mvar */
    array_t *bvars;             /* array of bvar_id's from most significant bit to least 
				   significant bit, has size encode_length */
    int *encoding;		/* internal use only */
};
typedef struct mvar_type mvar_type;

struct bvar_type {
    mdd_t *node;
    int mvar_id;
};
typedef struct bvar_type bvar_type;

struct mdd_hook_type {
    array_t *mvar_list;
    array_t *bvar_list;	
};

typedef struct mdd_hook_type mdd_hook_type;

struct mdd_gen {
    mdd_manager *manager;
    bdd_gen *bdd_gen;
    bdd_gen_status status;
    array_t *cube;		/* array of literals {0,1,2} of all vars */
    array_t *minterm;		/* current minterm */
    array_t *var_list;		/* list of var id's */
    boolean out_of_range;
}; 

typedef struct mdd_gen mdd_gen;

#define foreach_mdd_minterm(fn, gen, minterm, var_list)\
  for((gen) = mdd_first_minterm(fn, &minterm, var_list);\
      ((gen)->status != bdd_EMPTY) ? TRUE: mdd_gen_free(gen);\
      (void) mdd_next_minterm(gen, &minterm))
                                                                      

extern mdd_hook_type mdd_hook;

/* external functions */
EXTERN mdd_manager *mdd_init ARGS(());
EXTERN mdd_manager *mdd_init_empty ARGS(());
EXTERN unsigned int mdd_create_variables ARGS(());
EXTERN unsigned int mdd_create_variables_after
       ARGS((mdd_manager*, int, array_t*, array_t*, array_t* ));
EXTERN unsigned int mdd_create_variables_interleaved
       ARGS((mdd_manager*, int, int, array_t*));
EXTERN void mdd_quit ARGS(());
EXTERN mdd_t *mdd_case ARGS(());
EXTERN mdd_t *mdd_consensus ARGS(());
EXTERN mdd_t *mdd_encode ARGS(());
EXTERN mdd_t *mdd_literal ARGS(());
EXTERN void   mdd_search ARGS(());
EXTERN mdd_t *mdd_cofactor ARGS(());
EXTERN mdd_t *mdd_smooth ARGS(());
EXTERN mdd_t *mdd_and_smooth ARGS(());
EXTERN mdd_t *mdd_substitute ARGS(());
EXTERN array_t *mdd_get_support ARGS(());
EXTERN mdd_t *mdd_interval ARGS(()); 
EXTERN double mdd_count_onset ARGS(());
EXTERN array_t *mdd_ret_arr_bin_vars ARGS(());
EXTERN mdd_t *mdd_cproject ARGS(());
EXTERN mdd_t *mdd_mod ARGS((mdd_manager *mgr, int a_mvar_id, int b_mvar_id, int M));
EXTERN mdd_t *mdd_ineq_template_s ARGS((mdd_manager *mgr, int mvar1, int mvar2,  
								int zero_then_val, int one_else_val, int bottom_val));
EXTERN mdd_t *mdd_add_s ARGS((mdd_manager *mgr, int sum_id, int mvar_id1, int mvar_id2 ));
/* mdd_iter.c */
EXTERN mdd_gen *mdd_first_minterm ARGS((mdd_t *f, array_t **minterm_p, 
	array_t *var_list));
EXTERN boolean mdd_next_minterm ARGS((mdd_gen *mgen, array_t **minterm_p));
EXTERN void mdd_print_array ARGS((array_t *array));
EXTERN int mdd_gen_free ARGS((mdd_gen *mgen));

EXTERN mdd_t *mdd_func1c ARGS((mdd_manager *mgr, int mvar1, int mvar2, 
	boolean (*func1c) (int, int)));

EXTERN mdd_t *mdd_func2 ARGS((mdd_manager *mgr, int mvar1, int mvar2, 
	boolean (*func2) (int, int)));
/* functions of 2 variables used by mdd_func2 ARGS(()) */
EXTERN boolean eq2 ARGS((int x, int y));
EXTERN boolean geq2 ARGS((int x, int y));
EXTERN boolean gt2 ARGS((int x, int y));
EXTERN boolean leq2 ARGS((int x, int y));
EXTERN boolean lt2 ARGS((int x, int y));
EXTERN boolean neq2 ARGS((int x, int y));
EXTERN boolean unary_minus2 ARGS((int x, int y));

EXTERN mdd_t *mdd_func2c ARGS((mdd_manager *mgr,int mvar1, int mvar2, 
			       int constant, boolean (*func2c)(int, int, int)));

EXTERN mdd_t *mdd_func2c_mod ARGS((mdd_manager *mgr,int mvar1, int mvar2, 
			       int constant, boolean (*func3c)(int, int, int, int)));

/* should be in ../test */
EXTERN mdd_t *mdd_func3 ARGS((mdd_manager *mgr, int mvar1, int mvar2, int mvar3,
	boolean (*func3)(int, int, int)));
/* functions of 3 variables used by mdd_func3 ARGS(()) */
EXTERN boolean eq_plus3 ARGS((int x, int y, int z));
EXTERN boolean geq_plus3 ARGS((int x, int y, int z));
EXTERN boolean gt_plus3 ARGS((int x, int y, int z));
EXTERN boolean leq_plus3 ARGS((int x, int y, int z));
EXTERN boolean lt_plus3 ARGS((int x, int y, int z));
EXTERN boolean neq_plus3 ARGS((int x, int y, int z));
/* actually functions below can be obtained from the set above */
/* by just suppling the negation of the constant value */
EXTERN boolean eq_minus3 ARGS((int x, int y, int z));
EXTERN boolean geq_minus3 ARGS((int x, int y, int z));
EXTERN boolean gt_minus3 ARGS((int x, int y, int z));
EXTERN boolean leq_minus3 ARGS((int x, int y, int z));
EXTERN boolean lt_minus3 ARGS((int x, int y, int z));
EXTERN boolean neq_minus3 ARGS((int x, int y, int z));

EXTERN array_t *mdd_id_to_bdd_id_array(mdd_manager *mddManager, int mddId);
EXTERN array_t *mdd_id_to_bdd_array(mdd_manager *mddManager, int mddId);
EXTERN array_t *mdd_id_array_to_bdd_array(mdd_manager *mddManager, array_t *mddIdArray);
EXTERN array_t *mdd_id_array_to_bdd_id_array(mdd_manager *mddManager, array_t *mddIdArray);
EXTERN array_t *mdd_fn_array_to_bdd_rel_array(mdd_manager *mddManager, int mddId, array_t *mddFnArray);
EXTERN array_t *mdd_pick_arbitrary_minterms(mdd_manager *mgr, mdd_t *f, array_t *mddIdArr, int n);
EXTERN mvar_type mdd_get_var_by_id(mdd_manager *mddMgr, int id);

EXTERN boolean eq_plus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean geq_plus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean gt_plus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean leq_plus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean lt_plus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean neq_plus3mod ARGS((int x, int y, int z, int range));
/* actually functions below can be obtained from the set above */
/* by just suppling the negation of the constant value */
EXTERN boolean eq_minus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean geq_minus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean gt_minus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean leq_minus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean lt_minus3mod ARGS((int x, int y, int z, int range));
EXTERN boolean neq_minus3mod ARGS((int x, int y, int z, int range));

/* should be in ../test */
EXTERN mdd_t *mdd_process_constr ARGS(()); 
EXTERN mdd_t *mdd_fast_constr ARGS(()); 

/* should be in mdd_int.h */
EXTERN int toggle ARGS(());
EXTERN int no_bit_encode ARGS(());
EXTERN void print_strides ARGS(());
EXTERN void print_mvar_list ARGS(());
EXTERN void print_bdd_list_id ARGS(());
EXTERN void print_bvar_list_id ARGS(());
EXTERN void print_bdd ARGS(());
EXTERN mvar_type find_mvar_id ARGS(());
EXTERN void clear_all_marks ARGS(());
EXTERN void mdd_mark ARGS(());
EXTERN void mdd_unmark ARGS(());
EXTERN mvar_type find_mvar ARGS(());
EXTERN array_t *mdd_ret_mvar_list ARGS(());
EXTERN array_t *mdd_ret_bvar_list ARGS(());
EXTERN mdd_t *build_lt_c ARGS(());
EXTERN mdd_t *build_leq_c ARGS(());
EXTERN mdd_t *build_gt_c ARGS(());
EXTERN mdd_t *build_geq_c ARGS(());
EXTERN int num_bits ARGS(());
EXTERN int getbit ARGS(());
EXTERN int integer_get_num_of_digits ARGS(());
EXTERN int mdd_ret_bvar_id ARGS(());
EXTERN bvar_type mdd_ret_bvar ARGS(());
EXTERN void mdd_array_free ARGS((array_t *));
EXTERN array_t *mdd_array_duplicate ARGS((array_t *));
#endif


