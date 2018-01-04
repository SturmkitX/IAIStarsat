/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE dp_sat.h - *SAT 1.3 */
/*  SAT-based modal satisfiability */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

/* GLU modules */
#include "util.h"
#include "array.h"
#include "list.h"
#include "graph.h" 
#include "st.h"

/* *SAT modules */
#include "dag.h"
#include "common_sat.h"

/* SATO decision procedure */
#include "satotrie.h"

#ifndef DP_SAT
#define DP_SAT

/* Valuation for atoms */
#define VALUATE(value, sign)     (value * sign)
#define UNVALUATE(value)         ((value < 0) ? (value * -1) : value)

/* Castings for cnfs */
#define CAST_CLAUSE_ITEM(lsList_ptr) ((lsGeneric) (lsList_ptr))
#define UNCAST_CLAUSE_ITEM(gen)      ((lsList*) (gen))
#define CAST_LITERAL_ITEM(literal)   ((lsGeneric) (literal))
#define UNCAST_LITERAL_ITEM(gen)     ((int) (gen))

/* Castings for cnf_info */
#define CAST_CNF_INFO(cnf_info_ptr) ((char*) (cnf_info_ptr))
#define UNCAST_CNF_INFO(gen) ((cnf_info_t*) (gen))

/* Select the policy to convert xref item dags into cnfs.
   Root vertex is ALWAYS converted in Init_cnf_sat.
*/
#define EAGER_CNF_CONV 0   /* Convert them while running Test_cnf_sat */
#define GREEDY_CNF_CONV 1  /* Convert them while running Init_cnf_sat */

/* The sign of the cnf to get
   Polarities for optimized CNF conversion
*/
#define NEG_CNF -1          /* Get pointer to the neg cnf (negative polarity) */
#define BOTH_CNF 0          /* Both polarities */
#define POS_CNF  1          /* Get pointer to the pos cnf (positive polarity) */

/* The record holding the added atom and the corresponding clauses for 
   every subformula.
*/
typedef struct cnf_info {
  int    b_value;
  lsList *pos_added_lsList_ptr;
  lsList *neg_added_lsList_ptr;
} cnf_info_t;

/* Agent data structure: agents are checked separately so some kind of
   classification should occur since every agent has its own alphas and
   betas in the assignment 
*/
typedef struct agent {
  lsList *alpha_lsList_ptr;
  lsList *beta_lsList_ptr;
} agent_t;

/* Casting for agents */
#define CAST_AGENT(agent_ptr) ((stGeneric) (agent_ptr))
#define UNCAST_AGENT(gen)     ((agent_t*) (gen))


/* *********************************************************************** */
/* Initialization of the decision process */
/* *********************************************************************** */

/* Call this before attempting to run any module in this box! */
image_t  *Init_cnf_sat(dag_t *dag_ptr, int flag_conv);

/* This works for recursion */
image_t *Init_cnf_sat_rec(dag_t *dag_ptr, lsList *to_test_lsList_ptr);

/* *********************************************************************** */
/* Translation of dags into cnfs */
/* *********************************************************************** */

/* The xref information associated to a_vertex_ptr is scanned. If the requested
   cnf is already there then the pointer is returned, otherwise it is built.
   Make_cnf thus works transparently with different conversion policies. The sign 
   of the cnf to build or to return is determined by the flag sign. When the first
   cnf is built information regarding variables is suitably updated 
*/
lsList *Make_cnf(dag_t *dag_ptr, vertex_t *a_vertex_ptr, int sign);

/* *********************************************************************** */
/* Main decision procedure */
/* *********************************************************************** */
/* This starts the decision algorithm on the root vertex of dag_ptr.
   The procedure works the same for many logics since its behaviour 
   is influenced only by the function Test_star_consistency

   Test_star_consistency functions should take image_ptr and dag_ptr
   as parameters.

   and they should return 1 if the assignment containing the alphas
   and betas is consistent in the given logic, 0 otherwise.
*/
int Test_dp_sat(image_t *image_ptr, dag_t *dag_ptr,
		 Cons_func_ptr_t Test_star_consistency);

/* The recursive version: exported for the sake of consistency checking functions
*/
int Test_dp_sat_rec(image_t *image_ptr, dag_t *dag_ptr,
		    lsList *formula_lsList_ptr,
		    Cons_func_ptr_t Test_star_consistency);

/* *********************************************************************** */
/* Utilities for consistency checking */
/* *********************************************************************** */
/* Merge two lists of clauses */
lsList *Merge_formulae_to_new(lsList *first_lsList_ptr, lsList *second_lsList_ptr); 
void Merge_formulae(lsList *formula_lsList_ptr, lsList *added_lsList_ptr);

/* Swap two lists of clauses */
void Swap_formulae(lsList **first_lsList_ptr_ptr, lsList **second_lsList_ptr_ptr);  

/* Form the conjunction between the cnfs of each alpha */
lsList *Make_cnf_conj(dag_t *dag_ptr, lsList *alpha_lsList_ptr); 

/* *********************************************************************** */
/* Output routines */
/* *********************************************************************** */
void Print_cnf(lsList *formula_lsList_ptr);
void Print_single_call(vertex_t *beta_vertex_ptr, lsList *to_test_lsList_ptr);
void Print_simple_call(vertex_t *alpha_vertex_ptr, vertex_t *beta_vertex_ptr,
		       lsList *to_test_lsList_ptr);
void Print_complex_call(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr, 
			lsList *to_test_lsList_ptr);
void Print_alpha_beta(lsList *alpha_lsList_ptr, vertex_t *beta_vertex_ptr); 
void Print_alpha(lsList *alpha_lsList_ptr);
			
/* *********************************************************************** */
/* Utilities about cnf_info */
/* *********************************************************************** */
cnf_info_t *New_cnf_info(int b_value);

#define V_AUX(vertex)           \
((cnf_info_t*) (V_aux(vertex)))

#define b_value(cnf_info_ptr) \
(cnf_info_ptr->b_value)

#define pos_added_lsList_ptr(cnf_info_ptr) \
(cnf_info_ptr->pos_added_lsList_ptr)

#define neg_added_lsList_ptr(cnf_info_ptr) \
(cnf_info_ptr->neg_added_lsList_ptr)

/* *********************************************************************** */
/* Agents management & relevance checking */
/* *********************************************************************** */
agent_t *New_agent();
void    Clear_agent(stGeneric t_stGeneric);

#define Alpha_lsList_ptr(agent_ptr) \
(agent_ptr->alpha_lsList_ptr)
#define Beta_lsList_ptr(agent_ptr) \
(agent_ptr->beta_lsList_ptr)

/* Classify alphas and betas in mu according to different agents;
*/
void Classify_agents(image_t *image_ptr, dag_t *dag_ptr,
		     st_table *agents_st_table_ptr);
void Classify_agents_light(image_t *image_ptr, dag_t *dag_ptr,
			   st_table *agents_st_table_ptr);

/* Test for relevance */
lsList *Copy_relevant_atoms(image_t *image_ptr, lsList *source_lsList_ptr);
lsList *Keep_relevant_atoms(image_t *image_ptr, lsList *source_lsList_ptr);

/* Propositional relevance checking: */
#define Test_relevance(stack_table, value_table, idx) \
((stack_table[idx].f <= SP) \
|| ((stack_table[idx].f == SPP) && (value_table[UNVALUATE(stack_table[idx].v)] == TT)) \
|| ((stack_table[idx].f == SPN) && (value_table[UNVALUATE(stack_table[idx].v)] == FF)))     

/* Select atoms in between the bound */
#define Test_bound(cur_atom, lbound, hbound) ((cur_atom >= lbound) && (cur_atom <= hbound)) 

/* *********************************************************************** */
/* Evaluation of cnfs */
/* *********************************************************************** */

/* This function checks whether the assignment mu_st_table_ptr satisfies
   formula_lsList_ptr or not. Returns 1 if mu satisfies it, 0
   if mu does not satisfy it, -1 if mu could not completely
   simplify it. */
int Eval_cnf(lsList *formula_lsList_ptr, st_table *mu_st_table_ptr);
/* This function simplifies the formula under the assignment */
lsList *Assign_cnf(lsList *formula_lsList_ptr, int *mu_table_ptr);
/* This function simplifies the formula under the assignment */
lsList *Assign_cnf2(lsList *formula_lsList_ptr, st_table *mu_st_table_ptr);

/* Completely destroy a CNF */
void Free_cnf(lsList *formula_lsList_ptr); 

/* Buffer for clauses */
#define BUFDIM 5000
/* This function reads a stream of literals and returns the pointer to the list */
st_table *Parse_model(FILE *model_file);
/* This function reads a DIMACS file and returns the cnf */
lsList *Parse_cnf(FILE *cnf_file);

#endif





