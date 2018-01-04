/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE kdp.h - *SAT 1.3 */
/*  Consistency check in logic K */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "dp_sat.h"
#include "monitor.h"
#include "set.h"

/* Constants for dynamic backtracking */
#define NO_JUMP -1

/* *********************************************************************** */
/* The function for testing K consistency of an assignment */
/* *********************************************************************** */

/* This function applies the rule:
   
   KSAT(/\_i []alpha_i & /\ -[]beta_j) <=> 
      forall j KSAT((/\_i alpha_i) & -beta_j)

   The function handles multiagent reasoning by classifying alphas and betas
   in as many groups as agents are; alphas and betas are then checked
   independently for each agent.
*/
int Test_K_consistency(image_t *cur_image_ptr, dag_t *dag_ptr);


/* *********************************************************************** */
/* Macros */
/* *********************************************************************** */
#define IF_MODAL_ATOM \
cur_atom = UNVALUATE(Stack(cur_image_ptr)[i].v);\
if (Test_bound(cur_atom, first_modal_atom, last_modal_atom)) {\
  cur_vertex_ptr = Xref_vertex_ptr_table(dag_ptr)[UNSPREAD(cur_atom)];\
  if (V_value(V_ini_vertex_ptr(cur_vertex_ptr)) == ag_num) {

#define END_IF } }


