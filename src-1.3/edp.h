/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE edp.h - *SAT ver. 1.3 */
/*  Consistency check in logic */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "dp_sat.h"
#include "table.h"

/* Uncommment this to get debugging information */
/*  #define TRACE_CONS  */

/* *********************************************************************** */
/* The function for testing E consistency of an assignment */
/* *********************************************************************** */

/* This function applies the rule:
   
   ESAT(/\_i []alpha_i & /\ -[]beta_j) <=> 
      forall j forall i ( ESAT(alpha_i & -beta_j) or ESAT(-alpha_i & beta_j) )

   The function handles multiagent reasoning. The intermediate results might
   be memoized using a table.
*/
int Test_E_consistency(image_t *cur_image_ptr, dag_t *dag_ptr);


/* *********************************************************************** */
/* Macros */
/* *********************************************************************** */
#define IF_RELEVANT_MODAL_ATOM \
cur_atom = UNVALUATE(Stack(cur_image_ptr)[i].v);\
if (Test_relevance(Stack(cur_image_ptr), Value(cur_image_ptr), i) &&\
    Test_bound(cur_atom, first_modal_atom, last_modal_atom)) {\
  cur_vertex_ptr = Xref_vertex_ptr_table(dag_ptr)[UNSPREAD(cur_atom)];\
  if (V_value(V_ini_vertex_ptr(cur_vertex_ptr)) == ag_num) {

#define END_IF } }
