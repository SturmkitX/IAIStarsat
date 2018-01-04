/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE table.h - *SAT 1.3 */
/*  Memoizing with a sparse matrix */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include <malloc.h>

#include "util.h"
#include "sparse_int.h"
#include "sparse.h"

#ifndef TABLE
#define TABLE

#define TEST_SAT    1
#define TEST_UNSAT  0
#define TEST_FAIL  -1

/* Types 
 */
typedef sm_element sm_element_t;
typedef sm_matrix  sm_matrix_t;

/* Casting 
*/
#define CAST_RESULT(res)   ((char*) (res))
#define UNCAST_RESULT(gen) ((int) (gen)) 


/* *********************************************************************** */
/* Initialize and clear the memoizing table */
/* *********************************************************************** */
void Init_memoT(int dim);
void Clear_memoT(int dim);
void Force_no_memoT();

/* *********************************************************************** */
/* Accessing the structure */
/* *********************************************************************** */
/* Test if the matrix is being used; return 1 if so, 0 otherwise */
int Use_memoT();

/* Test a single element: 
   - if the element is there, the return value is either 
     TEST_SAT or TEST_UNSAT
   - if the element is not there, the return value is TEST_FAIL;
*/
int Test_memoT(int alpha, int beta);

/* Store a single element: a new location at alpha,beta is crated and the value
   is stored.
*/
void Store_memoT(int alpha, int beta, int res);

/* *********************************************************************** */
/* Accessing the matrix */
/* *********************************************************************** */
#define EMPTY_CELL  NIL(char)

#define Cell_value(sm_element_ptr) \
(sm_element_ptr->user_word) 



#endif




