/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE table.c - *SAT 1.3 */
/*  Memoizing with a sparse matrix */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "table.h"

/* The memoizing table is a global variable */
#ifdef OPTIMIZE
static int **TABLE_int;
#else
static sm_matrix_t *TABLE_sm_matrix_ptr;
#endif


/* *********************************************************************** */
/* Initialize and clear the memoizing table */
/* *********************************************************************** */

void Init_memoT(int dim)
{
#ifdef OPTIMIZE
  int i,j;
  TABLE_int = ALLOC(int*,dim);
  for (i = 0; i < dim; i++) {
    TABLE_int[i] = ALLOC(int,dim);
    for (j = 0; j < dim; j++)
      TABLE_int[i][j] = TEST_FAIL;
  }
#else
  TABLE_sm_matrix_ptr = sm_alloc();
#endif
  return;
}

void Clear_memoT(dim)
{
#ifdef OPTIMIZE
  int i;
  for (i = 0; i < dim; i++)
    FREE(TABLE_int[i]);
  FREE(TABLE_int);
#else
  sm_free(TABLE_sm_matrix_ptr);
#endif
  return;
}

void Force_no_memoT()
{
#ifdef OPTIMIZE
  TABLE_int = NULL;
#else
  TABLE_sm_matrix_ptr = NIL(sm_matrix_t);
#endif
  return;
}

/* *********************************************************************** */
/* Accessing the structure */
/* *********************************************************************** */
int Use_memoT()
{
#ifdef OPTIMIZE
  return (TABLE_int != NULL);
#else
  return (TABLE_sm_matrix_ptr != NIL(sm_matrix_t));
#endif
}

int Test_memoT(int alpha, int beta)
{
#ifdef OPTIMIZE
  return TABLE_int[alpha][beta];
#else
  int res;
  sm_element_t *sm_element_ptr; 

  sm_element_ptr = sm_find(TABLE_sm_matrix_ptr, alpha, beta);
  if (sm_element_ptr == NULL)
    res = TEST_FAIL;
  else
    res = UNCAST_RESULT(Cell_value((sm_element_ptr)));

  return res;
#endif
}

void Store_memoT(int alpha, int beta, int res)
{
#ifdef OPTIMIZE
  TABLE_int[alpha][beta] = res;
#else
  sm_element_t *sm_element_ptr;

  sm_element_ptr = sm_insert(TABLE_sm_matrix_ptr, alpha, beta);
  Cell_value(sm_element_ptr) = CAST_RESULT(res);
#endif
  return;
}








