/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE common_sat.h - *SAT 1.3 */
/*  Common definitions for decision procedures */

/*  *********************************************************************** */
/*  *********************************************************************** */

#ifndef COMMON_SAT
#define COMMON_SAT

/* Consistency checking functions
*/
typedef int (*Cons_func_ptr_t)();

/* Spreading atoms: you might wish to avoid zero! 
*/
#define SPREAD(original_value)   (original_value + 1)
#define UNSPREAD(spreaded_value) (spreaded_value - 1)

#endif


