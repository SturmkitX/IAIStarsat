/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE addglu.h - *SAT 1.3 */
/*  Additional definitions for GLU libraries */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "list.h"

#ifndef ADDGLU
#define ADDGLU

/* Generic pointer for hash tables */
typedef char* stGeneric;

#define lsForEachItemRev(                                      \
  list,  /* lsList, list to iterate */                         \
  gen,   /* lsGen, local variable for iterator */              \
  data   /* lsGeneric, variable to return data */              \
)				                               \
  for(gen = lsEnd(list); 				       \
      (lsPrev(gen, (lsGeneric *) &data, LS_NH) == LS_OK)       \
      || ((void) lsFinish(gen), 0);                            \
      )

#endif
