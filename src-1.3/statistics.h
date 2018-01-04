/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE statistics.h - *SAT 1.3 */
/*  Statistics on the modal formula */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

/* GLU modules */
#include "util.h"
#include "array.h"
#include "list.h"
#include "graph.h" 
#include "var_set.h"

/* *SAT modules */
#include "dag.h"
#include "common_sat.h"

#ifndef STATISTICS
#define STATISTICS 

/* Maximum modal depth handled by statistics */
#define MAX_DEPTH 1 << 10

/* Statistics main data structure */
typedef struct statistics {
  int       moffset;    /* Offset to modal atoms */
  var_set_t **matoms;   /* Modal atoms for each level */
  int       max_depth;  /* Maximum modal depth */
  int       size;       /* Number of nodes visited */
} statistics_t;

/* Initialize and compute statistics */
statistics_t *Compute_statistics(dag_t *dag_ptr);

/* Print out statistics */
void Print_statistics(dag_t *dag_ptr, statistics_t *statistics_ptr);

/* Testing whether an atom appears or not in a level */
#define Test_atom_at(statistics_ptr, matom, depth) \
((matom - statistics_ptr->moffset) >= 0 ? var_set_get_elt(statistics_ptr->matoms[depth], matom - statistics_ptr->moffset) : 0)

/* Counting how many atoms appear in a level */
#define Count_atoms_at(statistics_ptr, depth) \
var_set_n_elts(statistics_ptr->matoms[depth])

/* Access */
#define Size(stat_ptr) (stat_ptr->size)
#define Depth(stat_ptr) (stat_ptr->max_depth)

#endif




