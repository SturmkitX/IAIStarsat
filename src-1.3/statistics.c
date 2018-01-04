/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE statistics.c - *SAT 1.3 */
/*  Statistics on the modal formula */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "statistics.h"

/* Shortcuts -------------------------------------------------------------- */
#define Matoms(depth) statistics_ptr->matoms[depth]

/* Prototypes ------------------------------------------------------------- */

statistics_t *Int_init_statistics(int offset);
void Rec_compute_statistics(statistics_t *statistics_ptr, dag_t *dag_ptr,
			    vertex_t *vertex_ptr, int depth);

/* Interface -------------------------------------------------------------- */

statistics_t *Compute_statistics(dag_t *dag_ptr)
{
  statistics_t *t_statistics_ptr;

  /* The first modal atom is the 0-th element of each set */
  t_statistics_ptr = Int_init_statistics(((Lpa(dag_ptr) >= 0) ? (Lpa(dag_ptr) + 1): 0));

  Rec_compute_statistics(t_statistics_ptr, dag_ptr, Root_vertex_ptr(dag_ptr), 0);

  return t_statistics_ptr;
}

void Var_set_print(fp, set)
FILE *fp;
var_set_t *set;
{
  int i;
  for (i = 0; i < set->n_elts; i++) {
    fprintf(fp, "%2d ", var_set_get_elt(set, i));
  }
  fprintf(fp, "\n");
}

void Print_statistics(dag_t *dag_ptr, statistics_t *statistics_ptr)
{
  int i;

  printf("   ");
  for (i = statistics_ptr->moffset; i<=Lma(dag_ptr); i++)
    printf("%2d ",i);
  printf("\n");
  i = 0;
  while (statistics_ptr->matoms[i] != NIL(var_set_t)) {
    printf("%2d ", i);
    Var_set_print(stdout, statistics_ptr->matoms[i]);
    ++i;
  }
    
  return;
}
  
    

/* Private functions ------------------------------------------------------ */

/* Initialize statistics data structure */
statistics_t *Int_init_statistics(int offset)
{
  int          i;
  statistics_t *t_statistics_ptr;
  
  t_statistics_ptr = ALLOC(statistics_t, 1);
  t_statistics_ptr->moffset = offset;
  t_statistics_ptr->matoms = ALLOC(var_set_t*,MAX_DEPTH);
  for (i = 0; i < MAX_DEPTH; i++)
    t_statistics_ptr->matoms[i] = NIL(var_set_t);
  t_statistics_ptr->max_depth = 0;
  t_statistics_ptr->size=0;

  return t_statistics_ptr;
}

/* Traverse the formula looking for information:
   statistics_ptr is updated, vertex_ptr is the current vertex pointer, 
   depth is the current modal depth */
void Rec_compute_statistics(statistics_t *statistics_ptr, dag_t *dag_ptr,
			    vertex_t *vertex_ptr, int depth)
{
  lsList    sons_lsList;
  lsGen     sons_lsGen;
  lsGeneric son_lsGeneric;
  lsStatus  list_status; 

  /* Boldly no diamonds here */
  assert(V_op_code(vertex_ptr) != dia_code);

  /* Assesing maximum depth and number of nodes */
  if (depth > statistics_ptr->max_depth) {
    statistics_ptr->max_depth = depth;
  }
  ++(statistics_ptr->size);

  /* A propositional atom, true or false mean no data to collect */
  if (((V_op_code(vertex_ptr) == atom_code) && V_value(vertex_ptr) <= Lpa(dag_ptr)) ||
      (V_op_code(vertex_ptr) == top_code) ||
      (V_op_code(vertex_ptr) == bot_code))
    return;
  
  /* Anything else: possibly there are data to collect */
  /* If we arrived at this point we have an operator: and,or,not,implies,iff or box */
  if (V_op_code(vertex_ptr) == atom_code) {
    /* An atom here might only be a box: initialize the level (if not already done),
       collect the data and propagate the search */

    /* Initialize current level data */
    if (Matoms(depth) == NIL(var_set_t))
      Matoms(depth) = var_set_new((Lma(dag_ptr) - Lpa(dag_ptr)));

    /* Collect the data */
    var_set_set_elt(Matoms(depth), 
		    V_value(vertex_ptr) - statistics_ptr->moffset);
    
    /* Propagate the search */
    Rec_compute_statistics(statistics_ptr, dag_ptr,
			   Get_vertex_son(V_ini_vertex_ptr(vertex_ptr)),
			   (depth + 1));

  } else {
    /* An operator: propagate the search */

    sons_lsList = Get_vertex_sons(vertex_ptr);   /* This CREATES THE LIST! */
    lsForEachItem(sons_lsList, sons_lsGen, son_lsGeneric) {
      Rec_compute_statistics(statistics_ptr, dag_ptr,
			     UNCAST_VERTEX_ITEM(son_lsGeneric),
			     depth);
    }
    list_status = lsDestroy(sons_lsList, NULL);  /* This DESTROYS THE LIST! */

  }

  /* Finished! */
  return;
}


