/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE dag.h - *SAT 1.3 */
/*  Formula as a dag */

/*  *********************************************************************** */
/*  *********************************************************************** */

/* GLU modules */
#include "util.h"
#include "array.h"
#include "list.h"
#include "graph.h" 
#include "st.h"

/* *SAT modules */
#include "fnode.h"
#include "addglu.h"

#ifndef DAG
#define DAG

/* Comment this to disable garbage collection in the dag (TESTING ONLY!!!)
*/
#define GCOLLECT    

/* The maximum number of original atoms (either modal or propositional)
   that can be accomodated in the DAG structure. You can still have
   added variables up to the size of integers, because
   they do not matter to the DAG structure. It might not be safe to have more
   than 1 << 16 variables.
*/
#define MAXATOM 1 << 16

/* Propositional language 
*/
#define NCD    2    /* Negation, Conjunction, Disjunction */
#define NCDE   1    /* NCD + Equivalence */
#define NCDEI  0    /* NCDE + Implication */

/* Cnf conversion
*/
#define STD_CONVERSION 0
#define OPT_CONVERSION 1

/* Hashing 
*/
#define HASH_ATOM(value)    (atom_code + value) 
#define HASH_OP(key1, key2) (key1 + key2)

/* Castings for hash tables <key,value> 
   - key is an integer
   - value is a pointer to a list of vertex pointers 
   and for hash tables <key, value>
   - key as before
   - value is a pointer to a vertex
*/
#define CAST_KEY(key)           ((stGeneric) (key))
#define CAST_VALUE(lsList_ptr)  ((stGeneric) (lsList_ptr))
#define CAST_VVALUE(vertex_ptr) ((stGeneric) (vertex_ptr))
#define UNCAST_KEY(gen)         (( int) (gen))
#define UNCAST_VALUE(gen)       ((lsList*) (gen))
#define UNCAST_VVALUE(gen)      ((vertex_t*) (gen))

/* Castings for hash tables <key, value> 
   - key is a vertex pointer
   - value is an integer
*/
#define CAST_TKEY(vertex_ptr) ((stGeneric) vertex_ptr)
#define UNCAST_TKEY(gen)      ((vertex_t*) gen)
#define CAST_TVALUE(value)    ((stGenereric) (value))
#define UNCAST_TVALUE(gen)    ((int) (gen))

/* A dummy value for hash tables */
#define DUMMY_VALUE      NIL(char)

/* Casting for lists of vertex pointers and edge pointers 
*/
#define CAST_VERTEX_ITEM(vertex_ptr) ((lsGeneric) (vertex_ptr))
#define UNCAST_VERTEX_ITEM(gen)      ((vertex_t*) (gen))
#define CAST_EDGE_ITEM(edge_ptr)     ((lsGeneric) (edge_ptr))
#define UNCAST_EDGE_ITEM(gen)        ((edge_t*) (gen))

/* Casting for graph data 
*/
#define CAST_VERTEX_INFO(vertex_info_ptr) ((gGeneric) (vertex_info_ptr))
#define UNCAST_VERTEX_INFO(gen)           ((vertex_info_t*) (gen))

/* Information for xref items: the original formula referenced through
   a vertex in the top level formula DAG and
   (eventually) references to its cnfs (either pos or neg).  
   Initially only *ini_vertex_ptr is non NIL. 
   When CNF conversion is requested the result , 
   is referenced either through *pos_cnf_ptr or *neg_cnf_ptr; 
   the hash tables serve two purposes: as a list of atoms effectively in the
   formula, and as a reference to their vertices; they are initially empty,
   when the cnf conversion is requested they are filled up.
*/
typedef struct xref_info {
  vertex_t  *ini_vertex_ptr;    /* A formula []phi, phi propositional */
  lsList    *pos_lsList_ptr;    /* The cnf of phi */
  lsList    *neg_lsList_ptr;    /* The cnf of -phi */
} xref_info_t;


/* Information stored in any vertex: the original formula node,
   the key entry for the hash table (used for comparison between 
   subformulae and for subformulae ordering) and the reference 
   to xref_data (if any). 
*/
typedef struct vertex_info {
  fnode_t     *ini_fnode_ptr;  /* original node information */ 
  int         hash_key;        /* The hash keycode */
  xref_info_t *xref_info_ptr;  /* Reference to xref data if any */
} vertex_info_t;


/* The DAG structure
*/
typedef struct dag {
  st_table *uni_st_table_ptr;       /* Ensures uniqueness of nodes */
  st_table *trash_st_table_ptr;     /* Garbage collection */
  vertex_t **xref_vertex_ptr_table; /* Holds propositional and modal atoms */
  vertex_t *root_vertex_ptr;        /* The root of the DAG */
  graph_t  *inner_graph_ptr;        /* The graph handler */

  vertex_t *top_vertex_ptr; /* The constant T */
  vertex_t *bot_vertex_ptr; /* The constant F */
  
  int lpa;         /* The index to the last propositional atom. The initial
                      value is -1.  Once you add an atom, 
		      if atom > lpa the lpa = atom. */
  int lma;         /* The index to the last modal atom. The initial 
		      value is -1. lma is set to lpa at the beginning
		      of modal atoms replacement. 
		      Every new modal atom is lma + 1; */
  int laa;         /* The index to the last added atom. The initial 
		      value is -1. laa is set to lma at the end
		      of modal atom replacement.
		      Every new added atom is laa + 1; */
  int box_simplify; /* If <>0 enforces the rules []T => T 
			                         <>F => F */ 
  int cnf_conversion; /* The kind of cnf conversion required */

} dag_t;


/* *********************************************************************** */
/* Constructors */
/* *********************************************************************** */

/* Initialize the whole structure and return a pointer to it */
dag_t *Init_dag();

/* All the Add_ operations ensure uniqueness transparently using the
   internal hash table (except atoms, top and bottom, which are already
   there). Propositional simplification and internal sorting are part of
   the functions. Altering box_simplify, additional modal simplification
   may be asked for.  Every Add_ function returns the pointer to the
   uniquely added subformula.
*/

/* Logical constants: these are macros!
*/
#define dag_top(dag_ptr) (dag_ptr->top_vertex_ptr)
#define dag_bot(dag_ptr) (dag_ptr->bot_vertex_ptr)

/* Add an atom: since atoms are already there (in the xref) this
   simply returns an handle to the atom and updates internal 
   values. 
*/
vertex_t *Add_atom(dag_t *dag_ptr, fnode_t *atom_fnode_ptr);


/* Combine a formula in the dag with a unary operator 
   ("box", "dia" and "not" will do). 
*/
vertex_t *Add_unary_op(dag_t *dag_ptr, vertex_t *a_vertex_ptr, 
		       fnode_t *op_fnode_ptr);


/* Combine two subformulae in the dag using a binary operator.
   This constructor can be used to build a dag straightly out
   of a formula as a binary tree, or it can be used to combine operands
   of strictly binary connectives (such as "imp" and "iff"). 
*/
vertex_t *Add_binary_op(dag_t *dag_ptr, 
			vertex_t *a_vertex_ptr, vertex_t *b_vertex_ptr,
			fnode_t *op_fnode_ptr);


/* Combine n subformulae in the dag using a nary operator.
   This constructor can be used to build a dag out of 
   a formula as a nary tree. The subformulae are the element of the list. 
*/
vertex_t *Add_nary_op(dag_t *dag_ptr, lsList *vertices_lsList_ptr, 
		      fnode_t *op_fnode_ptr);

/* *********************************************************************** */
/* Access to dag parameters */
/* *********************************************************************** */

/* Access to variable parameters */
#define Lpa(dag_ptr) (dag_ptr->lpa)
#define Lma(dag_ptr) (dag_ptr->lma)
#define Laa(dag_ptr) (dag_ptr->laa)

/* Xref table iterator: iterates all the propositional atoms in the xref table.
   cnt must be an integer. 
*/
#define For_each_prop_xref_item(dag_ptr, cnt, vertex_ptr)                   \
for(cnt = 0;                                                                \
    (((vertex_ptr = dag_ptr->xref_vertex_ptr_table[cnt]) != NIL(vertex_t))  \
    || (cnt <= Lpa(dag_ptr))) && !(cnt > Lpa(dag_ptr)); cnt++)                                       

/* Xref table iterator: iterates the modal atoms in the xref table.
   cnt must be an integer.
*/
#define For_each_modal_xref_item(dag_ptr, cnt, vertex_ptr)                 \
for(cnt = (Lpa(dag_ptr) + 1);                                              \
    ((vertex_ptr = dag_ptr->xref_vertex_ptr_table[cnt]) != NIL(vertex_t))  \
    && (cnt <= Lma(dag_ptr)); cnt++)                                       


/* Access to the dag root */ 
#define Root_vertex_ptr(dag_ptr) \
(dag_ptr->root_vertex_ptr)

/* Access to the xref_table */
#define Xref_vertex_ptr_table(dag_ptr) \
(dag_ptr->xref_vertex_ptr_table)

/* *********************************************************************** */
/* Interface with fnode_t structures */
/* *********************************************************************** */

/* Visits recursively a fnode_t tree and returns the corresponding
   DAG. The tree MUST be nary, i.e. built using Make_formula_nary() and
   Make_operand_nary(). Modal subformulae simplification may
   be requested through box_simplify. If l_simplify = NCD
   the conversion gets rid of implication and coimplication: 
   			 (1)   A <-> B => -A v B & A v -B
			 (2)   A ->  B => -A v B 
   If l_simplify = NCDE (1) is not applied, and if l_simplify = NCDEI then
   the language is not restricted.
   Applying Make_dag to a binary tree is to be considered a no-no!
*/
dag_t *Make_dag(fnode_t *ntree_fnode_ptr,
		int box_simplify, int l_simplify, int cnf_conversion);

/* *********************************************************************** */
/* Interface with decision algorithms */
/* *********************************************************************** */
/* Visits recursively the main dag (starting from root vertex) and replaces
   every modal atom with a propositional atom. Uniqueness of replacing
   is guaranteed by the very same dag structure. Replaced subformulae are
   not removed and they are handled through the xref vertices pointers.
   The values of lma and laa get realigned properly. Also the unique table
   is properly updated; the top level formula as well as xref modal items
   do mantain the dag properties (unique formulae and ordered sons).
*/
void Replace_boxes(dag_t *dag_ptr);

/* *********************************************************************** */
/* Deconstructors */
/* *********************************************************************** */

/* Everything dies! */
void Clear_dag(dag_t *dag_ptr, nGeneric_func_ptr_t Clear_aux_func);

/* *********************************************************************** */
/* Tests */
/* *********************************************************************** */
int Are_dag_vtx_equal(vertex_t *a_vertex_ptr, vertex_t *b_vertex_ptr);
int Are_dag_vtx_compl_eq(vertex_t *a_vertex_ptr, vertex_t *b_vertex_ptr);

int Is_orphan(dag_t *dag_ptr, vertex_t *a_vertex_ptr);

#define Is_constant(dag_ptr, vertex_ptr) \
((vertex_ptr == dag_top(dag_ptr)) || (vertex_ptr == dag_bot(dag_ptr)))

#define Is_literal_vertex(vertex_ptr)                    \
((V_op_code(vertex_ptr) == atom_code) ||                 \
 ((V_op_code(vertex_ptr) == not_code) &&                 \
  (V_op_code(Get_vertex_son(vertex_ptr)) == atom_code)))

int Is_simple_vertex(vertex_t *a_vertex_ptr);
int Is_cnf_vertex(vertex_t *a_vertex_ptr);

int Generic_comp(lsGeneric a_gen, lsGeneric b_gen);
int Hash_key_comp(lsGeneric a_gen, lsGeneric b_gen);

/* *********************************************************************** */
/* Utilities about vertex_info */
/* *********************************************************************** */
vertex_info_t *New_vertex_info(fnode_t *ini_fnode_ptr, int hash_key);
void Clear_vertex_info_soft(gGeneric gen);
void Clear_vertex_info_hard(gGeneric gen, 
			    nGeneric_func_ptr_t Clear_aux_func);

#define Ini_fnode_ptr(vertex_info_ptr) \
(vertex_info_ptr->ini_fnode_ptr)
#define Hash_key(vertex_info_ptr) \
(vertex_info_ptr->hash_key)
#define Xref_info_ptr(vertex_info_ptr) \
(vertex_info_ptr->xref_info_ptr)

/* *********************************************************************** */
/* Utilities about xref_info */
/* *********************************************************************** */
xref_info_t *New_xref_info(vertex_t *ini_vertex_ptr);
void Clear_xref_info(xref_info_t  *xref_info);

#define Ini_vertex_ptr(xref_info_ptr) \
(xref_info_ptr->ini_vertex_ptr)
#define Pos_lsList_ptr(xref_info_ptr) \
(xref_info_ptr->pos_lsList_ptr)
#define Neg_lsList_ptr(xref_info_ptr) \
(xref_info_ptr->neg_lsList_ptr)


/* *********************************************************************** */
/* Utilities about dag vertices */
/* Direct access to all the information in vertices is simulated 
   using a set of macros */
/* *********************************************************************** */
#define Vertex_info(vertex_ptr)                \
(vertex_ptr->user_data)     

/* Access to ini_fnode data */
#define V_op_code(vertex_ptr)      \
Op_code(Ini_fnode_ptr(UNCAST_VERTEX_INFO(vertex_ptr->user_data)))
#define V_value(vertex_ptr)        \
Valuex(Ini_fnode_ptr(UNCAST_VERTEX_INFO(vertex_ptr->user_data)))
#define V_aux(vertex_ptr)        \
Aux(Ini_fnode_ptr(UNCAST_VERTEX_INFO(vertex_ptr->user_data)))

/* Access to vertex_info data */
#define V_hash_key(vertex_ptr)      \
Hash_key(UNCAST_VERTEX_INFO(vertex_ptr->user_data))
#define V_xref_info_ptr(vertex_ptr) \
Xref_info_ptr(UNCAST_VERTEX_INFO(vertex_ptr->user_data))
#define V_ini_fnode_ptr(vertex_ptr) \
Ini_fnode_ptr(UNCAST_VERTEX_INFO(vertex_ptr->user_data))

/* Access to xref_info data */
#define V_ini_vertex_ptr(vertex_ptr) \
(V_xref_info_ptr(vertex_ptr)->ini_vertex_ptr)
#define V_pos_lsList_ptr(vertex_ptr) \
(V_xref_info_ptr(vertex_ptr)->pos_lsList_ptr)
#define V_neg_lsList_ptr(vertex_ptr) \
(V_xref_info_ptr(vertex_ptr)->neg_lsList_ptr)     
#define V_prop_st_table_ptr(vertex_ptr) \
(V_xref_info_ptr(vertex_ptr)->prop_st_table_ptr)
#define V_mod_st_table_ptr(vertex_ptr) \
(V_xref_info_ptr(vertex_ptr)->mod_st_table_ptr)

/* Some utility function for vertices */
void Swap_vertex_ptr(vertex_t **a_vertex_ptr_ptr,
		     vertex_t **b_vertex_ptr_ptr);

vertex_t *Copy_vertex(graph_t *graph_ptr, vertex_t *source_vertex_ptr);
vertex_t *New_vertex(graph_t *graph_ptr, int op_code, int value, int hash_key);

vertex_t *Get_vertex_son(vertex_t *uop_vertex_ptr);
vertex_t *Get_vertex_ith_son(vertex_t *nop_vertex_ptr, int i);
lsList   Get_vertex_sons(vertex_t *nop_vertex_ptr);
lsList   Get_vertex_fathers(vertex_t *a_vertex_ptr);

/* *********************************************************************** */
/* Garbage collection & handling */
/* *********************************************************************** */

/* Appoint a vertex to be trashed. Checks for dag constants not to be 
   trashed. Returns either 0 (the insertion was successfull), 1 
   (the vertex was already trashed), or -1 (the vertex was a constant).*/
int Check_and_trash_vertex(dag_t *dag_ptr, vertex_t *a_vertex_ptr);

/* Appoint a list of vertices to be trashed. Checks for
   dag constants not to be trashed. Returns 0 if all the insertions where 
   successfull, 1 if at least one vertex was already trashed. */
int Check_and_trash_vertices(dag_t *dag_ptr, lsList vertices_lsList);

/* Use this if you want to garbage-collect the dag. 
   This routine takes care of operators and atoms. 
   When atoms are disposed, the xref table content and the
   lpa value are realigned to the new situation. Garbage collecting
   after replacing boxes is not guaranteed to be safe. */
void Garbage_collect(dag_t *dag_ptr);

/* *********************************************************************** */
/* Flags */
/* *********************************************************************** */
#define Box_simplify(dag_ptr)   (dag_ptr->box_simplify)
#define Cnf_conversion(dag_ptr) (dag_ptr->cnf_conversion)

/* *********************************************************************** */
/* Output routines */
/* *********************************************************************** */
void Print_dag_lisp(dag_t *dag_ptr);
void Print_dag_prolog(dag_t *dag_ptr);
void Print_dag_info(dag_t *dag_ptr); 
 
/* *********************************************************************** */
/* Miscellanea */
/* *********************************************************************** */
int Depth_eval(dag_t *dag_ptr);

#endif




