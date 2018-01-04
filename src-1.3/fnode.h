/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE fnode.h - *SAT 1.3 */
/*  Formula as a tree  */

/*  *********************************************************************** */
/*  *********************************************************************** */

#include <malloc.h>
#include "util.h"

#ifndef FNODE
#define FNODE

/* Internal representation of operators as integer codes */

#define nul_code  (int)  0 /* Empty constant for operators */
#define and_code  (int)  3 
#define or_code   (int)  5 
#define not_code  (int)  7 
#define imp_code  (int) 11 
#define iff_code  (int) 13 
#define box_code  (int) 17 
#define dia_code  (int) 23 
#define top_code  (int) 29 
#define bot_code  (int) 31 
#define atom_code (int) 37 

#define empty_code (int) 0 /* Empty constant for values */

typedef char* nGeneric; 
typedef nGeneric (*nGeneric_func_ptr_t)();

typedef struct fnode {
  int           op_code;           
  int           value;   
  nGeneric      aux;
  struct fnode  *left_fnode_ptr, *right_fnode_ptr;
} fnode_t;

/* *********************************************************************** */
/* Constructors */
/* *********************************************************************** */

fnode_t *Make_empty(void);
fnode_t *Make_fnode(void);

fnode_t *Make_formula_nary(int op_code, 
			   int value,
			   fnode_t *op_fnode_ptr);  

fnode_t *Make_operand_nary(fnode_t *head_fnode_ptr, fnode_t *tail_fnode_ptr);

fnode_t *Make_formula_binary(fnode_t *left_fnode_ptr, 
			     int op_code, 
			     int value,
			     fnode_t *right_fnode_ptr);

fnode_t *Copy_fnode(fnode_t *a_fnode_ptr);

/* *********************************************************************** */
/* Deconstructors */
/* *********************************************************************** */

void Clear_fnode(fnode_t *fnode_ptr, 
		 nGeneric_func_ptr_t Clear_aux_func);
void Clear_rec_fnode(fnode_t *fnode_ptr, 
		     nGeneric_func_ptr_t Clear_aux_func);

/* *********************************************************************** */
/* Preprocessing */
/* *********************************************************************** */

fnode_t *Convert_binary2nary(fnode_t *btree_fnode_ptr);
void    Flatten_and_or(fnode_t *ntree_fnode_ptr);
void    Flatten_double_not(fnode_t *ntree_fnode_ptr);
void    Convert_dia2box(fnode_t *ntree_fnode_ptr);
/* Handles -(A <-> B) as (A <-> -B) */
void    Convert_NNF(fnode_t *ntree_fnode_ptr, int flag_nnf);

/* *********************************************************************** */
/* Translations */
/* These translations require diamond free and single agent formulae! 
   They return diamond free and (possibly) multi agent formulae */
/* From Gasquet & Herzig paper */
/* *********************************************************************** */
void Translate_from_E_to_K(fnode_t *ntree_fnode_ptr);
void Translate_from_EM_to_K(fnode_t *ntree_fnode_ptr);

/* *********************************************************************** */
/* Tests */
/* *********************************************************************** */
int Is_simple(fnode_t *fnode_ptr);

#define Is_atom(fnode_ptr) ((fnode_ptr->op_code) == atom_code) 

#define Is_unary(fnode_ptr)            \
(((fnode_ptr->op_code) == box_code) || \
((fnode_ptr->op_code) == dia_code) ||  \
((fnode_ptr->op_code) == not_code))
     
#define Is_binary(fnode_ptr)           \
(((fnode_ptr->op_code) == and_code) || \
((fnode_ptr->op_code) == or_code)  ||  \
((fnode_ptr->op_code) == imp_code) ||  \
((fnode_ptr->op_code) == iff_code))
     
#define Is_nary(fnode_ptr)             \
(((fnode_ptr->op_code) == and_code) || \
((fnode_ptr->op_code) == or_code))  

/* *********************************************************************** */
/* Access to information */
/* *********************************************************************** */
#define Op_fnode_ptr(fnode_ptr) \
(fnode_ptr->left_fnode_ptr)
#define Next_fnode_ptr(fnode_ptr) \
(fnode_ptr->right_fnode_ptr)

#define Left_fnode_ptr(fnode_ptr) \
(fnode_ptr->left_fnode_ptr)
#define Right_fnode_ptr(fnode_ptr) \
(fnode_ptr->right_fnode_ptr)

/* Scrambled a little bit to avoid a clash with SATO macro */
#define Valuex(fnode_ptr) \
(fnode_ptr->value)
#define Op_code(fnode_ptr) \
(fnode_ptr->op_code)

/* *********************************************************************** */
/* Aux pointer manipulation */
/* *********************************************************************** */
#define Aux(fnode_ptr) \
(fnode_ptr->aux)

/* *********************************************************************** */
/* Pretty prenting */
/* *********************************************************************** */
void Print_fnode_lwb(fnode_t *fnode_ptr); 
void Print_fnode_cnf(fnode_t *fnode_ptr); 

#endif

