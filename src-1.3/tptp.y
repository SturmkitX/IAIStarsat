/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE alc.y - *SAT 1.3 */ 
/*  Grammar for the formula file (TPTP syntax) */

/*  *********************************************************************** */
/*  *********************************************************************** */

%{
#include <stdio.h>
#include "fnode.h"

#define YYMAXDEPTH 1000000
#define YYDEBUG 1

fnode_t *formula_as_tree;

%}

%union {
   int     l;
   char    s[256];
   fnode_t *f; 
}

/* Tokens and types */

%token LP RP COL
%token INWFF HYP CONJ DOT 
%token BOX POS AND OR IMP NOT TFALSE TTRUE
%token VAR RULE
%token <l> NUM 
%token <s> IDENT

%type <f> decl_list declaration
%type <f> formula complex_formula formula_list atom
%type <l> bool_op rule_op

%% /* Grammar rules */

input: decl_list
{formula_as_tree = $1;}
;

decl_list: INWFF declaration decl_list
{$$ = Make_formula_binary($2, and_code, empty_code, $3);}
| INWFF declaration
{$$ = $2;}
;

declaration: LP IDENT HYP formula RP DOT 
{$$ = $4;}
| LP IDENT CONJ formula RP DOT
{$$ = Make_formula_binary($4, not_code, empty_code, Make_empty());}
;

formula: complex_formula  
{$$ = $1;}
| atom 
{$$ = $1;}
;

complex_formula: LP rule_op RULE NUM COL formula RP
{$$ = Make_formula_binary($6, $2, $4, Make_empty());}
| NOT formula 
{$$ = Make_formula_binary($2, not_code, empty_code, Make_empty());}
| LP formula_list RP
{$$ = $2;}
;

formula_list: formula bool_op formula_list
{$$ = Make_formula_binary($1, $2, empty_code, $3);}
| formula
{$$ = $1;}
;

atom: VAR NUM
{$$ = Make_formula_binary(Make_empty(), atom_code, $2, Make_empty());}
| TTRUE
{$$ = Make_formula_binary(Make_empty(), top_code, empty_code, Make_empty());}
| TFALSE 
{$$ = Make_formula_binary(Make_empty(), bot_code, empty_code, Make_empty());}
;

bool_op: AND {$$ = and_code;} 
|        OR  {$$ = or_code;} 
|        IMP {$$ = imp_code;} 
;

rule_op: POS {$$ = dia_code;}
|        BOX {$$ = box_code;}       

%% /* End of grammar rules */

int yyerror(char *s) 
{
  printf("%s\n", s);
  exit(0);
}

