/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE lwb.y - *SAT 1.3 */
/*  Input grammar for the formula file (LWB syntax) */

/*  *********************************************************************** */
/*  *********************************************************************** */

%{
#include "fnode.h" 

#define YYMAXDEPTH 1000000

fnode_t *formula_as_tree;
%}

%union {
   int     l;
   int     i;
   fnode_t *f; 
}

/* Tokens */

%token LP RP
%token BOX DIA
%token AND IMP OR IFF NOT
%token TOP BOT
%token ATOM
%token <l> NUM 

%type <f> formula 
%type <f> boolean_expression rule_expression atomic_expression
%type <i> boolop ruleop

%% /* Grammar rules */

input: formula             {formula_as_tree = $1;}
;

formula: boolean_expression {$$ = $1;}
| rule_expression {$$ = $1;}
| atomic_expression {$$ = $1;}
;

boolean_expression: LP formula boolop formula RP {$$ = Make_formula_binary($2,$3,empty_code,$4);}
| LP NOT formula RP {$$ = Make_formula_binary($3,not_code,empty_code,Make_empty());}
;

rule_expression: LP ruleop formula RP {$$ = Make_formula_binary($3,$2,empty_code,Make_empty());}
;

atomic_expression: ATOM NUM {$$ = Make_formula_binary(Make_empty(),atom_code,$2,Make_empty());}
| TOP {$$ = Make_formula_binary(Make_empty(),top_code,empty_code,Make_empty());}
| BOT {$$ = Make_formula_binary(Make_empty(),bot_code,empty_code,Make_empty());}
;

boolop: AND {$$ = and_code;} 
|       IMP {$$ = imp_code;}
|       OR  {$$ = or_code;} 
|       IFF {$$ = iff_code;} 
;

ruleop: DIA {$$ = dia_code;}
| BOX {$$ = box_code;}       

%% /* End of grammar rules */

int yyerror(char *s) 
{
  printf("%s\n", s);
  exit(0);
}

