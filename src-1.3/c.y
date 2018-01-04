/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE c.y - *SAT 1.3 */
/*  Input grammar for the formula file (KsatC syntax) */

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
   char    s[30];
}

/* Tokens and types */
%token LP RP
%token <l> NUM
%token <s> IDENT

%token EQ
%token TOP BOT
%token BOX 
%token AND OR NOT

%type <f> formula 
%type <f> boolean_expression rule_expression atomic_expression
%type <f> other
%type <i> boolop boxop
%type <l> agent 

%% /* Grammar rules */

formula_file: IDENT EQ formula        {formula_as_tree = $3;} 
;

formula: boolean_expression {$$ = $1;}
| rule_expression {$$ = $1;}
| atomic_expression {$$ = $1;}
;

boolean_expression: boolop LP formula other RP 
{$$ = Make_formula_nary($1,empty_code,Make_operand_nary($3,$4));}
| NOT boolop LP formula other RP 
{$$ = Make_formula_nary(not_code, empty_code, 
			Make_formula_nary($2,empty_code,
					  Make_operand_nary($4,$5)));}
;

rule_expression: boxop agent LP formula RP {$$ = Make_formula_nary($1,$2,$4);}
| NOT boxop agent LP formula RP {$$ = Make_formula_nary(not_code, empty_code, Make_formula_nary($2,$3,$5));}
;

atomic_expression: NUM {$$ = Make_formula_nary(atom_code,$1,Make_empty());}
| NOT NUM {$$ = Make_formula_nary(not_code, empty_code, Make_formula_nary(atom_code,$2,Make_empty()));}
| TOP {$$ = Make_formula_nary(top_code,empty_code,Make_empty());}
| BOT {$$ = Make_formula_nary(bot_code,empty_code,Make_empty());}
;

other: formula other {$$ = Make_operand_nary($1,$2);}
| {$$ = Make_empty();}
;

boolop: AND {$$ = and_code;} 
|       OR  {$$ = or_code;} 
;

boxop: BOX {$$ = box_code;}
;

agent: LP NUM RP {$$ = $2;}
;  

/* End of formula rules */

%% /* End of grammar rules */

int yyerror(char *s) 
{
  printf("%s\n", s);
  exit(-1);
}
         

