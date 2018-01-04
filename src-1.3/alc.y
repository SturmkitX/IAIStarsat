/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE alc.y - *SAT 1.3 */ 
/*  Lexical analyzer for the formula file (KRIS syntax) */

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

/* Tokens and types */

%token LP RP
%token ALL SOME
%token AND IMP OR IFF NOT
%token TOP BOT
%token RULE CONC
%token <l> NUM 

%type <f> formula 
%type <f> boolean_expression rule_expression atomic_expression
%type <f> other
%type <i> uboolop bboolop nboolop ruleop
%type <l> rule 

%% /* Grammar rules */

input: formula {formula_as_tree = $1;}       
;

formula: boolean_expression {$$ = $1;}
| rule_expression {$$ = $1;}
| atomic_expression {$$ = $1;}
;

boolean_expression: LP uboolop formula RP 
{$$ = Make_formula_nary($2,empty_code,$3);}

| LP bboolop formula formula RP 
{$$ = Make_formula_nary($2,empty_code, Make_operand_nary($3,$4));}

| LP nboolop formula other RP 
{$$ = Make_formula_nary($2,empty_code,Make_operand_nary($3,$4));}
;

rule_expression: LP ruleop rule formula RP {$$ = Make_formula_nary($2,$3,$4);}
;

atomic_expression: CONC NUM {$$ = Make_formula_nary(atom_code,$2,Make_empty());}
| TOP {$$ = Make_formula_nary(top_code,empty_code,Make_empty());}
| BOT {$$ = Make_formula_nary(bot_code,empty_code,Make_empty());}
;

other: formula other {$$ = Make_operand_nary($1,$2);}
| {$$ = Make_empty();}
;

uboolop: NOT {$$ = not_code;} 
;

bboolop: IFF {$$ = iff_code;} 
|        IMP {$$ = imp_code;}
;

nboolop: AND {$$ = and_code;} 
|        OR  {$$ = or_code;} 
;

ruleop: SOME {$$ = dia_code;}
| ALL {$$ = box_code;}       

rule: RULE NUM {$$ = $2;}
;

%% /* End of grammar rules */

int yyerror(char *s) 
{
  printf("%s\n", s);
  exit(0);
}

