/* *********************************************************************** */
/* *********************************************************************** */

/* FILE tptp.lex - *SAT 1.3 */ 
/* Lexical analyzer for the formula file (TPTP syntax) */

/* *********************************************************************** */
/* *********************************************************************** */

%{
#include <stdio.h>
#include <string.h>

#include "fnode.h"
#include "y.tab.h"

int  number;
char name[256];
%}

%%

[ \t\n] ;    
"("     return LP;
")"     return RP; 
":"     return COL;
"box"   return BOX;         
"pos"   return POS;
"&"     return AND; 
"|"     return OR;
"=>"    return IMP;
"~"     return NOT;
"true"  return TTRUE;
"false" return TFALSE;
"v"     return VAR;
"r"     return RULE;

"inputformula" return INWFF;
"hypothesis,"  return HYP;
"conjecture,"  return CONJ;
"."            return DOT;

0|[1-9][0-9]* {   
  sscanf(yytext,"%d",&number);
  yylval.l=number;
  return NUM;
}

[A-Za-z][A-Za-z0-9_]*, { 
  sscanf(yytext,"%s",name); 
  strcpy(yylval.s,name);  
  return IDENT;
}

.  { 
  /* Error function */
  fprintf(stderr,"Illegal character %s	\n",yytext);
  return -1;
}
%%
