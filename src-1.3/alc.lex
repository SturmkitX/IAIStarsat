/* *********************************************************************** */
/* *********************************************************************** */

/* FILE alc.lex - *SAT 1.3 */ 
/* Lexical analyzer for the formula file (KRIS syntax) */

/* *********************************************************************** */
/* *********************************************************************** */

%{
#include <stdio.h>

#include "fnode.h"
#include "y.tab.h"

int number;
%}

%%

[ \n\t] ;    
"("      return LP;
")"      return RP; 
"ALL"    return ALL;         
"SOME"   return SOME;
"AND"    return AND; 
"IMP"    return IMP;
"OR"     return OR;
"IFF"    return IFF;
"NOT"    return NOT;
"TOP"    return TOP;
"BOTTOM" return BOT;
"R"      return RULE;
"C"      return CONC;

0|[1-9][0-9]* {   
  sscanf(yytext,"%d",&number);
  yylval.l=number;
  return NUM;
}

.  { 
  /* Error function */
  fprintf(stderr,"Illegal character\n");
  return -1;
}
%%
