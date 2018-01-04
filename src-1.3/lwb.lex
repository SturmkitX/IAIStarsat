/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE lwb.lex - *SAT 1.3 */ 
/*  Lexical analyzer for the formula file (LWB syntax) */

/*  *********************************************************************** */
/*  *********************************************************************** */

%{
#include <stdio.h>

#include "fnode.h" 
#include "y.tab.h"

int number;
%}

%%

[ \n\t] ;    
"("     return LP;
")"     return RP; 
"box"   return BOX;         
"dia"   return DIA;
"&"     return AND; 
"->"    return IMP;
"v"     return OR;
"<->"   return IFF;
"~"     return NOT;
"true"  return TOP;
"false" return BOT;
"p"     return ATOM;

0|[1-9][0-9]* {   
  sscanf(yytext,"%d",&number);
  yylval.l = number;
  return NUM;
}

.  { 
  /* Error function */
  fprintf(stderr,"Illegal character\n");
  return -1;
}
%%
