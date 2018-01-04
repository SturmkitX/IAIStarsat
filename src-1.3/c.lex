/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE c.lex - *SAT 1.3 */ 
/*  Lexical analyzer for the formula file (KsatC syntax) */

/*  *********************************************************************** */
/*  *********************************************************************** */


%{
#include <stdio.h>
#include <string.h>

#include "fnode.h"
#include "y.tab.h"

int number;
char name[30];
%}


%%


[ \n\t] ;    
"("     return LP;
")"     return RP; 

0|[1-9][0-9]* {   
  sscanf(yytext,"%d", &number);
  yylval.l = number;
  return NUM;
}

"="     return EQ;
"#"     return BOX;         
"-"     return NOT;
"^"     return AND; 
"v"     return OR;
"T"     return TOP;
"F"     return BOT;

[A-Za-z_][A-Za-z0-9_]* { 
  sscanf(yytext,"%s",name);
  strcpy(yylval.s,name);
  return IDENT;
}

.  { 
  /* Error function */
  fprintf(stderr,"Illegal character\n");
  return -1;
}
%%
