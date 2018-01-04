/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE monitor.h - *SAT 1.3 */
/*  Performance monitoring */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include <stdio.h>
#include <malloc.h>

#include "util.h"

#ifndef MONITOR
#define MONITOR

#define MAX_CLOCK   10
#define MAX_PARAM   30

/* Timings (MAX CLOCK) */
#define PARSE       0 /* Time for parsing the input formula */
#define PREPROCESS  1 /* Time for preprocessing the input formula */
#define TRANSLATE   2 /* Time for translating */
#define BUILD       3 /* Time to set up the data structure and initialize it */ 
#define DSAT        4 /* Time to run the decision procedure */

/* Parameters (MAX_PARAM) */

/* General */
#define REC_CALLS     0  /* Consistency checks (recursive calls) */ 
#define MODFAIL_NUM   1  /* Failed consistency checks */
#define EP_CALLS      2  /* Early pruning calls */
#define EPFAIL_NUM    3  /* Backtracks on early pruning */
#define BJ_CALLS      2  /* Backjumping calls */
#define BJFAIL_NUM    3  /* Backjumps */

/* Davis Putnam */
#define UNIT_NUM      10 /* Unit propagations */
#define PURE_NUM      11 /* Pure literals */
#define SPLIT_NUM     12 /* Splits */         
#define SPLIT_DEP_NUM 13 /* Spits on dependent variables */
#define SPLIT_MOD_NUM 14 /* Spits on modal atoms */
#define ASSIGN_NUM    15 /* Assignments found */
#define PROPFAIL_NUM  16 /* Backtracks on propositional inconsistencies */

/* Memory usage */
#define MAX_SATO_MEMORY     21 /* Maximum memory allocated by SATO */

typedef int clock_table_t[MAX_CLOCK]; /* Must accomodate all the timings */
typedef int param_table_t[MAX_PARAM]; /* Must accomodate all the parameters */

typedef struct monitor {
  clock_table_t timings;
  param_table_t params;
} monitor_t;

/* *********************************************************************** */
/* Constructors & Deconstructors */
/* *********************************************************************** */
monitor_t *Init_monitor();
void Clear_monitor(monitor_t *monitor_ptr);

/* *********************************************************************** */
/* CPU times */
/* *********************************************************************** */  
#define Start_clock(monitor_ptr, field) \
monitor_ptr->timings[field] = util_cpu_time()

#define Stop_clock(monitor_ptr, field) \
monitor_ptr->timings[field] = util_cpu_time() - monitor_ptr->timings[field]

#define Lap_time(monitor_ptr, field) \
(util_cpu_time() - monitor_ptr->timings[field])

#define Get_clock(monitor_ptr, field) \
(monitor_ptr->timings[field])

#define Print_clock(monitor_ptr, field) \
util_print_time(monitor_ptr->timings[field])

/* *********************************************************************** */
/* Parameters */
/* *********************************************************************** */
#define Inc_param(monitor_ptr, field) (monitor_ptr->params[field])++
#define Inc_param_by(monitor_ptr, field, inc) (monitor_ptr->params[field])+=inc

#define Get_param(monitor_ptr, field) (monitor_ptr->params[field])

#endif


