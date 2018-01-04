/*  *********************************************************************** */
/*  *********************************************************************** */

/*  FILE monitor.c - *SAT 1.3 */
/*  Performance monitoring */ 

/*  *********************************************************************** */
/*  *********************************************************************** */

#include "monitor.h"

/* *********************************************************************** */
/* Constructors & Deconstructors */
/* *********************************************************************** */
monitor_t *Init_monitor()
{
  monitor_t *t_monitor_ptr;
  int i;

  t_monitor_ptr = ALLOC(monitor_t, 1);
  for (i = 0; i < MAX_CLOCK; i++)   
    t_monitor_ptr->timings[i] = 0;
  for (i = 0; i < MAX_PARAM; i++)   
    t_monitor_ptr->params[i] = 0;

  return t_monitor_ptr;
}

void Clear_monitor(monitor_t *monitor_ptr)
{
  FREE(monitor_ptr);
}




