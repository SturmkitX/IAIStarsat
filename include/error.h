/*
 * Revision Control Information
 *
 * /projects/hsis/CVS/utilities/error/error.h,v
 * rajeev
 * 1.3
 * 1995/08/08 22:39:32
 *
 */
EXTERN void error_init ARGS((void));
EXTERN void error_append ARGS((char *));
EXTERN char *error_string ARGS((void));
EXTERN void error_cleanup ARGS((void));
