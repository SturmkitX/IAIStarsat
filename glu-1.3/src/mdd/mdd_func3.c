#include "mdd.h"

/*
 * MDD Package
 * $Source: /projects/development/hsv/CVSRepository/utilities/common/src/mdd/mdd_func3.c,v $
 * 
 * Author: Timothy Kam
 * $Date: 1998/09/15 21:08:11 $
 * $Revision: 1.7 $
 *
 * Copyright 1992 by the Regents of the University of California.
 *
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software is hereby granted, provided that the above copyright
 * notice and this permission notice appear in all copies.  This software
 * is made available as is, with no warranties.
 */

mdd_t *
mdd_func3(mgr, mvar1, mvar2, mvar3, func3)
mdd_manager *mgr; 
int mvar1; 
int mvar2; 
int mvar3;
boolean (*func3)();
{
    mvar_type x, y, z;
    array_t *child_list_x, *child_list_y, *child_list_z;
    int i, j, k;
    mdd_t *tx, *ty, *tz;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);
    mdd_t *one, *zero;

    one = mdd_one(mgr);
    zero = mdd_zero(mgr);

    x = array_fetch(mvar_type, mvar_list, mvar1);
    y = array_fetch(mvar_type, mvar_list, mvar2);
    z = array_fetch(mvar_type, mvar_list, mvar3);

    if (x.status == MDD_BUNDLED) {
	(void) fprintf(stderr, 
		"\nWarning: mdd_func3, bundled variable %s is used\n", x.name);
	fail("");
    }

    if (y.status == MDD_BUNDLED) {
	(void) fprintf(stderr,
		"\nWarning: mdd_func3, bundled variable %s is used\n", y.name);
	fail("");
    }

    if (z.status == MDD_BUNDLED) {
	(void) fprintf(stderr, 
		"\nWarning: mdd_func3, bundled variable %s is used\n", z.name);
	fail("");
    }





    child_list_x = array_alloc(mdd_t *, 0);
    for (i=0; i<x.values; i++) {
	child_list_y = array_alloc(mdd_t *, 0);
	for (j=0; j<y.values; j++) {
	    child_list_z = array_alloc(mdd_t *, 0);
	    for (k=0; k<z.values; k++) {
	        if (func3(i,j,k))
		    array_insert_last(mdd_t *, child_list_z, one);
                else
                    array_insert_last(mdd_t *, child_list_z, zero);
	    }
	    tz = mdd_case(mgr, mvar3, child_list_z);
	    array_insert_last(mdd_t *, child_list_y, tz);
	    array_free(child_list_z);
	}
	ty = mdd_case(mgr, mvar2, child_list_y);
	array_insert_last(mdd_t *, child_list_x, ty);
	array_free(child_list_y);
    }
    tx = mdd_case(mgr, mvar1, child_list_x);
    array_free(child_list_x);

    mdd_free(one);
    mdd_free(zero);

    return tx;
}

/***** internal functions *****/       

boolean 
eq_plus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x == y + z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
geq_plus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x >= y + z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
gt_plus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x > y + z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
leq_plus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x <= y + z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
lt_plus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x < y + z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
neq_plus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x != y + z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
eq_minus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x == y - z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
geq_minus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x >= y - z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
gt_minus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x > y - z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
leq_minus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x <= y - z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
lt_minus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x < y - z) answer = 1;
        else answer = 0;
    return (answer);
}

boolean 
neq_minus3(x, y, z)
int x; 
int y; 
int z;
{
    boolean answer;
    if (x != y - z) answer = 1;
        else answer = 0;
    return (answer);
}

