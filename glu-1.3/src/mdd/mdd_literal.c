#include "mdd.h"

/*
 * MDD Package
 * $Source: /projects/development/hsv/CVSRepository/utilities/common/src/mdd/mdd_literal.c,v $
 *
 * Author: Timothy Kam
 * $Date: 1998/09/15 21:08:13 $
 * $Revision: 1.7 $
 * $Date: 1998/09/15 21:08:13 $
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
mdd_literal(mgr, mvar, values)
mdd_manager *mgr;
int mvar;
array_t *values;
{
    mvar_type x;
    array_t *child_list_x;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);
    int i, j, set1, v;
    mdd_t *tx1;
    mdd_t *one, *zero;


    one = mdd_one(mgr);
    zero = mdd_zero(mgr);

    x = array_fetch(mvar_type, mvar_list, mvar);
    child_list_x = array_alloc(mdd_t *, 0);
    for (i=0; i<x.values; i++) {
	set1 = 0;
	for (j=0; j<array_n(values); j++) {
	    v = array_fetch(int, values, j);
	    if (i == v) set1 = 1;
	}
	if (set1 == 1) {
	    array_insert_last(mdd_t *, child_list_x, one);
	}
	else {
	    array_insert_last(mdd_t *, child_list_x, zero);
	}
    }
    tx1 = mdd_case(mgr, mvar, child_list_x);
    array_free(child_list_x);

    mdd_free(one);
    mdd_free(zero);

    return tx1;
}
