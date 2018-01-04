#include "mdd.h"

/*
 * MDD Package
 * $Source: /projects/development/hsv/CVSRepository/utilities/common/src/mdd/mdd_support.c,v $
 * 
 * Author: Timothy Kam
 * $Date: 1998/09/15 21:08:15 $
 * $Revision: 1.7 $
 *
 * Copyright 1992 by the Regents of the University of California.
 *
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software is hereby granted, provided that the above copyright
 * notice and this permission notice appear in all copies.  This software
 * is made available as is, with no warranties.
 */

array_t *
mdd_get_support(mdd_mgr, f)
mdd_manager *mdd_mgr;
mdd_t *f;
{
    array_t *full_list, *support_list;
    array_t *mvar_list = mdd_ret_mvar_list(mdd_mgr);
    array_t *bvar_list = mdd_ret_bvar_list(mdd_mgr);
    var_set_t *vset;
    int i, list_length;
    bvar_type bv;
    boolean present;


    /* initialize full list of mvar id's */
    list_length = array_n(mvar_list);
    full_list = array_alloc(boolean, list_length);
    for (i = 0; i < array_n(mvar_list); i++) {
	array_insert(boolean, full_list, i, 0);
    }

    vset = bdd_get_support(f);
    for (i = 0; i < array_n(bvar_list); i++) {
	if (var_set_get_elt(vset, i) == 1) {
	    bv = array_fetch(bvar_type, bvar_list, i);
	    (void) array_insert(boolean, full_list, bv.mvar_id, 1);
	}
    }

    support_list = array_alloc(int, 0);
    for (i = 0; i < array_n(mvar_list); i++) {
	present = array_fetch(boolean, full_list, i);
	if (present) array_insert_last(int, support_list, i);
    }

    (void) array_free(full_list);
    (void) var_set_free(vset);

    return support_list;
}
