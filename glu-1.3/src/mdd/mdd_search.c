#include "mdd.h"

/*
 * MDD Package
 * $Source: /projects/development/hsv/CVSRepository/utilities/common/src/mdd/mdd_search.c,v $
 *
 * Author: Timothy Kam
 * $Date: 1998/09/15 21:08:14 $
 * $Revision: 1.7 $
 *
 * Copyright 1992 by the Regents of the University of California.
 *
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software is hereby granted, provided that the above copyright
 * notice and this permission notice appear in all copies.  This software
 * is made available as is, with no warranties.
 */

void
mdd_pr_cubes(mgr)
mdd_manager *mgr;
{
    int i, j;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);
    mvar_type mv;

    for (i=0; i<array_n(mvar_list); i++) {
        mv = array_fetch(mvar_type, mvar_list, i);
        (void) printf("\n%s = ", mv.name);
        for (j=0; j<mv.encode_length; j++)
            (void) printf("%d",mv.encoding[j]);
    }
    (void) printf("\n");
}

void
mdd_pr_minterms(mgr)
mdd_manager *mgr;
{
	/* not implemented yet */

    int i, j;
    mvar_type mv;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);

    for (i=0; i<array_n(mvar_list); i++) {
        mv = array_fetch(mvar_type, mvar_list, i);
        (void) printf("\n%s = ", mv.name);
        for (j=0; j<mv.encode_length; j++)
            (void) printf("%d",mv.encoding[j]);
    }
    (void) printf("\n");
}

void
mdd_search(mgr, top, phase, minterms)
mdd_manager *mgr;
bdd_t *top;
int phase;
boolean minterms;
{
    int is_complemented;
    bdd_t *child, *top_uncomp;
    
    if (mdd_is_tautology(top,1)) {
	if (phase == 1) {
	    if (minterms == 1) mdd_pr_minterms(mgr);	
	    else mdd_pr_cubes(mgr);	
	}
        return;
    }
    if (mdd_is_tautology(top,0)) {
	if (phase == 0) {
	    if (minterms == 1) mdd_pr_minterms(mgr);	
	    else mdd_pr_cubes(mgr);	
	}
        return;
    }

    (void)bdd_get_node(top,&is_complemented);

    if (is_complemented != 0) { 
	phase = toggle(phase);
    }

    (void) mdd_mark(mgr, top, 1);

    if (is_complemented) top_uncomp = bdd_not(top); 
    else top_uncomp = mdd_dup(top);

    child = bdd_then(top_uncomp);
    mdd_search(mgr, child, phase, minterms);
    mdd_free(child);


    child = bdd_else(top_uncomp);
    (void) mdd_mark(mgr, top, 0);
    mdd_search(mgr, child, phase, minterms);
    mdd_unmark(mgr, top);

    mdd_free(top_uncomp);
    mdd_free(child);
    return;
}
