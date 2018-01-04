#include "mdd.h"

/*
 * MDD Package
 * $Source: /projects/development/hsv/CVSRepository/utilities/common/src/mdd/mdd_andsmoot.c,v $
 * 
 * Author: Timothy Kam
 * $Date: 1998/09/15 21:08:07 $
 * $Revision: 1.8 $
 *
 * Copyright 1992 by the Regents of the University of California.
 *
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software is hereby granted, provided that the above copyright
 * notice and this permission notice appear in all copies.  This software
 * is made available as is, with no warranties.
 */

mdd_t *
mdd_and_smooth(mgr, f, g, mvars)
mdd_manager *mgr;
mdd_t *f;
mdd_t *g;
array_t *mvars;
{
    int i, mv_no;
    unsigned int j;
    mvar_type mv;
    mdd_t *top;
    bdd_t *temp;

    array_t *bdd_vars = array_alloc(bdd_t *, 0);
    array_t *mvar_list = mdd_ret_mvar_list(mgr);


    if ( mvars == NIL( array_t ) ) {
	printf("\nWARNING: Empty Array of Smoothing Variables\n");
	array_free(bdd_vars);
	return ( bdd_and(f, g, 1, 1) ) ;
    }
    else if ( array_n(mvars) == 0)  {
	printf("\nWARNING: Empty Array of Smoothing Variables\n");
	array_free(bdd_vars);
	return ( bdd_and(f, g, 1, 1) ) ;
    }

    for (i=0; i<array_n(mvars); i++) {
	mv_no = array_fetch(int, mvars, i);
	mv = array_fetch(mvar_type, mvar_list, mv_no);
	if (mv.status == MDD_BUNDLED) {
	    (void) fprintf(stderr, 
		"\nmdd_andsmooth: bundled variable %s used\n",mv.name);
	    fail("");
	}


	for (j = 0;  j < mv.encode_length; j ++) {
	    temp = bdd_get_variable(mgr, mdd_ret_bvar_id(&mv,j) );
	    array_insert_last(bdd_t *, bdd_vars, temp);
	}
    }

    assert( array_n(bdd_vars) != 0 );
    top = bdd_and_smooth(f, g, bdd_vars);

    for (i = 0; i < array_n(bdd_vars); i++) {
	temp = array_fetch(bdd_t *, bdd_vars, i);
	bdd_free(temp);
    }
    array_free(bdd_vars);

    return top;
}
