#include "mdd.h"

/*
 * MDD Package
 * $Source: /projects/development/hsv/CVSRepository/utilities/common/src/mdd/mdd_uminus.c,v $
 *
 * Author: Timothy Kam
 * $Date: 1998/09/15 21:08:16 $
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
mdd_unary_minus_s(mgr, mvar1, mvar2)
mdd_manager *mgr;
int mvar1, mvar2;
{
    return (mdd_unary_minus(mgr, mvar1, mvar2));
}
