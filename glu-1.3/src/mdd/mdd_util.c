#include <stdio.h>
#include <math.h>
#include "util.h"
#include "mdd.h"

/*
 * MDD Package
 * $Source: /projects/development/hsv/CVSRepository/utilities/common/src/mdd/mdd_util.c,v $
 *
 * Author: Timothy Kam
 * $Date: 1998/09/16 00:21:29 $
 * $Revision: 1.12 $
 * $Id: mdd_util.c,v 1.12 1998/09/16 00:21:29 mooni Exp $
 * $Log: mdd_util.c,v $
 * Revision 1.12  1998/09/16 00:21:29  mooni
 * Added mdd_get_var_by_id.
 *
 * Revision 1.11  1998/09/15 21:08:16  ravi
 * Merged changes.
 *
 * Revision 1.1.1.7  1998/05/04 01:44:13  hsv
 * Berkeley 1.3 Alpha release
 *
 * Revision 1.2  1997/02/25 00:27:07  boldvis
 * Alignment between Boulder and Berkeley source code before the release
 *
 * Revision 1.5  1997/02/12 21:26:52  hsv
 * Fixed import conflicts.
 *
 * Revision 1.4  1996/11/04 22:59:45  hsv
 * Fixed spurious conflicts.
 *
 * Revision 1.3  1996/03/06 22:11:19  hsv
 * fixed the conflict
 *
 * Revision 1.2  1995/12/28 00:57:23  hsv
 * New version inside glu1.0
 * Revision 1.1.1.5  1996/11/04 22:52:29  hsv
 * Glu Version 1.1
 *
 * Revision 1.1  1996/01/18 19:00:37  shaz
 * Initial revision
 *
 * Revision 1.1  1996/01/18 18:21:27  shaz
 * Initial revision
 *
 * Revision 1.1  1996/01/18 02:31:47  shaz
 * Initial revision
 *
 * Revision 1.16  1995/08/08 22:40:49  rajeev
 * Changes made by shazqadeer.420 as of 8/8/95
 *
 * Revision 1.14  1994/07/08  23:08:42  gms
 * Bug fixed: Was too enthusiastic about freeing arrays
 *
 *
 * Copyright 1992 by the Regents of the University of California.
 *
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software is hereby granted, provided that the above copyright
 * notice and this permission notice appear in all copies.  This software
 * is made available as is, with no warranties.
 */

/****************************** FROM RAMIN ******************************/
	double		mdd_count_onset( );
	array_t*	mddRetBinVars( );
	array_t*	mdd_ret_arr_bin_vars( ); /* was mddRetArrBinVars */

static	bdd_t*		mddRetOnvalBdd( );
static	bdd_t*		mddIntRetOnvalBdd( );
	void		mddFreeBddArr( );
        mdd_t*          mdd_cproject( );
/***************************send bugs to gms***********************************/
extern bdd_t* bdd_cproject();
extern bdd_t* mdd_cproject();

/************************************************************************/
extern	double		bdd_count_onset( );
extern	mdd_t*		mdd_forall( );
	
/************************************************************************/
#define		mddGetVarById( mgr, id )	\
    array_fetch(mvar_type, mdd_ret_mvar_list((mgr)),(id))


int
toggle(x)
int x;
{
    if (x == 0) return 1;
    else {
	if (x == 1) return 0;
	else {
	    fail("toggle: invalid boolean value\n");
	    return -1;
	}
    }
}

int
no_bit_encode(n)
int n;
{
    int i = 0;
    int j = 1;

    if (n < 2) return 1; /* Takes care of mv.values <= 1 */

    while (j < n) {
	j = j * 2;
	i++;
    }
    return i;
}

void
print_mvar_list(mgr)
mdd_manager *mgr;
{
    mvar_type mv;
    int i;
    int no_mvar;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);

    no_mvar = array_n(mvar_list);
    printf("print_mvar_list:\n");
    printf("id\tname\tvalues\tbits\tstride\tstart_vertex\n");
    for (i=0; i<no_mvar; i++) {
        mv = array_fetch(mvar_type, mvar_list, i);
        (void) printf("%d\t%s\t%d\t%d\n", 
		mv.mvar_id, mv.name, mv.values, 
		mv.encode_length);
    }
}

void
print_strides(mvar_strides)
array_t *mvar_strides;
{
    int i, s;

    (void) printf("mvar_strides: ");
    for (i=0; i<array_n(mvar_strides); i++) {
        s = array_fetch(int, mvar_strides, i);
        (void) printf("%d ", s);
    }
    (void) printf("\n");
}

void
print_bdd_list_id(bdd_list)
array_t *bdd_list;
{
    bdd_t *b;
    int i, is_complemented;

    (void) printf("bdd_list id's: ");
    for (i=0; i<array_n(bdd_list); i++) {
        b = array_fetch(bdd_t *, bdd_list, i);
        (void)bdd_get_node(b, &is_complemented);
        if (is_complemented) (void) printf("!");
        (void) printf("%d ", bdd_top_var_id(b));
    }
    (void) printf("\n");
}

void
print_bvar_list_id(mgr)
mdd_manager *mgr;
{
    bvar_type bv;
    int i, is_complemented;
    array_t *bvar_list = mdd_ret_bvar_list(mgr);
 
    (void) printf("bvar_list id's: ");
    for (i=0; i<array_n(bvar_list); i++) {
        bv = array_fetch(bvar_type, bvar_list, i);
        (void)bdd_get_node(bv.node,&is_complemented);
        if (is_complemented) (void) printf("!");
	(void) printf("%d ", bdd_top_var_id(bv.node));
    }
    (void) printf("\n");
}

void
print_bdd(mgr, top)
bdd_manager *mgr;
bdd_t *top;  
{

    int is_complemented;
    bdd_t *child, *top_uncomp;

    if (bdd_is_tautology(top,1)) {
	(void) printf("ONE ");
        return;
    }
    if (bdd_is_tautology(top,0)) {
	(void) printf("ZERO ");
        return;
    }
    (void)bdd_get_node(top, &is_complemented);
    if (is_complemented != 0) (void) printf("!");
    (void) printf("%d ", bdd_top_var_id(top));
    (void) printf("v ");
    (void) printf("< ");

    if (is_complemented) top_uncomp = bdd_not(top);
    else top_uncomp = mdd_dup(top);

    child = bdd_then(top);

    print_bdd(mgr, child);
    (void) printf("> ");

    mdd_free(child);
    child = bdd_else(top);

    print_bdd(mgr, child);
    (void) printf("^ ");
    
    mdd_free(top_uncomp);
    mdd_free(child);

    return;
}

mvar_type 
find_mvar_id(mgr, id)
mdd_manager *mgr;
unsigned short id;
{
    mvar_type mv;
    bvar_type bv;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);
    array_t *bvar_list = mdd_ret_bvar_list(mgr);

    if (id >= array_n(bvar_list))
    	fail("find_mvar_id: invalid parameter range for id\n");
    bv = array_fetch(bvar_type, bvar_list, id);
    if ((bv.mvar_id < 0) || (bv.mvar_id >= array_n(mvar_list)))
    	fail("find_mvar_id: bvar contains invalid mvar_id\n");
    mv = array_fetch(mvar_type, mvar_list, bv.mvar_id);
    return mv;
}

void
clear_all_marks(mgr)
mdd_manager *mgr;
{
    int i, j;
    mvar_type mv;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);


    for (i=0; i<array_n(mvar_list); i++) {
	mv = array_fetch(mvar_type, mvar_list, i);
	for (j=0; j<mv.encode_length; j++)
	    mv.encoding[j] = 2;
    }
}

void
mdd_mark(mgr, top, phase)
mdd_manager *mgr;
bdd_t *top; /**** was bdd_node *bnode; --- changed by Serdar ***/
int phase;
{
    int i, top_id, found = 0;
    int bit_position = 0; /* initialize for lint */
    mvar_type mv;

    top_id = bdd_top_var_id(top);
    mv = find_mvar_id(mgr, top_id);

    for (i=0; i<(mv.encode_length); i++){
		if ( mdd_ret_bvar_id( &mv, i) == top_id ){
			bit_position = i;
			found = 1;
			break;
		};
    };
   
    
    if (found == 0)
	fail("mdd_mark: interleaving error\n");

    mv.encoding[bit_position] = phase;
    
}

void
mdd_unmark(mgr, top)
mdd_manager *mgr;
bdd_t *top; 
{
    int i, top_id, found = 0;
    int bit_position = 0; /* initialize for lint */
    mvar_type mv;


    top_id = bdd_top_var_id(top);
    mv = find_mvar_id(mgr, top_id);

    for (i=0; i<mv.encode_length; i++) 
		if ( mdd_ret_bvar_id( &mv, i) == top_id ){
			bit_position = i;
			found = 1;
			break;
		};

    if (found == 0)
	fail("mdd_unmark: interleaving error\n");
    mv.encoding[bit_position] = 2;
}

mvar_type 
find_mvar(mgr, name)
mdd_manager *mgr;
char *name;
{
    int i;
    mvar_type mv;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);

    for (i=0; i<array_n(mvar_list); i++) {
	mv = array_fetch(mvar_type, mvar_list, i);
        if (strcmp(mv.name, name) == 0) return mv;
    }
    fail("find_mvar: cannot find name in mvar_list\n");
    return mv;
}

array_t *
mdd_ret_mvar_list(mgr)
mdd_manager *mgr;
{
    bdd_external_hooks *hook;    
    array_t *mvar_list;

    hook =  bdd_get_external_hooks(mgr);
    mvar_list = ((mdd_hook_type *)(hook->mdd))->mvar_list;

    return mvar_list;
}

void
mdd_set_mvar_list(mgr, mvar_list)
mdd_manager *mgr;
array_t *mvar_list;
{
    bdd_external_hooks *hook;    

    hook =  bdd_get_external_hooks(mgr);
    ((mdd_hook_type *)(hook->mdd))->mvar_list = mvar_list;
}


array_t *
mdd_ret_bvar_list(mgr)
mdd_manager *mgr;
{
    bdd_external_hooks *hook;    
    array_t *bvar_list;

    hook =  bdd_get_external_hooks(mgr);
    bvar_list = ((mdd_hook_type *)(hook->mdd))->bvar_list;

    return bvar_list;
}


int
mdd_ret_bvar_id(mvar_ptr, i)
mvar_type *mvar_ptr;
int i;
{
	
	return ( array_fetch(int, mvar_ptr->bvars, i) );
}

bvar_type
mdd_ret_bvar(mvar_ptr, i, bvar_list)
mvar_type *mvar_ptr;
int i;
array_t *bvar_list;
{
	int bvar_id;
	
	bvar_id = array_fetch(int, mvar_ptr->bvars, i);
	
	return array_fetch(bvar_type, bvar_list, bvar_id);
}

/************************************************************************/
/* This pacakege implements counting the num of onset points of an Mdd.	*/
/************************************************************************/
/* Given an Mdd, returns the num of onset points.  By construction of	*/
/* Mdd's, some points not in the range of Mdd vars may be inculded 	*/
/* in the onset. These fake points must first be removed.		*/

double
mdd_count_onset( mddMgr, aMdd, mddIdArr )
	mdd_manager	*mddMgr;
	mdd_t		*aMdd;
	array_t		*mddIdArr;
{	
	bdd_t		*onvalBdd, *aOnvalBdd, *onsetBdd, *tmpBdd;
	double		onsetNum;
	array_t		*bddVarArr;
	int		i, arrSize, mddId;

	arrSize = array_n( mddIdArr );
	onvalBdd = bdd_one( mddMgr );

	for ( i = 0 ; i < arrSize ; i++ ) {
	    mddId = array_fetch( int, mddIdArr, i );
	    aOnvalBdd = mddRetOnvalBdd( mddMgr, mddId );

	    tmpBdd = bdd_and( onvalBdd, aOnvalBdd, 1, 1 );
	    bdd_free( onvalBdd );
	    bdd_free( aOnvalBdd );
	    onvalBdd = tmpBdd;
	}
	onsetBdd = bdd_and( onvalBdd, aMdd, 1, 1 );
	bdd_free( onvalBdd );

	bddVarArr = mdd_ret_arr_bin_vars( mddMgr, mddIdArr );
	onsetNum = bdd_count_onset( onsetBdd, bddVarArr );
	bdd_free( onsetBdd );
	mddFreeBddArr( bddVarArr );
	return( onsetNum );
}		/* mdd_count_onset */

/************************************************************************/
array_t*
mddRetBinVars( mddMgr, mddId )
	mdd_manager	*mddMgr;
	int		mddId;
{
	array_t		*bddVarArr;
	mvar_type	mVar;
	unsigned int	i, j;

	mVar = mddGetVarById( mddMgr, mddId );
	bddVarArr = array_alloc( bdd_t *, mVar.encode_length );	

        for (i = 0 ; i <  mVar.encode_length ; i++ ) {
	    j = mdd_ret_bvar_id( &mVar, i);
	    array_insert_last( bdd_t *, bddVarArr, 
			       bdd_get_variable( mddMgr, j ));
	}
	return( bddVarArr );
}		/* mddRetBinVars */

/************************************************************************/
/* Returns an array of binary vars (bdd_t *'s), given an array of 	*/
/* Mdd id's.								*/

array_t*
mdd_ret_arr_bin_vars( mddMgr, mddIdArr )
	mdd_manager	*mddMgr;
	array_t		*mddIdArr;
{
	array_t		*bddVarArr;
	unsigned int	k, j, i, arrSize;
	mvar_type	mVar;

	bddVarArr = array_alloc( bdd_t *, 3 * array_n( mddIdArr ));	

	arrSize = array_n( mddIdArr );
	for ( i = 0 ; i < arrSize ; i++ ) {
	    mVar = mddGetVarById( mddMgr, array_fetch( int, mddIdArr, i ));
            for ( k = 0 ; k < mVar.encode_length ; k++ ) {
		j = mdd_ret_bvar_id( &mVar, k);
		array_insert_last( bdd_t *, bddVarArr, 
				   bdd_get_variable( mddMgr, j ));
	    }
	}
	return( bddVarArr );
}		/* mdd_ret_arr_bin_vars */

/************************************************************************/
static	bdd_t*
mddRetOnvalBdd( mddMgr, mddId )
	mdd_manager	*mddMgr;
	int		mddId;
{
	bdd_t		*onvalBdd;
	mvar_type	mVar;
	int		valNum, high;
	array_t		*bddVarArr;	
	
	mVar = mddGetVarById( mddMgr, mddId );
	valNum = mVar.values;
	high = (int) pow( (double) 2, (double) mVar.encode_length ); 
	assert( (valNum == 1)  || ( (valNum <= high) && (valNum > high/2) ));
	if ( valNum == high )
	    onvalBdd = bdd_one( mddMgr );
	else {
	    bddVarArr = mddRetBinVars( mddMgr, mddId );
	    onvalBdd = mddIntRetOnvalBdd( mddMgr, valNum, 0, high, 
					  0, bddVarArr );
	    mddFreeBddArr( bddVarArr );
	}
	return( onvalBdd );
}		/* mddRetOnvalBdd */	

/************************************************************************/
static	bdd_t*
mddIntRetOnvalBdd( mddMgr, valNum, low, hi, level, bddVarArr )
	mdd_manager	*mddMgr;
	int		valNum, low, hi, level;
	array_t		*bddVarArr;
{
	int		mid;
	bdd_t		*curVar, *recBdd, *tmpBdd;
	bdd_t		*onvalBdd = NIL(bdd_t); /* initialized for lint */

	mid = (low + hi) / 2;
		curVar = array_fetch( bdd_t *, bddVarArr, level );

	if 	( valNum > mid ) {
	    recBdd = mddIntRetOnvalBdd( mddMgr, valNum, mid, hi, 
					level+1, bddVarArr );
	    tmpBdd = bdd_and( recBdd, curVar, 1, 1 );
	    bdd_free( recBdd );
	    onvalBdd = bdd_or( tmpBdd, curVar, 1, 0 );
	    bdd_free( tmpBdd );
	}
	else if ( valNum < mid ) {
	    recBdd = mddIntRetOnvalBdd( mddMgr, valNum, low, mid, 
					level+1, bddVarArr );
	    onvalBdd = bdd_and( recBdd, curVar, 1, 0 );
	    bdd_free( recBdd );
	}
	else if ( valNum == mid ) 
	    onvalBdd = bdd_not( curVar );
	return( onvalBdd );
}		/* mddIntRetOnvalBdd */

/************************************************************************/
/* Given an array of bdd nodes, frees the array.			*/

void
mddFreeBddArr( bddArr )
	array_t	*bddArr;
{
	int	i, arrSize;

	arrSize = array_n( bddArr );
	for ( i = 0 ; i < arrSize ; i++ ) 
	    bdd_free( array_fetch( bdd_t *, bddArr, i ) );
	array_free( bddArr );
}		/* mddFreeBddArr */

array_t  *
mdd_ret_bvars_of_mvar( mvar_ptr )
mvar_type	*mvar_ptr;
{

	return mvar_ptr->bvars;
}

/************************************************************************/
/* mdd_get_care_set returns the care set of the mdd manager */ 

mdd_t *mdd_get_care_set(mdd_mgr)
    mdd_manager *mdd_mgr;
{
    mdd_t *temp;
    mvar_type mv;
    mdd_manager *bdd_mgr;

    int mvar_id,i,j,val_j,value;
    array_t *mvar_list, *bvar_list;
    bdd_t *care_set, *care_val, *care_cube,*bit_j;
    
    mvar_list = mdd_ret_mvar_list(mdd_mgr);
    bvar_list = mdd_ret_bvar_list(mdd_mgr);
    bdd_mgr = mdd_mgr;
    
    care_set = bdd_one(bdd_mgr);
    
    for (mvar_id =0; mvar_id < array_n(mvar_list); mvar_id++)
        {
            mv = array_fetch(mvar_type, mvar_list, mvar_id);
            care_val = bdd_zero(bdd_mgr);
                
            for (i=0; i< (mv.values); i++)
                {
                    value = i;
                    care_cube = bdd_one(bdd_mgr);
                    for(j=0; j< mv.encode_length; j++ )
                        {
                            bit_j = bdd_get_variable(bdd_mgr,mdd_ret_bvar_id(&mv, j));
                            val_j = value % 2;
                            value = value/2;
                            temp = care_cube;
                            care_cube = bdd_and(temp,bit_j,1,val_j);
                            bdd_free(temp);
                        }
                    temp = care_val;
                    care_val = bdd_or(temp,care_cube,1,1);
                    bdd_free(temp);
                    bdd_free(care_cube);
                }
            temp = care_set;
            care_set = bdd_and(temp,care_val,1,1);
            bdd_free(care_val);
            bdd_free(temp);
        }
    return care_set;
}

/* Corrected mdd_cproject */
/* returns only valid carepoints */

mdd_t *mdd_cproject(mgr,T,mvars)
    mdd_manager *mgr;
    mdd_t *T;
    array_t *mvars;
{
    mdd_t *care_set, *new_T, *T_proj;
     array_t *bdd_vars;
    int i, mv_no;
    unsigned int j;
    mvar_type mv;
    bdd_t *temp;
    array_t *mvar_list = mdd_ret_mvar_list(mgr);


    care_set = mdd_get_care_set(mgr);
    new_T = bdd_and(T,care_set,1,1);
    bdd_free(care_set);

      if ( mvars == NIL(array_t) ) {
        T_proj = bdd_dup(T);
        printf("\nWARNING: Empty Array of Smoothing Variables\n");
        return T_proj;
    }
    else if ( array_n(mvars) == 0) {
        T_proj = bdd_dup(T);
        printf("\nWARNING: Empty Array of Smoothing Variables\n");
        return T_proj;
    }
                
        
    bdd_vars = array_alloc(bdd_t*, 0);     
    for (i=0; i<array_n(mvars); i++) {
        mv_no = array_fetch(int, mvars, i);
        mv = array_fetch(mvar_type, mvar_list, mv_no);
        if (mv.status == MDD_BUNDLED) {
            (void) fprintf(stderr, 
                        "\nmdd_smooth: bundled variable %s used\n",mv.name);
            fail("");
        }

        for (j = 0;j < mv.encode_length; j ++) {
            temp = bdd_get_variable(mgr, mdd_ret_bvar_id(&mv,j) );
            array_insert_last(bdd_t *, bdd_vars, temp);
        }
    }
        
  
    T_proj = bdd_cproject(new_T,bdd_vars);
    bdd_free(new_T);

    for (i=0; i<array_n(bdd_vars); i++) {
        temp = array_fetch(bdd_t *, bdd_vars, i);
        bdd_free(temp);
    }
    array_free(bdd_vars);

    
    return T_proj;
}

void
mdd_print_support(mdd_manager *mgr, mdd_t *f)
{
    array_t *support_list = mdd_get_support(mgr, f);
    array_t *mvar_list = mdd_ret_mvar_list(mgr);
    int nSupports = array_n(support_list);
    int i, j;
    mvar_type mv;
    int id;

    for (i = 0; i < nSupports; i++) {
	id = array_fetch(int, support_list, i);
	mv = array_fetch(mvar_type, mvar_list, id);
	if (id == mv.mvar_id)
	    printf("[%d] = %s\n", i, mv.name);
	else { /* needs to be checked */
	    for (j = 0; j < array_n(mvar_list); j++) {
		mv = array_fetch(mvar_type, mvar_list, j);
		if (id == mv.mvar_id) {
		    printf(" [%d] = %s", i, mv.name);
		    break;
		}
	    }
	}
    }
    printf("\n");
}

/**Function********************************************************************

  Synopsis    [Returns an array of BDD ids corresponding to a MDD variable.]

  Description [This function takes an MddId. It returns an array of BDD ids
  corresponding to the bits.]

  SideEffects []

******************************************************************************/
array_t *
mdd_id_to_bdd_id_array(mdd_manager *mddManager, int mddId)
{
  array_t     *bddIdArray;
  mvar_type   mddVar;
  unsigned int    i, j;
  
  mddVar = array_fetch(mvar_type, mdd_ret_mvar_list(mddManager), mddId);
  bddIdArray = array_alloc(int, mddVar.encode_length);
  
  for (i=0; i<mddVar.encode_length; i++){
    j = mdd_ret_bvar_id(&mddVar, i);
    array_insert_last(int, bddIdArray, j);
  }
  return bddIdArray;
}

/**Function********************************************************************

  Synopsis    [Returns an array of Bdd_t's corresponding to a Mdd variable.]

  Description [This function takes an MddId. It returns an array of bdd_t's
  corresponding to the bits.]

  SideEffects []

******************************************************************************/
array_t *
mdd_id_to_bdd_array(mdd_manager *mddManager, int mddId)
{
  array_t     *bddArray;
  mvar_type   mddVar;
  unsigned int    i, j;
  
  mddVar = array_fetch(mvar_type, mdd_ret_mvar_list(mddManager), mddId);
  bddArray = array_alloc(bdd_t*, mddVar.encode_length);
  
  for (i=0; i<mddVar.encode_length; i++){
    j = mdd_ret_bvar_id(&mddVar, i);
    array_insert_last(bdd_t*, bddArray,
                      bdd_get_variable((bdd_manager *)mddManager, j));
  }
  return bddArray;
}


/**Function********************************************************************

  Synopsis    [Returns an array of Bdd_t's corresponding to an array of Mdd
  ids.] 

  Description [This function takes an array of MddId's. For each MddId it
  returns an array of bdd_t's corresponding to the bits. These arrays of bdd_ts
  are concatenated together and returned.]

  SideEffects []

******************************************************************************/
array_t *
mdd_id_array_to_bdd_array(mdd_manager *mddManager, array_t *mddIdArray)
{
  array_t *bddArray;
  int i;

  bddArray = array_alloc(bdd_t*, 0);
  for (i=0; i<array_n(mddIdArray); i++){
    int mddId;
    array_t *tmpBddArray;
    
    mddId = array_fetch(int, mddIdArray, i);
    tmpBddArray = mdd_id_to_bdd_array(mddManager, mddId);
    array_append(bddArray, tmpBddArray);
    array_free(tmpBddArray);
  }
  return bddArray;
}

/**Function********************************************************************

  Synopsis    [Returns an array of bddId's corresponding to an array of Mdd
  ids.] 

  Description [This function takes an array of MddId's. For each MddId it
  returns an array of bddId's corresponding to the bits. These arrays of bddId's
  are concatenated together and returned.]

  SideEffects []

******************************************************************************/
array_t *
mdd_id_array_to_bdd_id_array(mdd_manager *mddManager, array_t *mddIdArray)
{
  array_t *bddIdArray;
  int i;

  bddIdArray = array_alloc(int, 0);
  for (i=0; i<array_n(mddIdArray); i++){
    int mddId;
    array_t *tmpBddIdArray;
    mddId = array_fetch(int, mddIdArray, i);
    tmpBddIdArray = mdd_id_to_bdd_id_array(mddManager, mddId);
    array_append(bddIdArray, tmpBddIdArray);
    array_free(tmpBddIdArray);
  }
  return bddIdArray;
}

/**Function********************************************************************

  Synopsis [Given an Mvf representing the functionality of a multi-valued
  variable, it returns an array of Bdd's representing the characteristic
  function of the relation of the various bits of the multi-valued variable.] 

  Description [Suppose y is a k-valued variable and takes values
              0,1,..,k-1. Then the input to this function is an array with k
              Mdds each representing the onset of the respective value of the
              variable (the ith Mdd representing the onset when y takes the
              value (i-1). Suppose m bits are needed to encode the k values of
              y. Then internally y is represented as y_0, y_1, ...,
              y_(m-1). Now the functionality of each bit of y can be computed
              by proper boolean operation on the functions representing the
              onsets of various values of y. For instance if y is a 4-valued
              variable. To achieve that we do the following:
              For each bit b{
                relation = 0;
                For each value j of the variable{
                  Ej = Encoding function of the jth value
                  Fj = Onset function of the jth value
                  If (b appears in the positive phase in Ej) then
                     relation += b * Fj 
                  else if (b appears in the negative phase in Ej) then
                     relation += b'* Fj
                  else if (b does not appear in Ej) then
                     relation += Ej
                }
              }
              Note that the above algorithm does not handle the case when a
              bit appears in both phases in the encoding of any value of the
              variable. Hence the assumption behind the above algorithm is that
              the values are encoded as cubes.
              The case when the encoding are functions can be handled by more
              complex algorithm. In that case, we will not be able to build the
              relation for each bit separately. Something to be dealt with in
              the later work.
              ]              
  SideEffects []

******************************************************************************/
array_t *
mdd_fn_array_to_bdd_rel_array(mdd_manager *mddManager, int mddId,
                              array_t *mddFnArray)
{
  array_t *bddRelationArray, *mddLiteralArray, *valueArray, *bddArray;
  mvar_type mddVar;
  int i, j, numValues, numEncodingBits;
  
  mddVar = array_fetch(mvar_type, mdd_ret_mvar_list(mddManager), mddId);
  numValues = array_n(mddFnArray);
  assert(mddVar.values == numValues);

  /*
   * The following is to check whether each encoding is cube or not.
   * Since Berkeley MDD package always does the cube encoding this checking has
   * been turned off currently.
   */
  
  valueArray = array_alloc(int, 1);
  mddLiteralArray = array_alloc(mdd_t*, 0);
  for (i=0; i<numValues; i++){
    mdd_t *mddLiteral;
    
    array_insert(int, valueArray, 0, i);
    /* Form the Mdd corresponding to this value */
    mddLiteral = mdd_literal(mddManager, mddId, valueArray);
    /* Check if this is a cube */
    if (bdd_is_cube(mddLiteral) == FALSE){ 
       fprintf(stderr, "The encoding of the variable %s for the value %d isnot a cube.\n It can result in wrong answers.\n", mddVar.name, i); 
    } 
    array_insert_last(mdd_t*, mddLiteralArray, mddLiteral);
  }
  array_free(valueArray);

  bddRelationArray = array_alloc(bdd_t*, 0);
  numEncodingBits = mddVar.encode_length;
  bddArray = mdd_id_to_bdd_array(mddManager, mddId);
  for (i=0; i<numEncodingBits; i++){
    bdd_t *bdd, *bddRelation, *bddNot;

    bddRelation = bdd_zero((bdd_manager *)mddManager);
    bdd = array_fetch(bdd_t*, bddArray, i);
    bddNot = bdd_not(bdd);
    for (j=0; j<numValues; j++){
      bdd_t *mddFn, *posCofactor, *negCofactor, *tmpBddRelation;
      mdd_t *mddLiteral, *literalRelation;
      
      mddLiteral = array_fetch(mdd_t*, mddLiteralArray, j);
      posCofactor = bdd_cofactor(mddLiteral, bdd);
      negCofactor = bdd_cofactor(mddLiteral, bddNot);
      mddFn = array_fetch(mdd_t*, mddFnArray, j);
      if (bdd_is_tautology(posCofactor, 0)){
        literalRelation = bdd_and(bddNot, mddFn, 1, 1);
      }
      else if (bdd_is_tautology(negCofactor, 0)){
        literalRelation = bdd_and(bdd, mddFn, 1, 1);
      }
      else {
        assert(bdd_equal(posCofactor, negCofactor));
        literalRelation = bdd_dup(mddFn);
      }
      bdd_free(posCofactor);
      bdd_free(negCofactor);
      tmpBddRelation = bdd_or(bddRelation, literalRelation, 1, 1);
      bdd_free(literalRelation);
      bdd_free(bddRelation);
      bddRelation = tmpBddRelation;
    }
    array_insert_last(bdd_t*, bddRelationArray, bddRelation);
    bdd_free(bdd);
    bdd_free(bddNot);
  }
  /* Free stuff */
  mdd_array_free(mddLiteralArray);
  array_free(bddArray);
  return bddRelationArray;
}


array_t *
mdd_pick_arbitrary_minterms(mddMgr, aMdd, mddIdArr, n)
  mdd_manager	*mddMgr;
  mdd_t		*aMdd;
  array_t	*mddIdArr;
  int		n;
{
    bdd_t	*onvalBdd, *aOnvalBdd, *onsetBdd, *tmpBdd;
    array_t	*bddVarArr;
    int		i, arrSize, mddId;
    array_t	*mintermArray;

    arrSize = array_n( mddIdArr );
    onvalBdd = bdd_one( mddMgr );

    for ( i = 0 ; i < arrSize ; i++ ) {
	mddId = array_fetch( int, mddIdArr, i );
	aOnvalBdd = mddRetOnvalBdd( mddMgr, mddId );

	tmpBdd = bdd_and( onvalBdd, aOnvalBdd, 1, 1 );
	bdd_free( onvalBdd );
	bdd_free( aOnvalBdd );
	onvalBdd = tmpBdd;
    }
    onsetBdd = bdd_and( onvalBdd, aMdd, 1, 1 );
    bdd_free( onvalBdd );

    bddVarArr = mdd_ret_arr_bin_vars(mddMgr, mddIdArr);
    mintermArray = bdd_bdd_pick_arbitrary_minterms(onsetBdd, bddVarArr,
	array_n(bddVarArr), n);
    bdd_free(onsetBdd);
    mddFreeBddArr(bddVarArr);
    return(mintermArray);
}


/* Internal macro to access the mvar_type structure for each MDD variable. */
mvar_type
mdd_get_var_by_id(mddMgr, id)
  mdd_manager	*mddMgr;
  int		id;
{
    return(mddGetVarById(mddMgr, id));
}
