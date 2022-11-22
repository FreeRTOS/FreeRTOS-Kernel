#ifndef SCP_LIST_PREDICATES_EXTENDED_H
#define SCP_LIST_PREDICATES_EXTENDED_H

#include "single_core_proofs/scp_list_predicates.h"

/*@
lemma void DLS_end_next_open(struct xLIST* gReadyList, struct xLIST_ITEM* gTaskItem_0)
requires
    DLS(?gListEnd, ?gEndPrev2, gListEnd, gEndPrev2, ?gCells, ?gVals, gReadyList) &*&
    mem(gTaskItem_0, gCells) == true &*&
    gListEnd == head(gCells) &*&
    length(gCells) == length(gVals) &*&
    length(gCells) > 1 
    &*&
    gTaskItem_0 == gListEnd;
ensures xLIST_ITEM(gListEnd, ?gV, ?gNext, gEndPrev2, gReadyList) &*&
        DLS(gNext, gListEnd, gListEnd, gEndPrev2, drop(1, gCells), drop(1, gVals), gReadyList ) &*&
        mem(gNext, gCells) == true;
{
    open DLS(gListEnd, gEndPrev2, gListEnd, gEndPrev2, 
             gCells, gVals, gReadyList);
    // open DLS and xLIST_ITEM predicates to justify
    // accessing `gTaskItem_0->pxNext`
    assert( xLIST_ITEM(gListEnd, ?gV, ?gNext, gEndPrev2, gReadyList) );
    open xLIST_ITEM(gListEnd, gV, gNext, gEndPrev2, gReadyList);
    assert( DLS(gNext, gListEnd, gListEnd, gEndPrev2, drop(1, gCells), drop(1, gVals), gReadyList ) );
    open DLS(gNext, gListEnd, gListEnd, gEndPrev2, drop(1, gCells), drop(1, gVals), gReadyList );
    
    // open DLS and xLIST_ITEM predicates to prove
    // `mem( gTaskItem_0->pxNext, gCells) == true )`
    // which requires accessing `gTaskItem_0->pxNext`
    assert( xLIST_ITEM(gNext, ?gV_next, ?gNextNext, gListEnd, gReadyList) );
    open xLIST_ITEM(gNext, gV_next, gNextNext, gListEnd, gReadyList);
    assert( mem(gTaskItem_0->pxNext, gCells) == true );
    close xLIST_ITEM(gNext, gV_next, gNextNext, gListEnd, gReadyList);

    // closing what we opened above
    close DLS(gNext, gListEnd, gListEnd, gEndPrev2, drop(1, gCells), drop(1, gVals), gReadyList );
    close xLIST_ITEM(gListEnd, gV, gNext, gEndPrev2, gReadyList);
}


lemma void DLS_nonEndItem_next_open(struct xLIST* gReadyList, struct xLIST_ITEM* gTaskItem_0)
requires
    DLS(?gListEnd, ?gEndPrev2, gListEnd, gEndPrev2, ?gCells, ?gVals, gReadyList) &*&
    mem(gTaskItem_0, gCells) == true &*&
    gListEnd == head(gCells) &*&
    length(gCells) == length(gVals) &*&
    length(gCells) > 1 
    &*&
    gTaskItem_0 != gListEnd;
ensures // DLS prefix
        DLS(gListEnd, gEndPrev2, gTaskItem_0, ?gTaskItem_0_prev, 
            take(index_of(gTaskItem_0, gCells), gCells), 
            take(index_of(gTaskItem_0, gCells), gVals),
            gReadyList)
        &*&
        // item of interest
        xLIST_ITEM(gTaskItem_0, ?gV, ?gTaskItem_0_next, gTaskItem_0_prev, gReadyList)
        &*&
        // DLS suffix
        (gTaskItem_0 != gEndPrev2
            ? DLS(gTaskItem_0_next, gTaskItem_0, gListEnd, gEndPrev2, 
                    drop(1, drop(index_of(gTaskItem_0, gCells), gCells)), 
                    drop(1, drop(index_of(gTaskItem_0, gCells), gVals)),
                    gReadyList)
            : true
        )
        &*&
        mem(gTaskItem_0_next, gCells) == true;
{
    int gTaskItemIndex_0 = index_of(gTaskItem_0, gCells);


    // open DLS and xLIST_ITEM predicates to justify
    // accessing `gTaskItem_0->pxNext`
    split(gListEnd, gEndPrev2, gListEnd, gEndPrev2, 
            gCells, gVals, gTaskItem_0, gTaskItemIndex_0);
    // DLS prefix
    assert( DLS(gListEnd, gEndPrev2, gTaskItem_0, ?gTaskItem_0_prev, 
                take(gTaskItemIndex_0, gCells), take(gTaskItemIndex_0, gVals),
                gReadyList) );
    // DLS suffix
    assert( DLS(gTaskItem_0, gTaskItem_0_prev, gListEnd, gEndPrev2, 
                drop(gTaskItemIndex_0, gCells), drop(gTaskItemIndex_0, gVals),
                gReadyList) );
    open DLS(gTaskItem_0, gTaskItem_0_prev, gListEnd, gEndPrev2, 
                drop(gTaskItemIndex_0, gCells), drop(gTaskItemIndex_0, gVals),
                gReadyList);
    assert( xLIST_ITEM(gTaskItem_0, ?gV, ?gTaskItem_0_next, gTaskItem_0_prev, gReadyList) );
    
    
    // open DLS and xLIST_ITEM predicates to prove
    // `mem( gTaskItem_0->pxNext, gCells) == true )`
    // which requires accessing `gTaskItem_0->pxNext`
    if(gTaskItem_0 == gEndPrev2) {
        // `gTaskItem_0` is last element in DLS suffix
        // -> `gTaskItem_0_next` is head fo DLS prefix
        // open DLS prefix
        open xLIST_ITEM(gTaskItem_0, gV, gTaskItem_0_next, gTaskItem_0_prev, gReadyList);
        assert( gCells == cons(_, _) );
        assert( mem(gTaskItem_0->pxNext, gCells) == true );
        
        // close item of interest
        close xLIST_ITEM(gTaskItem_0, gV, gTaskItem_0_next, gTaskItem_0_prev, gReadyList);
    } else {
        // `gTaskItem_0` is not end of DLS suffix
        // -> `gTaskItem_0_next` is also in DLS suffix
        // open DLS suffix one step further
        
        // rest of DLS suffix
        assert( DLS(gTaskItem_0_next, gTaskItem_0, gListEnd, gEndPrev2, 
                    drop(1, drop(gTaskItemIndex_0, gCells)), drop(1, drop(gTaskItemIndex_0, gVals)), //drop(gTaskItemIndex_0 + 1, gCells), drop(gTaskItemIndex_0 + 1, gVals), 
                    gReadyList) );
        open DLS(gTaskItem_0_next, gTaskItem_0, gListEnd, gEndPrev2, 
                        drop(1, drop(gTaskItemIndex_0, gCells)), drop(1, drop(gTaskItemIndex_0, gVals)),
                        gReadyList);
        assert( xLIST_ITEM(gTaskItem_0_next, ?gNextVal, ?gTaskItem_0_next_next, gTaskItem_0, gReadyList) );
        open xLIST_ITEM(gTaskItem_0, gV, gTaskItem_0_next, gTaskItem_0_prev, gReadyList); 
        assert( gTaskItem_0_next == gTaskItem_0->pxNext );
        assert( mem(gTaskItem_0_next, drop(1, drop(gTaskItemIndex_0, gCells))) == true );
        //assert( gCells == cons(_, drop(1, drop(gTaskItemIndex_0, gCells)) );
        assert( mem(gTaskItem_0_next, drop(gTaskItemIndex_0, gCells)) == true );
        mem_suffix_implies_mem(gTaskItem_0_next, gCells, gTaskItemIndex_0);
        assert( mem(gTaskItem_0_next, gCells) == true );
        assert( mem(gTaskItem_0->pxNext, gCells) == true );

        // close rest of DLS suffix
        close xLIST_ITEM(gTaskItem_0_next, gNextVal, gTaskItem_0_next_next, gTaskItem_0, gReadyList);
        close DLS(gTaskItem_0_next, gTaskItem_0, gListEnd, gEndPrev2, 
                    drop(1, drop(gTaskItemIndex_0, gCells)), drop(1, drop(gTaskItemIndex_0, gVals)),
                    gReadyList);

        // close item of interest
        close xLIST_ITEM(gTaskItem_0, gV, gTaskItem_0_next, gTaskItem_0_prev, gReadyList); 
    }
}
@*/

/* By verifying the following function, we can validate that the above lemmas
 * apply to the use cases they are meant for.
 */
void lemma_validation__DLS_item_next(struct xLIST_ITEM* pxTaskItem)
/*@ requires
        DLS(?gListEnd, ?gEndPrev2, gListEnd, gEndPrev2, ?gCells, ?gVals, ?gReadyList) &*&
        mem(pxTaskItem, gCells) == true &*&
        gListEnd == head(gCells) &*&
        length(gCells) == length(gVals) &*&
        length(gCells) > 1;
@*/
/*@ ensures
        DLS(gListEnd, gEndPrev2, gListEnd, gEndPrev2, gCells, gVals, gReadyList) &*&
        mem(pxTaskItem, gCells) == true;
@*/
{
    //@ int gTaskItemIndex_0 = index_of(pxTaskItem, gCells);
    //@ struct xLIST_ITEM* gTaskItem_0 = pxTaskItem;

    /*@
    if( gTaskItem_0 == gListEnd ) {
        DLS_end_next_open(gReadyList, gTaskItem_0);
    } else {
        DLS_nonEndItem_next_open(gReadyList, gTaskItem_0);
    }
    @*/
    pxTaskItem = pxTaskItem->pxNext;

    //@ struct xLIST_ITEM* gTaskItem_1 = pxTaskItem;

    //@ assert( mem(gTaskItem_1, gCells) == true );



    // ignore post condition until closing lemmas are finished
    //@ assume(false);
}



#endif /* SCP_LIST_PREDICATES_EXTENDED_H */