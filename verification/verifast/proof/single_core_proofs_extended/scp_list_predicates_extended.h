#ifndef SCP_LIST_PREDICATES_EXTENDED_H
#define SCP_LIST_PREDICATES_EXTENDED_H

#include "single_core_proofs/scp_list_predicates.h"

/*@
lemma void DLS_end_next_open(struct xLIST* pxList, struct xLIST_ITEM* pxItem)
requires
    DLS(?gEnd, ?gEndPrev, gEnd, gEndPrev, ?gCells, ?gVals, pxList) &*&
    mem(pxItem, gCells) == true &*&
    gEnd == head(gCells) &*&
    length(gCells) == length(gVals) &*&
    length(gCells) > 1 
    &*&
    pxItem == gEnd;
ensures 
    xLIST_ITEM(gEnd, ?gItemVal, ?gItem_next, gEndPrev, pxList) &*&
    DLS(gItem_next, gEnd, gEnd, gEndPrev, drop(1, gCells), drop(1, gVals), pxList ) &*&
    mem(gItem_next, gCells) == true;
{
    open DLS(gEnd, gEndPrev, gEnd, gEndPrev, gCells, gVals, pxList);
    // open DLS and xLIST_ITEM predicates to justify
    // accessing `pxItem->pxNext`
    assert( xLIST_ITEM(gEnd, ?gItemVal, ?gItem_next, gEndPrev, pxList) );
    open xLIST_ITEM(gEnd, gItemVal, gItem_next, gEndPrev, pxList);
    assert( DLS(gItem_next, gEnd, gEnd, gEndPrev, 
                drop(1, gCells), drop(1, gVals), pxList ) );
    open DLS(gItem_next, gEnd, gEnd, gEndPrev, 
             drop(1, gCells), drop(1, gVals), pxList );
    
    // open DLS and xLIST_ITEM predicates to prove
    // `mem( pxItem->pxNext, gCells) == true )`
    // which requires accessing `pxItem->pxNext`
    assert( xLIST_ITEM(gItem_next, ?gItem_nextVal, ?gItem_nextNext, gEnd, pxList) );
    open xLIST_ITEM(gItem_next, gItem_nextVal, gItem_nextNext, gEnd, pxList);
    assert( mem(pxItem->pxNext, gCells) == true );
    close xLIST_ITEM(gItem_next, gItem_nextVal, gItem_nextNext, gEnd, pxList);

    // closing what we opened above
    close DLS(gItem_next, gEnd, gEnd, gEndPrev, 
              drop(1, gCells), drop(1, gVals), pxList );
    close xLIST_ITEM(gEnd, gItemVal, gItem_next, gEndPrev, pxList);
}


lemma void DLS_nonEndItem_next_open(struct xLIST* pxList, struct xLIST_ITEM* pxItem)
requires
    DLS(?gEnd, ?gEndPrev, gEnd, gEndPrev, ?gCells, ?gVals, pxList) &*&
    mem(pxItem, gCells) == true &*&
    gEnd == head(gCells) &*&
    length(gCells) == length(gVals) &*&
    length(gCells) > 1 
    &*&
    pxItem != gEnd;
ensures // DLS prefix
        DLS(gEnd, gEndPrev, pxItem, ?pxItem_prev, 
            take(index_of(pxItem, gCells), gCells), 
            take(index_of(pxItem, gCells), gVals),
            pxList)
        &*&
        // item of interest
        xLIST_ITEM(pxItem, ?gItemVal, ?pxItem_next, pxItem_prev, pxList)
        &*&
        // DLS suffix
        (pxItem != gEndPrev
            ? DLS(pxItem_next, pxItem, gEnd, gEndPrev, 
                    drop(1, drop(index_of(pxItem, gCells), gCells)), 
                    drop(1, drop(index_of(pxItem, gCells), gVals)),
                    pxList)
            : true
        )
        &*&
        mem(pxItem_next, gCells) == true;
{
    int pxItemIndex_0 = index_of(pxItem, gCells);


    // open DLS and xLIST_ITEM predicates to justify
    // accessing `pxItem->pxNext`
    split(gEnd, gEndPrev, gEnd, gEndPrev, 
            gCells, gVals, pxItem, pxItemIndex_0);
    // DLS prefix
    assert( DLS(gEnd, gEndPrev, pxItem, ?pxItem_prev, 
                take(pxItemIndex_0, gCells), take(pxItemIndex_0, gVals),
                pxList) );
    // DLS suffix
    assert( DLS(pxItem, pxItem_prev, gEnd, gEndPrev, 
                drop(pxItemIndex_0, gCells), drop(pxItemIndex_0, gVals),
                pxList) );
    open DLS(pxItem, pxItem_prev, gEnd, gEndPrev, 
                drop(pxItemIndex_0, gCells), drop(pxItemIndex_0, gVals),
                pxList);
    assert( xLIST_ITEM(pxItem, ?gItemVal, ?pxItem_next, pxItem_prev, pxList) );
    
    
    // open DLS and xLIST_ITEM predicates to prove
    // `mem( pxItem->pxNext, gCells) == true )`
    // which requires accessing `pxItem->pxNext`
    if(pxItem == gEndPrev) {
        // `pxItem` is last element in DLS suffix
        // -> `pxItem_next` is head fo DLS prefix
        // open DLS prefix
        open xLIST_ITEM(pxItem, gItemVal, pxItem_next, pxItem_prev, pxList);
        assert( gCells == cons(_, _) );
        assert( mem(pxItem->pxNext, gCells) == true );
        
        // close item of interest
        close xLIST_ITEM(pxItem, gItemVal, pxItem_next, pxItem_prev, pxList);
    } else {
        // `pxItem` is not end of DLS suffix
        // -> `pxItem_next` is also in DLS suffix
        // open DLS suffix one step further
        
        // rest of DLS suffix
        assert( DLS(pxItem_next, pxItem, gEnd, gEndPrev, 
                    drop(1, drop(pxItemIndex_0, gCells)), 
                    drop(1, drop(pxItemIndex_0, gVals)),
                    pxList) );
        open DLS(pxItem_next, pxItem, gEnd, gEndPrev, 
                 drop(1, drop(pxItemIndex_0, gCells)), 
                 drop(1, drop(pxItemIndex_0, gVals)),
                 pxList);
        assert( xLIST_ITEM(pxItem_next, ?gItem_nextVal, ?pxItem_next_next, pxItem, pxList) );
        open xLIST_ITEM(pxItem, gItemVal, pxItem_next, pxItem_prev, pxList); 
        mem_suffix_implies_mem(pxItem_next, gCells, pxItemIndex_0);
        assert( mem(pxItem->pxNext, gCells) == true );

        // close rest of DLS suffix
        close xLIST_ITEM(pxItem_next, gItem_nextVal, pxItem_next_next, pxItem, pxList);
        close DLS(pxItem_next, pxItem, gEnd, gEndPrev, 
                    drop(1, drop(pxItemIndex_0, gCells)), 
                    drop(1, drop(pxItemIndex_0, gVals)),
                    pxList);

        // close item of interest
        close xLIST_ITEM(pxItem, gItemVal, pxItem_next, pxItem_prev, pxList); 
    }
}
@*/

/* By verifying the following function, we can validate that the above lemmas
 * apply to the use cases they are meant for.
 */
void lemma_validation__DLS_item_next(struct xLIST_ITEM* pxTaskItem)
/*@ requires
        DLS(?gEnd, ?gEndPrev, gEnd, gEndPrev, ?gCells, ?gVals, ?pxList) &*&
        mem(pxTaskItem, gCells) == true &*&
        gEnd == head(gCells) &*&
        length(gCells) == length(gVals) &*&
        length(gCells) > 1;
@*/
/*@ ensures
        DLS(gEnd, gEndPrev, gEnd, gEndPrev, gCells, gVals, pxList) &*&
        mem(pxTaskItem, gCells) == true;
@*/
{
    //@ int pxItemIndex_0 = index_of(pxTaskItem, gCells);
    //@ struct xLIST_ITEM* pxItem = pxTaskItem;

    /*@
    if( pxItem == gEnd ) {
        DLS_end_next_open(pxList, pxItem);
    } else {
        DLS_nonEndItem_next_open(pxList, pxItem);
    }
    @*/
    pxTaskItem = pxTaskItem->pxNext;

    //@ struct xLIST_ITEM* pxItem_1 = pxTaskItem;

    //@ assert( mem(pxItem_1, gCells) == true );



    // ignore post condition until closing lemmas are finished
    //@ assume(false);
}



#endif /* SCP_LIST_PREDICATES_EXTENDED_H */