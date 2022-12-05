#ifndef READY_LIST_PREDICATES_H
#define READY_LIST_PREDICATES_H

#include "single_core_proofs/scp_list_predicates.h"


#include "verifast_lists_extended.h"


/*@
// TODO: We know that the list of priority 0 is never empty.
//       It contains the idle task and nothing else.
predicate readyLists_p(list<list<struct xLIST_ITEM*> > gCellLists,
                       list<list<void*> > gOwnerLists) =
    configMAX_PRIORITIES == length(gCellLists) &*&
    List_array_p(&pxReadyTasksLists, configMAX_PRIORITIES, 
                 gCellLists, gOwnerLists) &*&
    length(gCellLists) == length(gOwnerLists) &*&
    // List of priority 0 always contains the idle task and the end marker
    // nothing else
    length( nth(0, gCellLists) ) == 2;


predicate List_array_p(List_t* array, int size, 
                       list<list<struct xLIST_ITEM*> > cellLists,
                       list<list<void*> > ownerLists) =
    size >= 0 &*&
    length(cellLists) == size &*&
    length(ownerLists) == length(cellLists) &*&
    size > 0
        ? (
            cellLists == cons(?gCells, ?gTailCellLists) &*&
            ownerLists == cons(?gOwners, ?gTailOwnerLists) &*&
            pointer_within_limits(array) == true &*&
            xLIST(array, ?gLen, ?gIndex, ?gListEnd, gCells, ?gVals, 
                  gOwners)
            &*&
            gLen < INT_MAX &*&
            List_array_p(array + 1, size - 1, gTailCellLists, gTailOwnerLists)
        )
        : (
            cellLists == nil &*&
            ownerLists == nil
        );

lemma void List_array_size_positive(List_t* pxArray)
requires List_array_p(pxArray, ?gSize, ?gCellLists, ?gOwnerLists);
ensures  
    List_array_p(pxArray, gSize, gCellLists, gOwnerLists) &*&
    gSize >= 0 &*& 
    gSize == length(gCellLists) &*& 
    length(gCellLists) == length(gOwnerLists);
{
    open  List_array_p(pxArray, gSize, gCellLists, gOwnerLists);
    close List_array_p(pxArray, gSize, gCellLists, gOwnerLists);
}

lemma void List_array_split(List_t* array, int index)
requires 
    List_array_p(array, ?gSize, ?gCellLists, ?gOwnerLists) &*& 
    0 <= index &*& index < gSize;
ensures 
    List_array_p(array, index, ?gPrefCellLists, ?gPrefOwnerLists) &*&
    gPrefCellLists == take(index, gCellLists) &*&
    gPrefOwnerLists == take(index, gOwnerLists) &*&
    pointer_within_limits(array) == true &*&
    xLIST(array + index, ?gLen, _, _, ?gCells, ?gVals, ?gOwners) &*&
    gLen < INT_MAX &*&
    gCells == nth(index, gCellLists) &*&
    gOwners == nth(index, gOwnerLists) &*&
    mem(gOwners, gOwnerLists) == true &*&
    List_array_p(array + index + 1, gSize-index-1, ?gSufCellLists, ?gSufOwnerLists) &*&
    gSufCellLists == drop(index+1, gCellLists) &*&
    gSufOwnerLists == drop(index+1, gOwnerLists);
{
    open List_array_p(array, gSize, gCellLists, gOwnerLists);

    if( index > 0 ) {
        List_array_split(array + 1, index - 1);
    }

    close List_array_p(array, index, take(index, gCellLists), take(index, gOwnerLists));
}

lemma void List_array_join(List_t* array)
requires
    List_array_p(array, ?gPrefSize, ?gPrefCellLists, ?gPrefOwnerLists) &*&
    xLIST(array + gPrefSize, ?gLen, _, _, ?gCells, _, ?gOwners) &*&
    gLen < INT_MAX &*&
    pointer_within_limits(array + gPrefSize) == true &*&
    List_array_p(array + gPrefSize + 1, ?gSufSize, ?gSufCellLists, ?gSufOwnerLists);
ensures 
    List_array_p(array, ?gSize, ?gCellLists, ?gOwnerLists) &*& 
    gSize == length(gCellLists) &*&
    length(gCellLists) == length(gOwnerLists) &*&
    gSize == gPrefSize + 1 + gSufSize &*&
    gCellLists == append(gPrefCellLists, cons(gCells, gSufCellLists)) &*&
    gOwnerLists == append(gPrefOwnerLists, cons(gOwners, gSufOwnerLists));
{
    open List_array_p(array, gPrefSize, gPrefCellLists, gPrefOwnerLists);
    List_array_size_positive(array + gPrefSize + 1);

    if( gPrefSize > 0 ) {
        List_array_join(array + 1);
    }

    close List_array_p(array, gPrefSize + 1 + gSufSize,
                       append(gPrefCellLists, cons(gCells, gSufCellLists)),
                       append(gPrefOwnerLists, cons(gOwners, gSufOwnerLists)));
}
@*/





/*@
lemma void List_array_p_index_within_limits(List_t* array, int index)
requires List_array_p(array, ?gSize, ?gCellLists, ?gOwnerLists) &*&
         0 <= index &*& index < gSize;
ensures List_array_p(array, gSize, gCellLists, gOwnerLists) &*&
        pointer_within_limits(&array[index]) == true;
{
    open List_array_p(array, gSize, gCellLists, gOwnerLists);
    if( index > 0) {
        List_array_p_index_within_limits(&array[1], index-1);
    }
    close List_array_p(array, gSize, gCellLists, gOwnerLists);
}
@*/



// -------------------------------------------------------------------------
// Lemmas to close the ready list predicate in different scenarios.
/*@
lemma void closeUnchanged_readyLists(list<list<struct xLIST_ITEM*> > cellLists,
                                     list<list<void*> > ownerLists)
requires 
    configMAX_PRIORITIES == length(cellLists) &*&
    configMAX_PRIORITIES == length(ownerLists) &*&
    length( nth(0, cellLists) ) == 2 &*&
    List_array_p(&pxReadyTasksLists, ?gIndex, ?gPrefCellLists, ?gPrefOwnerLists) &*&
    gIndex < length(cellLists) &*&
    xLIST(&pxReadyTasksLists + gIndex, ?gLen, _, _, ?gCells, ?gVals, ?gOwners) &*&
    gLen < INT_MAX &*&
    gCells == nth(gIndex, cellLists) &*&
    gOwners == nth(gIndex, ownerLists) &*&
    pointer_within_limits(&pxReadyTasksLists + gIndex) == true &*&
    List_array_p(&pxReadyTasksLists + gIndex + 1, configMAX_PRIORITIES - gIndex - 1,
                 ?gSufCellLists, ?gSufOwnerLists) &*&
    gPrefCellLists == take(gIndex, cellLists) &*&
    gSufCellLists == drop(gIndex+1, cellLists) &*&
    gPrefOwnerLists == take(gIndex, ownerLists) &*&
    gSufOwnerLists == drop(gIndex+1, ownerLists);
ensures
    readyLists_p(cellLists, ownerLists);
{
    // Prove `0 <= gIndex`:
        open List_array_p(&pxReadyTasksLists, gIndex, gPrefCellLists, gPrefOwnerLists);
        close List_array_p(&pxReadyTasksLists, gIndex, gPrefCellLists, gPrefOwnerLists);
    assert( 0 <= gIndex );
    
    List_array_join(&pxReadyTasksLists);
    assert( List_array_p(&pxReadyTasksLists, ?gSize, ?gCellLists2, ?gOwnerLists2) );
    
    append_take_nth_drop(gIndex, cellLists);
    append_take_nth_drop(gIndex, ownerLists);
    assert( gSize == configMAX_PRIORITIES );
    assert( gCellLists2 == cellLists );
    assert( gOwnerLists2 == ownerLists );

    close readyLists_p(cellLists, ownerLists);
}

lemma void closeReordered_readyLists(list<list<struct xLIST_ITEM*> > cellLists,
                                     list<list<void*> > ownerLists,
                                     list<struct xLIST_ITEM*> reorderedCells,
                                     list<void*> reorderedOwners,
                                     list<void*> tasks)
requires
    configMAX_PRIORITIES == length(cellLists) &*&
    configMAX_PRIORITIES == length(ownerLists) &*&
    length( nth(0, cellLists) ) == 2 &*&
    List_array_p(&pxReadyTasksLists, ?gIndex, ?gPrefCellLists, ?gPrefOwnerLists) &*&
    gIndex < length(cellLists) &*&
    xLIST(&pxReadyTasksLists + gIndex, ?gLen, _, _, reorderedCells, _, reorderedOwners) &*&
    gLen < INT_MAX &*&
    length(reorderedCells) == length(nth(gIndex, cellLists)) &*&
    length(reorderedOwners) == length(nth(gIndex, ownerLists)) &*&
    pointer_within_limits(&pxReadyTasksLists + gIndex) == true &*&
    List_array_p(&pxReadyTasksLists + gIndex + 1, configMAX_PRIORITIES - gIndex - 1,
                 ?gSufCellLists, ?gSufOwnerLists) &*&
    gPrefCellLists == take(gIndex, cellLists) &*&
    gSufCellLists == drop(gIndex+1, cellLists) &*&
    gPrefOwnerLists == take(gIndex, ownerLists) &*&
    gSufOwnerLists == drop(gIndex+1, ownerLists) &*&
    forall(ownerLists, (superset)(tasks)) == true &*&
    forall(reorderedOwners, (mem_list_elem)(tasks)) == true;
ensures
    readyLists_p(?gReorderedCellLists, ?gReorderedOwnerLists) &*&
    forall(gReorderedOwnerLists, (superset)(tasks)) == true;
{
    // Prove that `gIndex != 0 -> gIndex > 0`
    if(gIndex != 0) {
        open List_array_p(&pxReadyTasksLists, gIndex, gPrefCellLists, gPrefOwnerLists);
        close List_array_p(&pxReadyTasksLists, gIndex, gPrefCellLists, gPrefOwnerLists);
        assert( gIndex > 0 );
    }

    List_array_join(&pxReadyTasksLists);
    assert( List_array_p(&pxReadyTasksLists, configMAX_PRIORITIES, 
                         ?gReorderedCellLists, ?gReorderedOwnerLists) );

    if(gIndex == 0) {
        assert( nth(0, gReorderedCellLists) == reorderedCells );
    } else {
        nth_take(0, gIndex, cellLists);
        assert( nth(0, gReorderedCellLists) == nth(0, gPrefCellLists) );
        assert( nth(0, gPrefCellLists) == nth(0, cellLists) );
    }
    assert( length(nth(0, gReorderedCellLists)) == length(nth(0, cellLists)) );
    assert( length(nth(0, gReorderedCellLists)) == 2 );

    close readyLists_p(gReorderedCellLists, gReorderedOwnerLists);


    // Below we prove `forall(gReorderedOwnerLists, (superset)(tasks)) == true`
    forall_take(ownerLists, (superset)(tasks), gIndex);
    forall_drop(ownerLists, (superset)(tasks), gIndex+1);
    assert( forall(gPrefOwnerLists, (superset)(tasks)) == true );
    assert( forall(gSufOwnerLists, (superset)(tasks)) == true );
    forall_mem_implies_superset(tasks, reorderedOwners);
    assert( superset(tasks, reorderedOwners) == true );
    assert( forall(singleton(reorderedOwners), (superset)(tasks)) == true );
    assert( forall(cons(reorderedOwners, gSufOwnerLists), (superset)(tasks)) == true );

    forall_append(gPrefOwnerLists, cons(reorderedOwners, gSufOwnerLists),
                  (superset)(tasks));
}
@*/
#endif /* READY_LIST_PREDICATES_H */