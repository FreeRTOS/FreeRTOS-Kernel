#ifndef READY_LIST_PREDICATES_H
#define READY_LIST_PREDICATES_H

#include "single_core_proofs/scp_list_predicates.h"


/*@
// TODO: We know that the list of priority 0 is never empty.
//       It contains the idle task and nothing else.
predicate readyLists_p(list<list<struct xLIST_ITEM*> > gCellLists,
                       list<list<void*> > gOwnerLists) =
    configMAX_PRIORITIES == length(gCellLists) &*&
    List_array_p(&pxReadyTasksLists, configMAX_PRIORITIES, 
                 gCellLists, gOwnerLists);


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
            xLIST(array, ?gNumberOfItems, ?gIndex, ?gListEnd, gCells, ?gVals, 
                  gOwners)
            &*&
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
    xLIST(array + index, _, _, _, ?gCells, ?gVals, ?gOwners) &*&
    gCells == nth(index, gCellLists) &*&
    gOwners == nth(index, gOwnerLists) &*&
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
    xLIST(array + gPrefSize, _, _, _, ?gCells, _, ?gOwners) &*&
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

#endif /* READY_LIST_PREDICATES_H */