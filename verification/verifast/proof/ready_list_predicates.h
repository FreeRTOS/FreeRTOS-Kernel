#ifndef READY_LIST_PREDICATES_H
#define READY_LIST_PREDICATES_H

#include "single_core_proofs/scp_list_predicates.h"

/*@
predicate List_array_p(List_t* array, int size, 
                       list<list<struct xLIST_ITEM*> > cellLists) =
    size >= 0 &*&
    length(cellLists) == size &*&
    size > 0
        ? (
            cellLists == cons(?gCells, ?gTailcellLists) &*&
            pointer_within_limits(array) == true &*&
            xLIST(array, ?gNumberOfItems, ?gIndex, ?gListEnd, gCells, ?gVals)
            &*&
            List_array_p(array + 1, size - 1, gTailcellLists)
        )
        : cellLists == nil;

lemma void List_array_size_positive(List_t* pxArray)
requires List_array_p(pxArray, ?gSize, ?gCellLists);
ensures  List_array_p(pxArray, gSize, gCellLists) &*&
         gSize >= 0 &*& gSize == length(gCellLists);
{
    open  List_array_p(pxArray, gSize, gCellLists);
    close List_array_p(pxArray, gSize, gCellLists);
}

lemma void List_array_split(List_t* array, int index)
requires 
    List_array_p(array, ?gSize, ?gCellLists) &*& 
    0 <= index &*& index < gSize;
ensures 
    List_array_p(array, index, ?gPrefCellLists) &*&
    gPrefCellLists == take(index, gCellLists) &*&
    pointer_within_limits(array) == true &*&
    xLIST(array + index, _, _, _, ?gCells, ?vals) &*&
    gCells == nth(index, gCellLists) &*&
    List_array_p(array + index + 1, gSize-index-1, ?gSufCellLists) &*&
    gSufCellLists == drop(index+1, gCellLists);
{
    open List_array_p(array, gSize, gCellLists);

    if( index > 0 ) {
        List_array_split(array + 1, index - 1);
    }

    close List_array_p(array, index, take(index, gCellLists));
}

lemma void List_array_join(List_t* array)
requires
    List_array_p(array, ?gPrefSize, ?gPrefCellLists) &*&
    xLIST(array + gPrefSize, _, _, _, ?gCells, _) &*&
    pointer_within_limits(array + gPrefSize) == true &*&
    List_array_p(array + gPrefSize + 1, ?gSufSize, ?gSufCellLists);
ensures 
    List_array_p(array, ?gSize, ?gCellLists) &*& 
    gSize == length(gCellLists) &*&
    gSize == gPrefSize + 1 + gSufSize &*&
    gCellLists == append(gPrefCellLists, cons(gCells, gSufCellLists));
{
    open List_array_p(array, gPrefSize, gPrefCellLists);
    List_array_size_positive(array + gPrefSize + 1);

    if( gPrefSize > 0 ) {
        List_array_join(array + 1);
    }

    close List_array_p(array, gPrefSize + 1 + gSufSize,
                       append(gPrefCellLists, cons(gCells, gSufCellLists)));
}
@*/


/*@
// TODO: We know that the list of priority 0 is never empty.
//       It contains the idle task and nothing else.
predicate readyLists_p() =
    List_array_p(&pxReadyTasksLists, configMAX_PRIORITIES, ?gCellLists);
@*/


/*@
lemma void List_array_p_index_within_limits(List_t* array, int index)
requires List_array_p(array, ?gSize, ?gCellListss) &*&
         0 <= index &*& index < gSize;
ensures List_array_p(array, gSize, gCellListss) &*&
        pointer_within_limits(&array[index]) == true;
{
    open List_array_p(array, gSize, gCellListss);
    if( index > 0) {
        List_array_p_index_within_limits(&array[1], index-1);
    }
    close List_array_p(array, gSize, gCellListss);
}
@*/

#endif /* READY_LIST_PREDICATES_H */