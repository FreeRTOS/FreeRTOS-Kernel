#ifndef READY_LIST_PREDICATES_H
#define READY_LIST_PREDICATES_H

#include "single_core_proofs/scp_list_predicates.h"

/*@
predicate List_array_p(List_t* array, int size) =
    size >= 0 &*&
    size > 0
        ? (
            pointer_within_limits(array) == true &*&
            xLIST(array, 
                    ?uxNumberOfItems,
                    ?pxIndex,
                    ?xListEnd,
                    ?cells,
                    ?vals)
            &*&
            List_array_p(array + 1, size - 1)
        )
        : true;

lemma void List_array_get_l(List_t* array, int index)
requires List_array_p(array, ?size) &*& 
         0 <= index &*& index < size;
ensures List_array_p(array, index) &*&
        pointer_within_limits(array) == true &*&
        xLIST(array + index, 
                ?uxNumberOfItems,
                ?pxIndex,
                ?xListEnd,
                ?cells,
                ?vals) &*&
        List_array_p(array + index + 1, size-index-1);
{
    if( index == 0) {
        open List_array_p(array, size);
        close List_array_p(array, 0);
    } else {
        open List_array_p(array, size);
        List_array_get_l(array + 1, index - 1);
        close List_array_p(array, index);
    }
}
@*/


/*@
// TODO: We know that the list of priority 0 is never empty.
//       It contains the idle task and nothing else.
predicate readyLists_p() =
    List_array_p(&pxReadyTasksLists, configMAX_PRIORITIES);
@*/


/*@
lemma void List_array_p_index_within_limits(List_t* array, int index)
requires List_array_p(array, ?size) &*&
         0 <= index &*& index < size;
ensures List_array_p(array, size) &*&
        pointer_within_limits(&array[index]) == true;
{
    open List_array_p(array, size);
    if( index > 0) {
        List_array_p_index_within_limits(&array[1], index-1);
    }
    close List_array_p(array, size);
}
@*/

#endif /* READY_LIST_PREDICATES_H */