#ifndef READY_LIST_PREDICATES_H
#define READY_LIST_PREDICATES_H


/*@
// TODO: Replace List_p by Aaloks list predicate
predicate List_array_p(List_t* array, int size) =
    pointer_within_limits(array) == true &*&
    size > 0 &*&
    List_p(array) &*&
    size > 1
        ? List_array_p(array + 1, size - 1)
        : true;

// For testing purposes only!
// TODO: Replace by Aaloks list predicate
predicate List_p(List_t* l);
@*/


/*@
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