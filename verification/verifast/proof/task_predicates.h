#ifndef TASKS_GH

#define TASKS_GH

#include "nathan/list_predicates.h"


/*@
// This predicate represents the memory corresponding to an
// instance of type `TCB_t` aka `tskTaskControlBlock`.
predicate TCB_p(TCB_t * tcb) =
    malloc_block_tskTaskControlBlock(tcb) &*&
    tcb->pxTopOfStack |-> _ &*&

    xLIST_ITEM(&tcb->xStateListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xStateListItem) &*&
    xLIST_ITEM(&tcb->xEventListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xEventListItem) &*&
    
    tcb->uxPriority |-> _ &*&
    tcb->pxStack |-> _ &*&
    tcb->xTaskRunState |-> _ &*&
    tcb->xIsIdle |-> _ &*&
    
    // pcTaskName
    chars_(tcb->pcTaskName, 16, _) &*&

    tcb->uxCriticalNesting |-> _ &*&
    tcb->uxTCBNumber |-> _ &*&
    tcb->uxTaskNumber |-> _ &*&
    tcb->uxBasePriority |-> _ &*&
    tcb->uxMutexesHeld |-> _ &*&

    // void * pvThreadLocalStoragePointers[ 5 ];
    pointers_(tcb->pvThreadLocalStoragePointers, _, _) &*&

    integers__(tcb->ulNotifiedValue, _, _, _, _) &*&
    
    uchars_(tcb->ucNotifyState, 1, _) &*&

    tcb->ucDelayAborted |-> _;

    
@*/

#endif /* TASKS_GH */