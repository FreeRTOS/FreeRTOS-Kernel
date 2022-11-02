#ifndef TASKS_GH

#define TASKS_GH

#include "nathan/list_predicates.h"


/*@
// This predicate represents the memory corresponding to an
// uninitialised instance of type `TCB_t` aka `tskTaskControlBlock`.
predicate uninit_TCB_p(TCB_t * tcb, int stackSize) =
    malloc_block_tskTaskControlBlock(tcb) &*&
    tcb->pxTopOfStack |-> _ &*&

    xLIST_ITEM(&tcb->xStateListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xStateListItem) &*&
    xLIST_ITEM(&tcb->xEventListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xEventListItem) &*&
    
    tcb->uxPriority |-> _ &*&

    tcb->pxStack |-> ?stackPtr &*&
    stackPtr != 0 &*&
    (char*) stackPtr + stackSize <=  (char*) UINTPTR_MAX &*&
    chars_((char*) stackPtr, stackSize, _) &*&
    malloc_block_chars((char*) stackPtr, stackSize) &*&

    tcb->xTaskRunState |-> _ &*&
    tcb->xIsIdle |-> _ &*&
    
    // Assumes macro `configMAX_TASK_NAME_LEN` evaluates to 16.
    chars_(tcb->pcTaskName, 16, _) &*&

    tcb->uxCriticalNesting |-> _ &*&
    tcb->uxTCBNumber |-> _ &*&
    tcb->uxTaskNumber |-> _ &*&
    tcb->uxBasePriority |-> _ &*&
    tcb->uxMutexesHeld |-> _ &*&

    // void * pvThreadLocalStoragePointers[ 5 ];
    pointers_(tcb->pvThreadLocalStoragePointers, 5, _) &*&

    // We assume that the macro `configTASK_NOTIFICATION_ARRAY_ENTRIES`
    // evaluates to 1.
    integers__(tcb->ulNotifiedValue, 4, false, 1, _) &*&
    uchars_(tcb->ucNotifyState, 1, _) &*&

    tcb->ucDelayAborted |-> _;
@*/


/*@
// This predicate represents the memory corresponding to an
// initialised instance of type `TCB_t` aka `tskTaskControlBlock`.
predicate TCB_p(TCB_t * tcb, uint32_t ulFreeBytesOnStack) =
    malloc_block_tskTaskControlBlock(tcb) &*&
    tcb->pxStack |-> ?stackPtr &*&
    tcb->pxTopOfStack |-> ?topPtr &*&
    stack_p_2(stackPtr, ?ulStackDepth, topPtr, 
              ulFreeBytesOnStack, ?ulUsedCells, ?ulUnalignedBytes) &*&

    xLIST_ITEM(&tcb->xStateListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xStateListItem) &*&
    xLIST_ITEM(&tcb->xEventListItem, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xEventListItem) &*&
    
    tcb->uxPriority |-> _ &*&

    tcb->xTaskRunState |-> _ &*&
    tcb->xIsIdle |-> _ &*&
    
    // Assumes macro `configMAX_TASK_NAME_LEN` evaluates to 16.
    chars_(tcb->pcTaskName, 16, _) &*&

    tcb->uxCriticalNesting |-> _ &*&
    tcb->uxTCBNumber |-> _ &*&
    tcb->uxTaskNumber |-> _ &*&
    tcb->uxBasePriority |-> _ &*&
    tcb->uxMutexesHeld |-> _ &*&

    // void * pvThreadLocalStoragePointers[ 5 ];
    pointers(tcb->pvThreadLocalStoragePointers, 5, _) &*&

    // We assume that the macro `configTASK_NOTIFICATION_ARRAY_ENTRIES`
    // evaluates to 1.
    integers_(tcb->ulNotifiedValue, 4, false, 1, _) &*&
    uchars(tcb->ucNotifyState, 1, _) &*&

    tcb->ucDelayAborted |-> _;
@*/

#endif /* TASKS_GH */