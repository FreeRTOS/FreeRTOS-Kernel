#ifndef TASKS_GH

#define TASKS_GH

#include "single_core_proofs/list_predicates.h"


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
    uchars_((unsigned char*) tcb->ucNotifyState, 1, _) &*&

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

    tcb->uxCriticalNesting |-> ?uxCriticalNesting &*&
    tcb->uxTCBNumber |-> _ &*&
    tcb->uxTaskNumber |-> _ &*&
    tcb->uxBasePriority |-> _ &*&
    tcb->uxMutexesHeld |-> _ &*&

    // void * pvThreadLocalStoragePointers[ 5 ];
    pointers(tcb->pvThreadLocalStoragePointers, 5, _) &*&

    // We assume that the macro `configTASK_NOTIFICATION_ARRAY_ENTRIES`
    // evaluates to 1.
    integers_(tcb->ulNotifiedValue, 4, false, 1, _) &*&
    uchars((unsigned char*) tcb->ucNotifyState, 1, _) &*&

    tcb->ucDelayAborted |-> _;


predicate absTCB_p(TCB_t* tcb) =
    TCB_p(tcb, _);
@*/

/*@ 
// We have to segment TCBs into:
// (i) public parts that can be accessed by anyone after
//     following the appropriote synchronization steps and
// (ii) private parts that may only be used by the task itself
//      which the TCB represents
//
// The predicates below will be expanded iteratively.

predicate prvTCB_p(TCB_t* tcb, uint32_t ulFreeBytesOnStack) =
    tcb->pxStack |-> ?stackPtr &*&
    tcb->pxTopOfStack |-> ?topPtr &*&
    stack_p_2(stackPtr, ?ulStackDepth, topPtr, 
              ulFreeBytesOnStack, ?ulUsedCells, ?ulUnalignedBytes);

predicate pubTCB_p(TCB_t* tcb, UBaseType_t uxCriticalNesting) =
    tcb->uxCriticalNesting |-> uxCriticalNesting;
@*/

#endif /* TASKS_GH */