#ifndef TASKS_GH

#define TASKS_GH

#include "single_core_proofs/scp_list_predicates.h"


/*@
// This predicate represents the memory corresponding to an
// initialised instance of type `TCB_t` aka `tskTaskControlBlock`.
// The predicate itself is not used during the verification of 
// `vTaskSwitchContext`. However, we keep it around to allow proof authors to
// validate that the predicates below indeed capture specific segments of a TCB.
predicate TCB_p(TCB_t * tcb, uint32_t ulFreeBytesOnStack) =
    malloc_block_tskTaskControlBlock(tcb) &*&
    tcb->pxStack |-> ?stackPtr &*&
    tcb->pxTopOfStack |-> ?topPtr &*&
    stack_p_2(stackPtr, ?ulStackDepth, topPtr, 
              ulFreeBytesOnStack, ?ulUsedCells, ?ulUnalignedBytes) &*&

    xLIST_ITEM(&tcb->xStateListItem, _, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xStateListItem) &*&
    xLIST_ITEM(&tcb->xEventListItem, _, _, _, _, _) &*&
    struct_xLIST_ITEM_padding(&tcb->xEventListItem) &*&
    
    tcb->uxPriority |-> _ &*&

    tcb->xTaskRunState |-> ?gTaskRunState &*&
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
@*/

/*@ 
// We have to segment TCBs into:
// (i) public parts that can be accessed by anyone after
//     following the appropriote synchronization steps and
// (ii) private parts that may only be used by the task itself
//      which the TCB represents
//
// The predicates below will be expanded iteratively.

// This predicate captures the private part of a TCB that should only be
// accessed by the TCB represents or under specific circumstances where
// we are certain that the task is not running.
predicate prvSeg_TCB_p(TCB_t* tcb, uint32_t ulFreeBytesOnStack) =
    tcb->pxStack |-> ?stackPtr &*&
    tcb->pxTopOfStack |-> ?topPtr &*&
    stack_p_2(stackPtr, ?ulStackDepth, topPtr, 
              ulFreeBytesOnStack, ?ulUsedCells, ?ulUnalignedBytes);

// This predicate represents a shared part of a TCB that can be accessed by
// anyone. Note that this predicate only contains the minimal access rights 
// required by the `vTaskSwitchContext` proof. It can be extended in the future
// as needed.
predicate sharedSeg_TCB_p(TCB_t* tcb, TaskRunning_t state;) =
    tcb->xTaskRunState |-> state;

predicate coreLocalSeg_TCB_p(TCB_t* tcb, UBaseType_t uxCriticalNesting) =
    tcb->uxCriticalNesting |-> uxCriticalNesting;
@*/

#endif /* TASKS_GH */