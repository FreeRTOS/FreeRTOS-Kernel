#ifndef VERIFAST_LOCK_PREDICATES_H
#define VERIFAST_LOCK_PREDICATES_H




/* We follow a minimalistic approach during the definition of the
 * lock predicates. So far, the only encapsulate the resources and
 * invariants required to verify `vTaskSwitchContext`.
 * We are going to extend and refine them when we proceed to verify
 * other parts of FRTOS.
 */





/* ----------------------------------------------------------------------
 * Core local data and access restrictions.
 * Some data in FreeRTOS such as the pointer to TCB of the task running
 * on core `C` may only be accessed from core `C`. Such core-local data
 * protected by deactivating interrupts.
 */

/*@ 
predicate interruptState_p(uint32_t coreID, uint32_t state);

fixpoint bool interruptsDisabled_f(uint32_t);

predicate coreLocalInterruptInv_p() =
    pointer(&pxCurrentTCBs[coreID_f], ?currentTCB) &*&
    //pubTCB_p(currentTCB, 0) &*&
    integer_(&xYieldPendings[coreID_f], sizeof(BaseType_t), true, _) &*&
    coreLocalSeg_TCB_p(currentTCB, ?gCriticalNesting);
@*/


/* ----------------------------------------------------------------------
 * Predicates relevant for all locks
 */

/*@
predicate locked_p(list< pair<real, int> > lockHistory);
@*/



/* ----------------------------------------------------------------------
 * Task lock and associated global variables from `tasks.c`
 */

/*@
fixpoint int taskLockID_f();

// Represents an acquired task lock.
predicate taskLock_p(); 

// Represents the invariant associated with the the task lock, i.e.,
// access permissions to the resources protected by the lock.
predicate taskLockInv_p();
@*/

/* ----------------------------------------------------------------------
 * ISR lock and associated global variables from `tasks.c` 
 */

/*@
fixpoint int isrLockID_f();

// Represents an unacquired ISR lock.
predicate isrLock_p(); 

// Represents the invariant associated with the the ISR lock, i.e.,
// access permissions to the resources protected by the lock.
predicate isrLockInv_p();
@*/


/* ----------------------------------------------------------------------
 * Resources protected by both locks.
 * Note that the task lock may never be acquired after the ISR lock.
 */

/*@
fixpoint int taskISRLockID_f();

predicate taskISRLockInv_p() = 
    integer_((void*) &uxSchedulerSuspended, sizeof(UBaseType_t), false, _) &*&
    integer_(&xSchedulerRunning, sizeof(BaseType_t), true, _)
    &*&
    // top ready priority must be in range
        integer_((void*) &uxTopReadyPriority, sizeof(UBaseType_t), false, ?gTopReadyPriority) &*&
        0 <= gTopReadyPriority &*& gTopReadyPriority < configMAX_PRIORITIES
    &*&
    readyLists_p(?gCellLists) &*&
    true;



lemma void produce_taskISRLockInv();
requires locked_p(?heldLocks) &*&
         heldLocks == cons(?i, cons(?t, nil)) &*&
         i == pair(?f_isr, isrLockID_f()) &*&
         t == pair(?f_task, taskLockID_f());
ensures locked_p( cons( pair(_, taskISRLockID_f()), heldLocks) ) &*&
        taskISRLockInv_p();


lemma void consume_taskISRLockInv();
requires locked_p( cons( pair(_, taskISRLockID_f()), ?otherLocks) ) &*&
         taskISRLockInv_p();
ensures  locked_p(otherLocks);
@*/






#endif /* VERIFAST_LOCK_PREDICATES_H */