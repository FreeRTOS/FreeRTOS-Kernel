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
    pubTCB_p(currentTCB, 0) &*&
    integer_(&xYieldPendings[coreID_f], sizeof(BaseType_t), true, _);


predicate coreLocalLocked(uint32_t coreID);
@*/


/* ----------------------------------------------------------------------
 * Predicates relevant for all locks
 */

/*@
predicate locked(list< pair<real, int> > lockHistory);
@*/



/* ----------------------------------------------------------------------
 * Task lock and associated global variables from `tasks.c`
 */

/*@
fixpoint int taskLockID_f();

// Represents an acquired task lock.
predicate taskLock(); 

// Represents the invariant associated with the the task lock, i.e.,
// access permissions to the resources protected by the lock.
predicate taskLockInv();
@*/

/* ----------------------------------------------------------------------
 * ISR lock and associated global variables from `tasks.c` 
 */

/*@
fixpoint int isrLockID_f();

// Represents an unacquired ISR lock.
predicate isrLock(); 

// Represents the invariant associated with the the ISR lock, i.e.,
// access permissions to the resources protected by the lock.
predicate isrLockInv() =
    foreach<struct xLIST*>(?vfReadyLists, xList_gen);
@*/


/* ----------------------------------------------------------------------
 * Resources protected by both locks.
 * Note that the task lock may never be acquired after the ISR lock.
 */

/*@
fixpoint int taskISRLockID_f();

predicate taskISRLockInv() = 
    integer_((int*) &uxSchedulerSuspended, sizeof(UBaseType_t), false, _) &*&
    readyLists_p() &*&
    // Update: The current task on this core is interrupt protected.
    // TODO: Exclude from `allTasks`.
    // `allTasks` stores pointers to all currently valid tasks (i.e. TCB_t instances)
    //foreach(?tasks, absTCB_p) &*&
    // If a task is scheduled, it must be valid
    //[0.5]pointer(&pxCurrentTCBs[coreID_f()], ?scheduledTask) &*&
    //scheduledTask != NULL
    //    ? mem(scheduledTask, tasks) == true
    //    : true
    //&*&
    true;


lemma void produce_taskISRLockInv();
requires locked(?heldLocks) &*&
         heldLocks == cons(?i, cons(?t, nil)) &*&
         i == pair(?f_isr, isrLockID_f()) &*&
         t == pair(?f_task, taskLockID_f());
ensures locked( cons( pair(_, taskISRLockID_f()), heldLocks) ) &*&
        taskISRLockInv();


lemma void consume_taskISRLockInv();
requires locked( cons( pair(_, taskISRLockID_f()), ?otherLocks) ) &*&
         taskISRLockInv();
ensures  locked(otherLocks);
@*/






#endif /* VERIFAST_LOCK_PREDICATES_H */