#ifndef VERIFAST_LOCK_PREDICATES_H
#define VERIFAST_LOCK_PREDICATES_H

/* We follow a minimalistic approach during the definition of the
 * lock predicates. So far, the only encapsulate the resources and
 * invariants required to verify `vTaskSwitchContext`.
 * We are going to extend and refine them when we proceed to verify
 * other parts of FRTOS.
 */


/*@
// We assume tha `configNUM_CORES` evaluates to 1.
// TODO: Parametrise in terms of `configNUM_CORES`.
// PROBLEM: Shouldn't `configNUM_CORES` be greater than 1?
predicate otherGlobalVars() = 
    integer_(&uxCurrentNumberOfTasks, sizeof(UBaseType_t), false, _) 
    &*&
    integer_(&xTickCount, sizeof(TickType_t), false, _)
    &*&
    integer_(&uxTopReadyPriority, sizeof(UBaseType_t), false, _)
    &*&
    integer_(&xSchedulerRunning, sizeof(BaseType_t), true, _)
    &*&
    integer_(&xPendedTicks, sizeof(TickType_t), false, _)
    &*&
    integers_(&xYieldPendings, sizeof(BaseType_t), true, configNUM_CORES, _)
    &*&
    integer_(&uxTaskNumber, sizeof(UBaseType_t), false, _)
    &*&
    integer_(&xNextTaskUnblockTime, sizeof(TickType_t), false, _)
    &*&
    pointers(&xIdleTaskHandle, configNUM_CORES, _);
    
predicate unprotectedGlobalVars() =
	[_] integer_(&xSchedulerRunning, sizeof(BaseType_t), true, _);


@*/



/* ----------------------------------------------------------------------
 * Core local variables and access restrictions 
 */

/*@ 
predicate interruptState_p(uint32_t coreID, uint32_t state);

fixpoint bool interruptsDisabled_f(uint32_t);

predicate coreLocalGlobalVars() =
    pointer(&pxCurrentTCBs[coreID_f], _);

predicate coreLocalLocked(uint32_t coreID);

//lemma acquireCoreLocalPermissions();
//requires interruptState_p
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

// Represents an acquired task lock.
// `f` is the fraction held for the unacquired lock.
//predicate taskLocked(real f);    

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

// Represents an acquired ISR lock.
// `f` is the fraction held for the unacquired lock.
predicate isrLocked(real f);    

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
    integer_((int*) &uxSchedulerSuspended, sizeof(UBaseType_t), false, _);


lemma void get_taskISRLockInv();
requires locked(?heldLocks) &*&
         heldLocks == cons(?i, cons(?t, nil)) &*&
         i == pair(?f_isr, isrLockID_f()) &*&
         t == pair(?f_task, taskLockID_f());
ensures locked( cons( pair(_, taskISRLockID_f()), heldLocks) );
@*/



/*
void vf_validate_lock_predicate()
//@ requires module(tasks__pp, true);
//@ ensures true;
{
 //@ open_module();
 uxCurrentNumberOfTasks = 0;
 
 ///@ coreID_f_range();
 ///@ close coreLocalGlobalVars();
 ///@ close otherGlobalVars();
}
*/




#endif /* VERIFAST_LOCK_PREDICATES_H */