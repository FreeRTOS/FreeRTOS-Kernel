#ifndef VERIFAST_LOCK_PREDICATES_H
#define VERIFAST_LOCK_PREDICATES_H


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



/*
void vf_validate_lock_predicate()
//@ requires module(tasks__pp, true);
//@ ensures true;
{
 //@ open_module();
 uxCurrentNumberOfTasks = 0;
 
 //@ coreID_f_range();
 //@ close coreLocalGlobalVars();
 ///@ close otherGlobalVars();
}
*/




#endif /* VERIFAST_LOCK_PREDICATES_H */