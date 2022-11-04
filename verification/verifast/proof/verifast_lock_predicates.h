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
    integers_(&xYieldPendings, sizeof(BaseType_t), true, 1, _)
    &*&
    integer_(&uxTaskNumber, sizeof(UBaseType_t), false, _)
    &*&
    integer_(&xNextTaskUnblockTime, sizeof(TickType_t), false, _)
    &*&
    pointers(&xIdleTaskHandle, 1, _);
    
predicate unprotectedGlobalVars() =
	[_] integer_(&xSchedulerRunning, sizeof(BaseType_t), true, _);
@*/


/*
void vf_validate_lock_predicate()
//@ requires module(tasks__pp, true);
//@ ensures true;
{
 //@ open_module();
 uxCurrentNumberOfTasks = 0;
 
 //@ close tasks_global_vars();
}
*/

#endif /* VERIFAST_LOCK_PREDICATES_H */