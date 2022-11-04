#ifndef VERIFAST_LOCK_PREDICATES_H
#define VERIFAST_LOCK_PREDICATES_H


/* We assume that macros evaluate as follows:
 * - `configMAX_PRIORITIES` -> 32
*/
/*@
predicate tasks_global_vars() = 
    // Lists for ready and blocked tasks.
	//chars((char*) pxReadyTasksLists, 32 * sizeof(List_t), _) &*&
    //chars((char*) xDelayedTaskList1) &*&

    // Other file private variables. --------------------------------
    integer_((void*) uxCurrentNumberOfTasks, sizeof(UBaseType_t), false, _) 
    &*&
    
    
    true;
@*/



void vf_validate_lock_predicaet()
//@ requires module(tasks__pp, true);
//@ ensures true;
{
 //@ open_module();
 uxCurrentNumberOfTasks = 0;
 
 //@ close tasks_global_vars();
}

#endif /* VERIFAST_LOCK_PREDICATES_H */