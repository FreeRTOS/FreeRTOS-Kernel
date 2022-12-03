#ifndef VERIFAST_LOCK_PREDICATES_H
#define VERIFAST_LOCK_PREDICATES_H

#include "verifast_task_running_states.h"


/* We follow a minimalistic approach during the definition of the
 * lock predicates. So far, the only encapsulate the resources and
 * invariants required to verify `vTaskSwitchContext`.
 * We are going to extend and refine them when we proceed to verify
 * other parts of FRTOS.
 */

#include "verifast_lists_extended.h"



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
    [0.5]pointer(&pxCurrentTCBs[coreID_f], ?currentTCB) &*&
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
    // Access to global variables
        [0.5]pointer(&pxCurrentTCBs[coreID_f], ?gCurrentTCB) &*&
        integer_((void*) &uxSchedulerSuspended, sizeof(UBaseType_t), false, _) &*&
        integer_(&xSchedulerRunning, sizeof(BaseType_t), true, _)
    &*&
    // top ready priority must be in range
        integer_((void*) &uxTopReadyPriority, sizeof(UBaseType_t), false, ?gTopReadyPriority) &*&
        0 <= gTopReadyPriority &*& gTopReadyPriority < configMAX_PRIORITIES
    &*&
    // tasks / TCBs
        exists_in_taskISRLockInv_p(?gTasks, ?gStates)
        &*&
        // (RP-All) Read permissions for every task
        //          and recording of task states in state list
        // (∀t ∈ gTasks. 
        //      [1/2]sharedSeg_TCB_p(t, _))
        // ∧ 
        // ∀i. ∀t. gTasks[i] == t -> gStates[i] == t->xTaskRunState    
            foreach(gTasks, readOnly_sharedSeg_TCB_p(gTasks, gStates))
        &*&
        // (RP-Current) Read permission for task currently scheduled on this core
        // (RP-All) + (RP-Current) => Write permission for scheduled task
            [1/2]sharedSeg_TCB_p(gCurrentTCB, ?gCurrentTCB_state)
        &*&
        // TODO:
        // (RP-Unsched) Read permissions for unscheduled tasks
        // (RP-All) + (RP-Unsched) => Write permissions for unscheduled tasks
        // ∀t ∈ tasks. t->xTaskState == taskTASK_NOT_RUNNING
        //             -> [1/2]shared_TCB_p(t, taskTASK_NOT_RUNNING)
            foreach(gTasks, readOnly_sharedSeg_TCB_IF_not_running_p(gTasks, gStates))
        &*&
        readyLists_p(?gCellLists, ?gOwnerLists) 
        &*&
        // gTasks contains all relevant tasks
            mem(gCurrentTCB, gTasks) == true
            &*&
            // ∀l ∈ gOwnerLists. l ⊆ gTasks
                forall(gOwnerLists, (superset)(gTasks)) == true;


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



// Auxiliary predicate to assing names to existentially quantified variables.
// Having multiple `exists` chunks on the heap makes matching against their
// arguments ambiguous in most cases.
predicate exists_in_taskISRLockInv_p(list<void*> gTasks,
                                     list<TaskRunning_t> gStates) =
    exists(gTasks) &*&
    exists(gStates) &*&
    length(gTasks) == length(gStates) &*&
    distinct(gTasks) == true;

// Auxiliary function that allows us to partially apply the list argument.
//
// Notes:
// - Partial application of fixpoint functions in VeriFast is not documented.
//   The syntax for partially application is `(<fixpoint_fct>)(<first_arg>)`
// - VeriFast only supports partially applying the first argument, e.g.,
//   `(mem)(0)` is allowed but `(mem)(_)(nil)` is not.
fixpoint bool mem_list_elem<t>(list<t> xs, t x) {
    return mem(x, xs);
}

// Auxiliary predicate to allow foreach-quantification about fraction
// and reflection of `t->xTaskRunState` in state list.
predicate_ctor readOnly_sharedSeg_TCB_p
            (list<void*> tasks, list<TaskRunning_t> states)
            (TCB_t* t;) =
    mem(t, tasks) == true &*&
    [1/2]sharedSeg_TCB_p(t, nth(index_of(t, tasks), states));

predicate_ctor readOnly_sharedSeg_TCB_IF_not_running_p
            (list<void*> tasks, list<TaskRunning_t> states)
            (TCB_t* t;) =
    mem(t, tasks) == true &*&
    nth(index_of(t, tasks), states) == taskTASK_NOT_RUNNING
        ? [1/2]sharedSeg_TCB_p(t, taskTASK_NOT_RUNNING)
        : true;
@*/



/*@
lemma void nonauto_nth_update<t>(int i, int j, t y, list<t> xs);
  requires 0 <= i && i < length(xs) && 0 <= j && j < length(xs);
  ensures nth(i, update(j, y, xs)) == (i == j ? y : nth(i, xs));
@*/



/*@
lemma void update_readOnly_sharedSeg_TCB(TCB_t* t, 
                                         list<void*> tasks,
                                         list<TaskRunning_t> states, 
                                         int updatedIndex,
                                         TaskRunning_t s)
requires readOnly_sharedSeg_TCB_p(tasks, states)(t) &*&
         updatedIndex != index_of(t, tasks) &*&
         mem(t, tasks) == true &*&
         length(tasks) == length(states);
ensures  readOnly_sharedSeg_TCB_p(tasks, update(updatedIndex, s, states))(t);
{
    list<TaskRunning_t> states2 = update(updatedIndex, s, states);
    int t_index = index_of(t, tasks);

    if( updatedIndex < 0 || updatedIndex >= length(states) ) {
        update_out_of_bounds(updatedIndex, s, states);
    } else {
        open readOnly_sharedSeg_TCB_p(tasks, states)(t);
        open [1/2]sharedSeg_TCB_p(t, nth(t_index, states));

        mem_index_of(t, tasks);
        nth_update(t_index, updatedIndex, s, states);
        assert( nth(t_index, states) == nth(t_index, states2) );

        close [1/2]sharedSeg_TCB_p(t, nth(t_index, states2));
        close readOnly_sharedSeg_TCB_p(tasks, states2)(t);
    }
}


lemma void update_foreach_readOnly_sharedSeg_TCB(TCB_t* updatedTask, 
                                                 list<void*> tasks,
                                                 list<void*> subTasks,
                                                 list<TaskRunning_t> states, 
                                                 list<TaskRunning_t> states2, 
                                                 TaskRunning_t s)
requires
    mem(updatedTask, tasks) == true &*&
    length(tasks) == length(states) &*&
    foreach(subTasks, readOnly_sharedSeg_TCB_p(tasks, states)) &*&
    states2 == update(index_of(updatedTask, tasks), s, states) &*&
    distinct(tasks) == true &*&
    mem(updatedTask, subTasks) == false &*&
    subset(subTasks, tasks) == true;
ensures
    foreach(subTasks, readOnly_sharedSeg_TCB_p(tasks, states2));
{
    switch(subTasks) {
        case nil:   
            open foreach(nil, readOnly_sharedSeg_TCB_p(tasks, states));
            close foreach(nil, readOnly_sharedSeg_TCB_p(tasks, states2));
        case cons(h, rest):
            int index = index_of(updatedTask, tasks);
//            distinct_mem_remove(t, tasks);
//            neq_mem_remove(h, t, tasks);
//            index_of_different(h, t, tasks);
            open foreach(subTasks, readOnly_sharedSeg_TCB_p(tasks, states));
            assert( updatedTask != h );
            index_of_different(updatedTask, h, tasks);
            assert( index != index_of(h, tasks) );
            update_readOnly_sharedSeg_TCB(h, tasks, states, index, s);
            assert( mem(updatedTask, rest) == false );
            update_foreach_readOnly_sharedSeg_TCB(updatedTask, tasks, rest, 
                                                  states, states2, s);
            close foreach(subTasks, readOnly_sharedSeg_TCB_p(tasks, states2));
    }
}


lemma void close_updated_foreach_readOnly_sharedSeg_TCB(TCB_t* updatedTask, 
                                                        list<void*> tasks,
                                                        list<TaskRunning_t> states, 
                                                        list<TaskRunning_t> states2, 
                                                        TaskRunning_t s)
requires
    mem(updatedTask, tasks) == true &*&
    length(states) == length(tasks) &*&
    distinct(tasks) == true &*&
    foreach(remove(updatedTask, tasks), readOnly_sharedSeg_TCB_p(tasks, states)) &*&
    states2 == update(index_of(updatedTask, tasks), s, states) &*&
    [1/2]sharedSeg_TCB_p(updatedTask, s);
ensures
    foreach(tasks, readOnly_sharedSeg_TCB_p(tasks, states2));
{
    distinct_mem_remove(updatedTask, tasks);
    remove_result_subset(updatedTask, tasks);

    close readOnly_sharedSeg_TCB_p(tasks, states2)(updatedTask);
    update_foreach_readOnly_sharedSeg_TCB(updatedTask, tasks, 
                                          remove(updatedTask, tasks),
                                          states, states2, s);
    foreach_unremove(updatedTask, tasks);
}
@*/






#endif /* VERIFAST_LOCK_PREDICATES_H */