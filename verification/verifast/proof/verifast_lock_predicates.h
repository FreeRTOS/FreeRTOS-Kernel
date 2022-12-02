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
        exists_in_taskISRLockInv_p(?gTasks)
        &*&
        // Access permissions for every task
        // TODO: Convert to read permissions
        // ∀t ∈ gTasks. sharedSeg_TCB_p(t)
            foreach(gTasks, sharedSeg_TCB_p)
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
predicate exists_in_taskISRLockInv_p(list<void*> gTasks) =
    exists(gTasks);

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
@*/

/*
    foreach(itemLists, foreach_sharedSeg_TCB_of_itemOwner);

// Auxiliary prediactes to express nested quantification
// ∀gCells ∈ gCellLists. ∀item ∈ gCells. sharedSeg_TCB_p(item->pvOwner)
// TODO: Can we refactor this to make easier to understand?

    // We cannot acces `item->pvOwner` without the necessary points-to chunk.
    // TODO: Expose list of owners in ITEM and DLS predicates.

    predicate sharedSeg_TCB_of_itemOwner(struct xLIST_ITEM* item) =
        sharedSeg_TCB_p(item->pvOwner);

    predicate foreach_sharedSeg_TCB_of_itemOwner(list<struct xLIST_ITEM*> items) = 
        foreach(items, sharedSeg_TCB_of_itemOwner);


lemma void open_collection_of_sharedSeg_TCB(list<list<struct xLIST_ITEM*> > itemLists, 
                                            list<struct xLIST_ITEM*> items)
requires 
    collection_of_sharedSeg_TCB_p(itemLists) &*&
    mem(items, itemLists) == true;
ensures
    collection_of_sharedSeg_TCB_p(remove(items, itemLists)) &*&
    foreach(items, sharedSeg_TCB_of_itemOwner);
{
    open collection_of_sharedSeg_TCB_p(itemLists);
    foreach_remove(items, itemLists);
    open foreach_sharedSeg_TCB_of_itemOwner(items);
    close collection_of_sharedSeg_TCB_p(remove(items, itemLists));
}

// TODO: Add closing lemma
@*/






#endif /* VERIFAST_LOCK_PREDICATES_H */