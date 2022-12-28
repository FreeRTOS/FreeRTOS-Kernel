#ifndef PORT_CONTRACTS_H
#define PORT_CONTRACTS_H


// We want our proofs to hold for an arbitrary number of cores.
/* TODO: Can we use the original function `get_core_num` instead without
 *       adding the contract inside the pico sdk file (platform.h)?
 */
#undef portGET_CORE_ID
#define portGET_CORE_ID() VF__get_core_num()

/* FreeRTOS core id is always zero based.*/
static uint VF__get_core_num(void);
//@ requires true;
/*@ ensures 0 <= result &*& result < configNUM_CORES &*&
            result == coreID_f();
@*/

/*@
// Allow reference to core id in proofs.
fixpoint uint coreID_f();

lemma void coreID_f_range();
requires true;
ensures 0 <= coreID_f() &*& coreID_f() < configNUM_CORES;
@*/




#undef portDISABLE_INTERRUPTS
#define portDISABLE_INTERRUPTS  VF__portDISABLE_INTERRUPTS
uint32_t VF__portDISABLE_INTERRUPTS();
//@ requires interruptState_p(?coreID, ?state);
/*@ ensures result == state &*& 
            interruptState_p(coreID, ?newState) &*&
            interruptsDisabled_f(newState) == true &*&
            interruptsDisabled_f(state) == true
               ? newState == state 
               : coreLocalInterruptInv_p();
@*/

#undef portRESTORE_INTERRUPTS
#define portRESTORE_INTERRUPTS(ulState) VF__portRESTORE_INTERRUPTS(ulState)
void VF__portRESTORE_INTERRUPTS(uint32_t ulState);
/*@ requires interruptState_p(?coreID, ?tmpState) &*&
             (interruptsDisabled_f(tmpState) == true && interruptsDisabled_f(ulState) == false)
                ? coreLocalInterruptInv_p()
                : true;
 @*/
/*@ ensures interruptState_p(coreID, ulState);
@*/

#undef portGET_TASK_LOCK
#define portGET_TASK_LOCK  VF__portGET_TASK_LOCK
void VF__portGET_TASK_LOCK();
//@ requires [?f]taskLock_p() &*& locked_p(nil);
//@ ensures taskLockInv_p() &*& locked_p( cons( pair(f, taskLockID_f()), nil) );

#undef portRELEASE_TASK_LOCK
#define portRELEASE_TASK_LOCK VF__portRELEASE_TASK_LOCK
void VF__portRELEASE_TASK_LOCK();
//@ requires taskLockInv_p() &*& locked_p( cons( pair(?f, taskLockID_f()), nil) );
//@ ensures [f]taskLock_p() &*& locked_p(nil);

#undef portGET_ISR_LOCK
#define portGET_ISR_LOCK  VF__portGET_ISR_LOCK
void VF__portGET_ISR_LOCK();
//@ requires [?f]isrLock_p() &*& locked_p(?heldLocks);
//@ ensures isrLockInv_p() &*& locked_p( cons( pair(f, isrLockID_f()), heldLocks) );

#undef portRELEASE_ISR_LOCK
#define portRELEASE_ISR_LOCK VF__portRELEASE_ISR_LOCK
void VF__portRELEASE_ISR_LOCK();
//@ requires isrLockInv_p() &*& locked_p( cons( pair(?f, isrLockID_f()), ?heldLocks) );
//@ ensures [f]isrLock_p() &*& locked_p(heldLocks);


#endif /* PORT_CONTRACTS_H */