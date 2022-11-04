#ifndef VERIFAST_PORT_CONTRACTS_H
#define VERIFAST_PORT_CONTRACTS_H


/*@ 
predicate interruptState_p(uint32_t);

fixpoint bool interruptsEnabled_f(uint32_t);
@*/

#undef portDISABLE_INTERRUPTS
#define portDISABLE_INTERRUPTS  VF__portDISABLE_INTERRUPTS
uint32_t VF__portDISABLE_INTERRUPTS();
//@ requires interruptState_p(?state);
/*@ ensures result == state &*& 
            interruptState_p(?newState) &*&
            !interruptsEnabled_f(newState);
@*/

#undef portRESTORE_INTERRUPTS
#define portRESTORE_INTERRUPTS(ulState) VF__portRESTORE_INTERRUPTS(ulState)
void VF__portRESTORE_INTERRUPTS(uint32_t state);
//@ requires interruptState_p(_);
/*@ ensures interruptState_p(state);
@*/

#undef portGET_TASK_LOCK
#define portGET_TASK_LOCK  VF__portGET_TASK_LOCK
void VF__portGET_TaskLock();
//@ requires false;
//@ ensures true;

#undef portGET_ISR_LOCK
#define portGET_ISR_LOCK  VF__portGET_ISR_LOCK
void VF__portGET_ISR_LOCK();
//@ requires false;
//@ ensures true;

#endif /* VERIFAST_PORT_CONTRACTS_H */