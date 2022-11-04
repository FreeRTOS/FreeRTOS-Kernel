#ifndef VERIFAST_PORT_CONTRACTS_H
#define VERIFAST_PORT_CONTRACTS_H


/*@ 
predicate interruptsOn_p(bool status);
@*/

#undef portDISABLE_INTERRUPTS
#define portDISABLE_INTERRUPTS  VF__portDISABLE_INTERRUPTS
void VF__portDISABLE_INTERRUPTS();
//@ requires interruptsOn_p(_);
//@ ensures interruptsOn_p(false);

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