/*
 * port.xc
 *
 *  Created on: Jul 31, 2019
 *      Author: mbruno
 */

//#include "rtos_support.h"

extern "C" {

#include "FreeRTOSConfig.h" /* to get configNUM_CORES */
#ifndef configNUM_CORES
#define configNUM_CORES 1
#endif

void __xcore_interrupt_permitted_ugs_vPortStartSchedulerOnCore(void);

} /* extern "C" */

void vPortStartSMPScheduler( void )
{
    par (int i = 0; i < configNUM_CORES; i++) {
        __xcore_interrupt_permitted_ugs_vPortStartSchedulerOnCore();
    }
}
