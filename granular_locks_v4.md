# Introduction

Currently, the SMP FreeRTOS kernel implements critical section using a "Global locking" approach, where all data is protected by a pair of spinlocks (namely the Task Lock and ISR Lock). This means that every critical section contest for the pair of spinlocks, event if those critical sections access unrelated/orthogonal data.

The goal of this proposal is to granularize the spinlocks so that concurrent access to different data groups do no contest for the same spinlocks. This will reduce lock contention and hopefully increase performance of the SMP FreeRTOS kernel.

This document is Version 4 (V4) of the proposal to implement granular locking in SMP FreeRTOS. The V4 proposal describes a **"Dual Spinlock With Suspension"** approach to granular locking. For further context, please see the [summary of previous proposals](./granular_locks_prev.md) which describes what implementations were previously proposed and their associated issues.

Source code changes are based of [release V11.1.0 ](https://github.com/FreeRTOS/FreeRTOS-Kernel/tree/V11.1.0)of the FreeRTOS kernel.

# Data Groups

To granularize the spinlocks, FreeRTOS data will be organized into the following data groups, where each data group is protected by their own set of spinlocks.

- Kernel Data Group
  - All data in `tasks.c` and all event lists (e.g., `xTasksWaitingToSend` and `xTasksWaitingToReceive` in the queue objects)
- Queue Data Group
  - Each queue object (`Queue_t`) is its own data group (excluding the task lists)
- Event Group Data Group
  - Each event group object (`EventGroup_t`) is its own data group (excluding the task lists)
- Stream Buffer Data Group
  - Each stream buffer object (`StreamBuffer_t) is its own data group (excluding the task lists)
- Timers
  - All data in `timers.c` and timer objects and belong to the same Timer Data Group
- User/Port Data Groups
  - The user and ports are free to organize their own data in to data groups of their choosing

# Dual Spinlock With Suspension

The **"Dual Spinlock With Suspension"** uses a pair of spinlocks to protect each data group (namely the `xTaskSpinlock` and `xISRSpinlock` spinlocks).

```c
typedef struct
{
    #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) )
        portSPINLOCK_TYPE xTaskSpinlock;
        portSPINLOCK_TYPE xISRSpinlock;
    #endif /* #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) ) */
} xSomeDataGroup_t;
```

However, each data group must also allow for non-deterministic access with interrupts **enabled** by providing a pair of suspend/resume functions.

```c
static void prvSuspendSomeDataGroup( xSomeDataGroup_t * const pxSomDataGroup );
static void prvResumeSomeDataGroup( xSomeDataGroup_t * const pxSomDataGroup );
```

In simple terms, the "Dual Spinlock With Suspension" is an extension is the existing dual spinlock (i.e., Task and ISR spinlock) approach used in the SMP FreeRTOS kernel, but replicated across different data groups.

## Data Group Locking (Critical Sections)

**Locking a data group** involves disabling interrupts and taking the one or more the data groups spinlocks. This can be thought as a critical section for the data group. The procedure for locking a data group is as follows:

- When locking data group from a task
  1. Disable interrupts
  2. Take `xTaskSpinlock` of data group
  3. Increment nesting count
  4. Take `xISRSpinlock` of data group
  5. Increment nesting count
- When locking data group from an ISR
  1. Disable interrupts
  2. Take `xISRSpinlock` of data group
  3. Increment nesting count

When unlocking a data group, the procedure is reversed. Furthermore, since yield requests are pended when inside a critical section, exiting a task critical section will also need to handle any pended yields.

- When unlocking data group from a task
  1. Release `xISRSpinlock` of data group
  2. Decrement nesting count
  3. Release `xTaskSpinlock` of data group
  4. Decrement nesting count
  5. Reenable interrupts is nesting count is 0
  6. Trigger yield if there is a yield pending
- When unlocking data group form an ISR
  1. Release `xISRSpinlock` of data group
  2. Decrement nesting count
  3. Reenable interrupts is nesting count is 0

Locking multiple data groups in a nested manner is permitted, meaning if a code path has already locked data group A, it can then lock data group B. This is analogous to nested critical sections. However, care must be taken to avoid deadlocks. This can be achieved by organizing data groups into a hierarchy, where a higher layer data group cannot nest into a lower one.

```
                                       +-------------------+
                                       | Kernel Data Group |
                                       +-------------------+

  +-------------------+  +---------------------------+ +----------------+ +------------------+
  | Queue Data Groups |  | Stream Buffer Data Groups | | EG Data Groups | | Timer Data Group |
  +-------------------+  +---------------------------+ +----------------+ +------------------+

+----------------------------------------------------------------------------------------------+
|                                        User Data Groups                                      |
+----------------------------------------------------------------------------------------------+
```

If nested locking only occurs from bottom up (e.g., User data group can nested into a Queue data group which in turn can nested into Kernel data group), then deadlocking will never occurs.

## Data Group Suspension

FreeRTOS does not permit walking linked lists while interrupts are disabled to ensure deterministic ISR latency. Therefore, each data group must provide a method of suspension so that non-deterministic operations can be executed for a data group. While a data group is suspended:

- Preemption is disabled for the current task
- Interrupts remained enabled
- The data group's `xTaskSpinlock` is taken
- Any ISR that attempts to update the data group will have their access pended. These pended accesses will be handled on resumption

The logic of suspending a data group is analogous to the logic of `vTaskSuspendAll()`/`xTaskResumeAll()` and `prvLockQueue()`/`prvUnlockQueue()` in the existing SMP kernel.

The details of how ISR accesses are pended during suspension will be specific to each data group type, thus the implementation of the suspend/resumption functions also be specified to each data group type. However, the procedure for data group suspension and resumption will typically be as follows:

- Suspension
  1. Disable preemption
  2. Lock the data group
  3. Set a suspension flag that indicates the data group is suspended
  4. Unlock the data group, but keep holding `xTaskSpinlock`
- Resumption
  1. Lock the data group
  2. Clear the suspension flag
  3. Handle all pended accesses from ISRs
  4. Unlock the data group, thus releasing `xTaskSpinlock`

Suspending multiple data groups in a nested manner is permitted, meaning if a code path has already suspended data group A, it can then suspend data group B. This is analogous to nested `vTaskSuspendAll()` calls. Similar to data group locking, deadlocks can be avoided by organizing data groups into a hierarchy.

## Thread Safety Check

Under SMP, there are four sources of concurrent access for a particular data group:

- Preempting task on the same core
- Preempting ISR on the same core
- Concurrent task on another core
- Concurrent task on another core

This section checks that the data group locking and suspension mechanisms mentioned ensure thread safety from each concurrent source of access.

- Data Group Locked From Task: Interrupts are disabled, `xTaskSpinlock` and `xISRSpinlock` are taken
  - Task (same core): Context switch cannot occur because interrupts are disabled
  - Task (other core): The task will spin on `xTaskSpinlock`
  - ISR (same core): Interrupts on the current core are disabled
  - ISR (other core): ISR will spin on `xISRSpinlock`

- Data Group Locked From ISR: Interrupts are disabled, `xISRSpinlock` is taken
  - Task (same core): Context switch cannot because we are in an ISR
  - Task (other core): The task will spin on `xISRSpinlock`
  - ISR (same core): Interrupts on the current core are disabled
  - ISR (other core): ISR will spin on `xISRSpinlock`

- Data Group Suspended From Task: Preemption is disabled, `xTaskSpinlock` is taken
  - Task (same core): Context switch cannot because preemption is disabled
  - Task (other core): The task will spin on `xTaskSpinlock`
  - ISR (same core): Critical section is entered because `xISRSpinlock` is not held, but access is pended
  - ISR (other core): Critical section is entered because `xISRSpinlock` is not held, but access is pended

# Public API Changes

To support **"Dual Spinlock With Suspension"**, the following changes have been made to the public facing API. These changes are non-breaking, meaning that applications that can build against the existing SMP FreeRTOS kernel will still be able to build even with granular locking enabled (albeit less performant).

The following APIs have been added to lock/unlock a data group. This is called by FreeRTOS source code to lock/unlock their data groups. However, users can also create their own data groups and lock/unlock them in the same manner.

If granular locking is disabled, these macros simply revert to being the standard task enter/exit critical macros.

```c
#if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) )
    #define taskLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )    portLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )
    #define taskLOCK_DATA_GROUP_FROM_ISR( pxISRSpinlock )           portLOCK_DATA_GROUP_FROM_ISR( pxISRSpinlock )
    #define taskUNLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )  portUNLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )
    #define taskUNLOCK_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )      portUNLOCK_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )
#else
    #define taskLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )    taskENTER_CRITICAL()
    #define taskLOCK_DATA_GROUP_FROM_ISR( pxISRSpinlock )           taskENTER_CRITICAL_FROM_ISR()
    #define taskUNLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )  taskEXIT_CRITICAL()
    #define taskUNLOCK_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )      taskEXIT_CRITICAL_FROM_ISR( x )
#endif /* #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) ) */
```

The previous critical section macros are still provided and can be called by users. However, FreeRTOS source code will no longer call them. If called by the users, the port should implement a "user" data group. As a result, if an application previously relied on `taskENTER|EXIT_CRITICAL()` for thread safe access to some user data, the same code is still thread safe with granular locking enabled.

```c
#define taskENTER_CRITICAL()                portENTER_CRITICAL()
#define taskEXIT_CRITICAL()                 portEXIT_CRITICAL()
#define taskENTER_CRITICAL_FROM_ISR()       portENTER_CRITICAL_FROM_ISR()
#define taskEXIT_CRITICAL_FROM_ISR( x )     portEXIT_CRITICAL_FROM_ISR( x )
```

# Porting Interface

To support **"Dual Spinlock With Suspension"**, ports will need to provide the following macro definitions

## Port Config

The ports will need to provide the following port configuration macros

```c
#define portUSING_GRANULAR_LOCKS        1   // Enables usage of granular locks
#define portCRITICAL_NESTING_IN_TCB     0   // Disable critical nesting in TCB. Ports will need to track their own critical nesting
```

## Spinlocks

Ports will need to provide the following spinlock related macros macros

```c
/*
Data type for the port's implementation of a spinlock
*/
#define portSPINLOCK_TYPE               port_spinlock_t
```

A separate initialization macro is provided the individual spinlocks (i.e., `xTaskSpinlock` and `xISRSpinlock`) of each data group. This is so that targets (e.g., RP2040) that use hardware spinlocks have separate macros to allocate the hardware resource for each spinlock. For targets that support an atomic CAS instructions, the initialization of all spinlocks will be the same (i.e., just zero initialization an unsigned integer).

Furthermore, depending on the data group, the spinlocks can be initialized either statically or dynamically. This is reflected in the macros API pattern.

```c
#define portINIT_EVENT_GROUP_TASK_SPINLOCK( pxSpinlock )    _port_spinlock_init_eg_task( pxSpinlock )
#define portINIT_EVENT_GROUP_ISR_SPINLOCK( pxSpinlock )     port_spinlock_init_eg_isr( pxSpinlock )
#define portINIT_QUEUE_TASK_SPINLOCK( pxSpinlock )          port_spinlock_init_queue_task( pxSpinlock )
#define portINIT_QUEUE_ISR_SPINLOCK( pxSpinlock )           port_spinlock_init_queue_isr( pxSpinlock )
#define portINIT_STREAM_BUFFER_TASK_SPINLOCK( pxSpinlock )  port_spinlock_init_sb_task( pxSpinlock )
#define portINIT_STREAM_BUFFER_ISR_SPINLOCK( pxSpinlock )   port_spinlock_init_sb_isr( pxSpinlock )
#define portINIT_KERNEL_TASK_SPINLOCK_STATIC                PORT_SPINLOCK_STATIC_INIT_KERNEL_TASK
#define portINIT_KERNEL_ISR_SPINLOCK_STATIC                 PORT_SPINLOCK_STATIC_INIT_KERNEL_ISR
#define portINIT_TIMERS_TASK_SPINLOCK_STATIC                PORT_SPINLOCK_STATIC_INIT_TIMERS_TASK
#define portINIT_TIMERS_ISR_SPINLOCK_STATIC                 PORT_SPINLOCK_STATIC_INIT_TIMERS_ISR
```

## Locking Functions

The port will need to provide implementations for functions to lock/unlock a data group according the procedures described above. Typical implementations of each function is demonstrated below:

```c
#if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) )
    #define taskLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )    portLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )
    #define taskLOCK_DATA_GROUP_FROM_ISR( pxISRSpinlock )           portLOCK_DATA_GROUP_FROM_ISR( pxISRSpinlock )
    #define taskUNLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )  portUNLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )
    #define taskUNLOCK_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )      portUNLOCK_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )
#endif /* #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) ) */
```

Example implementation of `portLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )` and `portUNLOCK_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )`. Note that:

- `pxTaskSpinlock` is made optional in case users want to create their own data groups that are protected only be a single lock.
- The kernel implements the `xTaskUnlockCanYield()` function to indicate whether a yield should occur when a critical section exits. This function takes into account whether there are any pending yields and whether preemption is currently disabled.

```c
void vPortLockDataGroup( port_spinlock_t *pxTaskSpinlock, port_spinlock_t *pxISRSpinlock )
{
    portDISABLE_INTERRUPTS();

    BaseType_t xCoreID = xPortGetCoreID();

    /* Task spinlock is optional and is always taken first */
    if( pxTaskSpinlock != NULL )
    {
        vPortSpinlockTake( pxTaskSpinlock, portMUX_NO_TIMEOUT );
        uxCriticalNesting[ xCoreID ]++;
    }

    /* ISR spinlock must always be provided */
    vPortSpinlockTake( pxISRSpinlock, portMUX_NO_TIMEOUT );
    uxCriticalNesting[ xCoreID ]++;
}

void vPortUnlockDataGroup( port_spinlock_t *pxTaskSpinlock, port_spinlock_t *pxISRSpinlock )
{
    BaseType_t xCoreID = xPortGetCoreID();
    BaseType_t xYieldCurrentTask;

    configASSERT( uxCriticalNesting[ xCoreID ] > 0U );

    /* Get the xYieldPending stats inside the critical section. */
    xYieldCurrentTask = xTaskUnlockCanYield();

    /* ISR spinlock must always be provided */
    vPortSpinlockRelease( pxISRSpinlock );
    uxCriticalNesting[ xCoreID ]--;

    /* Task spinlock is optional and is always taken first */
    if( pxTaskSpinlock != NULL )
    {
        vPortSpinlockRelease( pxTaskSpinlock);
        uxCriticalNesting[ xCoreID ]--;
    }

    assert(uxCriticalNesting[ xCoreID ] >= 0);

    if( uxCriticalNesting[ xCoreID ] == 0 )
    {
        portENABLE_INTERRUPTS();

        /* When a task yields in a critical section it just sets xYieldPending to
         * true. So now that we have exited the critical section check if xYieldPending
         * is true, and if so yield. */
        if( xYieldCurrentTask != pdFALSE )
        {
            portYIELD();
        }
        else
        {
            mtCOVERAGE_TEST_MARKER();
        }
    }
}
```

Example implementation of `portLOCK_DATA_GROUP_FROM_ISR( pxISRSpinlock )` and `portUNLOCK_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )`. Note that only `pxISRSpinlock` needs to be provided since ISR critical sections take a single lock.

```c
UBaseType_t uxPortLockDataGroupFromISR( port_spinlock_t *pxISRSpinlock )
{
    UBaseType_t uxSavedInterruptStatus = 0;

    uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();

    vPortSpinlockTake( pxISRSpinlock, portMUX_NO_TIMEOUT );
    uxCriticalNesting[xPortGetCoreID()]++;

    return uxSavedInterruptStatus;
}

```c
void vPortUnlockDataGroupFromISR( UBaseType_t uxSavedInterruptStatus, port_spinlock_t *pxISRSpinlock )
{
    BaseType_t xCoreID = xPortGetCoreID();

    vPortSpinlockRelease( pxISRSpinlock );
    uxCriticalNesting[ xCoreID ]--;

    assert(uxCriticalNesting[ xCoreID ] >= 0);

    if( uxCriticalNesting[ xCoreID ] == 0 )
    {
        portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );
    }
}
```

# Source Specific Changes

- Added a `xTaskSpinlock` and `xISRSpinlock` to the data structures of each data group
- All calls to `taskENTER/EXIT_CRITICAL[_FROM_ISR]()` have been replaced with `taskLOCK/UNLOCK_DATA_GROUP[_FROM_ISR]()`.
- Added `xTaskUnlockCanYield()` which indicates whether a yield should occur when exiting a critical (i.e., unlocking a data group). Yields should not occur if preemption is disabled (such as when exiting a critical section inside a suspuension block).

## Tasks (Kernel Data Group)

- Some functions are called from nested critical sections of other data groups, thus an extra critical section call needs to be added to lock/unlock the kernel data group:
  - `vTaskInternalSetTimeOutState()`
  - `xTaskIncrementTick()`
  - `vTaskSwitchContext()`
  - `xTaskRemoveFromEventList()`
  - `vTaskInternalSetTimeOutState()`
  - `eTaskConfirmSleepModeStatus()`
  - `xTaskPriorityDisinherit()`
  - `pvTaskIncrementMutexHeldCount()`
- Some functions are called from nested suspension blocks of other data gropus, thus an extra suspend/resume call need to be added:
  - `vTaskPlaceOnEventList()`
  - `vTaskPlaceOnUnorderedEventList()`
  - `vTaskPlaceOnEventListRestricted()`
- `prvCheckForRunStateChange()` has been removed
- Updated `vTaskSuspendAll()` and `xTaskResumeAll()`
    - Now holds the `xTaskSpinlock` during kernel suspension
    - Also increments/decrements `xPreemptionDisable` to prevent yield from occuring when exiting a critical section from inside a kernel suspension block.

## Queue

- Added `queueSUSPEND()` and `queueRESUME()`
  - If granular locks are disabled, reverts to the previous `prvLockQueue()` and `prvUnlockQueue()`
  - If granular locks are enabled, will suspend/resume the queue data group

## Event Groups

- Added `eventSUSPEND()` and `eventRESUME()`
  - If granular locks are disabled, reverts to the previous `vTaskSuspendAll()` and `xTaskResumeAll()` calls
  - If granular locks are enabled, will suspend/resume the EG data group
- `xEventGroupSetBits()` and `vEventGroupDelete()` will manually walk the task lists (which belong to the kernel data group). Thus, an extra `vTaskSuspendAll()`/`xTaskResumeAll()` is added to ensure that the kernel data group is suspended while walking those tasks lists.

## Stream Buffer

- Added `sbSUSPEND()` and `sbRESUME()`
  - If granular locks are disabled, reverts to the previous `vTaskSuspendAll()` and `xTaskResumeAll()` calls
  - If granular locks are enabled, will suspend/resume the stream buffer data group

## Timers

- Timers don't have a suspend/resume function. The existing `vTaskSuspendAll()`/`xTaskResumeAll()` calls are valid don't rely on freezing the tick count which is part of the kernel data group, thus these calls are valid.

# Prerequisite Refactoring

A number of refactoring commits have been added to make the addition of granular locking changes simpler:

1. Move critical sections inside `xTaskPriorityInherit()`

Currently, `xTaskPriorityInherit()` is called with wrapping critical sections. The critical sections have now be moved inside the function so that they have accesss to the kernel data group's spinlocks.

2. Move critical section into `vTaskPriorityDisinheritAfterTimeout()`

Currently, `vTaskPriorityDisinheritAfterTimeout()` is called wrapping critical sections, where the highest priority waiting task is separately obtained via `prvGetDisinheritPriorityAfterTimeout()`. The critical section and checking of the highest priority have been all been moved into `vTaskPriorityDisinheritAfterTimeout()` as all of these operations access the kernel data group.

3. Allow `vTaskPreemptionEnable()` to be nested

Currently, nested calls of `vTaskPreemptionEnable()` is not supported. However, nested calls are required for granular locking due the the occurence of nested suspension across multiple data groups.

Thus, `vTaskPreemptionEnable()` has been updated to support nested calls. This is done by changing `xPreemptionDisable` to a count, where a non-zero count means that the current task cannot be preempted.

# Performance Metrics

Todo

