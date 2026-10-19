# FreeRTOS SMP Granular Locks — Design

## Introduction

Historically, the SMP FreeRTOS kernel has implemented critical sections using a "Global Locking" approach, where all kernel data is protected by a single pair of spinlocks (the Task Lock and ISR Lock). Every critical section contests for this pair of spinlocks, even when the sections protect unrelated data.

This document describes the **"Dual Spinlock With Data Group Locking"** scheme that replaces global locking with per-data-group locks. The goal is to reduce contention between concurrent operations on independent kernel objects (queues, event groups, stream buffers, etc.) so that the SMP kernel scales better with the number of cores.

Granular locking is opt-in via the new port-layer configuration `portUSING_GRANULAR_LOCKS`. With it disabled the kernel behaves exactly as before; with it enabled the per-data-group locks described below are used.

Source-code changes are layered on the V11.1.0 release of the upstream FreeRTOS kernel.

### Status (as of this branch)

- Implemented in the kernel against `configNUMBER_OF_CORES > 1` builds.
- Verified on the Espressif ESP32 (Xtensa, dual-core) target via the ESP-IDF FreeRTOS unit-test suite.
- Other ports remain to be updated; reference port macros and the porting checklist are listed in the *Porting Interface* section.

# Data Groups

To make the spinlocks granular, FreeRTOS data will be organized into the following data groups, where each data group is protected by their own set of spinlocks.

- Kernel Data Group
  - All data in `tasks.c` and all event lists (e.g., `xTasksWaitingToSend` and `xTasksWaitingToReceive` in the queue objects)
- Queue Data Group
  - Each queue object (`Queue_t`) is its own data group (excluding the task lists)
- Event Group Data Group
  - Each event group object (`EventGroup_t`) is its own data group (excluding the task lists)
- Stream Buffer Data Group
  - Each stream buffer object (`StreamBuffer_t`) is its own data group (excluding the task lists)
- Timers
  - All data in `timers.c` and timer objects,  belong to the same Timer Data Group
- User/Port Data Groups
  - The user and ports are free to organize their own data in to data groups of their choosing

# Dual Spinlock With Data Group Locking

The **"Dual Spinlock With Data Group Locking"** uses a pair of spinlocks to protect each data group (namely the `xTaskSpinlock` and `xISRSpinlock` spinlocks).

```c
typedef struct
{
    #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) )
        portSPINLOCK_TYPE xTaskSpinlock;
        portSPINLOCK_TYPE xISRSpinlock;
    #endif /* #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) ) */
} xSomeDataGroup_t;
```

However, each data group must also allow for non-deterministic access with interrupts **enabled** by providing a pair of lock/unlock functions. These functions must block access to other tasks trying to access members of a data group and must pend access to ISRs trying to access members of the data group.

```c
static void prvLockSomeDataGroupForTasks( xSomeDataGroup_t * const pxSomDataGroup );
static void prvUnlockSomeDataGroupForTasks( xSomeDataGroup_t * const pxSomDataGroup );
```

In simple terms, the "Dual Spinlock With Data Group Locking" is an extension is the existing dual spinlock (i.e., Task and ISR spinlock) approach used in the SMP FreeRTOS kernel, but replicated across different data groups.

## Data Group Critical Sections (Granular Locks)

A critical section for a data group can be achieved as follows:

- When entering a data group critical section from a task
  1. Disable interrupts
  2. Take `xTaskSpinlock` of data group
  3. Take `xISRSpinlock` of data group
  4. Increment nesting count
- When entering data group critical section from an ISR
  1. Disable interrupts
  2. Take `xISRSpinlock` of data group
  3. Increment nesting count

When exiting a data group critical section, the procedure is reversed. Furthermore, since yield requests are pended when inside a critical section, exiting a task critical section will also need to handle any pended yields.

- When exiting a data group critical section from a task
  1. Release `xISRSpinlock` of data group
  2. Release `xTaskSpinlock` of data group
  3. Decrement nesting count
  4. Reenable interrupts if nesting count is 0
  5. Trigger yield if there is a yield pending
- When exiting data group critical section form an ISR
  1. Release `xISRSpinlock` of data group
  2. Decrement nesting count
  3. Reenable interrupts if nesting count is 0

Entering multiple data group critical sections in a nested manner is permitted. This means, if a code path has already entered a critical section in data group A, it can then enter a critical section in data group B. This is analogous to nested critical sections. However, care must be taken to avoid deadlocks. This can be achieved by organizing data groups into a hierarchy, where a higher layer data group cannot nest into a lower one.

```
                                           +-------------------+
                                           | Kernel Data Group |
                                           +-------------------+

  +-------------------+  +---------------------------+ +--------------------------+ +------------------+
  | Queue Data Groups |  | Stream Buffer Data Groups | | Event Groups Data Groups | | Timer Data Group |
  +-------------------+  +---------------------------+ +--------------------------+ +------------------+

+------------------------------------------------------------------------------------------------------+
|                                            User Data Groups                                          |
+------------------------------------------------------------------------------------------------------+
```

If nested locking only occurs from bottom up (e.g., User data group can nested into a Queue data group which in turn can nested into Kernel data group), then deadlocking will never occur.

## Data Group Locking

FreeRTOS does not permit walking linked lists while interrupts are disabled to ensure deterministic ISR latency. Therefore, each data group must provide a method of locking so that non-deterministic operations can be executed for a data group. While a data group is locked:

- Preemption is disabled for the current task
- Interrupts remained enabled
- The data group's `xTaskSpinlock` is taken to prevent tasks running on other cores from accessing the data group
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

Locking multiple data groups in a nested manner is permitted, meaning if a code path has already locked data group A, it can then lock data group B. This is analogous to nested `vTaskSuspendAll()` calls. Similar to data group locking, deadlocks can be avoided by organizing data groups into a hierarchy.

## Thread Safety Check

Under SMP, there are four sources of concurrent access for a particular data group:

- Preempting task on the same core
- Preempting ISR on the same core
- Concurrent task on another core
- Concurrent ISR on another core

This section checks that the data group critical section and locking mechanisms mentioned, ensure thread safety from each concurrent source of access.

- Data Group Critical Section from tasks: Interrupts are disabled, `xTaskSpinlock` and `xISRSpinlock` are taken
  - Task (same core): Context switch cannot occur because interrupts are disabled
  - Task (other cores): The task will spin on `xTaskSpinlock`
  - ISR (same core): Interrupts on the current core are disabled
  - ISR (other cores): ISR will spin on `xISRSpinlock`

- Data Group Critical Sections from ISRs: Interrupts are disabled, `xISRSpinlock` is taken
  - Task (same core): Context switch cannot occur because we are in an ISR
  - Task (other cores): The task will spin on `xISRSpinlock`
  - ISR (same core): Interrupts on the current core are disabled
  - ISR (other cores): ISR will spin on `xISRSpinlock`

- Data Group Locking from tasks: Preemption is disabled, `xTaskSpinlock` is taken
  - Task (same core): Context switch cannot occur because preemption is disabled
  - Task (other cores): The task will spin on `xTaskSpinlock`
  - ISR (same core): Critical section is entered because `xISRSpinlock` is not held, but access is pended
  - ISR (other cores): Critical section is entered because `xISRSpinlock` is not held, but access is pended

# Public API Changes

To support **"Dual Spinlock With Data Group Locking"**, the following changes have been made to the public facing API. These changes are non-breaking, meaning that applications that can build against the existing SMP FreeRTOS kernel will still be able to build even with granular locking enabled (albeit less performant).

The following APIs have been added to enter/exit a critical section in a data group. This are called by FreeRTOS source code to mark critical sections in data groups. However, users can also create their own data groups and enter/exit critical sections in the same manner.

If granular locking is disabled, these macros simply revert to being the standard task enter/exit critical macros.

```c
#if ( portUSING_GRANULAR_LOCKS == 1 )
    #define data_groupENTER_CRITICAL()                                    portENTER_CRITICAL_DATA_GROUP( ( portSPINLOCK_TYPE * ) pxTaskSpinlock, ( portSPINLOCK_TYPE * ) pxISRSpinlock )
    #define data_groupENTER_CRITICAL_FROM_ISR()                           portENTER_CRITICAL_DATA_GROUP_FROM_ISR( ( portSPINLOCK_TYPE * ) pxISRSpinlock )
    #define data_groupEXIT_CRITICAL()                                     portEXIT_CRITICAL_DATA_GROUP( ( portSPINLOCK_TYPE * ) pxTaskSpinlock, ( portSPINLOCK_TYPE * ) pxISRSpinlock )
    #define data_groupEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )    portEXIT_CRITICAL_DATA_GROUP_FROM_ISR( uxSavedInterruptStatus, ( portSPINLOCK_TYPE * ) pxISRSpinlock )
#else /* #if ( portUSING_GRANULAR_LOCKS == 1 ) */
    #define data_groupENTER_CRITICAL()                                    taskENTER_CRITICAL()
    #define data_groupENTER_CRITICAL_FROM_ISR()                           taskENTER_CRITICAL_FROM_ISR()
    #define data_groupEXIT_CRITICAL()                                     taskEXIT_CRITICAL()
    #define data_groupEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )    taskEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )
#endif /* #if ( portUSING_GRANULAR_LOCKS == 1 ) */
```

In case of the kernel data group (tasks.c), the granular locking macros make use of the existing `vTaskEnter/ExitCritical<FromISR>()` functions to establish critical sections.


```c
#if ( portUSING_GRANULAR_LOCKS == 1 )
    #define kernelENTER_CRITICAL()                                    vTaskEnterCritical()
    #define kernelENTER_CRITICAL_FROM_ISR()                           vTaskEnterCriticalFromISR()
    #define kernelEXIT_CRITICAL()                                     vTaskExitCritical()
    #define kernelEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )    vTaskExitCriticalFromISR( uxSavedInterruptStatus )
#else /* #if ( portUSING_GRANULAR_LOCKS == 1 ) */
    #define kernelENTER_CRITICAL()                                    taskENTER_CRITICAL()
    #define kernelENTER_CRITICAL_FROM_ISR()                           taskENTER_CRITICAL_FROM_ISR()
    #define kernelEXIT_CRITICAL()                                     taskEXIT_CRITICAL()
    #define kernelEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )    taskEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )
#endif /* #if ( portUSING_GRANULAR_LOCKS == 1 ) */
```

The previous critical section macros, viz., `taskENTER/EXIT_CRITICAL()` are still provided and can be called by users. However, FreeRTOS source code will no longer call them. If called by the users, the port should implement a "user" data group. As a result, if an application previously relied on `taskENTER/EXIT_CRITICAL()` for thread safe access to some user data, the same code is still thread safe with granular locking enabled.

```c
#define taskENTER_CRITICAL()                portENTER_CRITICAL()
#define taskEXIT_CRITICAL()                 portEXIT_CRITICAL()
#define taskENTER_CRITICAL_FROM_ISR()       portENTER_CRITICAL_FROM_ISR()
#define taskEXIT_CRITICAL_FROM_ISR( x )     portEXIT_CRITICAL_FROM_ISR( x )
```

# Porting Interface

To support **"Dual Spinlock With Data Group Locking"**, ports will need to provide the following macro definitions

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

Macros are provided for the spinlocks for initializing them either statically or dynamically. This is reflected in the macros API pattern.

```c
#define portINIT_SPINLOCK( pxSpinlock )    _port_spinlock_init( pxSpinlock )
#define portINIT__SPINLOCK_STATIC          PORT_SPINLOCK_STATIC_INIT
```

## Critical Section Macros

The port will need to provide implementations for macros to enter/exit a data group critical section according the procedures described above. Typical implementations of each macro is demonstrated below:

```c
#if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) )
    #define portENTER_CRITICAL_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )     vPortEnterCriticalDataGroup( pxTaskSpinlock, pxISRSpinlock )
    #define portENTER_CRITICAL_DATA_GROUP_FROM_ISR( pxISRSpinlock )            uxPortEnterCriticalDataGroupFromISR( pxISRSpinlock )
    #define portEXIT_CRITICAL_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )      vPortExitCriticalDataGroup( pxTaskSpinlock, pxISRSpinlock )
    #define portEXIT_CRITICAL_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )          vPortExitCriticalDataGroupFromISR( x, pxISRSpinlock )
#endif /* #if ( ( portUSING_GRANULAR_LOCKS == 1 ) && ( configNUMBER_OF_CORES > 1 ) ) */
```

Example implementation of `portENTER_CRITICAL_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )` and `portEXIT_CRITICAL_DATA_GROUP( pxTaskSpinlock, pxISRSpinlock )`. Note that:

- `pxTaskSpinlock` is made optional in case users want to create their own data groups that are protected only be a single lock.
- The kernel implements the `xTaskUnlockCanYield()` function to indicate whether an yield should occur when a critical section exits. This function takes into account whether there are any pending yields and whether preemption is currently disabled.

```c
void vPortEnterCriticalDataGroup( port_spinlock_t *pxTaskSpinlock, port_spinlock_t *pxISRSpinlock )
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

void vPortExitCriticalDataGroup( port_spinlock_t *pxTaskSpinlock, port_spinlock_t *pxISRSpinlock )
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

Example implementation of `portENTER_CRITICAL_DATA_GROUP_FROM_ISR( pxISRSpinlock )` and `portEXIT_CRITICAL_DATA_GROUP_FROM_ISR( x, pxISRSpinlock )`. Note that only `pxISRSpinlock` needs to be provided since ISR critical sections take a single lock.

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
- All calls to `taskENTER/EXIT_CRITICAL[_FROM_ISR]()` have been replaced with `data_groupENTER/EXIT_CRITICAL[_FROM_ISR]()`.
- Added `xTaskUnlockCanYield()` which indicates whether a yield should occur when exiting a critical (i.e., unlocking a data group). Yields should not occur if preemption is disabled (such as when exiting a critical section inside a suspension block).

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

- Added `queueLOCK()` and `queueUNLOCK()`
  - If granular locks are disabled, reverts to the previous `prvLockQueue()` and `prvUnlockQueue()`
  - If granular locks are enabled, will lock/unlock the queue data group for tasks

## Event Groups

- Added `eventLOCK()` and `eventUNLOCK()`
  - If granular locks are disabled, reverts to the previous `vTaskSuspendAll()` and `xTaskResumeAll()` calls
  - If granular locks are enabled, will lock/unlock the event groups data group for tasks
- `xEventGroupSetBits()` and `vEventGroupDelete()` will manually walk the task lists (which belong to the kernel data group). Thus, an extra `vTaskSuspendAll()`/`xTaskResumeAll()` is added to ensure that the kernel data group is suspended while walking those tasks lists.

## Stream Buffer

- Added `sbLOCK()` and `sbUNLOCK()`
  - If granular locks are disabled, reverts to the previous `vTaskSuspendAll()` and `xTaskResumeAll()` calls
  - If granular locks are enabled, will lock/unlock the stream buffer data group for tasks

## Timers

- Timers don't have a lock/unlock function. The existing `vTaskSuspendAll()`/`xTaskResumeAll()` calls are valid as they rely on freezing the tick count which is part of the kernel data group.

# Prerequisite Refactoring

A number of refactoring commits have been added to make the addition of granular locking changes simpler:

1. Move critical sections inside `xTaskPriorityInherit()`

Currently, `xTaskPriorityInherit()` is called with wrapping critical sections. The critical sections have now be moved inside the function so that they have access to the kernel data group's spinlocks.

2. Move critical section into `vTaskPriorityDisinheritAfterTimeout()`

Currently, `vTaskPriorityDisinheritAfterTimeout()` is called wrapping critical sections, where the highest priority waiting task is separately obtained via `prvGetDisinheritPriorityAfterTimeout()`. The critical section and checking of the highest priority have been all been moved into `vTaskPriorityDisinheritAfterTimeout()` as all of these operations access the kernel data group.

3. Allow `vTaskPreemptionEnable()` to be nested

Currently, nested calls of `vTaskPreemptionEnable()` is not supported. However, nested calls are required for granular locking due the occurrence of nested suspension across multiple data groups.

Thus, `vTaskPreemptionEnable()` has been updated to support nested calls. This is done by changing `xPreemptionDisable` to a count, where a non-zero count means that the current task cannot be preempted.

# TCB Locks

When `portUSING_GRANULAR_LOCKS == 1` and `configNUMBER_OF_CORES > 1`, each TCB carries an additional spinlock (`xTCBSpinlock`) that guards TCB-specific fields touched by preemption-disable / preemption-enable paths (`uxPreemptionDisable`, `uxDeferredStateChange`). The TCB lock is acquired via `vTaskTCBEnterCritical()` / `vTaskTCBExitCritical()` and lives below the kernel data group in the lock hierarchy. Using a per-TCB lock here avoids contention on the kernel data-group lock for the common case where a task only needs to inspect or update its own preemption-disable state.

# Deferred State Changes

Calls that change a task's run state (`vTaskDelete()`, `vTaskSuspend()`) cannot run their full effect while the target task has preemption disabled, because doing so would yield from a TCB whose owner asked not to be preempted. Granular locks introduce `uxDeferredStateChange` on the TCB to record the requested transition (`tskDEFERRED_DELETION`, `tskDEFERRED_SUSPENSION`). The deferred work is then performed at the next `xTaskPreemptionEnableWithYieldStatus()` once the preemption-disable count drops to zero, outside the TCB critical section so that any context switch and the post-state-change ready-list manipulation happen in a regular kernel critical section.

# ISR-Only Kernel Critical Section Helpers

`prvKernelEnterISROnlyCritical()` / `prvKernelExitISROnlyCritical()` are internal helpers used to enter the kernel data group from a context that is already inside a surrounding data-group critical section (and therefore already has interrupts disabled and holds the surrounding data group's ISR spinlock). Unlike `kernelENTER_CRITICAL_FROM_ISR()` / `kernelEXIT_CRITICAL_FROM_ISR()`, they do not touch the interrupt state — the outer section owns that — and they only acquire/release the kernel ISR spinlock and adjust the per-core kernel critical-nesting count. `xTaskRemoveFromEventList()` and `xTaskRemoveFromEventListFromISR()` use these helpers so that callers walking an event list while holding e.g. a queue's spinlock do not need to know whether they are in task or ISR context.

# Event-List TOCTOU Considerations

Under granular locks, an event list (`xTasksWaitingToSend`, `xTasksWaitingToReceive`, queue-set container waiting list) is protected by the kernel ISR spinlock, while the surrounding queue / event-group critical section only holds that data group's own spinlocks. The kernel API `xTaskRemoveFromEventList()` re-checks list emptiness under the kernel ISR lock before removing an entry, so callers must call it directly rather than gating it on an outer `listLIST_IS_EMPTY()` check. The outer check can race with a concurrent removal from the tick ISR on another core; the inner re-check is authoritative.

The only places where an outer empty-check is retained on purpose are the `prvUnlockQueue()` drain loops, where the surrounding queue ISR spinlock prevents concurrent additions to the wait list and the outer check exists for early loop termination, not for race avoidance.

# Known Limitations

- Under `configRUN_MULTIPLE_PRIORITIES == 1`, the relaxed lock hierarchy means that an unblock triggered by a tick on one core may take effect on the unblocking core a little later than under global locking. The single-highest-priority invariant continues to hold under `configRUN_MULTIPLE_PRIORITIES == 0`.
- The design has been exercised on the Xtensa SMP port (ESP32). Other ports — including the upstream POSIX, ARMv7-M and ARMv8-M SMP ports — need to provide the spinlock, critical-nesting, and yield primitives listed in *Porting Interface* before they can opt in.

# Performance Metrics

Performance numbers will be added once the upstream port reference has the porting checklist completed. Initial measurements on ESP32 (Xtensa, dual-core, 240 MHz) show reduced contention on multi-queue workloads where unrelated tasks send to / receive from distinct queues concurrently; full benchmark methodology and numbers will be published with this PR's review pass.

