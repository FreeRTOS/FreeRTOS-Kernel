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

## Scheduler Suspension

`vTaskSuspendAll()` locks the kernel data group. It takes the kernel's `xTaskSpinlock` and holds it until `xTaskResumeAll()`, as the single kernel lock does without granular locks. Tasks on other cores therefore stay out of kernel critical sections while the scheduler is suspended.

A lock that a task holds while it calls into the kernel is above the kernel data group in the lock order. A task that takes such a lock while it has suspended the scheduler takes the two locks in the reverse order. If a task on another core holds that lock at the same moment and waits for the kernel's `xTaskSpinlock`, each core waits for the spinlock that the other core holds, and neither continues.

With granular locks, no lock that is held across a call into the kernel may therefore be taken while the scheduler is suspended. Two kinds of lock follow this rule.

- The data group locks. A queue operation, for example, takes the queue's `xTaskSpinlock` first. When it blocks the calling task, or changes a priority for a mutex, it takes the kernel's `xTaskSpinlock` while it still holds the queue's. The API functions of these objects must not be called while the scheduler is suspended.
  - queues, semaphores, mutexes and queue sets
  - event groups
  - stream buffers and message buffers
  - software timers, whose API functions send commands to the timer queue
- Locks of other components and of application code. The ESP-IDF ring buffer, for example, holds its own spinlock while it calls `vTaskPlaceOnEventList()` and `xTaskRemoveFromEventList()`, so its API functions must not be called while the scheduler is suspended either.

The rule includes the calls that never block, such as `uxQueueMessagesWaiting()` or `xQueueSend()` with a block time of 0, because they also take the object's lock. Task notifications and the other functions in `task.h` use only the kernel data group. They follow the existing rule that a function that can cause a context switch must not be called while the scheduler is suspended. Interrupts are not restricted. The `FromISR` functions take only `xISRSpinlock` locks.

The rule also covers code that the kernel itself runs while it has suspended the scheduler.

- the callback of `uxTaskCallForEachTask()`
- the tickless idle hooks `configPRE_SUPPRESS_TICKS_AND_SLEEP_PROCESSING()` and `portSUPPRESS_TICKS_AND_SLEEP()`
- the `traceMALLOC()` and `traceFREE()` macros of the heap implementations

The kernel's timer task is a known exception, open for discussion. `prvProcessTimerOrBlockTask()` calls `vQueueWaitForMessageRestricted()` on the timer queue while it has suspended the scheduler, which takes the timer queue's lock in the reverse order. It can deadlock with a task on another core that blocks on a full timer queue, for example in `xTimerStart()` with a block time.

Without granular locks there is a single kernel lock, so the order of two locks cannot be reversed, and the rule does not apply.

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

These changes are non-breaking: an application that builds against the SMP kernel without granular locks also builds with granular locks enabled.

The kernel files use the following macros, declared in `task.h` with `portUSING_GRANULAR_LOCKS == 1`, for the critical sections and locks of a data group. Each data group passes its own `xTaskSpinlock` and `xISRSpinlock`.

```c
taskDATA_GROUP_ENTER_CRITICAL( pxTaskSpinlock, pxISRSpinlock )
taskDATA_GROUP_EXIT_CRITICAL( pxTaskSpinlock, pxISRSpinlock )
taskDATA_GROUP_ENTER_CRITICAL_FROM_ISR( pxISRSpinlock, puxSavedInterruptStatus )
taskDATA_GROUP_EXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus, pxISRSpinlock )
taskDATA_GROUP_LOCK( pxTaskSpinlock )
taskDATA_GROUP_UNLOCK( pxTaskSpinlock )
taskDATA_GROUP_PROMOTE_LOCK_TO_CRITICAL( pxISRSpinlock )
taskDATA_GROUP_DEMOTE_CRITICAL_TO_LOCK( pxISRSpinlock )
```

`taskDATA_GROUP_ENTER_CRITICAL()` and `taskDATA_GROUP_LOCK()` are functions in `tasks.c` (`vTaskDataGroupEnterCritical()`, `vTaskDataGroupLock()`), because they check the run state of the calling task. The exit and `FROM_ISR` forms are macros. A port can set `portDATA_GROUP_CRITICAL_SECTIONS_AS_FUNCTIONS` to 1 to have them called as functions in `tasks.c` instead, which expand the same macro bodies. Ports and applications can create their own data groups with the same macros.

Each kernel file maps its own critical section macros (`queueENTER_CRITICAL()`, `event_groupsENTER_CRITICAL()`, `sbENTER_CRITICAL()`, `tmrENTER_CRITICAL()`) and lock macros to these when granular locks are enabled, and to `taskENTER_CRITICAL()`, the queue lock or the scheduler suspension otherwise. The kernel data group uses `vTaskEnterCritical()` and the related functions:

```c
#if ( portUSING_GRANULAR_LOCKS == 1 )
    #define kernelENTER_CRITICAL()                                    vTaskEnterCritical()
    #define kernelENTER_CRITICAL_FROM_ISR()                           vTaskEnterCriticalFromISR()
    #define kernelEXIT_CRITICAL()                                     vTaskExitCritical()
    #define kernelEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )    vTaskExitCriticalFromISR( uxSavedInterruptStatus )
#else
    #define kernelENTER_CRITICAL()                                    taskENTER_CRITICAL()
    #define kernelENTER_CRITICAL_FROM_ISR()                           taskENTER_CRITICAL_FROM_ISR()
    #define kernelEXIT_CRITICAL()                                     taskEXIT_CRITICAL()
    #define kernelEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )    taskEXIT_CRITICAL_FROM_ISR( uxSavedInterruptStatus )
#endif
```

`taskENTER_CRITICAL()` and `taskEXIT_CRITICAL()` and their `FROM_ISR` forms are still provided for applications, but the kernel files no longer call them with granular locks. The port decides what they protect. A port can implement them as a "user" data group, so that code that relied on them for data shared between tasks stays thread safe. Such a section then does not exclude the kernel data group or any other data group.

# Porting Interface

A port that sets `portUSING_GRANULAR_LOCKS` to 1 provides the following. `FreeRTOS.h` stops the build with an `#error` if one of the spinlock macros or `portCHECK_IF_IN_ISR()` is missing, and if `configNUMBER_OF_CORES` is 1 or `configUSE_TASK_PREEMPTION_DISABLE` is 0.

## Port Config

```c
#define portUSING_GRANULAR_LOCKS        1   /* Enables granular locks. */
#define portCRITICAL_NESTING_IN_TCB     0   /* The port keeps a critical nesting count per core. */
```

With `portCRITICAL_NESTING_IN_TCB == 0` the port provides `portGET_CRITICAL_NESTING_COUNT()`, `portSET_CRITICAL_NESTING_COUNT()`, `portINCREMENT_CRITICAL_NESTING_COUNT()` and `portDECREMENT_CRITICAL_NESTING_COUNT()`, each taking a core ID, as the SMP kernel already requires when the count is not kept in the task control block.

## Spinlocks

```c
#define portSPINLOCK_TYPE                           port_spinlock_t
#define portINIT_SPINLOCK( pxSpinlock )             _port_spinlock_init( pxSpinlock )
#define portINIT_SPINLOCK_STATIC                    PORT_SPINLOCK_STATIC_INIT
#define portGET_SPINLOCK( xCoreID, pxSpinlock )     _port_spinlock_take( xCoreID, pxSpinlock )
#define portRELEASE_SPINLOCK( xCoreID, pxSpinlock ) _port_spinlock_give( xCoreID, pxSpinlock )
#define portCHECK_IF_IN_ISR()                       _port_in_isr()
```

- `portGET_SPINLOCK()` must let a core take a spinlock it already holds, and `portRELEASE_SPINLOCK()` must then release it the same number of times. The kernel takes a task's TCB spinlock again while it holds it, for example in `vTaskDelete()` of a task that runs on another core.
- `portGET_SPINLOCK()` is called with interrupts enabled for the task spinlock of a data group (`taskDATA_GROUP_LOCK()` and the first step of `vTaskDataGroupEnterCritical()`).
- Taking and releasing a spinlock must order memory as an acquire and a release.

`portENTER_CRITICAL()` and `portEXIT_CRITICAL()` and their `FROM_ISR` forms are what `taskENTER_CRITICAL()` and the others call (see *Public API Changes*).

## Optional

- `portDATA_GROUP_CRITICAL_SECTIONS_AS_FUNCTIONS`: 1 to call the data group exit and `FROM_ISR` macros as functions (default 0).
- `portBASE_TYPE_ENTER_CRITICAL()` and `portBASE_TYPE_EXIT_CRITICAL()`: a port that can read a `BaseType_t` sized member atomically defines them. The kernel then uses them for the functions that read one such member, with granular locks too. With the default definitions the kernel takes the data group or kernel critical section instead. A port that defines them away can define `portBASE_TYPE_EXIT_CRITICAL()` as an acquire fence to keep the ordering of the spinlock.

# Source Specific Changes

- Added a `xTaskSpinlock` and `xISRSpinlock` to the data structures of each data group.
- With granular locks, the critical sections of each file take the spinlocks of the data group they change instead of the kernel's.

## Tasks (Kernel Data Group)

- Some functions are called from critical sections of other data groups, so they take the kernel data group's locks themselves:
  - `vTaskInternalSetTimeOutState()`
  - `xTaskIncrementTick()`
  - `vTaskSwitchContext()`
  - `xTaskRemoveFromEventList()`
  - `eTaskConfirmSleepModeStatus()`
  - `xTaskPriorityDisinherit()`, only when the holder's priority is inherited
- Some functions are called while another data group is locked, so they suspend the kernel data group themselves:
  - `vTaskPlaceOnEventList()`
  - `vTaskPlaceOnUnorderedEventList()`
  - `vTaskPlaceOnEventListRestricted()`
- `vTaskSuspendAll()` takes the kernel data group's `xTaskSpinlock` and holds it until `xTaskResumeAll()`, and records the core that suspended the scheduler (see *Scheduler Suspension*).
- `pvTaskIncrementMutexHeldCount()` changes the held count of the calling task without the kernel critical section. Only the holding task writes it, inside the mutex's queue critical section.

## Queue

- Added `queueLOCK()` and `queueUNLOCK()`
  - If granular locks are disabled, reverts to the previous `prvLockQueue()` and `prvUnlockQueue()`
  - If granular locks are enabled, will lock/unlock the queue data group for tasks

## Event Groups

- Added `event_groupsLOCK()` and `event_groupsUNLOCK()`
  - If granular locks are disabled, reverts to the previous `vTaskSuspendAll()` and `xTaskResumeAll()` calls
  - If granular locks are enabled, will lock/unlock the event groups data group for tasks
- `xEventGroupSetBits()` and `vEventGroupDelete()` will manually walk the task lists (which belong to the kernel data group). Thus, an extra `vTaskSuspendAll()`/`xTaskResumeAll()` is added to ensure that the kernel data group is suspended while walking those tasks lists.
  - `xEventGroupSetBits()` suspends the kernel data group only when `xTasksWaitingForBits` is not empty. Tasks are added to that list only while the event group is locked (`xEventGroupWaitBits()` and `xEventGroupSync()`), and `xEventGroupSetBits()` holds the same lock, so a list that is empty when it is checked stays empty for the rest of the call and there is nothing to walk. Removal by the tick, `vTaskDelete()`, `vTaskSuspend()` or `xTaskAbortDelay()` can only shorten the list.

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

Thus, `vTaskPreemptionEnable()` has been updated to support nested calls. This is done by changing `uxPreemptionDisable` to a count, where a non-zero count means that the current task cannot be preempted.

# TCB Locks

When `portUSING_GRANULAR_LOCKS == 1` and `configNUMBER_OF_CORES > 1`, each TCB carries an additional spinlock (`xTCBSpinlock`) that guards TCB-specific fields touched by preemption-disable / preemption-enable paths (`uxPreemptionDisable`, `uxDeferredStateChange`). The TCB lock is acquired via `vTaskTCBEnterCritical()` / `vTaskTCBExitCritical()` and lives below the kernel data group in the lock hierarchy. Using a per-TCB lock here avoids contention on the kernel data-group lock for the common case where a task only needs to inspect or update its own preemption-disable state.

# Deferred State Changes

Calls that change a task's run state (`vTaskDelete()`, `vTaskSuspend()`) cannot run their full effect while the target task has preemption disabled, because doing so would yield from a TCB whose owner asked not to be preempted. Granular locks introduce `uxDeferredStateChange` on the TCB to record the requested transition (`tskDEFERRED_DELETION`, `tskDEFERRED_SUSPENSION`). The deferred work is then performed at the next `xTaskPreemptionEnableWithYieldStatus()` once the preemption-disable count drops to zero, outside the TCB critical section so that any context switch and the post-state-change ready-list manipulation happen in a regular kernel critical section.

# ISR-Only Kernel Critical Section Helpers

`prvKernelEnterISROnlyCritical()` / `prvKernelExitISROnlyCritical()` are internal helpers used to enter the kernel data group from a context that is already inside a surrounding data-group critical section (and therefore already has interrupts disabled and holds the surrounding data group's ISR spinlock). Unlike `kernelENTER_CRITICAL_FROM_ISR()` / `kernelEXIT_CRITICAL_FROM_ISR()`, they do not touch the interrupt state — the outer section owns that — and they only acquire/release the kernel ISR spinlock and adjust the per-core kernel critical-nesting count. `xTaskRemoveFromEventList()` and `xTaskRemoveFromEventListFromISR()` use these helpers so that callers walking an event list while holding e.g. a queue's spinlock do not need to know whether they are in task or ISR context.

# Event-List Check and Removal Races

Under granular locks, a queue's event lists (`xTasksWaitingToSend`, `xTasksWaitingToReceive`, and the waiting list of a queue set container) are changed under two locks. A task adds itself to an event list while it holds the queue's task spinlock, with the queue locked. Every removal holds the kernel ISR spinlock. Interrupts do not add to event lists.

A queue checks an event list with `listLIST_IS_EMPTY()` before it calls `xTaskRemoveFromEventList()` or `xTaskRemoveFromEventListFromISR()`, which take the kernel ISR spinlock. Each check is made while the queue holds a lock that excludes additions, so the list can only shrink while the check is in effect.

- Task functions check inside the queue critical section, which holds the queue's task spinlock.
- `FromISR` functions and the queue set notification check while they hold the queue's ISR spinlock and the queue is unlocked.
- `prvUnlockQueue()` checks while its caller still holds the queue's task spinlock from `queueLOCK()`.

An empty list therefore stays empty, and skipping the call gives the same result as the call. A list that was not empty can be emptied by a removal on another core, for example a timeout in the tick, so the remove functions check the list again under the kernel ISR spinlock.

# Behaviour Changes

Two changes in this branch can be noticed by application code. The rule for code that runs while the scheduler is suspended is described in *Scheduler Suspension*.

## Nested Preemption Disable

This applies to every build with `configUSE_TASK_PREEMPTION_DISABLE == 1`, with or without granular locks. Before this branch, `vTaskPreemptionDisable()` set a flag in the task, and `vTaskPreemptionEnable()` cleared it and always asked the task's core to yield. The flag is now a count (`uxPreemptionDisable`):

- `vTaskPreemptionDisable()` adds one and `vTaskPreemptionEnable()` subtracts one, so the calls can be nested. Preemption is enabled again only when the count reaches zero.
- While the count is above zero, a yield requested for the task's core is recorded and not sent. `vTaskSwitchContext()` records the yield in the same way.
- When the count reaches zero, the core yields only if a yield was recorded meanwhile.
- Before the scheduler starts, both functions do nothing.

Code that calls `vTaskPreemptionDisable()` more than once now needs the same number of `vTaskPreemptionEnable()` calls. Code that relied on a yield from every `vTaskPreemptionEnable()` no longer gets one. With granular locks, `vTaskSuspend()` and `vTaskDelete()` of a task with preemption disabled take effect when the task enables preemption again (*Deferred State Changes*).

## Tick Hook After the Switch Decision

With granular locks, `xTaskIncrementTick()` calls `vApplicationTickHook()` after it has left the kernel critical section, because queue functions called from the hook take the queue's locks, which must not be taken inside the kernel data group. The return value of `xTaskIncrementTick()` is decided before the hook runs. A task that the hook makes ready on the tick's core therefore runs at that core's next yield point, not at the end of the tick interrupt. Without granular locks the hook runs inside `xTaskIncrementTick()` as before.

# Known Limitations

- Under `configRUN_MULTIPLE_PRIORITIES == 1`, the relaxed lock hierarchy means that an unblock triggered by a tick on one core may take effect on the unblocking core a little later than under global locking. The single-highest-priority invariant continues to hold under `configRUN_MULTIPLE_PRIORITIES == 0`.
- The design has been exercised on the Xtensa SMP port (ESP32). Other ports — including the upstream POSIX, ARMv7-M and ARMv8-M SMP ports — need to provide the spinlock, critical-nesting, and yield primitives listed in *Porting Interface* before they can opt in.

# Performance Metrics

Performance numbers will be added once the upstream port reference has the porting checklist completed. Initial measurements on ESP32 (Xtensa, dual-core, 240 MHz) show reduced contention on multi-queue workloads where unrelated tasks send to / receive from distinct queues concurrently; full benchmark methodology and numbers will be published with this PR's review pass.

