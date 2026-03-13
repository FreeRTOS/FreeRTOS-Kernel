This directory tree contains the master copy of the FreeRTOS Armv8-M and
Armv8.1-M ports.
Do not use the files located here!  These files are copied into separate
FreeRTOS/Source/portable/[compiler]/ARM_[CM23|CM33|CM52|CM55|CM85|STAR_MC3]_NNN directories
prior to each FreeRTOS release.

If your Armv8-M/Armv8.1-M application uses TrustZone then use the files from the
FreeRTOS/Source/portable/[compiler]/ARM_[CM23|CM33|CM52|CM55|CM85|STAR_MC3] directories.

If your Armv8-M/Armv8.1-M application does not use TrustZone then use the files from
the FreeRTOS/Source/portable/[compiler]/ARM_[CM23|CM33|CM52|CM55|CM85|STAR_MC3]_NTZ directories.

Note:
The Armv8-M ports support SMP (multicore) systems when both MPU and TrustZone are disabled.
However, this has only been validated on Arm Cortex-M33 Non-TrustZone Non-MPU port.

SMP Boot Sequence
---------------------------------------

Primary core flow:

1. Perform core-specific and shared initialization (e.g., zero-initialize `.bss`).
2. Jump to `main()`, create user tasks, optionally pin tasks to specific cores.
3. Call `vTaskStartScheduler()` which invokes `xPortStartScheduler()`.
4. `xPortStartScheduler()` configures the primary core tick timer and signals secondary cores that shared init is complete using the `ucPrimaryCoreInitDoneFlag` variable.
5. Call the application-defined `configWAKE_SECONDARY_CORES` function.
6. Wait until all secondary cores report as brought up.
7. Once all cores are up, call `vStartFirstTask()` to schedule the first task on the primary core.

Secondary core flow:

1. Perform core-specific initialization.
2. Wait until the primary core signals that shared initialization has completed (that is, `ucPrimaryCoreInitDoneFlag` is set to 1). Once this occurs,
the application-defined `configWAKE_SECONDARY_CORES` function is invoked by the primary core to carry out the subsequent steps.
3. Program the inter-processor signaling mechanism (e.g., Arm Doorbell Mechanism) to be used by the kernel to interrupt that core and request that it perform a context switch.
4. Call `vPortConfigureInterruptPriorities` function to setup per core interrupt priorities.
5. If Pointer Authentication (PAC) or Branch Target Identification (BTI) is supported, call `vConfigurePACBTI` with `pdTRUE` as the input parameter to configure the per-core special-purpose CONTROL register
with the appropriate PACBTI settings.
6. Signal the primary that this secondary is online and ready by setting its flag in the `ucSecondaryCoresReadyFlags` array.
7. Issue an SVC with immediate value `102` (portSVC_START_SCHEDULER), which will call `vRestoreContextOfFirstTask()` to start scheduling on this core.


Inter-core notification
---------------------------------------

On SMP systems the application must provide an implementation of the `vInterruptCore( uint8_t ucCoreID )` function. The kernel calls this function
to interrupt another core and request that it perform a context switch (e.g., when a higher-priority task becomes ready on that core).

Typical platform implementation: write a doorbell flag/bit or other inter-processor signaling register targeting `ucCoreID`. This should cause a
"doorbell" (or equivalent) IRQ on the secondary core. In the secondary core’s doorbell IRQ handler, check the reason for the interrupt and, if it is a
schedule request, trigger a context switch (i.e., by calling `portYIELD_FROM_ISR`).

Notes:

* `vInterruptCore` is declared weak in the port so that platforms can override it. If your hardware lacks a dedicated doorbell, use any available
inter-core interrupt/messaging mechanism to achieve the same effect.

* The application must define `configCORE_ID_REGISTER`, usually in `FreeRTOSConfig.h` to the memory-mapped address of the platform register used
to read the current core ID. The port reads this register to determine the executing core and to index per-core scheduler state.

* The application must define `configWAKE_SECONDARY_CORES`, usually in `FreeRTOSConfig.h`, to point to the application/platform-specific function
that wakes up and make the secondary cores ready after the primary core completes initialisation.
