# Arm Cortex-R82 FreeRTOS Kernel Port

# Overview

- This directory contains the FreeRTOS Kernel port for Arm Cortex-R82 based on Armv8-R AArch64 architecture.
- It provides the portable layer required by the kernel to run on this architecture.

# Supported toolchains

The port is supported and tested on the following toolchains:

  * Arm Compiler for Embedded v6.23 (armclang).
  * Arm GNU toolchain v14.2.

# Cache Coherency

- This port assumes the hardware or model is fully cache coherent.
- The port does not perform cache maintenance for shared buffers.
- If your hardware or model doesn't support full cache coherency, you must handle cache clean/invalidate operations, memory attributes, and any additional barriers in your BSP/application (especially around shared-memory regions).

# MPU Support

- This port supports the FreeRTOS MPU on both single-core and SMP (multi-core) configurations. Enable via `configENABLE_MPU = 1`; the port programs MPU regions per task on each active core.

- Minimum MPU granularity and alignment: 64 bytes. Ensure any user‑defined region base and size are 64‑byte aligned.

# SMP Multicore Bring-up

For SMP systems using this port, the application only needs to start the scheduler on the primary core and issue an SVC from each secondary core once they are online. The kernel coordinates the rest and ensures all cores are properly managed.

- Developer-facing summary: call `vTaskStartScheduler()` on the primary core; each secondary core, in its **reset handler**, performs its local init and then issues an SVC (immediate value `106`) to hand off to the kernel. The port will bring all cores under the scheduler.

Primary core flow:

1. Perform core-specific and shared initialization (e.g., set EL1 stack pointer, zero-initialize `.bss`).
2. Jump to `main()`, create user tasks, optionally pin tasks to specific cores.
3. Call `vTaskStartScheduler()` which invokes `xPortStartScheduler()`.
4. `xPortStartScheduler()` configures the primary core tick timer and signals secondary cores that shared init is complete using the `ucPrimaryCoreInitDoneFlag` variable.
5. Wait until all secondary cores report as brought up.
6. Once all cores are up, call `vPortRestoreContext()` to schedule the first task on the primary core.

Secondary core flow (to be done in each core’s reset handler):

1. Perform core-specific initialization (e.g., set EL1 stack pointer).
2. Wait for the primary core's signal that shared initialization is complete (i.e., `ucPrimaryCoreInitDoneFlag` set to 1).
3. Update `VBAR_EL1` from the boot vector table to the FreeRTOS vector table.
4. Initialize the GIC redistributor and enable SGIs so interrupts from the primary core are receivable; signal the primary that this secondary is online and ready by setting the its flag in the `ucSecondaryCoresReadyFlags` array.
5. Issue an SVC with immediate value `106` (i.e., `portSVC_START_FIRST_TASK`) to enter `FreeRTOS_SWI_Handler`, which will call `vPortRestoreContext()` based on the SVC number to start scheduling on this core.
