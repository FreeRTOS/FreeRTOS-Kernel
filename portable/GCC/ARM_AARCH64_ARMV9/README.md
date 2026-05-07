# Armv9-A Architecture Port

This port extends the AArch64 SRE (System Register Enable) port with Armv9-A
architectural features. It targets processors implementing FEAT_SVE2, FEAT_MTE2,
FEAT_PAuth, FEAT_BTI, and FEAT_RME.

## Relationship to ARM_AARCH64_SRE

This port is based on `ARM_AARCH64_SRE` and shares the same GICv3 system
register interface and generic timer infrastructure. The Armv9 additions are
guarded by `configARMV9_*` configuration flags — when all flags are disabled
(default), this port behaves identically to the Armv8 SRE port.

**Note:** This port is currently maintained as a separate directory from
`ARM_AARCH64_SRE`. A future decision will determine whether to fold these
changes into the existing SRE port (behind `configARMV9_*` guards) or maintain
them as a distinct port. Until that decision is made, this directory exists
independently to avoid regression risk to the Armv8 user base.

## Configuration Flags

All flags default to 0 (disabled). Set in `FreeRTOSConfig.h`:

| Flag | Feature |
|------|---------|
| `configARMV9_SVE2` | SVE2 register save/restore (Z0-Z31, P0-P15, FFR) |
| `configARMV9_SSVE` | Streaming SVE mode (SVCR save/restore) |
| `configARMV9_TASK_VL` | Per-task vector length (ZCR_EL1) |
| `configARMV9_PAC` | Per-task PAC key loading |
| `configARMV9_PAC_FRAME` | PAC-signed saved context frame |
| `configARMV9_MTE_HEAP` | MTE-tagged heap allocations |
| `configARMV9_MTE_STACK` | MTE-tagged task stacks |
| `configARMV9_BTI` | BTI landing pads in port assembly |
| `configARMV9_RME` | Realm Management Extension |
| `configARMV9_RME_EL2` | EL2 hypervisor operation |

## Hardware Prerequisites

- `CPACR_EL1.ZEN = 3` (SVE access from EL1/EL0)
- `CPTR_EL3.EZ = 1` (no SVE trap from EL3)
- `ZCR_EL2` / `ZCR_EL1` configured for desired vector length
- `SCTLR_EL1.EnIA = 1` (PAC enabled)
- `SCR_EL3.API/APK = 1`, `HCR_EL2.API/APK = 1` (PAC not trapped)
- `SCTLR_EL1.ATA = 1` (MTE enabled)
- `TCR_EL1.TBI0 = 1` (Top Byte Ignore for MTE pointers)
- MMU with GP bit (BTI) and Tagged Normal memory (MTE)

## Files

| File | Description |
|------|-------------|
| `port.c` | Task initialization, tick handler, critical sections |
| `portASM.S` | Context switch macros with `#if configARMV9_SVE2` guards |
| `portmacro.h` | Type definitions, macros, config flag declarations |
| `README.md` | This file |

## Context Switch Frame Layout

### With `configARMV9_SVE2 = 0` (Armv8 compatible)
```
[SP] → FPU flag + critical nesting (16 bytes)
       FPSR + FPCR (16 bytes)
       Q0-Q31 (512 bytes)
       SPSR + ELR (16 bytes)
       X0-X30 (256 bytes)
```

### With `configARMV9_SVE2 = 1`
```
[SP] → FPU flag + critical nesting (16 bytes)
       P0-P15 + FFR (3 × VL bytes, 16-byte aligned)
       Z0-Z31 (32 × VL bytes)
       FPSR + FPCR (16 bytes)
       SPSR + ELR (16 bytes)
       X0-X30 (256 bytes)
```

Total SVE frame at VL=128: 32×16 + 3×16 + 16 = 576 bytes
Total SVE frame at VL=256: 32×32 + 3×32 + 16 = 1136 bytes
