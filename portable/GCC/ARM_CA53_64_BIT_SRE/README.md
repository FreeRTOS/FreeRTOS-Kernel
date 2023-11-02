# ARM_CA53_64_BIT_SRE port

Initial port to support Armv8-A architecture in FreeRTOS kernel was written for
Arm Cortex-A53 processor.

* ARM_CA53_64_BIT_SRE
    * System Register interace to access Arm GIC registers

This port is generic and can be used as a starting point for other Armv8-A
application processors. Therefore, the port `Arm_AARCH64_SRE` is renamed as
`Arm_AARCH64_SRE`. The existing projects that use old port `Arm_AARCH64_SRE`,
should migrate to renamed port `Arm_AARCH64_SRE`.

**NOTE**

This port uses System Register interace to access Arm GIC registers.
