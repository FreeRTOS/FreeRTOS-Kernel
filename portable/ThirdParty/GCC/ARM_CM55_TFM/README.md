# Target of this port

This port adds support for FreeRTOS applications to call the secure services
in Trusted Firmware M (TF-M) through Platform Security Architecture (PSA) APIs
on ARM Cortex-M55 based platforms.

To use this port please follow the documentation of the
[ARM_CM55_TFM port](../ARM_CM33_TFM/README.md), with the following additions:

* Instead of the kernel files in the
```freertos_kernel\portable\GCC\ARM_CM33_NTZ``` folder the
files in the ```freertos_kernel\portable\GCC\ARM_CM55_NTZ``` must be used.

* The ```os_wrapper_freertos.c``` file can be reused without modification from
the ```portable/ThirdParty/GCC/ARM_CM33_TFM``` folder.

* ARM Cortex-M55 supports MVE, so FreeRTOS kernel can be configured with the
```configENABLE_MVE`` macro. The setting of this macro is decided by the
setting in Secure Side which is platform-specific. If the Secure Side enables
Non-Secure access to MVE, then this macro can be configured as 0 or 1.
Otherwise, this macro can only be configured as 0.

*Copyright (c) 2022, Arm Limited. All rights reserved.*
