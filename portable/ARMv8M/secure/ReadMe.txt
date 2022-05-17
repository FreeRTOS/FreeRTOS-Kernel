This directory tree contains the master copy of the FreeRTOS Armv8-M and
Armv8.1-M ports.
Do not use the files located here!  These file are copied into separate
FreeRTOS/Source/portable/[compiler]/ARM_CM[23|33]_NNN directories prior to
each FreeRTOS release.
For Cortex CM55 use ARM_CM[33]_NNN.

If your Armv8-M/Armv8.1-M application uses TrustZone then use the files from the
FreeRTOS/Source/portable/[compiler]/ARM_CM[23|33] directories.
For Cortex CM55 use ARM_CM[33].

If your Armv8-M/Armv8.1-M application does not use TrustZone then use the files from
the FreeRTOS/Source/portable/[compiler]/ARM_CM[23|33]_NTZ directories.
For Cortex CM55 use ARM_CM[33].
