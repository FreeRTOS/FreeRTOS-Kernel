This directory tree contains the master copy of the FreeRTOS Armv8-M and
Armv8.1-M ports.
Do not use the files located here!  These file are copied into separate
FreeRTOS/Source/portable/[compiler]/ARM_[CM23|CM33|CM52|CM55|CM85|STAR_MC3]_NNN directories
prior to each FreeRTOS release.

If your Armv8-M/Armv8.1-M application uses TrustZone then use the files from the
FreeRTOS/Source/portable/[compiler]/ARM_[CM23|CM33|CM52|CM55|CM85|STAR_MC3] directories.

If your Armv8-M/Armv8.1-M application does not use TrustZone then use the files from
the FreeRTOS/Source/portable/[compiler]/ARM_[CM23|CM33|CM52|CM55|CM85|STAR_MC3]_NTZ directories.
