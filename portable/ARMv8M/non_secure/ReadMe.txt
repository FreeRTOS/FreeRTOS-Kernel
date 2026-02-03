This directory tree contains the master copy of the FreeRTOS Armv8-M and
Armv8.1-M ports.
Do not use the files located here!  These file are copied into separate
FreeRTOS/Source/portable/[compiler]/ARM_CM[23|33|52|55|85]_NNN and
FreeRTOS/Source/portable/[compiler]/STAR_MC3_NNN directories prior to
each FreeRTOS release.

If your Armv8-M/Armv8.1-M application uses TrustZone then use the files from the
FreeRTOS/Source/portable/[compiler]/ARM_CM[23|33|52|55|85] and
FreeRTOS/Source/portable/[compiler]/STAR_MC3 directories.

If your Armv8-M/Armv8.1-M application does not use TrustZone then use the files from
the FreeRTOS/Source/portable/[compiler]/ARM_CM[23|33|52|55|85]_NTZ and
FreeRTOS/Source/portable/[compiler]/STAR_MC3_NTZ directories.
