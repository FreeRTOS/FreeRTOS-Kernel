
# This script must be run from the directory in which it resides,
# i.e., `FreeRTOS-Kernel/verification/verifast`.

# Expected arguments:
# $1 : The path to the verifast IDE binary, i.e., `vfide`.
# $2 : The path to the pico sdk installation, usually stored in an environment
#      variable called `$PICO_SDK_PATH`.



VFIDE="$1"
echo Path to vfide binary : "\'$VFIDE\'"
PICO_SDK_PATH="$2"
echo Path to the Pico SDK : "\"$PICO_SDK_PATH\""


SOURCE_DIR="../.."
HEADER_DIR="$SOURCE_DIR/include"

TASK_H="$HEADER_DIR/task.h"
TASKS_C="$SOURCE_DIR/tasks.c"

PROOF_SETUP_DIR="proof_setup"
GENERATED_HEADERS_DIR="$PROOF_SETUP_DIR/generated"

FREERTOS_SMP_DEMO_DIR="demos/FreeRTOS-SMP-Demos"


# We replaced the following include paths:
# `$FREERTOS_SMP_DEMO_DIR/FreeRTOS/Demo/CORTEX_M0+_RP2040/build/generated/pico_base`
# ->
# `$GENERATED_HEADERS_DIR/pico_base`

"$VFIDE" "$HEADER_DIR" \
-I $PROOF_SETUP_DIR -D VERIFAST_PROOF "$TASKS_C" \
-I $FREERTOS_SMP_DEMO_DIR/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include \
-I $PICO_SDK_PATH/src/common/pico_base/include \
-I $FREERTOS_SMP_DEMO_DIR/FreeRTOS/Source/include  \
-I $GENERATED_HEADERS_DIR/pico_base \
-I $PICO_SDK_PATH/src/boards/include \
-I $PICO_SDK_PATH/src/rp2_common/cmsis/include \
-I $FREERTOS_SMP_DEMO_DIR/FreeRTOS/Demo/CORTEX_M0+_RP2040/OnEitherCore \
-I $PICO_SDK_PATH/src/rp2040/hardware_regs/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_base/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_clocks/include \
-I $PICO_SDK_PATH/src/rp2040/hardware_structs/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_claim/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_sync/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_gpio/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_irq/include \
-I $PICO_SDK_PATH/src/common/pico_sync/include \
-I $PICO_SDK_PATH/src/common/pico_time/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_timer/include \
-I $PICO_SDK_PATH/src/common/pico_util/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_resets/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_pll/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_vreg/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_watchdog/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_xosc/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_exception/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_multicore/include \
-I $PICO_SDK_PATH/src/common/pico_stdlib/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_uart/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_divider/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_runtime/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_printf/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_bootrom/include \
-I $PICO_SDK_PATH/src/common/pico_bit_ops/include \
-I $PICO_SDK_PATH/src/common/pico_divider/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_double/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_int64_ops/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_float/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_malloc/include \
-I $PICO_SDK_PATH/src/rp2_common/boot_stage2/include \
-I $PICO_SDK_PATH/src/common/pico_binary_info/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_stdio/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_stdio_uart/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_stdio_usb/include \
-I $PICO_SDK_PATH/lib/tinyusb/src \
-I $PICO_SDK_PATH/lib/tinyusb/src/common \
-I $PICO_SDK_PATH/lib/tinyusb/hw \
-I $PICO_SDK_PATH/src/rp2_common/pico_fix/rp2040_usb_device_enumeration/include \
-I $PICO_SDK_PATH/src/rp2_common/pico_unique_id/include \
-I $PICO_SDK_PATH/src/rp2_common/hardware_flash/include \
-I $PICO_SDK_PATH/src/common/pico_usb_reset_interface/include \


# Defines used during the built of the FreeRTOS SMP Demo that might be relevant
# in the future:
# -D CFG_TUSB_DEBUG=0 -D CFG_TUSB_MCU=OPT_MCU_RP2040 -D CFG_TUSB_OS=OPT_OS_PICO -D FREE_RTOS_KERNEL_SMP=1 -D LIB_FREERTOS_KERNEL=1 -D LIB_PICO_BIT_OPS=1 -D LIB_PICO_BIT_OPS_PICO=1 -D LIB_PICO_DIVIDER=1 -D LIB_PICO_DIVIDER_HARDWARE=1 -D LIB_PICO_DOUBLE=1 -D LIB_PICO_DOUBLE_PICO=1 -D LIB_PICO_FIX_RP2040_USB_DEVICE_ENUMERATION=1 -D LIB_PICO_FLOAT=1 -D LIB_PICO_FLOAT_PICO=1 -D LIB_PICO_INT64_OPS=1 -D LIB_PICO_INT64_OPS_PICO=1 -D LIB_PICO_MALLOC=1 -D LIB_PICO_MEM_OPS=1 -D LIB_PICO_MEM_OPS_PICO=1 -D LIB_PICO_MULTICORE=1 -D LIB_PICO_PLATFORM=1 -D LIB_PICO_PRINTF=1 -D LIB_PICO_PRINTF_PICO=1 -D LIB_PICO_RUNTIME=1 -D LIB_PICO_STANDARD_LINK=1 -D LIB_PICO_STDIO=1 -D LIB_PICO_STDIO_UART=1 -D LIB_PICO_STDIO_USB=1 -D LIB_PICO_STDLIB=1 -D LIB_PICO_SYNC=1 -D LIB_PICO_SYNC_CORE=1 -D LIB_PICO_SYNC_CRITICAL_SECTION=1 -D LIB_PICO_SYNC_MUTEX=1 -D LIB_PICO_SYNC_SEM=1 -D LIB_PICO_TIME=1 -D LIB_PICO_UNIQUE_ID=1 -D LIB_PICO_UTIL=1 -D PICO_BOARD=\"pico\" -D PICO_BUILD=1 -D PICO_CMAKE_BUILD_TYPE=\"Release\" -D PICO_COPY_TO_RAM=0 -D PICO_CXX_ENABLE_EXCEPTIONS=0 -D PICO_NO_FLASH=0 -D PICO_NO_HARDWARE=0 -D PICO_ON_DEVICE=1 -D PICO_TARGET_NAME=\"on_core_zero\" -D PICO_USE_BLOCKED_RAM=0 \
