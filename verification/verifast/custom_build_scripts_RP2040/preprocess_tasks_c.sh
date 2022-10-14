#!/bin/zsh
ps -o comm= -p $$

PP_SCRIPT_WD=`pwd`
DEMO_DIR="$PP_SCRIPT_WD/../FreeRTOS/Demo/CORTEX_M0+_RP2040/"
#LOG_DIR="`pwd`/build_logs"
#BUILD_LOG="$LOG_DIR/build_log--`date +'%y_%m_%d--%H_%M'`.txt"
TIMESTAMP=`date +'%y_%m_%d--%H_%M'`
LOG_PP_OUT_DIR="$PP_SCRIPT_WD/log_preprocessed_files"
LOG_PP_TASK_C="$LOG_PP_OUT_DIR/tasks--pp--$TIMESTAMP.c"
LOG_PP_TASK_C_PRAGMA_COMMENTS="$LOG_PP_OUT_DIR/tasks--pp--pragma_comments--$TIMESTAMP.c"

PP_OUT_DIR="$PP_SCRIPT_WD/../preprocessed_files"
PP_TASK_C="$PP_OUT_DIR/tasks--pp.c"

pwd
mkdir $LOG_PP_OUT_DIR

# Relevant clang flags:
# -E
# -C
# -P : surpresses line/file pragmas


clang -E -C  -DFREE_RTOS_KERNEL_SMP=1 -DLIB_FREERTOS_KERNEL=1 -DLIB_PICO_BIT_OPS=1 -DLIB_PICO_BIT_OPS_PICO=1 -DLIB_PICO_DIVIDER=1 -DLIB_PICO_DIVIDER_HARDWARE=1 -DLIB_PICO_DOUBLE=1 -DLIB_PICO_DOUBLE_PICO=1 -DLIB_PICO_FLOAT=1 -DLIB_PICO_FLOAT_PICO=1 -DLIB_PICO_INT64_OPS=1 -DLIB_PICO_INT64_OPS_PICO=1 -DLIB_PICO_MALLOC=1 -DLIB_PICO_MEM_OPS=1 -DLIB_PICO_MEM_OPS_PICO=1 -DLIB_PICO_MULTICORE=1 -DLIB_PICO_PLATFORM=1 -DLIB_PICO_PRINTF=1 -DLIB_PICO_PRINTF_PICO=1 -DLIB_PICO_RUNTIME=1 -DLIB_PICO_STANDARD_LINK=1 -DLIB_PICO_STDIO=1 -DLIB_PICO_STDIO_UART=1 -DLIB_PICO_STDLIB=1 -DLIB_PICO_SYNC=1 -DLIB_PICO_SYNC_CORE=1 -DLIB_PICO_SYNC_CRITICAL_SECTION=1 -DLIB_PICO_SYNC_MUTEX=1 -DLIB_PICO_SYNC_SEM=1 -DLIB_PICO_TIME=1 -DLIB_PICO_UTIL=1 -DPICO_BOARD=\"pico\" -DPICO_BUILD=1 -DPICO_CMAKE_BUILD_TYPE=\"Release\" -DPICO_COPY_TO_RAM=0 -DPICO_CXX_ENABLE_EXCEPTIONS=0 -DPICO_NO_FLASH=0 -DPICO_NO_HARDWARE=0 -DPICO_ON_DEVICE=1 -DPICO_STACK_SIZE=0x1000 -DPICO_TARGET_NAME=\"on_core_one\" -DPICO_USE_BLOCKED_RAM=0 -DmainRUN_FREE_RTOS_ON_CORE=1 -I/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040/OnEitherCore -I/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/portable/ThirdParty/GCC/RP2040/include -I/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_base/include -I/Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040/build/generated/pico_base -I/Users/reitobia/programs/pico-sdk/src/boards/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_platform/include -I/Users/reitobia/programs/pico-sdk/src/rp2040/hardware_regs/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_base/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_clocks/include -I/Users/reitobia/programs/pico-sdk/src/rp2040/hardware_structs/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_claim/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_sync/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_gpio/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_irq/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_sync/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_time/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_timer/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_util/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_resets/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_pll/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_vreg/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_watchdog/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_xosc/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_exception/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_multicore/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_stdlib/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_uart/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/hardware_divider/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_runtime/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_printf/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_bootrom/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_bit_ops/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_divider/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_double/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_int64_ops/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_float/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_malloc/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/boot_stage2/include -I/Users/reitobia/programs/pico-sdk/src/common/pico_binary_info/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_stdio/include -I/Users/reitobia/programs/pico-sdk/src/rp2_common/pico_stdio_uart/include    -c /Users/reitobia/repos2/FreeRTOS-Kernel/verification/verifast/demos/FreeRTOS-SMP-Demos/FreeRTOS/Source/tasks.c   &>$LOG_PP_TASK_C

echo Preprocessed output with pragmas written to:
echo $LOG_PP_TASK_C

ls $LOG_PP_OUT_DIR
echo
sed 's|^#|// &|g' $LOG_PP_TASK_C  >  $LOG_PP_TASK_C_PRAGMA_COMMENTS
echo
ls $LOG_PP_OUT_DIR

echo Preprocessed output with pragma comments written to:
echo $LOG_PP_TASK_C_PRAGMA_COMMENTS

pwd
mkdir "$PP_OUT_DIR"
echo Copying preprocessed `tasks.c` file with pragma comments
echo "$LOG_PP_TASK_C_PRAGMA_COMMENTS"
echo to
echo "$PP_TASK_C"
cp "$LOG_PP_TASK_C_PRAGMA_COMMENTS" "$PP_TASK_C"
