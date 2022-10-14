# This script must be run from the directory in which it resides,
# i.e., `FreeRTOS-Kernel/verification/verifast`.




VFIDE="$1"
echo Path to vfide binary : "\'$VFIDE\'"

PP_SCRIPT="custom_build_scripts_RP2040/preprocess_tasks_c.sh"
PP_TASK_C="preprocessed_files/tasks--pp.c"


$VFIDE $PP_TASK_C
