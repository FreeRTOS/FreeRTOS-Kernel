# This script must be run from the directory in which it resides,
# i.e., `FreeRTOS-Kernel/verification/verifast`.




VFIDE="$1"
echo Path to vfide binary : "\'$VFIDE\'"

START_WD=`pwd`
PP_SCRIPT_DIR="$START_WD/custom_build_scripts_RP2040"
PP_SCRIPT="./preprocess_tasks_c.sh"
PP_TASK_C="$START_WD/preprocessed_files/tasks--pp.c"

cd "$PP_SCRIPT_DIR"
pwd
ls
"$PP_SCRIPT"
cd "$START_WD"

echo "\n\nPreprocessing script finished\n\n"

$VFIDE $PP_TASK_C
