# This script must be run from the directory in which it resides,
# i.e., `FreeRTOS-Kernel/verification/verifast`.

# This script expects the following command line arguments:
# $1 : Absolute path to the VeriFast directory


VF_DIR="$1"
echo Path to vfide binary : "\'$VFIDE\'"

START_WD=`pwd`
PP_SCRIPT_DIR="$START_WD/custom_build_scripts_RP2040"
PP_SCRIPT="./preprocess_tasks_c.sh"
PP_TASK_C="$START_WD/preprocessed_files/tasks--pp.c"

cd "$PP_SCRIPT_DIR"
pwd
ls
"$PP_SCRIPT" "$VF_DIR"
cd "$START_WD"

echo "\n\nPreprocessing script finished\n\n"

"$VF_DIR/bin/vfide" "$PP_TASK_C"
