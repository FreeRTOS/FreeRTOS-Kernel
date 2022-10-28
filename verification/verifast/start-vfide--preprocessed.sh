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

FONT_SIZE=16

cd "$PP_SCRIPT_DIR"
pwd
ls
"$PP_SCRIPT" "$VF_DIR"
cd "$START_WD"

echo "\n\nPreprocessing script finished\n\n"

# Remarks:
# - Need z3v4.5 to handle bitvector arithmetic
"$VF_DIR/bin/vfide" "$PP_TASK_C" \
    -codeFont "$FONT_SIZE" -traceFont "$FONT_SIZE" \
    -prover z3v4.5
#    -target 32bit -prover z3v4.5 \
# TODO: If we set the target to 32bit, VF create `uint` chunks instead of `char` chunks during malloc
