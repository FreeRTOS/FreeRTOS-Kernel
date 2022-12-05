# This script must be run from the directory in which it resides,
# i.e., `FreeRTOS-Kernel/verification/verifast`.

# This script expects the following command line arguments:
# $1 : Absolute path to the VeriFast directory


VF_DIR="$1"
echo Path to vfide binary : "\'$VFIDE\'"

START_WD=`pwd`
PP_SCRIPT_DIR="$START_WD/custom_build_scripts_RP2040"
PP_SCRIPT="./preprocess_tasks_c.sh"
PP_TASK_C="$START_WD/preprocessed_files/tasks__pp.c"

FONT_SIZE=17
if [ "$2" != "" ]
then
  FONT_SIZE="$2"
fi

# Flags to SKIP expensive proofs:
# - VERIFAST_SKIP_BITVECTOR_PROOF__STACK_ALIGNMENT
# Currently, these flags are set manually in the preprocessing script.


cd "$PP_SCRIPT_DIR"
pwd
ls
"$PP_SCRIPT" "$VF_DIR"
cd "$START_WD"

echo "\n\nPreprocessing script finished\n\n"

# Remarks:
# - Recently, provenance checks have been added to VF that break old proofs
#   involving pointer comparisons. The flag `-assume_no_provenance` turns them
#   off.
# - Need z3v4.5 to handle bitvector arithmetic
"$VF_DIR/bin/vfide" "$PP_TASK_C" \
    -I proof_setup \
    -I proofs \
    -codeFont "$FONT_SIZE" -traceFont "$FONT_SIZE" \
    -assume_no_provenance \
    -disable_overflow_check
  #  -prover z3v4.5
#    -target 32bit -prover z3v4.5 \
# TODO: If we set the target to 32bit, VF create `uint` chunks instead of `char` chunks during malloc
