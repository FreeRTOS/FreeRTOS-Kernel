# This script must be run from the directory in which it resides,
# i.e., `FreeRTOS-Kernel/verification/verifast`.

# This script expects the following command line arguments:
# $1 : Absolute path to the VeriFast directory


# Relative or absolute path to the directory this script and `paths.sh` reside in.
PREFIX=`dirname $0`
# Absolute path to the base of this repository.
REPO_BASE_DIR="$1"

# Load functions used to compute paths.
. "$PREFIX/paths.sh"


VF_PROOF_BASE_DIR="$2"
VF_DIR="$3"
echo Path to vfide binary : "\'$VFIDE\'"

PP_SCRIPT_DIR=`pp_script_dir $REPO_BASE_DIR`
PP_SCRIPT="`pp_script_dir $REPO_BASE_DIR`/preprocess_tasks_c.sh"
PP_TASK_C=`pp_vf_tasks_c $REPO_BASE_DIR`

PROOF_SETUP_DIR=`vf_proof_setup_dir $REPO_BASE_DIR`
PROOF_FILES_DIR=`vf_proof_dir $REPO_BASE_DIR`

FONT_SIZE=17
if [ "$4" != "" ]
then
  FONT_SIZE="$4"
fi

# Flags to SKIP expensive proofs:
# - VERIFAST_SKIP_BITVECTOR_PROOF__STACK_ALIGNMENT
# Currently, these flags are set manually in the preprocessing script.


"$PP_SCRIPT" "$REPO_BASE_DIR" "$VF_PROOF_BASE_DIR" "$VF_DIR"

echo "\n\nPreprocessing script finished\n\n"

echo "File"
echo $PP_TASK_C

# Remarks:
# - Recently, provenance checks have been added to VF that break old proofs
#   involving pointer comparisons. The flag `-assume_no_provenance` turns them
#   off.
# - Need z3v4.5 to handle bitvector arithmetic
"$VF_DIR/bin/vfide" "$PP_TASK_C" \
    -I $PROOF_SETUP_DIR \
    -I $PROOF_FILES_DIR \
    -assume_no_provenance \
    -disable_overflow_check \
    "$PP_TASK_C" \
    -codeFont "$FONT_SIZE" -traceFont "$FONT_SIZE" \
  #  -prover z3v4.5
#    -target 32bit -prover z3v4.5 \
# TODO: If we set the target to 32bit, VF create `uint` chunks instead of `char` chunks during malloc
