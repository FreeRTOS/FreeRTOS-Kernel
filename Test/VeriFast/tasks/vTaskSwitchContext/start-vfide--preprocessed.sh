#!/bin/bash

# Relative or absolute path to the directory this script and `paths.sh` reside in.
PREFIX=`dirname $0`
# Absolute path to the base of this repository.
REPO_BASE_DIR="$1"
# Absolute path the VeriFast installation directory
VF_DIR="$2"

# Load functions used to compute paths.
. "$PREFIX/paths.sh"


VF_PROOF_BASE_DIR=`vf_proof_base_dir $REPO_BASE_DIR`


PP_SCRIPT_DIR=`pp_script_dir $REPO_BASE_DIR`
#PP_SCRIPT="`pp_script_dir $REPO_BASE_DIR`/prepare_file_for_VeriFast.sh"
PREP="$PP_SCRIPT_DIR/prepare_file_for_VeriFast.sh"
TASK_C=`vf_annotated_tasks_c $REPO_BASE_DIR`
PP_TASK_C=`pp_vf_tasks_c $REPO_BASE_DIR`

PROOF_SETUP_DIR=`vf_proof_setup_dir $REPO_BASE_DIR`
PROOF_FILES_DIR=`vf_proof_dir $REPO_BASE_DIR`

PP_ERR_LOG="`pp_log_dir $REPO_BASE_DIR`/preprocessing_errors.txt"

FONT_SIZE=17
if [ "$3" != "" ]
then
  FONT_SIZE="$3"
fi


"$PREP" "$TASK_C" "$PP_TASK_C" "$PP_ERR_LOG" \
  "$REPO_BASE_DIR" "$VF_PROOF_BASE_DIR" "$VF_DIR"

echo Load file into VF
echo "$PP_TASK_C"

# Remarks:
# - Recently, provenance checks have been added to VF that break old proofs
#   involving pointer comparisons. The flag `-assume_no_provenance` turns them
#   off.

"$VF_DIR/bin/vfide" "$PP_TASK_C" \
    -I $PROOF_SETUP_DIR \
    -I $PROOF_FILES_DIR \
    -assume_no_provenance \
    -disable_overflow_check \
    "$PP_TASK_C" \
    -codeFont "$FONT_SIZE" -traceFont "$FONT_SIZE" \
