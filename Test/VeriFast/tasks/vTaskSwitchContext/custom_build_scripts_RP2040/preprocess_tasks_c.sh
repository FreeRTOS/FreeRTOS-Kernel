#!/bin/zsh
ps -o comm= -p $$

# This script expects the following command line arguments:
# $1 : Absolute path to the root dir of this repository
# $2 : Absolute path to the root of the directory containing the VeriFast proofs
# $3 : Absolute path to the VeriFast directory

REPO_BASE_DIR="$1"
VF_PROOF_BASE_DIR="$2"
VF_DIR="$3"

# Load functions used to compute paths.
. "$VF_PROOF_BASE_DIR/paths.sh"


VF_PROOF_MOD_SRC_DIR=`vf_proof_mod_src_dir $REPO_BASE_DIR`
VF_PROOF_MOD_HEADER_DIR=`vf_proof_mod_header_dir $REPO_BASE_DIR`

TASKS_C=`vf_annotated_tasks_c $REPO_BASE_DIR`

PROOF_SETUP_DIR=`vf_proof_setup_dir $REPO_BASE_DIR`
PROOF_FILES_DIR=`vf_proof_dir $REPO_BASE_DIR`
PICO_SDK_DIR=`pico_sdk_dir $REPO_BASE_DIR`
SMP_DEMO_DIR=`smp_demo_dir $REPO_BASE_DIR`


PP_SCRIP_DIR=`pp_script_dir $REPO_BASE_DIR`
#BUILD_LOG="$LOG_DIR/build_log--`date +'%y_%m_%d--%H_%M'`.txt"
TIMESTAMP=`date +'%y_%m_%d--%H_%M'`
PP_LOG_DIR=`pp_log_dir $REPO_BASE_DIR`
LOG_PP_TASK_C="$PP_LOG_DIR/tasks--pp--$TIMESTAMP.c"
LOG_PP_ERR="$PP_LOG_DIR/error--$TIMESTAMP.c"

LOG_VF_RW_TASK_C="$PP_LOG_DIR/tasks--vf_rw--$TIMESTAMP.c"

PP_OUT_DIR="$VF_PROOF_BASE_DIR/preprocessed_files"
PP_TASK_C=`pp_vf_tasks_c $REPO_BASE_DIR`


# Flags to SKIP expensive proofs:
# - VERIFAST_SKIP_BITVECTOR_PROOF__STACK_ALIGNMENT


mkdir $PP_LOG_DIR

# Relevant clang flags:
# -E
# -C
# -P : surpresses line/file pragmas

echo start preprocessor
"$PP_SCRIP_DIR/preprocess_file.sh" $TASKS_C $LOG_PP_TASK_C $LOG_PP_ERR  $REPO_BASE_DIR $VF_PROOF_BASE_DIR $VF_DIR 

echo "\n\nPreprocessed output with pragmas written to:"
echo $LOG_PP_TASK_C


echo "\n\nApplying VeriFast rewrites. Result written to:"
echo $LOG_VF_RW_TASK_C
cp "$LOG_PP_TASK_C" "$LOG_VF_RW_TASK_C"
"$PP_SCRIP_DIR/vf_rewrite.sh" "$LOG_VF_RW_TASK_C"


mkdir `pp_out_dir $REPO_BASE_DIR`
echo "\n\nCopying preprocessed tasks.c file with pragma comments and VF rewrites"
echo "$LOG_VF_RW_TASK_C"
echo to
echo "$PP_TASK_C"
cp "$LOG_VF_RW_TASK_C" "$PP_TASK_C"
