#!/bin/zsh
ps -o comm= -p $$

# This script expects the following command line arguments:
# $1 : Absolute path to the root dir of this repository
# $2 : Absolute path to the root of the directory containing the VeriFast proofs
# $3 : Absolute path to the VeriFast directory

SRC_FILE="$1"
OUT_FILE="$2"
FILE_PP_ERR_LOG="$3"
REPO_BASE_DIR="$4"
VF_PROOF_BASE_DIR="$5"
VF_DIR="$6"

echo SRC_FILE
echo "$1"
echo OUT_FILE
echo "$2"
echo FILE_PP_ERR_LOG
echo "$3"
echo REPO_BASE_DIR
echo "$4"
echo VF_PROOF_BASE_DIR 
echo "$5"
echo VF_DIR 
echo "$6"

# Load functions used to compute paths.
. "$VF_PROOF_BASE_DIR/paths.sh"


VF_PROOF_MOD_SRC_DIR=`vf_proof_mod_src_dir $REPO_BASE_DIR`
VF_PROOF_MOD_HEADER_DIR=`vf_proof_mod_header_dir $REPO_BASE_DIR`
PROOF_SETUP_DIR=`vf_proof_setup_dir $REPO_BASE_DIR`
PROOF_FILES_DIR=`vf_proof_dir $REPO_BASE_DIR`
PICO_SDK_DIR=`pico_sdk_dir $REPO_BASE_DIR`
SMP_DEMO_DIR=`smp_demo_dir $REPO_BASE_DIR`

TASKS_C=`vf_annotated_tasks_c $REPO_BASE_DIR`


PP_SCRIPT_DIR=`pp_script_dir $REPO_BASE_DIR`
#BUILD_LOG="$LOG_DIR/build_log--`date +'%y_%m_%d--%H_%M'`.txt"
TIMESTAMP=`date +'%y_%m_%d--%H_%M'`
PP_LOG_DIR=`pp_log_dir $REPO_BASE_DIR`
RW_LOG_DIR=`rw_log_dir $REPO_BASE_DIR`
LOG_PP_TASK_C="$PP_LOG_DIR/tasks--pp--$TIMESTAMP.c"
LOG_PP_ERR="$PP_LOG_DIR/error--$TIMESTAMP.c"

LOG_VF_RW_TASK_C="$PP_LOG_DIR/tasks--vf_rw--$TIMESTAMP.c"

PP_OUT_DIR="$VF_PROOF_BASE_DIR/preprocessed_files"
PP_TASK_C=`pp_vf_tasks_c $REPO_BASE_DIR`


FILE_PP_LOG="$PP_LOG_DIR/pp.c"
FILE_RW_LOG="$PP_LOG_DIR/rw.c"


mkdir $PP_LOG_DIR

# Preprocessing the source file
# Output is written to '$FILE_PP_LOG' and error report is written to 
# '$FILE_PP_ERR_LOG'.
"$PP_SCRIPT_DIR/preprocess_file_for_verification.sh" $SRC_FILE \
    $FILE_PP_LOG $FILE_PP_ERR_LOG \
    $REPO_BASE_DIR $VF_PROOF_BASE_DIR $VF_DIR 

cp "$FILE_PP_LOG" "$FILE_RW_LOG"
"$PP_SCRIPT_DIR/vf_rewrite.sh" "$FILE_RW_LOG"
cp "$FILE_RW_LOG" "$OUT_FILE"