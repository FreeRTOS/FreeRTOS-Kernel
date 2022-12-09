#!/bin/zsh
ps -o comm= -p $$

# This script expects the following command line arguments:
# $1 : Absolute path to the root dir of this repository
# $2 : Absolute path to the root of the directory containing the VeriFast proofs
# $3 : Absolute path to the VeriFast directory

REPO_BASE_DIR="$1"
VF_PROOF_BASE_DIR="$2"
VF_DIR="$3"

PP_SCRIPT_WD=`pwd`
VF_PROOF_MOD_SRC_DIR="$VF_PROOF_BASE_DIR/src"
VF_PROOF_MOD_HEADER_DIR="$VF_PROOF_BASE_DIR/include"

TASKS_C="$VF_PROOF_MOD_SRC_DIR/tasks.c"

PROOF_SETUP_DIR="$VF_PROOF_BASE_DIR/proof_setup"
PROOF_FILES_DIR="$VF_PROOF_BASE_DIR/proof"
PICO_SDK_DIR="$VF_PROOF_BASE_DIR/sdks/pico-sdk"
SMP_DEMO_DIR="$VF_PROOF_BASE_DIR/demos/FreeRTOS-SMP-Demos"


#LOG_DIR="`pwd`/build_logs"
#BUILD_LOG="$LOG_DIR/build_log--`date +'%y_%m_%d--%H_%M'`.txt"
TIMESTAMP=`date +'%y_%m_%d--%H_%M'`
LOG_PP_OUT_DIR="$PP_SCRIPT_WD/log_preprocessed_files"
LOG_PP_TASK_C="$LOG_PP_OUT_DIR/tasks--pp--$TIMESTAMP.c"
LOG_PP_ERR="$LOG_PP_OUT_DIR/error--$TIMESTAMP.c"

LOG_VF_RW_TASK_C="$LOG_PP_OUT_DIR/tasks--vf_rw--$TIMESTAMP.c"

PP_OUT_DIR="$VF_PROOF_BASE_DIR/preprocessed_files"
PP_TASK_C="$PP_OUT_DIR/tasks__pp.c"


# Flags to SKIP expensive proofs:
# - VERIFAST_SKIP_BITVECTOR_PROOF__STACK_ALIGNMENT


pwd
mkdir $LOG_PP_OUT_DIR

# Relevant clang flags:
# -E
# -C
# -P : surpresses line/file pragmas

echo start preprocessor
./preprocess_file.sh $TASKS_C $LOG_PP_TASK_C $LOG_PP_ERR  $REPO_BASE_DIR $VF_PROOF_BASE_DIR $VF_DIR 

echo "\n\nPreprocessed output with pragmas written to:"
echo $LOG_PP_TASK_C


echo "\n\nApplying VeriFast rewrites. Result written to:"
echo $LOG_VF_RW_TASK_C
cp "$LOG_PP_TASK_C" "$LOG_VF_RW_TASK_C"
./vf_rewrite.sh "$LOG_VF_RW_TASK_C"


pwd
mkdir "$PP_OUT_DIR"
echo "\n\nCopying preprocessed tasks.c file with pragma comments and VF rewrites"
echo "$LOG_VF_RW_TASK_C"
echo to
echo "$PP_TASK_C"
cp "$LOG_VF_RW_TASK_C" "$PP_TASK_C"
