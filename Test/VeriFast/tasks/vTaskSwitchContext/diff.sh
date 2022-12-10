#!/bin/bash



# Relative or absolute path to the directory this script and `paths.sh` reside in.
PREFIX=`dirname $0`
# Absolute path to the base of this repository.
REPO_BASE_DIR="$1"

# Load functions used to compute paths.
. "$PREFIX/paths.sh"

VF_PROOF_BASE_DIR=`vf_proof_base_dir $REPO_BASE_DIR`



# Load functions used to compute paths.
. "$PREFIX/paths.sh"

VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

PP_SCRIPT_DIR=`pp_script_dir $REPO_BASE_DIR`

echo preprocessing production version of 'tasks.c'
"$PP_SCRIPT_DIR/preprocess_file_for_diff.sh" \
    `prod_tasks_c $REPO_BASE_DIR` \
    `pp_prod_tasks_c $REPO_BASE_DIR` \
    "`pp_log_dir $REPO_BASE_DIR`/err1.txt" \
    $REPO_BASE_DIR \
    $VF_PROOF_BASE_DIR

echo preprocessing verified version of 'tasks.c'
"$PP_SCRIPT_DIR/preprocess_file_for_diff.sh" \
    `vf_annotated_tasks_c $REPO_BASE_DIR` \
    `pp_vf_tasks_c $REPO_BASE_DIR` \
    "`pp_log_dir $REPO_BASE_DIR`/err2.txt" \
    $REPO_BASE_DIR \
    $VF_PROOF_BASE_DIR

# pp script args
# SRC_FILE="$1"
# OUT_FILE="$2"
# ERR_FILE="$3"
# REPO_BASE_DIR="$4"
# VF_PROOF_BASE_DIR="$5"



printf "\n\n\n"
echo Diff:
echo -----------------------------------------------------
echo
git diff --no-index "`pp_log_dir $REPO_BASE_DIR`/err1.txt" `pp_vf_tasks_c $REPO_BASE_DIR`