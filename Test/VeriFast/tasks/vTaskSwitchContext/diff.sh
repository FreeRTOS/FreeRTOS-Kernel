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
PP="$PP_SCRIPT_DIR/preprocess_file_for_diff.sh"
LOG_DIR=`pp_log_dir $REPO_BASE_DIR`
STATS_DIR=`stats_dir $REPO_BASE_DIR`

# Unpreprocessed verions of tasks.c
PROD_TASKS_C=`prod_tasks_c $REPO_BASE_DIR`
VF_TASKS_C=`vf_annotated_tasks_c $REPO_BASE_DIR`

# Preprocessed versions of tasks.c
PP_OUT_DIR=`pp_out_dir $REPO_BASE_DIR`
PP_PROD_TASKS_C=`pp_prod_tasks_c $REPO_BASE_DIR`
PP_VF_TASKS_C=`pp_vf_tasks_c $REPO_BASE_DIR`

DIFF_REPORT=`diff_report $REPO_BASE_DIR`

# Ensure that all output directories exist
if [ ! -d "$LOG_DIR" ]; then
    mkdir "$LOG_DIR"
fi
if [ ! -d "$STATS_DIR" ]; then
    mkdir "$STATS_DIR"
fi
if [ ! -d "$PP_OUT_DIR" ]; then
    mkdir "$PP_OUT_DIR"
fi

echo preprocessing production version of 'tasks.c'
$PP $PROD_TASKS_C $PP_PROD_TASKS_C \
    "$LOG_DIR/pp_prod_tasks_c_error_report.txt" \
    $REPO_BASE_DIR $VF_PROOF_BASE_DIR

echo preprocessing verified version of 'tasks.c'
$PP $VF_TASKS_C $PP_VF_TASKS_C \
    "$LOG_DIR/pp_vf_tasks_c_error_report.txt" \
    $REPO_BASE_DIR $VF_PROOF_BASE_DIR

# pp script args
# SRC_FILE="$1"
# OUT_FILE="$2"
# ERR_FILE="$3"
# REPO_BASE_DIR="$4"
# VF_PROOF_BASE_DIR="$5"



echo Computing diff. Output written to:
echo \"$DIFF_REPORT\"

git diff --no-index --ignore-all-space $PP_PROD_TASKS_C $PP_VF_TASKS_C \
> "$DIFF_REPORT"