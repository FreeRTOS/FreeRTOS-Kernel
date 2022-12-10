# Returns the absolute path to the directory containing the VeriFast proofs
# concerning `vTaskSwitchContext` in `tasks.c`.
#
# Expected arguments:
# $1 : Absolute path to the repository's base directory.
function vf_proof_base_dir() {
    REPO_BASE_DIR="$1"
    echo "$REPO_BASE_DIR/Test/VeriFast/tasks/vTaskSwitchContext"
}

# Returns the absolute path to the directory containing modified versions of
# FreeRTOS source files. The VeriFast proofs use these modified verions instead
# of the original files.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function vf_proof_mod_src_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/src"
}

# Returns the absolute path to the directory containing modified versions of
# FreeRTOS header files. The VeriFast proofs use these modified verions instead
# of the original files.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function vf_proof_mod_header_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/include"
}

# Returns the absolute path to the directory containing everything related to
# the setup of the VeriFast proofs.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function vf_proof_setup_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/proof_setup"
}

# Returns the absolute path to the directory containing all lemmas and 
# definitions used written for the VeriFast proofs.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function vf_proof_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/proof"
}

# Returns the absolute path to the version of `tasks.c` containing the VeriFast
# proof annotations.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function vf_annotated_tasks_c() {
    REPO_BASE_DIR="$1"
    VF_MOD_SRC_DIR=`vf_proof_mod_src_dir $REPO_BASE_DIR`

    echo "$VF_MOD_SRC_DIR/tasks.c"
}


# Returns the absolute path to the directory containing the preprocessing scripts.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function pp_script_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/custom_build_scripts_RP2040"
}

# Returns the absolute path to the preprocesor's output direcotry.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function pp_out_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/preprocessed_files"
}

# Returns the absolute path to the preprocesor's log direcotry.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function pp_log_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/pp_log"
}

# Returns the absolute path to the preprocessed version of `tasks.c` containing 
# the VeriFast proof annotations. This is the file that is processed by 
# VeriFast.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function pp_vf_tasks_c() {
    REPO_BASE_DIR="$1"
    PP_OUT_DIR=`pp_out_dir $REPO_BASE_DIR`

    echo "$PP_OUT_DIR/tasks_vf_pp.c"
}

# Returns the absolute path to the pico sdk.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function pico_sdk_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/sdks/pico-sdk"
}

# Returns the absolute path to the smp_demo_dir.
#
# Expected arguments:
# $1 : Absolute path to the repository's base 
function smp_demo_dir() {
    REPO_BASE_DIR="$1"
    VF_PROOF_DIR=`vf_proof_base_dir $REPO_BASE_DIR`

    echo "$VF_PROOF_DIR/demos/FreeRTOS-SMP-Demos"
}


