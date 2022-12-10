#!/bin/bash
SRC_FILE="$1"
OUT_FILE="$2"
ERR_FILE="$3"
REPO_BASE_DIR="$4"
VF_PROOF_BASE_DIR="$5"
VF_DIR="$6"


# Load functions used to compute paths.
. "$VF_PROOF_BASE_DIR/paths.sh"

# Load variables storing preprocessor flags.
. "`pp_script_dir $REPO_BASE_DIR`/pp_flags.sh" "$REPO_BASE_DIR" "$VF_PROOF_BASE_DIR" "$VF_DIR"



VF_PROOF_MOD_SRC_DIR=`vf_proof_mod_src_dir $REPO_BASE_DIR`
VF_PROOF_MOD_HEADER_DIR=`vf_proof_mod_header_dir $REPO_BASE_DIR`


PROOF_SETUP_DIR=`vf_proof_setup_dir $REPO_BASE_DIR`
PROOF_FILES_DIR=`vf_proof_dir $REPO_BASE_DIR`
PICO_SDK_DIR=`pico_sdk_dir $REPO_BASE_DIR`
SMP_DEMO_DIR=`smp_demo_dir $REPO_BASE_DIR`



# Flags to SKIP expensive proofs:
# - VERIFAST_SKIP_BITVECTOR_PROOF__STACK_ALIGNMENT




# Relevant clang flags:
# -E : Run preprocessor
# -C : Include comments in output
# -P : Surpresses line/file pragmas

echo start preprocessor
clang -E -C \
\
${BUILD_FLAGS[@]} \
${VERIFAST_FLAGS[@]} \
${RP2040_INLCUDE_FLAGS[@]} \
${PICO_INCLUDE_FLAGS[@]} \
-I"$REPO_BASE_DIR/include" \
\
-c "$SRC_FILE" \
1>"$OUT_FILE" 2>"$ERR_FILE"