#!/bin/bash
SRC_FILE="$1"
OUT_FILE="$2"
ERR_FILE="$3"
REPO_BASE_DIR="$4"
VF_PROOF_BASE_DIR="$5"
VF_DIR="$6"


echo SRC_FILE:
echo $SRC_FILE
echo OUT_FILE:
echo $OUT_FILE
echo ERR_FILE:
echo $ERR_FILE
echo REPO_BASE_DIR:
echo $REPO_BASE_DIR
echo VF_PROOF_BASE_DIR:
echo $VF_PROOF_BASE_DIR
echo VF_DIR:
echo $VF_DIR

# Load functions used to compute paths.
. "$VF_PROOF_BASE_DIR/paths.sh"

# Load variables storing preprocessor flags.
. "`pp_script_dir $REPO_BASE_DIR`/pp_flags.sh" "$REPO_BASE_DIR" "$VF_PROOF_BASE_DIR" "$VF_DIR"


# Flags to SKIP expensive proofs:
# - VERIFAST_SKIP_BITVECTOR_PROOF__STACK_ALIGNMENT




# Relevant clang flags:
# -E : Run preprocessor
# -C : Include comments in output
# -P : Surpresses line/file pragmas

echo start preprocessor
clang -E -P \
\
${BUILD_FLAGS[@]} \
${RP2040_INLCUDE_FLAGS[@]} \
${PICO_INCLUDE_FLAGS[@]} \
-I`prod_header_dir $REPO_BASE_DIR` \
\
-c "$SRC_FILE" \
1>"$OUT_FILE" 2>"$ERR_FILE"