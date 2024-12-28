#!/usr/bin/env bash

# Run the C preprocessor on the second half of a file only: 
# 1. Split the file at the first occurrence of //SYSTEM_HEADERS
# 2. Run the C preprocessor on the second chunk
# 3. Concatenate the first chunk and preprocessed second chunk
# 
# Usage:
#   ./process.sh <input-file> [<output-file>]

set -euo pipefail

# Check arguments
if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <input-file> [<output-file>]"
  exit 1
fi

INPUT_FILE="$1"
OUTBASE="${INPUT_FILE%.c}"
DEFAULT_OUTPUT="${OUTBASE}-out.c"

# If user provided the second argument, use it; otherwise use our default
OUTPUT_FILE="${2:-$DEFAULT_OUTPUT}"

# Create a temporary directory and ensure it's cleaned up on exit
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

# 1. Split the file at the first occurrence of string "//SYSTEM_HEADERS"
csplit -s -f "${TMP_DIR}/split_" -n 1 "$INPUT_FILE" "/\/\/SYSTEM_HEADERS/"

# 2. Run the C preprocessor on the second chunk
ROOT_DIR="$(pwd)"

# Need to figure out where the cerberus posix headers are
eval "$(opam env)"

# gcc flags, stored in an array for robustness
GCC_FLAGS=(
  # "-H" # Print the include tree - useful for debugging 
  "-E" "-P" "-CC" "-x" "c"
  "-I${ROOT_DIR}/../include"
  "-I."
  "-I${OPAM_SWITCH_PREFIX}/lib/cerberus/runtime/libc/include/posix"
  "-DCN_ENV" "-DWAR_CN_309"
  "-DCN_TEST" # A few things need to be modified for cn-test
)

# Print the exact command for debug purposes  
# echo "Running gcc command:"
# echo gcc "${GCC_FLAGS[@]}" "${TMP_DIR}/split_1" -o "${TMP_DIR}/split_1_out.c"
# echo ""

# echo "Include tree:" 
gcc "${GCC_FLAGS[@]}" "${TMP_DIR}/split_1" -o "${TMP_DIR}/split_1_out.c"

# 3. Concatenate the first chunk and preprocessed second chunk
cat "${TMP_DIR}/split_0" "${TMP_DIR}/split_1_out.c" > "$OUTPUT_FILE"

echo "\nDone. Merged output is in: $OUTPUT_FILE"
