#!/usr/bin/env bash

# Need to set this to max size of static array used in client.h
ARRAY_MAX=128
NUM_SAMPLES=1000

set -euo pipefail

# Check arguments
if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <input-file> [<testgen-dir>]"
  exit 1
fi

INPUT_FILE="$1"
OUTBASE="${INPUT_FILE%.c}"
OUTPUT_FILE="${OUTBASE}-gen.c"

./process-cn-test.sh "${INPUT_FILE}" "${OUTPUT_FILE}" > /dev/null 

# Create a temporary directory and ensure it's cleaned up on exit
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT
TESTGEN_DIR="${2:-$TMP_DIR}"

ROOT_DIR="$(pwd)"

eval "$(opam env)"

# CN flags, stored in an array for robustness
CN_FLAGS=(
  "--output=${TESTGEN_DIR}"
  "--include=${ROOT_DIR}/../include/wars.h"
  # "-I${ROOT_DIR}/../include" # Already preprocessed away 
  "-I${OPAM_SWITCH_PREFIX}/lib/cerberus/runtime/libc/include/posix"
  "--magic-comment-char-dollar"
  "-DCN_ENV" "-DCN_TEST"
  "--max-array-length=${ARRAY_MAX}"
  "--with-static-hack" # TODO remove when CN preprocessor limitations fixed 
  "--num-samples=${NUM_SAMPLES}"
)

# Sanity check - $OUTPUT_FILE should be verifiable if $INPUT_FILE is 
# echo "Sanity check - running the verifier:" 
# cn verify "${CN_FLAGS[@]}" "${OUTPUT_FILE}" 

TEST_GEN_CMD=(cn test "${CN_FLAGS[@]}" "${OUTPUT_FILE}")
echo "Running the test generator:"
echo "${TEST_GEN_CMD[@]}"
"${TEST_GEN_CMD[@]}"