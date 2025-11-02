#!/bin/bash

# This script now receives:
#  $1 -> benchs directory
#  $2 -> output directory (OUTPUT_DIR)
BENCH_DIR="$1"
OUTPUT_DIR="$2"

if [ -z "$BENCH_DIR" ] || [ -z "$OUTPUT_DIR" ]; then
  echo "Usage: $0 <benchs_dir> <output_dir>" >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# color logger (use script dir to find it)
source "${SCRIPT_DIR}/color-logger.bash"

JOBLOGS="${OUTPUT_DIR}/logs"

info "Generate proofs from '${BENCH_DIR}' into '${OUTPUT_DIR}/proofs' (logs -> ${JOBLOGS}/cvc5.txt)"


export OUTPUT_DIR JOBLOGS

# Go to benchmark directory to avoid path issues
pushd "${BENCH_DIR}" > /dev/null

# Create output directories
fd . -t d -X mkdir -p $OUTPUT_DIR/proofs/{} \;

fd -tf -e 'smt2' -j ${PARALLEL_JOBS:-8} | \
  parallel --joblog "${JOBLOGS}/cvc5.txt" --timeout "${CVC5_TIMEOUT:-30}" --will-cite --bar -j${PARALLEL_JOBS:-8} \
  'cvc5 --dag-thresh=0 --produce-proofs --dump-proofs  --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token ./{} > '"$OUTPUT_DIR"'/proofs/{.}.proof' \;

popd > /dev/null