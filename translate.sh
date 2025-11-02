#!/bin/bash
. color-logger.bash

# Usage: translate.sh <job_dir> <benchmark_dir>
JOB_DIR="$1"
BENCH_DIR="$2"

if [ -z "$JOB_DIR" ] || [ -z "$BENCH_DIR" ]; then
  echo "Usage: $0 <job_dir> <benchmark_dir>" >&2
  exit 1
fi

# Directories inside job_dir
RUNDIR="${JOB_DIR}/run"
PROOFS_DIR="${JOB_DIR}/proofs"
JOBLOGS="${JOB_DIR}/logs"

# export vars so GNU parallel jobs can use them
export BENCH_DIR RUNDIR PROOFS_DIR JOBLOGS

info "Translating proofs..."

# Ensure convert/small and convert/large exist
mkdir -p "${RUNDIR}/convert/small" "${RUNDIR}/convert/large"

# translate to lambdapi all .elab files (alethe -> convert)
# run from the alethe dir so "../convert/..." points to RUNDIR/convert/...
pushd "${RUNDIR}/alethe" > /dev/null

for dir in "convert/small" "convert/large" "results"; do
  fd . -t d -X mkdir -p ${RUNDIR}/${dir}/{} \;
done

info "Translating small .elab files (< ${PROOF_SPLIT_LIMIT:-1M})..."

# small files (< PROOF_SPLIT_LIMIT MB)
fd -tf -e 'elab' -j $(nproc) --size -${PROOF_SPLIT_LIMIT:-1M} | \
  parallel --joblog "${JOBLOGS}/translate_small_logs.txt" --timeout "${CARCARA_TRANSLATE_TIMEOUT:-60}" --will-cite --bar -j${PARALLEL_JOBS:-8} \
    'carcara translate --no-elab -i {} "$BENCH_DIR/{.}.smt2" 1> "../convert/small/{.}.lp" 2> /dev/null'  \;

info "Translating large .elab files (> ${PROOF_SPLIT_LIMIT:-1M})..."

## large files (> PROOF_SPLIT_LIMIT MB)
fd -tf -e 'elab' -j $(nproc) --size +${PROOF_SPLIT_LIMIT:-1M} | \
  parallel --joblog "${JOBLOGS}/translate_large_logs.txt" --timeout "${CARCARA_TRANSLATE_TIMEOUT:-60}" --will-cite --bar -j${PARALLEL_JOBS:-8} \
    'carcara translate --no-elab -i {} "$BENCH_DIR/{.}.smt2" -n "$SEGMENT_SIZE" -o "../convert/large/{.}" 2>/dev/null'

popd > /dev/null
