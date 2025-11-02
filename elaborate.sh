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

pushd "${PROOFS_DIR}" > /dev/null

info  "Setup ${PROOFS_DIR} directory..."

for dir in "alethe"; do
  fd . -t d -X mkdir -p ${RUNDIR}/${dir}/{} \;
done

popd > /dev/null

info  "Elaborating proofs..."

# export vars so GNU parallel jobs can use them
export BENCH_DIR RUNDIR PROOFS_DIR JOBLOGS TEST_NAME

# ELAB: process .proof files under job-specific proofs directory
pushd "${PROOFS_DIR}" > /dev/null
  fd . -tf -e 'proof' -j $(nproc) | \
    parallel --joblog "${JOBLOGS}/elab_logs.txt" --timeout "${CARCARA_CHECK_ELAB_TIMEOUT:-60}" --will-cite --bar -j${PARALLEL_JOBS:-8} \
      'carcara elaborate --no-print-with-sharing --expand-let-bindings -i --log off {} "$BENCH_DIR/{.}.smt2" 1> "$RUNDIR/alethe/{.}.elab"'  \;
popd > /dev/null
