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

for dir in "alethe" "convert" "results"; do
  fd . -t d -X mkdir -p ${RUNDIR}/${dir}/{} \;
done

popd > /dev/null

info  "Elaborating proofs..."

# export vars so GNU parallel jobs can use them
export BENCH_DIR RUNDIR PROOFS_DIR JOBLOGS TEST_NAME

# translate to lambdapi all .elab files (alethe -> convert)
pushd "${RUNDIR}/alethe" > /dev/null

  fd -tf -e 'elab' -j 8 ${TEST_NAME} | \
    parallel --joblog "${JOBLOGS}/translate_logs.txt" --timeout 10s --will-cite --bar -j8 \
    'carcara translate --no-elab -i {} "$BENCH_DIR/{.}.smt2" 1> "../convert/{.}.lp" 2> /dev/null'  \;

popd > /dev/null
