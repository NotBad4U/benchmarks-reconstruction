#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/color-logger.bash"

JOB_DIR="$1"
if [ -z "${JOB_DIR}" ]; then
  echo "Usage: $0 <job_dir>" >&2
  exit 1
fi

RUNDIR="${JOB_DIR}/run"
JOBLOGS="${JOB_DIR}/logs"
RESULTS_DIR="${RUNDIR}/results"

export RESULTS_DIR JOBLOGS RESULTS_DIR

pushd "${RUNDIR}" > /dev/null
    info  "Checking proofs..."

    # --- SMALL ---
    pushd convert/small > /dev/null
      info "Checking small proofs..."

      fd -tf -e 'lp' -j 8 \
        | parallel --timeout "${LAMBDAPI_CHECK_TIMEOUT:-60}" \
          --joblog "${JOBLOGS}/lambdapi_small_checks.txt" \
          --will-cite --bar -j8 \
          'hyperfine --warmup 3 --max-runs 10 --time-unit millisecond --export-json "${RESULTS_DIR}/{.}.json" "lambdapi check -w -v0 {}"' 2> /dev/null
    popd > /dev/null

    # --- LARGE ---
    pushd convert/large > /dev/null
      info "Checking large proofs..."

      fd -td -d 1 \
        | sed 's:/*$::' \
        | parallel --timeout "${LAMBDAPI_CHECK_TIMEOUT:-120}" \
          --joblog "${JOBLOGS}/lambdapi_large_checks.txt" \
          --will-cite --bar -j8 \
          'hyperfine --warmup 0 --max-runs 1 --time-unit millisecond --export-json "${RESULTS_DIR}/{}.json" "make -j8 -C {}"' 2> /dev/null
    popd > /dev/null
popd > /dev/null