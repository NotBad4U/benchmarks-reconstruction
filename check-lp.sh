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
    if [ -d "convert/small" ]; then
    pushd convert/small > /dev/null
      info "Checking small proofs..."

      fd -tf -e 'lp' -j $(nproc) \
        | parallel --timeout "${LAMBDAPI_CHECK_TIMEOUT:-60}" \
          --joblog "${JOBLOGS}/lambdapi_small_checks.txt" \
          --will-cite --bar -j${PARALLEL_JOBS:-8} \
          'hyperfine --warmup 3 --max-runs ${MAX_RUN_HYPERFINE_SMALL:-10} --time-unit millisecond --export-json "${RESULTS_DIR}/{.}.json" "lambdapi check -w -v0 {}"' 2> /dev/null
    popd > /dev/null
    else
      warn "No small proofs (<${PROOF_SPLIT_LIMIT}B) to check (directory convert/small does not exist)."
    fi

    # --- LARGE ---
    if [ -d "convert/large" ]; then
      pushd convert/large > /dev/null
        info "Checking large proofs..."

        fd -td . -j $(nproc) \
          -x sh -c 'fd -td . "$1" -d 1 -q || printf "%s\n" "$1"' sh {} \
          | sed 's:/*$::' \
          | parallel --timeout "${LAMBDAPI_CHECK_TIMEOUT:-120}" \
            --joblog "${JOBLOGS}/lambdapi_large_checks.txt" \
            --will-cite --bar -j${PARALLEL_JOBS:-8} \
            'hyperfine --warmup 0 --max-runs ${MAX_RUN_HYPERFINE_LARGE:-1} --time-unit millisecond --export-json "${RESULTS_DIR}/{}.json" "make -j8 -C {}"' 2> /dev/null
      popd > /dev/null
    else
      warn "No large proofs (>${PROOF_SPLIT_LIMIT}B) to check (directory convert/large does not exist)."
    fi
popd > /dev/null