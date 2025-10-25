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

pushd "${RUNDIR}" > /dev/null
    info  "Checking proofs..."

    pushd convert > /dev/null
      fd -tf -e 'lp' -j 8 | parallel --joblog "${JOBLOGS}/lambdapi-checks.txt" --timeout "${LAMBDAPI_CHECK_TIMEOUT:-60}" --will-cite --bar -j8  'hyperfine --warmup 3 --max-runs 10 --time-unit millisecond --export-json ../results/{.}.json  "lambdapi check {}"' 2> /dev/null  \;
    popd > /dev/null

    pushd results > /dev/null
      info "Remove empty file in results/"
      find . -type f -empty -delete
    popd > /dev/null
popd > /dev/null