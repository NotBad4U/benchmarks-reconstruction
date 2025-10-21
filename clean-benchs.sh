#!/bin/bash

. color-logger.bash

BENCH_DIR="$1"

if [ -z "$BENCH_DIR" ]; then
    echo "Usage: $0 <bench_dir>"
    exit 1
fi

if [ ! -d "$BENCH_DIR" ]; then
    echo "Directory '$BENCH_DIR' does not exist"
    exit 1
fi

pushd "$BENCH_DIR" > /dev/null

# Remove starexec file
find . -type f -name "*.txt" -print0 | xargs -0 -r rm -f

# Remove file with status sat and unknown
info "remove files with status sat"
rg -l "status sat" | xargs -r -I {} rm -f {}

info "remove files with status unknown"
rg -l "status unknown" | xargs -r -I {} rm -f {}

# Clean empty file
find . -type f -empty -delete

# Clean empty directory
info "remove empty directory in benchs"
find . -type d -empty -delete

popd > /dev/null