#!/bin/bash

# Run all benchmarks found under benchs/ (subdirectories at depth 2).
# For each benchs/<category>/<bench> this script:
#  - runs `python3 jobs.py --benchmark-dir benchs/<category>/<bench>`
#  - locates the job output directory created in output/
#  - removes heavy intermediate data (proofs, run/alethe, run/convert)
#  - archives the remaining job directory (logs + run/results) into a timestamped batch folder
#
#  Running each benchmark as a separate job directory reduces contention and
#  resource exhaustion (e.g. file descriptor limits) when processing large numbers
#  of benchmarks. This per-benchmark isolation makes failures easier to contain.

source color-logger.bash

# Create a timestamped directory for this batch run
BATCH_DIR="/home/acoltell/public/benchmarks-$(date +%Y%m%d-%H%M%S)"
mkdir -p "${BATCH_DIR}"

info "Starting benchmark batch, results will be in: ${BATCH_DIR}"

# Use fd to find subdirectories at depth 2 in benchs/
while IFS= read -r -d '' subdir; do
    info "Processing benchmark directory: ${subdir}"
    
    # # Run the benchmark - pass full path including benchs/
    python3 jobs.py --benchmark-dir "benchs/${subdir}" < /dev/null

    # Get the last created job directory
    jobdir=$(/bin/ls -td -- output/*/ 2>/dev/null | head -n1)
    if [ -z "${jobdir}" ]; then
        error "No job directory found for ${subdir}"
        continue
    fi
    jobid=$(basename "${jobdir}")

    info "Cleaning up job directory ${jobid}..."

    # Remove unneeded directories, keeping only results and logs
    rm -rf "${jobdir}/proofs" "${jobdir}/run/alethe" #"${jobdir}/run/convert"

    # # Create tar archive with parent/subdir structure in name
    tarfile="${BATCH_DIR}/${jobid}.tar.gz"
    tar -czf "${tarfile}" -C "$(dirname "${jobdir}")" "$(basename "${jobdir}")"

    info "Archived results to: ${tarfile}"

    # Remove the original job directory to save space
    rm -rf "${jobdir}"
done < <(fd --type d --min-depth 2 --max-depth 2 --base-directory benchs --print0)

info "Batch processing complete. Results are in: ${BATCH_DIR}"