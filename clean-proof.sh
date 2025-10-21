#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# color logger (use script dir to find it)
source "${SCRIPT_DIR}/color-logger.bash"

PROOFS_DIR="$1"

if [ -z "${PROOFS_DIR}" ]; then
    echo "Usage: $0 <proofs_dir>" >&2
    exit 1
fi

info "Removing empty proof files in '${PROOFS_DIR}'"
# Remove empty proof files
fd --type f --size 0b -e proof "${PROOFS_DIR}" | xargs -r -I {} rm -f "{}"

info "Removing proof files containing only 'unsat' in '${PROOFS_DIR}'"
# Remove proof files that contain only "unsat" (optionally surrounded by whitespace/newline)
rg -l --hidden --no-messages -g '*.proof' '^\s*unsat\s*$' "${PROOFS_DIR}" | xargs -r -I {} rm -f "{}"