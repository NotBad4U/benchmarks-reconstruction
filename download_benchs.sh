#!/usr/bin/env bash
# Download SMT-LIB benchmark sets.
#
#   ./download_benchs.sh              # QF_UF and UF (the default set)
#   ./download_benchs.sh LIA UF       # pick explicitly
#   BENCHS_DIR=$HOME/benchs ./download_benchs.sh
set -eu

BENCHS_DIR="${BENCHS_DIR:-benchs}"
mkdir -p "$BENCHS_DIR"
pushd "$BENCHS_DIR" > /dev/null

url_for() {
  case "$1" in
    LIA)      echo "https://zenodo.org/records/16740866/files/LIA.tar.zst?download=1" ;;
    QF_UFLIA) echo "https://zenodo.org/records/16740866/files/QF_UFLIA.tar.zst?download=1" ;;
    UFLIA)    echo "https://zenodo.org/records/16740866/files/UFLIA.tar.zst?download=1" ;;
    QF_UF)    echo "https://zenodo.org/records/16740866/files/QF_UF.tar.zst?download=1" ;;
    UF)       echo "https://zenodo.org/records/16740866/files/UF.tar.zst?download=1" ;;
    *)        echo "Unknown key: $1" >&2; exit 1 ;;
  esac
}

# Default to the two sets the benchmark actually runs on.  The others
# (LIA, QF_UFLIA, UFLIA) are still available by name.
TARGETS="${*:-QF_UF UF}"

for name in $TARGETS; do
  archive="${name}.tar.zst"

  if [ -d "$name" ]; then
    echo "✓ $name already exists, skipping."
    continue
  fi

  echo "→ Downloading $name ..."
  if command -v curl >/dev/null 2>&1; then
    curl -fL --retry 3 --retry-delay 2 -o "$archive" "$(url_for "$name")"
  elif command -v wget >/dev/null 2>&1; then
    wget -O "$archive" "$(url_for "$name")"
  else
    echo "Error: need curl or wget installed." >&2
    exit 1
  fi

  echo "→ Extracting $archive ..."
  if tar --help 2>&1 | grep -q -- '--zstd'; then
    tar --zstd -xf "$archive"
  elif command -v unzstd >/dev/null 2>&1; then
    unzstd -c "$archive" | tar -xf -
  elif command -v zstdcat >/dev/null 2>&1; then
    zstdcat "$archive" | tar -xf -
  else
    echo "Error: no zstd decompressor found. Try 'brew install zstd'." >&2
    exit 1
  fi

  if [ -d "non-incremental/$name" ]; then
    mv "non-incremental/$name" "$name"
    rm -rf non-incremental
  elif [ -d "$name" ]; then
    echo "Note: found $name at top-level."
  else
    echo "Error: expected non-incremental/$name after extraction." >&2
    exit 1
  fi

  rm -f "$archive"
  echo "✓ Ready: $name"
done

# --- keep only benchmarks that can have a proof ------------------------------
# Folded in from the old clean-benchs.sh, which needed ripgrep (absent on the
# cluster).  Only `unsat` instances produce a proof to reconstruct; sat and
# unknown ones would just run cvc5 for nothing.  Done before the rewrites below
# so those do not waste time on files about to be deleted.
#
# `grep --null` rather than `-Z`: on BSD grep (macOS) `-Z` means decompress.
echo "-> removing StarExec metadata (*.txt)"
find . -type f -name '*.txt' -delete

before=$(find . -type f | wc -l | tr -d ' ')
{ grep -rl --null -e 'status sat' -e 'status unknown' . || true; } | xargs -0 rm -f
find . -type f -empty -delete
find . -type d -empty -delete
after=$(find . -type f | wc -l | tr -d ' ')
echo "-> removed $((before - after)) sat/unknown/empty benchmarks, $after kept"

# --- normalise symbols the downstream tools cannot handle --------------------
# The cluster has no `fd`, so fall back to `find`.  And GNU sed (Linux) takes
# `-i` with no argument while BSD sed (macOS) requires `-i ''`, so pick once.
if command -v fd > /dev/null 2>&1; then
  list_files() { fd -t f -0; }
else
  list_files() { find . -type f -print0; }
fi

if sed --version > /dev/null 2>&1; then
  SED_INPLACE=(-i -E)        # GNU
else
  SED_INPLACE=(-i '' -E)     # BSD / macOS
fi

rewrite() {
  echo "-> rewriting: $1"
  list_files | xargs -0 -n 200 sed "${SED_INPLACE[@]}" "$1"
}

rewrite 's/\$/_/g'
rewrite 's/(declare-fun[[:space:]]+)apply/\1_apply/g'   # `apply` is reserved
rewrite 's/\|([-+*])i\|/|i\1|/g'
rewrite 's/\|([-+*])r\|/|r\1|/g'
rewrite 's/\|([-+*])f\|/|f\1|/g'

popd > /dev/null
