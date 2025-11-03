#!/usr/bin/env bash
mkdir -p benchs
pushd benchs > /dev/null

#!/bin/sh
set -eu

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

# Use all sets by default; or pass names as args, e.g. ./script.sh LIA UF
TARGETS="${*:-LIA QF_UFLIA UFLIA QF_UF UF}"

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

case "$(uname -s)" in
  Darwin) fd -t f -x sed -i '' 's/\$/_/g' {} ;;  # macOS
  *)      fd -t f -x sed -i 's/\$/_/g' {} ;;     # Linux/others
esac

# Fix CLEARSY benchmarks that use reserved 'apply' symbol
case "$(uname -s)" in
  Darwin) fd -t f -x sed -i '' -E 's/(declare-fun[[:space:]]+)apply/\1_apply/g' {} ;;  # macOS
  *)      fd -t f -x sed -i -E 's/(declare-fun[[:space:]]+)apply/\1_apply/g' {} ;;     # Linux/others
esac
case "$(uname -s)" in
  Darwin) fd -t f -x sed -i '' -E 's/\|([-+*])i\|/|i\1|/g' {} ;;  # macOS
  *)      fd -t f -x sed -i -E 's/\|([-+*])i\|/|i\1|/g' {} ;;     # Linux/others
esac
case "$(uname -s)" in
  Darwin) fd -t f -x sed -i '' -E 's/\|([-+*])r\|/|r\1|/g' {} ;;  # macOS
  *)      fd -t f -x sed -i -E 's/\|([-+*])r\|/|r\1|/g' {} ;;     # Linux/others
esac
case "$(uname -s)" in
  Darwin) fd -t f -x sed -i '' -E 's/\|([-+*])f\|/|f\1|/g' {} ;;  # macOS
  *)      fd -t f -x sed -i -E 's/\|([-+*])f\|/|f\1|/g' {} ;;     # Linux/others
esac

popd > /dev/null
