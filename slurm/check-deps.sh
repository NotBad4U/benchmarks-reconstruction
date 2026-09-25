#!/bin/bash
# Report which system dependencies of the toolchain are present on this host.
#
#   bash slurm/check-deps.sh
#
# Read-only and takes seconds, so it is safe on the login node.  Run it there
# first, then inside a job (`srun --partition=scavenge --pty bash`) if you want
# to be sure -- login and compute nodes do not always carry the same packages.
#
# Why each entry matters is in the note column: setup.job builds carcara, OCaml
# and lambdapi from source, so the toolchain needs a working C build
# environment plus a few dev libraries that opam cannot install without root.

PASS=0; FAIL=0
MISSING=""

say() { # status name note
  case "$1" in
    ok)   printf '  \033[32m%-4s\033[0m %-14s %s\n' OK   "$2" "$3"; PASS=$((PASS+1)) ;;
    miss) printf '  \033[31m%-4s\033[0m %-14s %s\n' MISS "$2" "$3"; FAIL=$((FAIL+1))
          MISSING="$MISSING $2" ;;
    warn) printf '  \033[33m%-4s\033[0m %-14s %s\n' WARN "$2" "$3" ;;
  esac
}

have() { # name note
  if command -v "$1" >/dev/null 2>&1; then
    say ok "$1" "$(command -v "$1")"
  else
    say miss "$1" "$2"
  fi
}

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

lib() { # name header linkflags note
  name="$1"; hdr="$2"; flags="$3"; note="$4"
  printf '#include <%s>\nint main(void){return 0;}\n' "$hdr" > "$TMP/t.c"
  if ! ${CC:-cc} -c "$TMP/t.c" -o "$TMP/t.o" 2>/dev/null; then
    say miss "$name" "no <$hdr> -- $note"
  elif ! ${CC:-cc} "$TMP/t.c" -o "$TMP/t" $flags 2>/dev/null; then
    say miss "$name" "header found but $flags does not link -- $note"
  else
    say ok "$name" "<$hdr> + $flags"
  fi
}

echo "=== host: $(hostname)  $( [ -r /etc/os-release ] && . /etc/os-release && echo "$PRETTY_NAME" ) ==="

echo
echo "--- C build environment (carcara's GMP, OCaml, every opam C stub) ---"
have cc         "no C compiler: nothing below will build"
have c++        "OCaml and some C++ stubs want it"
have make       "required by every from-source build here"
have ar         "static archives for GMP and OCaml"
have ranlib     "same"
have m4         "GMP's configure aborts without it (hit for real: job 130513)"
have patch      "opam applies patches to sources"
have pkg-config "ocaml-ssl and conf-libev locate libraries with it"
have perl       "OpenSSL's configure is Perl; only matters if we build OpenSSL"

echo
echo "--- archive and fetch tools (cvc5 zip, opam tarballs, benchmark .tar.zst) ---"
have curl   "download_benchs.sh falls back to wget"
have git    "carcara, lambdapi-stdlib and opam repo clones"
have unzip  "setup.job unpacks the cvc5 static release with it"
have tar    "everything"
have gzip   "opam tarballs"
have bzip2  "opam tarballs"
have xz     "opam tarballs"
have rsync  "opam uses it to sync local repos"
if tar --help 2>&1 | grep -q -- '--zstd'; then
  say ok "tar --zstd" "benchmark archives unpack directly"
elif command -v unzstd >/dev/null 2>&1 || command -v zstdcat >/dev/null 2>&1; then
  say warn "tar --zstd" "absent, but unzstd/zstdcat is here (the script falls back)"
else
  say miss "zstd" "no way to unpack the .tar.zst benchmark archives"
fi

echo
echo "--- dev libraries opam needs and cannot install without root ---"
lib gmp     gmp.h          "-lgmp"          "why3 -> zarith needs it"
lib mpfr    mpfr.h         "-lmpfr -lgmp"   "only if rug is switched to system libs"
lib openssl openssl/ssl.h  "-lssl -lcrypto" "lambdapi -> dream -> ssl/lwt_ssl"
lib libev   ev.h           "-lev"           "lambdapi -> dream -> conf-libev, a hard fail when absent"
lib zlib    zlib.h         "-lz"            "camlzip, if anything in the chain pulls it"

echo
echo "--- python (benchmark.job's venv and collects.py) ---"
have python3 "benchmark.job loads a Python module, so a bare login shell may lack it"
python3 -c 'import sys, venv; print("  venv module  : ok, python " + ".".join(map(str, sys.version_info[:3])))' 2>/dev/null \
  || echo "  venv module  : MISSING"

echo
echo "--- modules that could supply anything missing ---"
if type module >/dev/null 2>&1; then
  for pat in M4 GMP MPFR OpenSSL libev zlib pkgconf pkg-config Python Rust OCaml zstd; do
    hits="$(module -t avail 2>&1 | grep -i "^$pat" | tr '\n' ' ')"
    printf '  %-12s %s\n' "$pat" "${hits:-(none)}"
  done
else
  echo "  no 'module' command in this shell -- source /etc/profile.d/lmod.sh first"
fi

echo
echo "=== $PASS ok, $FAIL missing ==="
[ -n "$MISSING" ] && echo "missing:$MISSING"
exit 0
