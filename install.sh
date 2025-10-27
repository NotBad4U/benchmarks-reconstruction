#!/usr/bin/env bash
set -euo pipefail

#------------------------------------------------------------------------------
# Helpers
#------------------------------------------------------------------------------
NPROC="$(nproc || echo 8)"
DEPS_DIR="$HOME/deps"
mkdir -p "$DEPS_DIR"

#------------------------------------------------------------------------------
# 0. System packages
#------------------------------------------------------------------------------
echo "[*] Updating APT and installing base dependencies..."
sudo apt-get update
sudo apt-get install -y \
  build-essential cmake \
  python3 python3-venv python3-pip \
  m4 autoconf automake libtool pkg-config \
  libgmp-dev \
  curl git wget unzip \
  opam \
  rsync \
  libffi-dev libssl-dev \
  zlib1g-dev

#------------------------------------------------------------------------------
# 1. Install cvc5 @ commit 8aeaa1938d
#    Ref: https://github.com/cvc5/cvc5/blob/main/INSTALL.rst
#------------------------------------------------------------------------------
echo "[*] Cloning and building cvc5..."
pushd "$DEPS_DIR"
if [ ! -d cvc5 ]; then
    git clone https://github.com/cvc5/cvc5.git
fi
pushd cvc5
git fetch origin
git checkout 8aeaa1938d

echo "[*] Configuring cvc5..."
./configure.sh --auto-download

echo "[*] Building cvc5..."
pushd build
make -j"$NPROC"

echo "[*] Installing cvc5 (sudo)..."
sudo make install
popd  # leave build
popd  # leave cvc5
popd  # leave $DEPS_DIR

#------------------------------------------------------------------------------
# 2. Install Rust (non-interactive) + source cargo env
#------------------------------------------------------------------------------
echo "[*] Installing Rust toolchain (rustup)..."
# -y means skip prompt, defaults to stable, writes ~/.cargo/env
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

# Make cargo available in *this* shell
# shellcheck disable=SC1090
. "$HOME/.cargo/env"

#------------------------------------------------------------------------------
# 3. Install carcara from branch lambdapi-translate
#------------------------------------------------------------------------------
echo "[*] Installing carcara (cargo install --path cli)..."
pushd "$DEPS_DIR"
if [ ! -d carcara ]; then
    git clone --branch lambdapi-translate https://github.com/NotBad4U/carcara.git
fi
pushd carcara
# We install from local path `cli` with the "release-lto" profile
cargo install --profile release-lto --path cli
popd  # leave carcara
popd  # leave $DEPS_DIR

#------------------------------------------------------------------------------
# 4. CLI tools via cargo: hyperfine, ripgrep, fd-find
#------------------------------------------------------------------------------
echo "[*] Installing hyperfine, ripgrep, fd-find via cargo..."
cargo install --locked hyperfine
cargo install ripgrep
cargo install fd-find

#------------------------------------------------------------------------------
# 5. Install Lambdapi (dev-3.0.0-8-gdfc302e9) with OCaml 5.0.0 via opam
#    Ref: https://github.com/Deducteam/lambdapi/blob/master/README.md
#------------------------------------------------------------------------------
echo "[*] Initializing opam and OCaml 5.0.0..."
if [ ! -d "$HOME/.opam" ]; then
    opam init -y --disable-sandboxing
fi

# Load opam env in this shell
eval "$(opam env --shell=bash)"

# Create (or select) a switch with OCaml 5.0.0
if ! opam switch list --short | grep -q "^ocaml-5\.0\.0$"; then
    opam switch create ocaml-5.0.0 5.0.0 -y
fi
opam switch ocaml-5.0.0
eval "$(opam env --shell=bash)"

echo "[*] Cloning Lambdapi..."
pushd "$DEPS_DIR"
if [ ! -d lambdapi ]; then
    git clone https://github.com/Deducteam/lambdapi.git
fi
pushd lambdapi
git fetch origin
git checkout dev-3.0.0-8-gdfc302e9 || git checkout tags/dev-3.0.0-8-gdfc302e9 || true

echo "[*] Installing Lambdapi dependencies with opam..."
opam install . -y

echo "[*] Building Lambdapi..."
make build

echo "[*] Installing Lambdapi (dune install)..."
make install

popd  # leave lambdapi
popd  # leave $DEPS_DIR

#------------------------------------------------------------------------------
# 6. Install lambdapi-stdlib (branch order-lemmas)
#------------------------------------------------------------------------------
echo "[*] Installing lambdapi-stdlib (make install)..."
pushd "$DEPS_DIR"
if [ ! -d lambdapi-stdlib ]; then
    git clone --branch order-lemmas https://github.com/NotBad4U/lambdapi-stdlib.git
fi
pushd lambdapi-stdlib
make install
popd  # leave lambdapi-stdlib
popd  # leave $DEPS_DIR

#------------------------------------------------------------------------------
# 8. Final PATH hints
#------------------------------------------------------------------------------
echo
echo "===================================================================="
echo " Setup complete."
echo
echo " Recommended: add these lines to your ~/.bashrc if not present:"
echo '  . "$HOME/.cargo/env"'
echo '  eval \"\$(opam env --shell=bash)\"'
echo
echo " You now have:"
echo "  - cvc5            (commit 8aeaa1938d) installed system-wide"
echo "  - Rust + cargo    (cargo on PATH if you source ~/.cargo/env)"
echo "  - carcara         (installed via cargo install --path cli)"
echo "  - hyperfine       (cargo install --locked hyperfine)"
echo "  - ripgrep         (cargo install ripgrep)"
echo "  - fd-find         (cargo install fd-find)"
echo "  - lambdapi        (version dev-3.0.0-8-gdfc302e9 via dune install)"
echo "  - lambdapi-stdlib (branch order-lemmas, make install)"
echo "===================================================================="
