#!/bin/bash

. color-logger.bash

check_binary() {
  if ! which "$1" > /dev/null; then
    ( >&2 echo "$2" )
    exit 1
  fi
}

# info "Check if binaries are installed.."

check_binary "cvc5" "$(cat <<EOF
You will need cvc5 to run this script.
Install it using your package manager. E.g. for homebrew:
brew install cvc5
EOF
)"

success "CVC5 installed ✔"

check_binary "carcara" "$(cat <<EOF
You will need carcara to run this script.
Install it using your package manager. E.g. for homebrew:
brew install carcara
EOF
)"

success "Carcara installed ✔"

check_binary "lambdapi" "$(cat <<EOF
You will need lambdapi to run this script.
Install it using your package manager. E.g. for homebrew:
brew install lambdapi
EOF
)"

success "Lambdapi installed ✔"

check_binary "parallel" "$(cat <<EOF
You will need parallel to run this script.
Install it using your package manager. E.g. for homebrew:
brew install parallel
EOF
)"

success "parallel installed ✔"

# ripgrep (rg)
check_binary "rg" "$(cat <<EOF
You will need ripgrep (rg) to run this script.
You can install ripgrep following the instructions at:
https://github.com/BurntSushi/ripgrep?tab=readme-ov-file#installation
EOF
)"

success "ripgrep installed ✔"

# fd (find-fd)
check_binary "rg" "$(cat <<EOF
You will need fd (i.e. fd-find) to run this script.
You can install find-fd following the instructions at:
https://github.com/sharkdp/fd?tab=readme-ov-file#installation
EOF
)"

success "fd installed ✔"

# hyperfine
check_binary "hyperfine" "$(cat <<EOF
You will need hyperfine to run this script.
You can install hyperfine following the instructions at:
https://github.com/sharkdp/hyperfine?tab=readme-ov-file#installation
EOF
)"

success "hyperfine installed ✔"