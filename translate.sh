#!/bin/bash

. color-logger.bash

SCRIPT_VERSION=1.0.0

######## setup

show_help() {
  cat << EOF
NAME v$SCRIPT_VERSION
  run - Run the Lambdapi translation benchmarks.

DESCRIPTION
  Run the benchmark of the Lambdapi translation from the paper.

  Run test of a specific benchmark
  '$ run -t NAME' 

  Run test with the large proof who are excluded by default
  '$ run -n 3000 -s 500 -l' 

OPTIONS
  -h          Show help
  -n <value>  Set a proof as large if the number of step is greater than <value> (default = 1000)
  -s <value>  Split the proof into chunck of size <value> (default = 300)
  -t <name>   If specified, only run tests containing this string in their names
  -l          Test all test including large proof.
  -g          (Re)generate the proof with CVC5
EOF
}

check_binary() {
  if ! which "$1" > /dev/null; then
    ( >&2 echo "$2" )
    exit 1
  fi
}

function cleanup()
{
    rm -rf $RUNDIR
}
trap cleanup ERR

function finish()
{
    debug "benchmark interrupted"
}
trap finish EXIT


# CLI ##################################

OPTSTRING=":n:s:t:lgh"

THRESHOLD_LG_PROOF=1000
SPLIT_SIZE=300
TEST_NAME=
GEN_PROOF=false
CHECK_LARGE_PROOF=false

while getopts ${OPTSTRING} opt; do
  case ${opt} in
    n)
      echo "Option -n was triggered, Argument: ${OPTARG}"; THRESHOLD_LG_PROOF=${OPTARG}
      ;;
    s)
      echo "Option -s was triggered, Argument: ${OPTARG}"; SPLIT_SIZE=${OPTARG}
      ;;
    t)
      echo "Option -t was triggered, Argument: ${OPTARG}"; TEST_NAME=${OPTARG}
      ;;
    l)
      echo "Option -l was triggered"; CHECK_LARGE_PROOF=true
      ;;
    g)
      echo "Option -g was triggered"; GEN_PROOF=true
      ;;
    h)
      show_help
      exit 0
      ;;
    :)
      echo "Option -${OPTARG} requires an argument."
      exit 1
      ;;
    ?)
      echo "Invalid option: -${OPTARG}."
      show_help
      exit 1
      ;;
  esac
done

echo "Configuration found:"

if [ "$THRESHOLD_LG_PROOF" == 1000 ]; then echo "THRESHOLD_LARGE_PROOF = 1000 (default)"; else echo "THRESHOLD_LARGE_PROOF = '$THRESHOLD_LG_PROOF'"; fi

if [ "$SPLIT_SIZE" == 300 ]; then echo "SPLIT_SIZE = 300 (default)"; else echo "SPLIT_SIZE = '$SPLIT_SIZE'"; fi

if [ -n "$TEST_NAME" ]; then echo "Only run tests containing '$TEST_NAME'"; fi

if $CHECK_LARGE_PROOF; then echo "Include large proofs";  else  echo "Exclude large proofs";  fi 

if $GEN_PROOF; then echo "Generate the proof";  else  echo "Skip proof generation";  fi 


# Main  ###############################

# info "Check if binaries are installed.."

check_binary "cvc5" "$(cat <<EOF
You will need cvc5 to run this script.
Install it using your package manager. E.g. for homebrew:
brew install cvc5
EOF
)"

success "CVC5 ✔"

check_binary "carcara" "$(cat <<EOF
You will need carcara to run this script.
Install it using your package manager. E.g. for homebrew:
brew install carcara
EOF
)"

success "Carcara ✔"

check_binary "lambdapi" "$(cat <<EOF
You will need lambdapi to run this script.
Install it using your package manager. E.g. for homebrew:
brew install lambdapi
EOF
)"

success "Lambdapi ✔"

check_binary "parallel" "$(cat <<EOF
You will need parallel to run this script.
Install it using your package manager. E.g. for homebrew:
brew install parallel
EOF
)"

success "parallel ✔"

info "Generate the working directory run..."

RUNDIR="${VARIABLE:=run}"

# rm -rf $RUNDIR
# mkdir $RUNDIR

for dir in "alethe" "convert" "results"; do
    fd . 'benchs/' -t d -X mkdir -p $RUNDIR/{} \;
    mv $RUNDIR/benchs $RUNDIR/$dir
done

## GENERATE PROOF

if [ -d proofs ]; then
    info "Proof directory found"
else
    info "Generate proof directory: proofs"
    fd . 'benchs/' -t d -X mkdir -p proofs/{} \;
    mv proofs/benchs/* proofs
    rm -rf proofs/benchs

    pushd benchs  > /dev/null
    # fd -tf -e 'smt2' -j 8 ${TEST_NAME} -x sh -c 'cvc5 --dag-thresh=0 --produce-proofs --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token {} > ../proofs/{.}.proof' \;
    fd -tf -e 'smt2' -j 8 ${TEST_NAME} | parallel --will-cite --bar -j8 'cvc5 --tlimit=500 --dag-thresh=0 --produce-proofs --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token {} > ../proofs/{.}.proof' \;
    popd  > /dev/null
    grep -l -r -E "^sat" proofs | xargs -I {} rm {}
    grep -l -r -E "^unknown" proofs | xargs -I {} rm {}
fi  


## GENERATE ELAB PROOF

info  "Elaborating proofs..."

pushd proofs  > /dev/null
fd -tf -e 'proof' -j 8 ${TEST_NAME} | parallel --will-cite --bar -j8 'carcara check --log off -i {} ../benchs/{.}.smt2 1> /dev/null 2> /dev/null ; carcara elaborate --no-print-with-sharing --expand-let-bindings -i --log off {} ../benchs/{.}.smt2 1> ../run/alethe/{.}.elab 2> /dev/null'  \;
popd  > /dev/null

## TRANSLATE AND CHECK ELAB PROOF

pushd run > /dev/null
    info  "Translating elaborated proofs..."

    pushd alethe > /dev/null
    find . -type d -empty -delete
    fd -tf -e 'elab' -j 8 ${TEST_NAME} | parallel --will-cite --bar -j8  'carcara translate  --no-elab --why3 -i {} ../../benchs/{.}.smt2 1> ../convert/{.}.lp 2> /dev/null'  \;
    popd > /dev/null

    # info  "Checking proofs..."

    # pushd convert > /dev/null
    # fd -tf -e 'lp' -j 8 ${TEST_NAME} | parallel --will-cite --bar -j8  'hyperfine --warmup 3 --max-runs 10 --export-json ../results/{.}.json  "lambdapi check --timeout=3 {}"' 2> /dev/null  \;
    # popd > /dev/null
popd > /dev/null

## CHECK RESULT

