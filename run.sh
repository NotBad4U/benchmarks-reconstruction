rm -rf proofs

check_binary() {
  if ! which "$1" > /dev/null; then
    ( >&2 echo "$2" )
    exit 1
  fi
}



check_binary "cvc5" "$(cat <<EOF
You will need cvc5 to run this script.
Install it using your package manager. E.g. for homebrew:
brew install cvc5
EOF
)"

check_binary "carcara" "$(cat <<EOF
You will need carcara to run this script.
Install it using your package manager. E.g. for homebrew:
brew install carcara
EOF
)"

check_binary "lambdapi" "$(cat <<EOF
You will need lambdapi to run this script.
Install it using your package manager. E.g. for homebrew:
brew install lambdapi
EOF
)"

function cleanup()
{
    rm -rf $RUNDIR
}

trap cleanup ERR

function finish()
{
    echo "finish"
}

trap finish EXIT

RUNDIR="${VARIABLE:=run}"

rm -rf $RUNDIR
mkdir $RUNDIR

for dir in "alethe" "convert" "results"; do
    fd . 'benchs/' -j 8 -t d -X mkdir -p $RUNDIR/{} \;
    mv $RUNDIR/benchs $RUNDIR/$dir
done

# GENERATE PROOF

if [ -d proofs ]; then
    echo "Proof directory found"
else
    echo "Generate proof directory: proofs"
    fd . 'benchs/' -j 8 -t d -X mkdir -p proofs/{} \;
    mv proofs/benchs/* proofs
    rm -rf proofs/benchs

    pushd benchs  > /dev/null
    fd -tf -e 'smt2' -j 8 -x sh -c 'cvc5 --dag-thresh=0 --produce-proofs --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token {} > ../proofs/{.}.proof' \;
    popd  > /dev/null
    grep -l -r -E "^sat" proofs | xargs -I {} rm {}
    grep -l -r -E "^unknown" proofs | xargs -I {} rm {}
fi  


# GENERATE ELAB PROOF

pushd proofs  > /dev/null
fd -tf -e 'proof' -j 8 -x sh -c 'carcara check --log off -i {} ../benchs/{.}.smt2 1> /dev/null 2> /dev/null ; carcara elaborate --no-print-with-sharing --expand-let-bindings -i --log off {} ../benchs/{.}.smt2 1> ../run/alethe/{.}.elab 2> /dev/null'  \;
popd  > /dev/null


pushd run > /dev/null

    pushd alethe > /dev/null
    find . -type d -empty -delete
    fd -tf -e 'elab' -j 8 -x sh -c 'carcara translate  --no-elab --why3 -i {} ../../benchs/{.}.smt2 1> ../convert/{.}.lp 2> /dev/null'  \;
    popd > /dev/null

    pushd convert > /dev/null
    fd -tf -e 'lp' -j 8 -x sh -c 'hyperfine --warmup 3 --max-runs 10 --export-json ../results/{.}.json  "lambdapi check --timeout=3 {}"'  \;
    popd
popd > /dev/null