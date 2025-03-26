source color-logger.bash

rm -rf proofs

info "Proof directory not found"
mkdir proofs

info "Generate proof directory: proofs"
fd . 'benchs/' -t d -X mkdir -p proofs/{} \;
mv proofs/benchs/* proofs
rm -rf proofs/benchs


pushd benchs  > /dev/null

fd -tf -e 'smt2' -j 8 ${TEST_NAME} | parallel --will-cite --bar -j8 'cvc5 --tlimit=10000 --dag-thresh=0 --produce-proofs --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token {} > ../proofs/{.}.proof' \;

info "Remove empty directories in proof "
find . -type d -empty -delete

popd  > /dev/null
