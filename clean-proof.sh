#!/bin/bash


if [ -d proofs ]; then
    echo 'Directory proofs does not exist'
fi

# Clean side effect of calling CVC5

# Remove empty proof file because CVC5 timeout
fd --size 0b -e proof | xargs -I {} rm {}

# Remove proof file where it is unsat but CVC5 did not produce a proof
fd --size 6B -e proof | xargs -I {} rm {}