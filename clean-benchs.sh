#!/bin/bash

. color-logger.bash

if [ -d benchs ]; then
    echo 'Directory benchs does not exist'
fi

pushd benchs

# Remove starexec file
find . -type f -name "*.txt" |  xargs -I {} rm {}

# Remove file with status sat and unknown
rg -l "status sat" |  xargs -I {} rm {}
rg -l "status unknown" |  xargs -I {} rm {}

# Clean empty directory
find . -type d -empty -delete

popd