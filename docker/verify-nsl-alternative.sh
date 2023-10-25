#!/bin/bash

# exit when any command fails
set -e

NSL_DIR="/gobra/Go/nsl"
additionalGobraArgs="-I $NSL_DIR -I $NSL_DIR/.verification/precedence -I $NSL_DIR/../.modules --module github.com/viperproject/ProtocolVerificationCaseStudies/nsl --parallelizeBranches"
mkdir -p "$NSL_DIR/.gobra"

echo "Verifying the alternative NSL Initiator. This might take some time..."
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $NSL_DIR \
    --gobraDirectory "$NSL_DIR/.gobra" \
    --recursive \
    --includePackages initiator2 \
    $additionalGobraArgs
