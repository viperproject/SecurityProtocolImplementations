#!/bin/bash

# exit when any command fails
set -e

NSL_DIR="/gobra/Go/nsl"
additionalGobraArgs="-I $NSL_DIR -I $NSL_DIR/.verification/precedence -I $NSL_DIR/../.modules --module github.com/viperproject/ProtocolVerificationCaseStudies/nsl --parallelizeBranches"
mkdir -p "$NSL_DIR/.gobra"

echo "Verifying the NSL Initiator. This might take some time..."
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $NSL_DIR \
    --gobraDirectory "$NSL_DIR/.gobra" \
    --recursive \
    --includePackages initiator \
    $additionalGobraArgs

echo "Verifying the NSL Responder. This might take some time..."
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $NSL_DIR \
    --gobraDirectory "$NSL_DIR/.gobra" \
    --recursive \
    --includePackages responder \
    $additionalGobraArgs

echo "Verifying the NSL trace invariants and main package. This might take some time..."
# verify packages located in the current directory and in `common`:
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $NSL_DIR \
    --gobraDirectory "$NSL_DIR/.gobra" \
    --directory "$NSL_DIR" "$NSL_DIR/common" \
    $additionalGobraArgs
