#!/bin/bash

# exit when any command fails
set -e

DH_DIR="/gobra/Go/dh"
additionalGobraArgs="-I $DH_DIR -I $DH_DIR/.verification/precedence -I $DH_DIR/../.modules --module github.com/viperproject/ProtocolVerificationCaseStudies/dh --parallelizeBranches"
mkdir -p "$DH_DIR/.gobra"

echo "Verifying the DH Initiator. This might take some time..."
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $DH_DIR \
    --gobraDirectory "$DH_DIR/.gobra" \
    --recursive \
    --includePackages initiator \
    $additionalGobraArgs

echo "Verifying the DH Responder. This might take some time..."
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $DH_DIR \
    --gobraDirectory "$DH_DIR/.gobra" \
    --recursive \
    --includePackages responder \
    $additionalGobraArgs

echo "Verifying the DH trace invariants and main package. This might take some time..."
# verify packages located in the current directory and in `common`:
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $DH_DIR \
    --gobraDirectory "$DH_DIR/.gobra" \
    --directory "$DH_DIR" "$DH_DIR/common" \
    $additionalGobraArgs
