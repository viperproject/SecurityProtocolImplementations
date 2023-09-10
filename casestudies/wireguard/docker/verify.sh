#!/bin/bash

# exit when any command fails
set -e

scriptDir=$(dirname "$0")
mkdir -p .gobra

additionalGobraArgs="-I $scriptDir/verification -I $scriptDir/.modules-precedence -I $scriptDir/.modules -I $scriptDir --module github.com/viperproject/ProtocolVerificationCaseStudies/wireguard --gobraDirectory $scriptDir/.gobra --parallelizeBranches"

# verify initiator
echo "Verifying the Initiator. This might take some time..."
java -Xss128m -jar gobra.jar \
    --recursive \
    --includePackages initiator \
    $additionalGobraArgs

# verify responder
echo "Verifying the Responder. This might take some time..."
java -Xss128m -jar gobra.jar \
    --recursive \
    --includePackages responder \
    $additionalGobraArgs

echo "Verifying packages containing lemmas and trace invariants. This might take some time..."
packages="common messageCommon messageInitiator messageResponder labelLemma labelLemmaCommon labelLemmaInitiator labelLemmaResponder"
java -Xss128m -jar gobra.jar \
    --recursive \
    --includePackages $packages \
    $additionalGobraArgs
