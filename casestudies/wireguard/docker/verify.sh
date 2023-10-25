#!/bin/bash

# exit when any command fails
set -e

scriptDir=$(dirname "$0")
mkdir -p "$scriptDir/.gobra"

additionalGobraArgs="-I $scriptDir/verification -I $scriptDir/.modules-precedence -I $scriptDir/.modules -I $scriptDir --module github.com/viperproject/ProtocolVerificationCaseStudies/wireguard --parallelizeBranches"

# verify initiator
echo "Verifying the Initiator. This might take some time..."
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $scriptDir \
    --gobraDirectory "$scriptDir/.gobra" \
    --recursive \
    --includePackages initiator \
    $additionalGobraArgs

# verify responder
echo "Verifying the Responder. This might take some time..."
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $scriptDir \
    --gobraDirectory "$scriptDir/.gobra" \
    --recursive \
    --includePackages responder \
    $additionalGobraArgs

echo "Verifying packages containing lemmas and trace invariants. This might take some time..."
packages="common messageCommon messageInitiator messageResponder labelLemma labelLemmaCommon labelLemmaInitiator labelLemmaResponder"
java -Xss128m -jar /gobra/gobra.jar \
    --projectRoot $scriptDir \
    --gobraDirectory "$scriptDir/.gobra" \
    --recursive \
    --includePackages $packages \
    $additionalGobraArgs
