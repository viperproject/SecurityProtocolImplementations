#!/bin/bash

# this script is invoked as part of CI to verify all packages

scriptDir=$(dirname "$0")

# flag whether this script is currently executed as part of a CI
isCi=$CI

# create .gobra folder if it does not exist yet:
mkdir -p $scriptDir/.gobra

gobraJar="/gobra/gobra.jar"
additionalGobraArgs="-I $scriptDir -I $scriptDir/.verification --module github.com/viperproject/ReusableProtocolVerificationLibrary  --parallelizeBranches"

if [ $isCi ]; then
    echo -e "\033[0Ksection_start:`date +%s`:verify[collapsed=true]\r\033[0KVerifying packages"
fi
java -Xss128m -jar $gobraJar \
    --projectRoot $scriptDir \
    --gobraDirectory "$scriptDir/.gobra" \
    --recursive \
    $additionalGobraArgs
exitCode=$?
if [ $isCi ]; then
    echo -e "\033[0Ksection_end:`date +%s`:verify\r\033[0K"
fi

# set exit code:
exit $exitCode
