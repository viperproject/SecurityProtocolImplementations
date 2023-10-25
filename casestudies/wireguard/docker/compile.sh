#!/bin/bash

# exit when any command fails
set -e

scriptDir=$(dirname "$0")

# temporarily switch to `$scriptDir`:
(cd "$scriptDir" && go build -v -o wireguard-gobra)
