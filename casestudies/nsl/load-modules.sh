#!/bin/bash -e

# iterates over directories, downloads go modules, and creates corresponding symlinks for verification
# these directory are created in the folder `folderName` in the directory in which this
# script is located. In this folder, there is a subfolder for each module found in subdirectories.
# I.e. The `folderName` is not created in the same folder as the module that requires the modules but
# the `folderName` is one-level outside and shared.

folderName="$1"

# gets absolute path to the directory in which this file is placed:
scriptDir=$(cd $(dirname "$0"); pwd)

# download modules and get json output where they are stored:
downloadOutput=$(go mod download -json)
# output one package per line:
modules=$(echo $downloadOutput | jq --compact-output '.')
for module in $modules; do
    moduleName=$(echo $module | jq --raw-output '.Path')
    moduleDir=$(echo $module | jq --raw-output '.Dir')
    echo "$moduleName is at $moduleDir"
    prefixedModuleName="$scriptDir/$folderName/$moduleName"
    pathToModule=$(dirname "$prefixedModuleName")
    moduleBasename=$(basename "$prefixedModuleName")
    mkdir -p $pathToModule
    ln -s $moduleDir $prefixedModuleName
done
