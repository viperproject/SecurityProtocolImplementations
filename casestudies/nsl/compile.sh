#!/bin/bash

scriptDir=$(dirname "$0")
oldPwd=$(pwd)

cd $scriptDir
go build -v -o nsl
cd $oldPwd
