#!/bin/bash

# exit when any command fails
set -e

SCRIPT_DIR=$(dirname "$0")

VERIFAST="verifast"

# get all `.c` files in the current directory but ignore `crypto.c` and `io.c`
# because these implementations are trusted and thus should not be verified:
C_FILES=($(find $SCRIPT_DIR -type f \( -iname "*.c" ! -iname "crypto.c" ! -iname "io.c" \) | sort))

# iterate over each file and verify it:
for FILE in "${C_FILES[@]}"
do
    $VERIFAST -allow_dead_code -shared -c $FILE
done
