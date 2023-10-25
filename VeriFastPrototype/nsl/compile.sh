#!/bin/bash

# exit when any command fails
set -e

SCRIPT_DIR=$(dirname "$0")
VERIFAST=$(which verifast)
VERIFAST_BIN="$(dirname "$VERIFAST")"

# copy files in this directory and all `.h` files from the library
# to some temporary directory to then verify them:

# try linux and fall-back to macOS:
TMP_DIR=$(mktemp -d -t verification-XXXXXXXXXX -p "$SCRIPT_DIR/.." 2>/dev/null || mktemp -d "$SCRIPT_DIR/../verification-XXXXXXXXXX")

# copy reusable verification library:
# LIB_FILES=($(find $SCRIPT_DIR/../reusable_verification_library -type f \( -iname \*.gh -o -iname \*.h \)))
LIB_FILES=($(find $SCRIPT_DIR/../reusable_verification_library -type f \( -iname \*.gh -o -iname \*.h  -o -iname \*.c \)))
for LIB_FILE in "${LIB_FILES[@]}"
do
    cp "$LIB_FILE" "$TMP_DIR"
done

# remove the header files containing dummy definitions as we use the NSL-specific ones instead:
rm "$TMP_DIR/protocol_specific_definitions.gh"
rm "$TMP_DIR/protocol_specific_event_params.gh"
rm "$TMP_DIR/protocol_specific_event_lemma.c"

# additional files needed for successful compilation:
cp "$VERIFAST_BIN/threading.c" "$TMP_DIR"

# copy NSL:
NSL_FILES=($(find $SCRIPT_DIR/ -type f \( -iname \*.gh -o -iname \*.h -o -iname \*.c \)))

for FILE in "${NSL_FILES[@]}"
do
    FILENAME=$(basename "$FILE")
    DEST_FILE="$TMP_DIR/$FILENAME"
    if [[ -e "$DEST_FILE" ]]
    then
        echo "File already exists: $FILE"
        exit 1
    else
        cp "$FILE" "$DEST_FILE"
    fi
done

# verify all `.c` files in the tmp folder:
C_FILES=($TMP_DIR/*.c)
C_FILES_STR=$(printf "%s " "${C_FILES[@]}")

# compile initiator and responder
gcc $C_FILES_STR -iquote $VERIFAST_BIN -lcrypto -lpthread -o $SCRIPT_DIR/nsl

rm -r $TMP_DIR
