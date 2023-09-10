#!/bin/bash

# exit when any command fails
set -e

SCRIPT_DIR=$(dirname "$0")

VERIFAST="verifast"

# copy files in this directory and all `.h` files from the library
# to some temporary directory to then verify them:

# try linux and fall-back to macOS:
TMP_DIR=$(mktemp -d -t verification-XXXXXXXXXX -p "$SCRIPT_DIR/.." 2>/dev/null || mktemp -d "$SCRIPT_DIR/../verification-XXXXXXXXXX")

# copy reusable verification library:
LIB_FILES=($(find $SCRIPT_DIR/../reusable_verification_library -type f \( -iname \*.gh -o -iname \*.h \)))
for LIB_FILE in "${LIB_FILES[@]}"
do
    cp "$LIB_FILE" "$TMP_DIR"
done

# remove the header files containing dummy definitions as we use the NSL-specific ones instead:
rm "$TMP_DIR/protocol_specific_definitions.gh"
rm "$TMP_DIR/protocol_specific_event_params.gh"

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

# verify all `.c` files in the tmp folder except `main.c` and `messages.c`,
# which are trusted and thus should not be verified:
C_FILES=($(find $TMP_DIR -type f \( -iname "*.c" ! -iname "main.c" ! -iname "messages.c" \) | sort))

# iterate over each file and verify it:
for FILE in "${C_FILES[@]}"
do
    $VERIFAST -allow_dead_code -shared -D PROTOCOL_SPECIFIC_VERIFICATION -c $FILE
done

rm -r $TMP_DIR
