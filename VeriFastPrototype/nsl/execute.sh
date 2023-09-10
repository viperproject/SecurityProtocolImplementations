#!/bin/bash

# exit when any command fails
set -e

SCRIPT_DIR=$(dirname "$0")

source $SCRIPT_DIR/compile.sh

function initiator() {
    source $SCRIPT_DIR/runInitiator.sh
}

function responder() {
    source $SCRIPT_DIR/runResponder.sh
}

# execute initiator and responder in parallel and wait until they are done:
RESPONDER_TEMP_FILE=$(mktemp)
responder > $RESPONDER_TEMP_FILE &
# wait for 1 sec to make sure that responder has started up
sleep 1
INITIATOR_TEMP_FILE=$(mktemp)
initiator > $INITIATOR_TEMP_FILE &
wait

# print initiator and responder output:
echo -e "\n\n======== Initiator Output ========"
cat $INITIATOR_TEMP_FILE

echo -e "\n\n======== Responder Output ========"
cat $RESPONDER_TEMP_FILE

rm $INITIATOR_TEMP_FILE
rm $RESPONDER_TEMP_FILE
