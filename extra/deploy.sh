#! /bin/bash
# Local folder with static site contents
OUTPUT_DIR=_site/
# Remote user and host to connect to
PLCLUB_ACCOUNT=plclub@eniac
# Location of folder relative to remote user's home directory
# This variable may also need to be set in ./deploy_remote.sh
REMOTE_FOLDER=html/
# Script to run on remote e.g. to make a backup before syncing
# this should be relative to the top-level repo folder
REMOTE_SCRIPT=./extra/deploy_remote.sh

# Synchronize our local folder to the remote
rsync -vr $OUTPUT_DIR $PLCLUB_ACCOUNT:$REMOTE_FOLDER

# Run the remote helper script
ssh $PLCLUB_ACCOUNT "bash -s" < $REMOTE_SCRIPT
