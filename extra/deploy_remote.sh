# This script is run on the remote (plclub@eniac)
# it is launched by ./deploy.sh
REMOTE_FOLDER=website_repo_test
tar -zc -f $REMOTE_FOLDER-$(date '+%F').tar.gz $REMOTE_FOLDER
