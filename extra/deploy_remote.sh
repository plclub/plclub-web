# This script is run on the remote (plclub@eniac)
# it is launched by ./deploy.sh
REMOTE_FOLDER=html/
cd $REMOTE_FOLDER
git add .
git commit -m "Automated commit"
