#!/bin/sh

## This script deploy Cerberus UI and send it to the server
## PS: only works in my machine due to SSH credentials

echo "Deploying webpack..."
npm run deploy

echo "Copying files to server..."
scp dist/main.bundle.js server@svr-pes20-cerberus.cl.cam.ac.uk:/local/data/server/public
scp dist/main.bundle.js.gz server@svr-pes20-cerberus.cl.cam.ac.uk:/local/data/server/public
scp dist/style.bundle.css server@svr-pes20-cerberus.cl.cam.ac.uk:/local/data/server/public
scp dist/style.bundle.css.gz server@svr-pes20-cerberus.cl.cam.ac.uk:/local/data/server/public

echo "Deleting local files..."
rm -v dist/main.bundle.js dist/main.bundle.js.gz
rm -v dist/style.bundle.css dist/style.bundle.css.gz
