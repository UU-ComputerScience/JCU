./stop.sh
git checkout -f -- .
git pull origin master
brunch build ./resources/static/brunch
make deps
cabal install --disable-documentation
./uglify.sh