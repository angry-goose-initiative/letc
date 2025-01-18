#!/usr/bin/env bash
#Useful: https://vi.stackexchange.com/questions/5619/generate-ctags-for-bash-variables
REPO_ROOT=`git rev-parse --show-toplevel`

cd $REPO_ROOT
echo "Generating $REPO_ROOT/tags"

ctags -R --guess-language-eagerly --languages=all --kinds-all=* --regex-sh='/^[ \t]*(local)?[ \t]*([A-Za-z0-9_-]+)=/\2/v,variable,variables/' --exclude=results .
