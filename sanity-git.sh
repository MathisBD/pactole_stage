#!/bin/sh

# This script checks that pactole archive is in a correct state:
# - no coq file should be there but not cited in _CoqProject (untrackedvfiles).
# - no file cited in _CoqProject should be absent (unfoundvfiles).
#
# NOTE: we do note check that compilation succeeds. It is too long and
# should be checked by CI anyway..

# To enable this as a pre-commit check, do (assuming you do NOT
# already have a pre-commit script in .git/hooks):
#
# cp sanity-git.sh .git/hooks/pre-commit
# chmod u+x .git/hooks/pre-commit
#
# Note that you will need to do that on each local clone you have, as
# it is not versionized.

AUXFILES=".allvfiles .trackedfiles .untrackedvfiles .unfoundvfiles"

# Removing tolerated untracked files.
# FIXME: Shouldn't we remove them from archive until we need them
# again?
# this is a regexp, typically:
# TOLERATED="Foo/Bar/toto.v\\|Baz/titi.v"
TOLERATED="Util/FSets/OrderedType.v"

find . -name "*.v" | sed -e 's/\.\///' | grep -v "\.#\\|*~" | grep -v $TOLERATED > .allvfiles

grep -v "^-\\|^[[:space:]]*#\\|^[[:space:]]*$" _CoqProject > .trackedfiles

grep -v -f .trackedfiles .allvfiles > .untrackedvfiles
EXITCODE1=$?
grep -v -f .allvfiles .trackedfiles  > .unfoundvfiles
EXITCODE2=$?

if [ "$EXITCODE1" -eq 0 ]
then
    echo "#################################"
    echo "* WARNING! The .v files below are not listed in _CoqProject"
    echo
    cat .untrackedvfiles
    echo
    echo "** Suspect commented lines..."
    echo
    grep -v "^-\\|^[[:space:]]*$\\|~$" _CoqProject | grep "^[[:space:]]*#" | grep "\.v$"
    echo
    echo "#################################"
    echo
    EXITCODE=1
fi

if [ "$EXITCODE2" -eq 0 ];
then
    echo "#################################"
    echo "* WARNING! The .v files above are listed in _CoqProject but were not found"
    echo
    cat .unfoundvfiles
    echo
    echo "#################################"
    EXITCODE=1
fi

RED='\033[0;31m'
NC='\033[0m' # No Color

if [ "$EXITCODE2" -eq 1 -a "$EXITCODE1" -eq 1 ];
then
    EXITCODE=0
    echo "Sanity check OK"
else
    echo "${RED}Commit was aborted for the reason described above.${NC}"
    echo
    echo "The_coqProject seems to be outdated wrt actual files in your"
    echo "working directory."
    echo
    echo "Please fix the problem above or use \"git commit --no-verify.\""
    echo "if you know what you are doing."
    echo
fi

rm -f $AUXFILES

exit $EXITCODE
