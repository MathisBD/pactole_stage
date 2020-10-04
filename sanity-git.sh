#!/bin/sh

AUXFILES=".allvfiles .trackedfiles .untrackedvfiles .unfoundvfiles"

# Removing tolerated untracked files.
# FIXME: Shouldn't we remove them from archive until we need them
# again?
# this is a regexp, typically:
# TOLERATED="Foo/Bar/toto.v\\|Baz/titi.v"
TOLERATED="Util/FSets/OrderedType.v"

find . -name "*.v" | sed -e 's/\.\///' | grep -v $TOLERATED > .allvfiles

grep -v "^-\\|^[[:space:]]*#\\|^[[:space:]]*$\\|~$" _CoqProject > .trackedfiles

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

if [ "$EXITCODE2" -eq 1 -a "$EXITCODE1" -eq 1 ];
then
    echo Everything seems find
    EXITCODE=0
fi

# rm .trackedfiles

rm -f $AUXFILES

exit $EXITCODE
