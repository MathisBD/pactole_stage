#!/bin/sh

rm -rf ./package
mkdir ./package
mkdir ./package/MMultiset

cp -r MMultiset/Preliminary.v MMultiset/MMultisetInterface.v MMultiset/MMultisetFacts.v MMultiset/MMultisetMap.v ./package/MMultiset/

cp Preliminary.v Robots.v Positions.v FormalismRd.v SortingR.v MultisetSpectrum.v RDVinR.v makefile _CoqProject ./package/

make -C package -j 3 RDVinR.vo
make -C package clean
rm -f package/.*.aux
tar cvfz package.tgz package 
