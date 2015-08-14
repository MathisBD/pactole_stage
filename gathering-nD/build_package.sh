#!/bin/sh

rm -rf ./package
mkdir ./package
mkdir ./package/MMultiset
mkdir ./package/GatheringinR

cp -r MMultiset/Preliminary.v MMultiset/MMultisetInterface.v MMultiset/MMultisetFacts.v MMultiset/MMultisetWMap.v MMultiset/MMultisetMap.v ./package/MMultiset/

cp Preliminary.v Robots.v Positions.v CommonFormalism.v FlexibleFormalism.v RigidFormalism.v MultisetSpectrum.v makefile _CoqProject ./package/

cp GatheringinR/SortingR.v GatheringinR/Definitions.v GatheringinR/Algorithm.v GatheringinR/Impossibility.v ./package/GatheringinR/

make -C package -j 3 GatheringinR/Algorithm.vo GatheringinR/Impossibility.vo
make -C package clean
rm -f package/.*.aux
tar cvfz package.tgz package 
