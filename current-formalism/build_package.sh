#!/bin/sh

rm -rf ./package
mkdir ./package
mkdir ./package/MMaps
mkdir ./package/MMultiset
mkdir ./package/Convergence
mkdir ./package/Gathering
mkdir ./package/Gathering/InR
mkdir ./package/Gathering/InR2

coq_makefile -f _CoqProject -o makefile

cp -r MMaps/MMapInterface.v MMaps/MMapFacts.v MMaps/MMapWeakList.v ./package/MMaps/

cp -r MMultiset/Preliminary.v MMultiset/MMultisetInterface.v MMultiset/MMultisetFacts.v MMultiset/MMultisetWMap.v MMultiset/MMultisetExtraOps.v ./package/MMultiset/

cp Preliminary.v Lexprod.v Robots.v Configurations.v Streams.v CommonFormalism.v CommonRealFormalism.v RigidFormalism.v FlexibleFormalism.v MultisetSpectrum.v SetSpectrum.v Similarity.v makefile _CoqProject ./package/

cp Convergence/Impossibility_2G_1B.v ./package/Convergence/

cp Gathering/Definitions.v Gathering/FlexDefinitions.v ./package/Gathering/

cp Gathering/InR/Rcomplements.v Gathering/InR/Algorithm.v Gathering/InR/Impossibility.v ./package/Gathering/InR/

cp Gathering/InR2/R2geometry.v Gathering/InR2/Algorithm.v Gathering/InR2/FSyncFlexNoMultAlgorithm.v ./package/Gathering/InR2/

make -C package -j 3 Gathering/InR/Algorithm.vo Gathering/InR/Impossibility.vo Gathering/InR2/Algorithm.vo Gathering/InR2/FSyncFlexNoMultAlgorithm.vo Convergence/Impossibility_2G_1B.vo
make -C package clean
rm -f package/.*.aux package/*/.*.aux package/*/*/.*.aux
tar cvfz package.tgz package
