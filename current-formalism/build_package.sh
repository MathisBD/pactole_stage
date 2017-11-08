#!/bin/sh

rm -rf ./package
mkdir ./package
mkdir ./package/Util
mkdir ./package/Util/FSets
mkdir ./package/Util/FMaps
mkdir ./package/Util/MMultiset
mkdir ./package/Spaces
mkdir ./package/Spectra
mkdir ./package/Models
mkdir ./package/Convergence
mkdir ./package/Gathering
mkdir ./package/Gathering/InR
mkdir ./package/Gathering/InR2
#mkdir ./package/Exploration

coq_makefile -f _CoqProject -o Makefile

cp Util/FSets/OrderedType.v Util/FSets/FSetInterface.v Util/FSets/FSetFacts.v Util/FSets/FSetList.v ./package/Util/FSets/

cp Util/FMaps/FMapInterface.v Util/FMaps/FMapFacts.v Util/FMaps/FMapList.v ./package/Util/FMaps/

cp Util/MMultiset/Preliminary.v Util/MMultiset/MMultisetInterface.v Util/MMultiset/MMultisetFacts.v Util/MMultiset/MMultisetWMap.v Util/MMultiset/MMultisetExtraOps.v ./package/Util/MMultiset/

cp Util/Preliminary.v Util/Lexprod.v Util/Stream.v Util/Bijection.v ./package/Util/

cp  Robots.v RobotInfo.v Configurations.v CommonFormalism.v Setting.v Makefile _CoqProject ./package/

cp Spaces/RealMetricSpace.v Spaces/Similarity.v Spaces/R.v Spaces/R2.v Spaces/Graph.v Spaces/Isomorphism.v ./package/Spaces

cp Spectra/Definition.v Spectra/MultisetSpectrum.v Spectra/SetSpectrum.v Spectra/LimitedMultisetSpectrum.v Spectra/LimitedSetSpectrum.v ./package/Spectra

cp Models/Rigid.v Models/DiscreteGraph.v Models/Similarity.v ./package/Models/
# Models/Flexible.v Models/RigidFlexibleEquivalence.v

cp Convergence/Impossibility_2G_1B.v Convergence/Algorithm_noB.v ./package/Convergence/

cp Gathering/Definitions.v ./package/Gathering/

cp Gathering/InR/Algorithm.v Gathering/InR/Impossibility.v ./package/Gathering/InR/

cp Gathering/InR2/Algorithm.v ./package/Gathering/InR2/
# Gathering/InR2/FSyncFlexNoMultAlgorithm.v

## Specific to the MoRoVer workshop
cp Template.v script.bak ./package/

make -C package -j 3 Gathering/InR/Algorithm.vo Gathering/InR/Impossibility.vo Gathering/InR2/Algorithm.vo Convergence/Impossibility_2G_1B.vo
# Gathering/InR2/FSyncFlexNoMultAlgorithm.vo
make -C package cleanall
rm -f package/.*.aux package/*/.*.aux package/*/*/.*.aux
tar cvfz package.tgz package
