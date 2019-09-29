#!/bin/sh

# Remove any previous archive
rm -rf ./package/ package.tgz

# Create all the required (sub-)directories
mkdir ./package
mkdir ./package/Util
mkdir ./package/Util/FSets
mkdir ./package/Util/FMaps
mkdir ./package/Util/MMultiset
mkdir ./package/Core
mkdir ./package/Spaces
mkdir ./package/Spectra
mkdir ./package/Models
mkdir ./package/Convergence
mkdir ./package/Gathering
mkdir ./package/Gathering/InR
mkdir ./package/Gathering/InR2
mkdir ./package/Exploration

# Create a fresh Makefile from the _CoqPoject
coq_makefile -f _CoqProject -o Makefile

# Copy files into each directory
cp Util/FSets/FSetInterface.v Util/FSets/FSetFacts.v Util/FSets/FSetList.v ./package/Util/FSets/

cp Util/FMaps/FMapInterface.v Util/FMaps/FMapFacts.v Util/FMaps/FMapList.v ./package/Util/FMaps/

cp Util/MMultiset/Preliminary.v Util/MMultiset/MMultisetInterface.v Util/MMultiset/MMultisetFacts.v Util/MMultiset/MMultisetWMap.v Util/MMultiset/MMultisetExtraOps.v ./package/Util/MMultiset/

cp Util/Coqlib.v Util/Preliminary.v Util/SetoidDefs.v Util/NumberComplements.v Util/ListComplements.v Util/Ratio.v Util/Lexprod.v Util/Stream.v Util/Bijection.v ./package/Util/

cp Core/Robots.v Core/RobotInfo.v Core/Configurations.v Core/Formalism.v ./package/Core/

cp Setting.v Makefile _CoqProject ./package/

cp Spaces/RealVectorSpace.v Spaces/RealMetricSpace.v Spaces/RealNormedSpace.v Spaces/EuclideanSpace.v Spaces/Similarity.v Spaces/R.v Spaces/R2.v Spaces/Graph.v Spaces/Ring.v Spaces/Grid.v Spaces/Isomorphism.v ./package/Spaces/

cp Spectra/Definition.v Spectra/MultisetSpectrum.v Spectra/SetSpectrum.v Spectra/LimitedMultisetSpectrum.v Spectra/LimitedSetSpectrum.v ./package/Spectra/

cp Models/Rigid.v Models/Flexible.v Models/Similarity.v Models/RigidFlexibleEquivalence.v Models/DiscreteGraph.v Models/ContinuousGraph.v Models/GraphEquivalence.v ./package/Models/

cp Convergence/Impossibility_2G_1B.v Convergence/Algorithm_noB.v ./package/Convergence/

cp Gathering/Definitions.v Gathering/WithMultiplicity.v Gathering/Impossibility.v ./package/Gathering/

cp Gathering/InR/Algorithm.v Gathering/InR/Impossibility.v ./package/Gathering/InR/

cp Gathering/InR2/Algorithm.v ./package/Gathering/InR2/
#Gathering/InR2/FSyncFlexNoMultAlgorithm.v Gathering/InR2/Peleg.v

cp Exploration/Definitions.v Exploration/ImpossibilityKDividesN.v Exploration/Tower.v ./package/Exploration/

# Specific to the MoRoVer'17 and FuReTherMoRe'19 workshops
cp Template.v script.bak ./package/

# Compile the archive to make sure it works
make -C package -j 3 \
  Gathering/InR/Algorithm.vo \
  Gathering/InR/Impossibility.vo \
  Gathering/InR2/Algorithm.vo \
  Convergence/Impossibility_2G_1B.vo \
  Exploration/ImpossibilityKDividesN.vo \
  Exploration/Tower.v
# Gathering/InR2/FSyncFlexNoMultAlgorithm.vo

# Clean the compilation
make -C package cleanall
rm package/Makefile.conf

# Create the actual archive
tar cfz package.tgz package
