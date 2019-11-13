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
mkdir ./package/Observations
mkdir ./package/Models
mkdir ./package/CaseStudies
mkdir ./package/CaseStudies/Convergence
mkdir ./package/CaseStudies/Gathering
mkdir ./package/CaseStudies/Gathering/InR
mkdir ./package/CaseStudies/Gathering/InR2
mkdir ./package/CaseStudies/Exploration

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

cp Observations/Definition.v Observations/MultisetObservation.v Observations/SetObservation.v Observations/LimitedMultisetObservation.v Observations/LimitedSetObservation.v ./package/Observations/

cp Models/Rigid.v Models/Flexible.v Models/Similarity.v Models/RigidFlexibleEquivalence.v Models/DiscreteGraph.v Models/ContinuousGraph.v Models/GraphEquivalence.v ./package/Models/

cp CaseStudies/Convergence/Impossibility_2G_1B.v CaseStudies/Convergence/Algorithm_noB.v ./package/CaseStudies/Convergence/

cp CaseStudies/Gathering/Definitions.v CaseStudies/Gathering/WithMultiplicity.v CaseStudies/Gathering/Impossibility.v ./package/CaseStudies/Gathering/

cp CaseStudies/Gathering/InR/Algorithm.v CaseStudies/Gathering/InR/Impossibility.v ./package/CaseStudies/Gathering/InR/

cp CaseStudies/Gathering/InR2/Algorithm.v ./package/CaseStudies/Gathering/InR2/
#Gathering/InR2/FSyncFlexNoMultAlgorithm.v Gathering/InR2/Peleg.v

cp CaseStudies/Exploration/Definitions.v CaseStudies/Exploration/ImpossibilityKDividesN.v CaseStudies/Exploration/Tower.v ./package/CaseStudies/Exploration/

# Specific to workshops/lectures
cp exercises.v ./package/

# Compile the archive to make sure it works
time make -C package -j 3

# Clean the compilation
make -C package cleanall
rm package/Makefile.conf

# Create the actual archive
tar cfz package.tgz package
