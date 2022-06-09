AA

This repository stores the Coq code of the Pactole project,
dedicated to formal verification of mobile robotic swarm protocols.

# Overall Structure

- *Setting.v*: All you need to setup a working framework. A good starting point.
- *Util/*: Extension the to the Coq standard library that are not specific to Pactole
- *Core/*: The core the the Pactole framework, implementing the Look/Compute/Move cycle
- *Spaces/*: Spaces in which robots evolve
- *Observations/*: Types of robot views of the configuration
- *Models/*: Additional properties of some models
- *CasesStudies/*
  - *Convergence/*: Convergence of robots in the 2D Euclidean plane
  - *Gathering/*: Gathering in R or R² for various models
  - *Exploration/*: Exploration of a ring with stop
  - *Volume/*: Life line connection in the 2D Euclidean plane

# Contributing

The golden rule is that **MASTER SHOULD COMPILE AT ALL TIME** and does not
contains in-progress developments.

More precisely, development never happens on master: each topic should have
its own branch (feel free to create one if needed) and work happens there,
even when several people are involved.

Once a set of changes (e.g. a new case study) is complete and polished enough
(comments, adequate identation, no use of generated hypothesis names, etc.),
you may merge it to master by squashing its commits into meaningful pieces
(only a few, usually one may be enough) or submit a pull request.

# Fast Compiling when developing

During development you can benefit from coq's "vos/vok" generation to
speed up compilation. The only specificity of Pactole concerns
compilation of the files named xxx_Assumptions.v. This files print the
sets of assumptions used in the proofs of final lemmas in Case
studies. Compiling these files for vos/vok target would raise errors.
We provide adapted targets:

## Very fast but unsafe

make [-j] vos-nocheck

Replaces "make vos". Prefer this when developing.

### proofgeneral

For easy use of this feature you can use the auto compilation feature
of proofgeneral. menu:

menu: Coq / Auto Compilation / Compile Before Require
and then: Coq / Auto Compilation / vos compilation

Now you can transparently script in any buffer, all needed file will
be compiled quickly. Don't forget to make a big fat "make" from time
to time.

## slow, almost safe, very parallelisable

make [-j] vok-nocheck

replaces "make vok". Prefer this once a day.

## Completely safe

make [-j]

This is the only way to make a really safe compilation including all
xxx_Assumption.v. You should always do this once in a while to make
sure some universe constraints aren't failing and to check if you did
not miss an remaining axiom.
