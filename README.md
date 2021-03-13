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

