Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteGraphFormalism.
Require Import Pactole.AtomicGraphFormalism.


Print Module Location.

Module GraphEquivalence (N : Size)(Names : Robots(N))(Spect : Spectrum(Location)(N))
                        (Common : CommonFormalism.Sig(Location)(N)(Spect)).

Module Atom := AtomicGraphFormalism.Make(N)(Names)(Spect)(Common).
Module Disc := DiscreteGraphFormalism.Make(N)(Names)(Spect)(Common).
