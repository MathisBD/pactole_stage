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
Require Import Pactole.Positions.
Require Import Pactole.FormalismRd.



Module RigidFormalism (Location : MetricSpace)(N : Size)(Spect : Spectrum(Location)(N)).

Module Names := Spect.Names.
Module Pos := Spect.Pos.


Lemma the_chosen_one {A} eqA (HeqA : Reflexive eqA) :
  forall f : Location.t -> A, Proper (Location.eq ==> eqA) f ->
  forall δ pos local_target,
  let chosen_target := Location.mul 1%R local_target in
  eqA (f (if Rle_bool δ (Location.dist chosen_target pos) then chosen_target else local_target))
      (f local_target).
Proof. intros f Hf ? ? ?. simpl. destruct Rle_bool; apply Hf; try rewrite Location.mul_one; reflexivity. Qed.


