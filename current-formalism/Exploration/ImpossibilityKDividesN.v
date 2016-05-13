Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Exploration.Definitions.
Require Import Pactole.DiscreteASyncFormalism.


Set Implicit Arguments.


(** The setting is an arbitrary metric space over R. *)
Declare Module Loc : DiscreteSpace.


(** There are nG good robots and no byzantine ones. *)
Parameter nG : nat.

Module K : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End K.

(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module Defs := Definitions.ExplorationDefs(Loc)(K).
Export Defs.



(* final theorem: In the asynchronous model, if k divide n, 
   then the exploration of a n-node ring is not possible. *)

Theorem no_exploration : forall k, k < n -> k mod n = 0 -> ~ ValidSolExplorationStop r d.
Proof.

Save.
