(** Template file for Pactole *)

(* Helping typeclass resolution avoid infinite loops. *)
Typeclasses eauto := (bfs).

(* The general Pactoel framework. *)
Require Import Pactole.Setting.

(* The space in which robots evolve.  (in subdirectory Spaces/)
   Possible choices include: R, R2, Ring, ... *)
Require Import Pactole.Spaces.R2.

(* The type of spectrum.  (in subdirectory Spectra/)
   Possible choices include: multiset, set, their variants with limited radius, ... *)
Require Import Pactole.Spectra.MultisetSpectrum.

(* Optionally, you can add constraint on the model such as rigid move, or using simlarities. *)
Require Import Pactole.Models.Similarity.
Require Import Pactole.Models.Rigid.
Close Scope R_scope.


(* Define the number of robots: first the number of good ones, then the number of byzantine ones. *)
Parameter n : nat.
Axiom n_non_0 : n <> 0.
Instance MyRobots : Names := Robots (2 * n) 0.
(* Here, we have [2 * n] good robots and no byzantine ones, with [n] arbitrary but non null. *)


(* Define what the space and the state of a robot are.
   Here the state only contains the position of the robot, which is in the real plane.
   The first [R2] is the space, whereas the second one is the state (which must contain the space). *)
Instance Info : IsLocation R2 R2 := OnlyLocation.

(* What can demons choose to change of frame of reference?
   Here we use similarities. *)
Instance FC : frame_choice (Similarity.similarity R2) := FrameChoiceSimilarity.

(* What choices can demons make for the state update?
   Here they do not make any choice, hence we use [Datatypes.unit]. *)
Instance UC : update_choice Datatypes.unit := {update_choice_EqDec := unit_eqdec}.


(* Finally, define what the update funciton is. *)
Instance UpdateFun : update_function Datatypes.unit := {update := fun _ _ pt _ => pt }.
Proof. now repeat intro. Defined.

(* If you have constraints on your model, now is the time to prove them.
   Here, we prove that our update function is indeed rigid. *)
Instance Update : RigidUpdate.
Proof. split. now intros. Qed.


(* The setup is now complete, you can start working.
   Here we have a dummy example where robot never move, and thus they solve the stop problem. *)

Definition stall (e : execution) := Stream.hd e == Stream.hd (Stream.tl e).

Definition my_problem : execution -> Prop := fun e => Stream.forever stall e.

(* This is the robogram itself. *)
Definition my_robogram (s : spectrum) : R2 := origin.

(* We must prove that equal spectra gives equal destinations.
   This is non trivial as both equalities are arbitrary equivalence relations. *)
Lemma my_robogram_compat : Proper (equiv ==> equiv) my_robogram.
Proof. repeat intro. reflexivity. Qed.

(* This combines the robogram and its compatibility proof. *)
Definition full_robogram : robogram := {|
  pgm := my_robogram;
  pgm_compat := my_robogram_compat |}.

Theorem my_solution : forall d config,
  Fair d -> (* this is actually useless *)
  my_problem (execute full_robogram d config).
Proof.
Admitted.
