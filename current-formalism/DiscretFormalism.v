Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import ZArith.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Pactole.CommonRealFormalism.



Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].


Module Make (Location : RealMetricSpace)(N : Size)(Spect : Spectrum(Location)(N))
            (Common : CommonRealFormalism.Sig(Location)(N)(Spect)).

Import Common.
Notation "s ⁻¹" := (Sim.inverse s) (at level 99).

Inductive State: rdy2Look:bool | rdy2compute:bool | rdy2Move.

(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
Record  demonic_action := {

   step := (Names.ident -> State) -> Names.ident -> option (State -> State).
  (* Le demon prend une foction qui a chaque robot donne son état, les robots, et dit si un 
     robot change d'état ou non. C'est le modele assynchrone.*)