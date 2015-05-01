Require Import Utf8_core.
Require Import SetoidList.
Require Import Rbase.
Require Import Preliminary.
Require Import Robots.
Require Import Positions.
Require SetSpectrum.


Module Type Radius.
  Parameter radius : R.
End Radius.


Module Make(Loc : MetricSpace)(N : Size)(R : Radius) <: Spectrum (Loc)(N).

Module M := SetSpectrum.Make(Loc)(N).
Module Names := M.Names.
Module Pos := M.Pos.

Notation "m1  ≡  m2" := (M.eq m1 m2) (at level 70).
Notation "m1  [=]  m2" := (M.eq m1 m2) (at level 70, only parsing).


(** Building a spectrum from a position *)

(** Inclusion is not possible because M has the same signature and we want to restrict the functions. *)
Definition t := M.t.
Definition eq := M.eq.
Definition eq_equiv := M.eq_equiv.
Definition eq_dec := M.eq_dec.
Definition In := M.In.


Definition from_config pos : M.t :=
  M.M.filter (fun x => Rle_bool (Loc.dist x Loc.origin) R.radius) (M.set (Pos.list pos)).

Instance from_config_compat : Proper (Pos.eq ==> eq) from_config.
Proof.
intros pos1 pos2 Hpos x. unfold from_config.
f_equiv. apply M.MProp.MP.Dec.F.filter_ext.
+ intros y z Hyz. rewrite Hyz. reflexivity.
+ intro. reflexivity.
+ now apply M.set_compat, eqlistA_PermutationA_subrelation, Pos.list_compat.
Qed.

Definition is_ok s pos := forall l,
  In l s <-> (Loc.dist l Loc.origin <= R.radius)%R /\ exists id : Names.ident, Loc.eq l (pos id).

Theorem from_config_spec : forall pos, is_ok (from_config pos) pos.
Proof.
unfold from_config, is_ok. intros. rewrite M.M.filter_spec, Rle_bool_spec.
- rewrite M.set_spec, Pos.list_spec. intuition.
- intros x y Hxy. now rewrite Hxy.
Qed.

End Make.
