Require Import Utf8_core.
Require Import SetoidList.
Require Import MSets.
Require Import Rbase.
Require Import Preliminary.
Require Import Robots.
Require Import Positions.
Require MultisetSpectrum.


Module Type Radius.
  Parameter radius : R.
End Radius.


Module Make(Loc : MetricSpace)(N : Size)(R : Radius) <: Spectrum (Loc)(N).

Module M := MultisetSpectrum.Make(Loc)(N).
Module Names := M.Names.
Module Pos := M.Pos.

Notation "m1  [=]  m2" := (M.eq m1 m2) (at level 70).


(** Building a spectrum from a position *)

(** Inclusion is not possible because M has the same signature and we want to restrict the functions. *)
Definition t := M.t.
Definition eq := M.eq.
Definition eq_equiv := M.eq_equiv.
Definition eq_dec := M.eq_dec.
Definition In := M.In.


Definition from_config pos : M.t :=
  M.M.filter (fun x _ => Rle_bool (Loc.dist x Loc.origin) R.radius) (M.multiset (Pos.list pos)).

Instance from_config_compat : Proper (Pos.eq ==> eq) from_config.
Proof.
intros pos1 pos2 Hpos x. unfold from_config.
f_equiv. apply M.M.filter_compat, M.multiset_compat, eqlistA_PermutationA_subrelation, Pos.list_compat; trivial.
intros ? ? Heq ? ? ?. subst. rewrite Heq. reflexivity.
Qed.

Definition is_ok s pos := forall l,
  M.multiplicity l s = if Rle_dec (Loc.dist l Loc.origin) R.radius
                       then countA_occ _ Loc.eq_dec l (Pos.list pos) else 0.

Theorem from_config_spec : forall pos, is_ok (from_config pos) pos.
Proof.
unfold from_config, is_ok, Rle_bool. intros pos l. rewrite M.filter_spec.
- destruct (Rle_dec (Loc.dist l Loc.origin)); trivial. apply M.from_config_spec.
- intros x y Heq _ _ _. destruct (Rle_dec (Loc.dist x Loc.origin) R.radius),
                                          (Rle_dec (Loc.dist y Loc.origin) R.radius);
   reflexivity || rewrite Heq in *; contradiction.
Qed.

End Make.
