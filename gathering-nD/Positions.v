(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Equalities.
Require Import SetoidList.
Require Import Reals.
Require Import Pactole.Preliminary.
Require Import Robots.


(** * Positions *)

(** This module signature represents the space in which robots evolve.
    It can be anything as long as it is a non-trivial real metric space.

    The framework for robots should be more general as for instance a ring is not a metric space.
    It seems that we only need a decidable type for locations and a notion of distance.  *)
Module Type RealMetricSpaceDef <: DecidableType.
  Parameter t : Type.
  Parameter origin : t.
  Parameter eq : t -> t -> Prop.
  Parameter dist : t -> t -> R.
  Parameter eq_dec : forall x y, {eq x y} + {~eq x y}.
  
  Parameter add : t -> t -> t.
  Parameter mul : R -> t -> t. (* underlying field is R *)
  Parameter opp : t -> t.
  
  Declare Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Declare Instance mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
  Declare Instance opp_compat : Proper (eq ==> eq) opp.
  
  Parameter eq_equiv : Equivalence eq.
  Parameter dist_defined : forall x y, dist x y = 0%R <-> eq x y.
  Parameter dist_sym : forall y x, dist x y = dist y x.
  Parameter triang_ineq : forall x y z, (dist x z <= dist x y + dist y z)%R.
  
  Parameter add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Parameter add_comm : forall u v, eq (add u v) (add v u).
  Parameter add_origin : forall u, eq (add u origin) u.
  Parameter add_opp : forall u, eq (add u (opp u)) origin.
  Parameter add_distr : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Parameter mult_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Parameter plus_morph : forall a b u, eq (add (mul a u) (mul b u)) (mul (a + b) u).
  
  (* TODO: add the missing properties *)
  Parameter mul_1 : forall u, eq (mul 1 u) u.
  Parameter non_trivial : exists u v, ~eq u v.
End RealMetricSpaceDef.

Module Type RealMetricSpace.
  Include RealMetricSpaceDef.
  
  Declare Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Parameter dist_pos : forall x y, (0 <= dist x y)%R.
  Parameter mul_opp : forall a u, eq (mul a (opp u)) (opp (mul a u)).
  Parameter add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Parameter add_reg_r : forall w u v, eq (add u w) (add v w) -> eq u v.
  Parameter opp_origin : eq (opp origin) origin.
  Parameter opp_opp : forall u, eq (opp (opp u)) u.
  Parameter mul_0 : forall u, eq (mul 0 u) origin.
  Parameter mul_origin : forall a, eq (mul a origin) origin.
  Parameter mul_reg_l : forall k u v, k <> 0%R -> eq (mul k u) (mul k v) -> eq u v.
  Parameter mul_reg_r : forall k k' u, ~eq u origin -> eq (mul k u) (mul k' u) -> k = k'.
  Parameter minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).

  Definition middle u v := mul (1/2)%R (add u v).
End RealMetricSpace.


Module MakeRealMetricSpace (Def : RealMetricSpaceDef) : RealMetricSpace
    with Definition t := Def.t
    with Definition eq := Def.eq
    with Definition eq_dec := Def.eq_dec
    with Definition origin := Def.origin
    with Definition dist := Def.dist
    with Definition add := Def.add
    with Definition mul := Def.mul
    with Definition opp := Def.opp.
  
  Include Def.

  (** Proofs of two derivable properties about MetricSpace *)
  Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Proof.
  intros x x' Hx y y' Hy. apply Rle_antisym.
  + replace (dist x' y') with (0 + dist x' y' + 0)%R by ring. symmetry in Hy.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply triang_ineq.
    rewrite Rplus_assoc. apply Rplus_le_compat_l, triang_ineq.
  + replace (dist x y) with (0 + dist x y + 0)%R by ring. symmetry in Hx.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply triang_ineq.
    rewrite Rplus_assoc. apply Rplus_le_compat_l, triang_ineq.
  Qed.
  
  Lemma dist_pos : forall x y, (0 <= dist x y)%R.
  Proof.
  intros x y. apply Rmult_le_reg_l with 2%R.
  + apply Rlt_R0_R2.
  + do 2 rewrite double. rewrite Rplus_0_r.
    assert (Hx : eq x x) by reflexivity. rewrite <- dist_defined in Hx. rewrite <- Hx.
    setoid_rewrite dist_sym at 3. apply triang_ineq.
  Qed.
  
  Lemma add_reg_r : forall w u v, eq (add u w) (add v w) -> eq u v.
  Proof.
  intros w u v Heq. setoid_rewrite <- add_origin.
  now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
  Qed.
  
  Lemma add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Proof. setoid_rewrite add_comm. apply add_reg_r. Qed.
  
  Lemma opp_origin : eq (opp origin) origin.
  Proof. apply (add_reg_r origin). now rewrite add_comm, add_opp, add_origin. Qed.
  
  Lemma opp_opp : forall u, eq (opp (opp u)) u.
  Proof. intro u. apply (add_reg_l (opp u)). now rewrite add_opp, add_comm, add_opp. Qed.
  
  Lemma mul_0 : forall u, eq (mul 0 u) origin.
  Proof.
  intro u. apply (add_reg_l u).
  rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite plus_morph.
  ring_simplify (1 + 0)%R. now rewrite mul_1.
  Qed.
  
  Lemma minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).
  Proof.
  intros k u. apply (add_reg_l (mul k u)).
  rewrite add_opp. rewrite plus_morph. ring_simplify (k + - k)%R.
  apply mul_0.
  Qed.
  
  Lemma mul_origin : forall a, eq (mul a origin) origin.
  Proof. Admitted.
  
  Lemma mul_opp : forall a u, eq (mul a (opp u)) (opp (mul a u)).
  Proof.
  intros a u. apply (add_reg_l (mul a u)). rewrite <- add_distr.
  setoid_rewrite add_opp. now rewrite mul_origin.
  Qed.
  
  Lemma mul_reg_l : forall k u v, k <> 0%R -> eq (mul k u) (mul k v) -> eq u v.
  Proof.
  intros k u v Hk Heq. setoid_rewrite <- mul_1.
  replace 1%R with (/k * k)%R by now field.
  setoid_rewrite <- mult_morph. rewrite Heq.
  reflexivity.
  Qed.
  
  Lemma mul_reg_r : forall k k' u, ~eq u origin -> eq (mul k u) (mul k' u) -> k = k'.
  Proof.
  intros k k' u Hu Heq. destruct (Rdec k k') as [| Hneq]; trivial.
  assert (Heq0 : eq (mul (k -k') u)  origin).
  { unfold Rminus. rewrite <- plus_morph, minus_morph, Heq. apply add_opp. }
  elim Hu. rewrite <- mul_1. rewrite <- (Rinv_l (k - k')).
  - rewrite <- mult_morph. rewrite Heq0. apply mul_origin.
  - intro Habs. apply Hneq. now apply Rminus_diag_uniq.
  Qed.
  
  Definition middle u v := mul (1/2)%R (add u v).
  
End MakeRealMetricSpace.


Module Type Position(Location : DecidableType)(N : Size)(Names : Robots(N)).
  Definition t := Names.ident -> Location.t.
  Definition eq pos₁ pos₂ := forall id : Names.ident, Location.eq (pos₁ id) (pos₂ id).
  Declare Instance eq_equiv : Equivalence eq.
  Declare Instance eq_bisim : Bisimulation t.
  Declare Instance eq_subrelation : subrelation eq (Logic.eq ==> Location.eq)%signature.
  
  Definition map (f : Location.t -> Location.t) (pos : t) := fun id => f (pos id).
  Declare Instance map_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) map.
  
  Parameter Gpos : t -> list Location.t.
  Parameter Bpos : t -> list Location.t.
  Parameter list : t -> list Location.t.
  Declare Instance Gpos_compat : Proper (eq ==> eqlistA Location.eq) Gpos.
  Declare Instance Bpos_compat : Proper (eq ==> eqlistA Location.eq) Bpos.
  Declare Instance list_compat : Proper (eq ==> eqlistA Location.eq) list.
  
  Parameter Gpos_spec : forall pos, Gpos pos = List.map (fun g => pos (Good g)) Names.Gnames.
  Parameter Bpos_spec : forall pos, Bpos pos = List.map (fun g => pos (Byz g)) Names.Bnames.
  Parameter list_spec : forall pos, list pos = List.map pos Names.names.

  Parameter Gpos_InA : forall l pos, InA Location.eq l (Gpos pos) <-> exists g, Location.eq l (pos (Good g)).
  Parameter Bpos_InA : forall l pos, InA Location.eq l (Bpos pos) <-> exists b, Location.eq l (pos (Byz b)).
  Parameter list_InA : forall l pos, InA Location.eq l (list pos) <-> exists id, Location.eq l (pos id).
  
  Parameter Gpos_length : forall pos, length (Gpos pos) = N.nG.
  Parameter Bpos_length : forall pos, length (Bpos pos) = N.nB.
  Parameter list_length : forall pos, length (list pos) = N.nG + N.nB.
  
  Parameter list_map : forall f, Proper (Location.eq ==> Location.eq) f -> 
    forall pos, list (map f pos) = List.map f (list pos).
  Parameter map_merge : forall f g, Proper (Location.eq ==> Location.eq) f ->
    Proper (Location.eq ==> Location.eq) g ->
    forall pos, eq (map g (map f pos)) (map (fun x => g (f x)) pos).
  Parameter map_id : forall pos, eq (map Datatypes.id pos) pos.
End Position.


Module Make(Location : DecidableType)(N : Size)(Names : Robots(N)) : Position(Location)(N)(Names)
  with Definition t := Names.ident -> Location.t.

(** A position is a mapping from identifiers to locations.  Equality is extensional. *)
Definition t := Names.ident -> Location.t.
Definition eq (pos₁ pos₂ : t) : Prop := forall id, Location.eq (pos₁ id) (pos₂ id).

Instance eq_equiv : Equivalence eq.
Proof. split.
+ intros pos x. reflexivity.
+ intros d1 d2 H r. symmetry. apply H.
+ intros d1 d2 d3 H12 H23 x. transitivity (d2 x); auto.
Qed.

Instance eq_bisim : Bisimulation t.
Proof. exists eq. apply eq_equiv. Defined.

Instance eq_subrelation : subrelation eq (Logic.eq ==> Location.eq)%signature.
Proof. intros ? ? Hpos ? id ?. subst. apply Hpos. Qed.

(** Pointwise mapping of a function on a position *)
Definition map (f : Location.t -> Location.t) (pos : t) := fun id => f (pos id).

Instance map_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) map.
Proof. intros f g Hfg ? ? Hpos id. unfold map. apply Hfg, Hpos. Qed.

(** Positions seen as lists *)
Definition Gpos (pos : t) := Names.Internals.fin_map (fun g => pos (Good g)).
Definition Bpos (pos : t) := Names.Internals.fin_map (fun b => pos (Byz b)).
Definition list pos := Gpos pos ++ Bpos pos.

Instance Gpos_compat : Proper (eq ==> eqlistA Location.eq) Gpos.
Proof. repeat intro. unfold Gpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance Bpos_compat : Proper (eq ==> eqlistA Location.eq) Bpos.
Proof. repeat intro. unfold Bpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance list_compat : Proper (eq ==> eqlistA Location.eq) list.
Proof. repeat intro. unfold list. now apply (eqlistA_app _); apply Gpos_compat || apply Bpos_compat. Qed.

Lemma Gpos_spec : forall pos, Gpos pos = List.map (fun g => pos (Good g)) Names.Gnames.
Proof. intros. unfold Gpos, Names.Gnames, Names.Internals.Gnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma Bpos_spec : forall pos, Bpos pos = List.map (fun g => pos (Byz g)) Names.Bnames.
Proof. intros. unfold Bpos, Names.Bnames, Names.Internals.Bnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma list_spec : forall pos, list pos = List.map pos Names.names.
Proof.
intros. unfold list. unfold Names.names, Names.Internals.names.
rewrite map_app, Gpos_spec, Bpos_spec. now do 2 rewrite map_map.
Qed.

Lemma Gpos_InA : forall l pos, InA Location.eq l (Gpos pos) <-> exists g, Location.eq l (pos (Good g)).
Proof. intros. unfold Gpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma Bpos_InA : forall l pos, InA Location.eq l (Bpos pos) <-> exists b, Location.eq l (pos (Byz b)).
Proof. intros. unfold Bpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma list_InA : forall l pos, InA Location.eq l (list pos) <-> exists id, Location.eq l (pos id).
Proof.
intros. unfold list. rewrite (InA_app_iff _). split; intro Hin.
+ destruct Hin as [Hin | Hin]; rewrite Gpos_InA in Hin || rewrite Bpos_InA in Hin; destruct Hin; eauto.
+ rewrite Gpos_InA, Bpos_InA. destruct Hin as [[g | b] Hin]; eauto.
Qed.

Lemma Gpos_length : forall pos, length (Gpos pos) = N.nG.
Proof. intro. unfold Gpos. apply Names.Internals.fin_map_length. Qed.

Lemma Bpos_length : forall pos, length (Bpos pos) = N.nB.
Proof. intro. unfold Bpos. apply Names.Internals.fin_map_length. Qed.

Lemma list_length : forall pos, length (list pos) = N.nG + N.nB.
Proof. intro. unfold list. now rewrite app_length, Gpos_length, Bpos_length. Qed.

Lemma list_map : forall f, Proper (Location.eq ==> Location.eq) f -> 
  forall pos, list (map f pos) = List.map f (list pos).
Proof.
intros f Hf pos. unfold list, map, Gpos, Bpos.
repeat rewrite Names.Internals.map_fin_map. rewrite List.map_app. reflexivity.
Qed.

Lemma map_merge : forall f g, Proper (Location.eq ==> Location.eq) f -> Proper (Location.eq ==> Location.eq) g ->
  forall pos, eq (map g (map f pos)) (map (fun x => g (f x)) pos).
Proof. repeat intro. reflexivity. Qed.

Lemma map_id : forall pos, eq (map Datatypes.id pos) pos.
Proof. repeat intro. reflexivity. Qed.

End Make.


(** **  Spectra  **)

Module Type Spectrum(Location : DecidableType)(N : Size). (* <: DecidableType *)
  Module Names := Robots.Make(N).
  Module Pos := Make(Location)(N)(Names).
  
  (** Spectra are a decidable type *)
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  Parameter eq_dec : forall x y : t, {eq x y} + {~eq x y}.
  
  (** A predicate characterizing correct spectra for a given local position *)
  Parameter from_config : Pos.t -> t.
  Declare Instance from_config_compat : Proper (Pos.eq ==> eq) from_config.
  Parameter is_ok : t -> Pos.t -> Prop.
  Parameter from_config_spec : forall config, is_ok (from_config config) config.
End Spectrum.
