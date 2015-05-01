Require Import Equalities.
Require Import SetoidList.
Require Import Reals.
Require Import Robots.


(** * Positions *)

(** This module signature represents the metric space in which robots evolve.
    It can be anything (discrete or continuous) as long as it is a metric space.

    The framework for robots should be more general as for instance a ring is not a metric space.
    It seems that we only need a decidable type for locations and a notion of distance.  *)
Module Type MetricSpaceDef <: DecidableType.
  Parameter t : Type.
  Parameter origin : t.
  Parameter eq : t -> t -> Prop.
  Parameter dist : t -> t -> R.
  Parameter eq_dec : forall x y, {eq x y} + {~eq x y}.
  
  Parameter add : t -> t -> t.
  Parameter mul : R -> t -> t.
  Parameter opp : t -> t.
  
  Declare Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Declare Instance mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
  Declare Instance opp_compat : Proper (eq ==> eq) opp.
  
  Parameter eq_equiv : Equivalence eq.
  Parameter dist_defined : forall x y, dist x y = 0%R <-> eq x y.
  Parameter dist_sym : forall y x, dist x y = dist y x.
  Parameter triang_ineq : forall x y z, (dist x z <= dist x y + dist y z)%R.
  
  Parameter plus_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Parameter add_comm : forall u v, eq (add u v) (add v u).
  Parameter add_origin : forall u, eq (add u origin) u.
  Parameter add_opp : forall u, eq (add u (opp u)) origin.
  Parameter mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Parameter add_distr : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Parameter plus_distr : forall a b u, eq (mul (a + b) u) (add (mul a u) (mul b u)).
  (* The multiplicative identity is missing *)
End MetricSpaceDef.


Module Type MetricSpace.
  Include MetricSpaceDef.
  
  Declare Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Parameter dist_pos : forall x y, (0 <= dist x y)%R.
End MetricSpace.


Module MakeMetricSpace (Def : MetricSpaceDef) : MetricSpace
    with Definition t := Def.t
    with Definition eq := Def.eq
    with Definition eq_dec := Def.eq_dec
    with Definition origin := Def.origin
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
End MakeMetricSpace.


Module Type Position(Location : DecidableType)(N:Size)(Names : Robots(N)).
  Definition t := Names.ident -> Location.t.
  Definition eq pos₁ pos₂ := forall id : Names.ident, Location.eq (pos₁ id) (pos₂ id).
  Declare Instance eq_equiv : Equivalence eq.
  Declare Instance eq_bisim : Bisimulation t.

  Definition map (f : Location.t -> Location.t) (pos : t) := fun id => f (pos id).
  Declare Instance map_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) map.

  Parameter Gpos : t -> list Location.t.
  Parameter Bpos : t -> list Location.t.
  Parameter list : t -> list Location.t.
  Declare Instance Gpos_compat : Proper (eq ==> eqlistA Location.eq) Gpos.
  Declare Instance Bpos_compat : Proper (eq ==> eqlistA Location.eq) Bpos.
  Declare Instance list_compat : Proper (eq ==> eqlistA Location.eq) list.

  Parameter Gpos_spec : forall l pos, InA Location.eq l (Gpos pos) <-> exists g, Location.eq l (pos (Good g)).
  Parameter Bpos_spec : forall l pos, InA Location.eq l (Bpos pos) <-> exists b, Location.eq l (pos (Byz b)).
  Parameter list_spec : forall l pos, InA Location.eq l (list pos) <-> exists id, Location.eq l (pos id).
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

Lemma Gpos_spec : forall l pos, InA Location.eq l (Gpos pos) <-> exists g, Location.eq l (pos (Good g)).
Proof. intros. unfold Gpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma Bpos_spec : forall l pos, InA Location.eq l (Bpos pos) <-> exists b, Location.eq l (pos (Byz b)).
Proof. intros. unfold Bpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma list_spec : forall l pos, InA Location.eq l (list pos) <-> exists id, Location.eq l (pos id).
Proof.
intros. unfold list. rewrite (InA_app_iff _). split; intro Hin.
+ destruct Hin as [Hin | Hin]; rewrite Gpos_spec in Hin || rewrite Bpos_spec in Hin; destruct Hin; eauto.
+ rewrite Gpos_spec, Bpos_spec. destruct Hin as [[g | b] Hin]; eauto.
Qed.

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
