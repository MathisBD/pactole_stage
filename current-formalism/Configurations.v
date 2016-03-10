(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Omega.
Require Import Equalities.
Require Import SetoidList.
Require Import Reals.
Require Import Pactole.Preliminary.
Require Import Robots.


(** * Configurations *)

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
  Parameter mul : R -> t -> t. (* the underlying field is R *)
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
  Parameter mul_distr_add : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Parameter mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Parameter add_morph : forall a b u, eq (add (mul a u) (mul b u)) (mul (a + b) u).
  
  Parameter mul_1 : forall u, eq (mul 1 u) u.
  Parameter unit : t. (* TODO: is it really a good name? *)
  Parameter non_trivial : ~eq unit origin.
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
  Parameter opp_distr_add : forall u v, eq (opp (add u v)) (add (opp u) (opp v)).
  Parameter mul_0 : forall u, eq (mul 0 u) origin.
  Parameter mul_origin : forall a, eq (mul a origin) origin.
  Parameter mul_reg_l : forall k u v, k <> 0%R -> eq (mul k u) (mul k v) -> eq u v.
  Parameter mul_reg_r : forall k k' u, ~eq u origin -> eq (mul k u) (mul k' u) -> k = k'.
  Parameter minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).
  Parameter mul_integral : forall k u, eq (mul k u) origin -> k = 0%R \/ eq u origin.

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
  
  Lemma opp_distr_add : forall u v, eq (opp (add u v)) (add (opp u) (opp v)).
  Proof.
  intros u v. apply (add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
  setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
  Qed.
  
  Lemma mul_0 : forall u, eq (mul 0 u) origin.
  Proof.
  intro u. apply (add_reg_l u).
  rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite add_morph.
  ring_simplify (1 + 0)%R. now rewrite mul_1.
  Qed.
  
  Lemma minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).
  Proof.
  intros k u. apply (add_reg_l (mul k u)).
  rewrite add_opp. rewrite add_morph. ring_simplify (k + - k)%R.
  apply mul_0.
  Qed.
  
  Lemma mul_origin : forall k, eq (mul k origin) origin.
  Proof.
  intro k. apply add_reg_l with (mul k origin).
  rewrite <- mul_distr_add. setoid_rewrite add_origin. reflexivity.
  Qed.
  
  Lemma mul_opp : forall a u, eq (mul a (opp u)) (opp (mul a u)).
  Proof.
  intros a u. apply (add_reg_l (mul a u)). rewrite <- mul_distr_add.
  setoid_rewrite add_opp. now rewrite mul_origin.
  Qed.
  
  Lemma mul_reg_l : forall k u v, k <> 0%R -> eq (mul k u) (mul k v) -> eq u v.
  Proof.
  intros k u v Hk Heq. setoid_rewrite <- mul_1.
  replace 1%R with (/k * k)%R by now field.
  setoid_rewrite <- mul_morph. rewrite Heq.
  reflexivity.
  Qed.
  
  Lemma mul_reg_r : forall k k' u, ~eq u origin -> eq (mul k u) (mul k' u) -> k = k'.
  Proof.
  intros k k' u Hu Heq. destruct (Rdec k k') as [| Hneq]; trivial.
  assert (Heq0 : eq (mul (k -k') u)  origin).
  { unfold Rminus. rewrite <- add_morph, minus_morph, Heq. apply add_opp. }
  elim Hu. rewrite <- mul_1. rewrite <- (Rinv_l (k - k')).
  - rewrite <- mul_morph. rewrite Heq0. apply mul_origin.
  - intro Habs. apply Hneq. now apply Rminus_diag_uniq.
  Qed.
  
  Definition middle u v := mul (1/2)%R (add u v).
  
  Lemma mul_integral : forall k u, eq (mul k u) origin -> k = 0%R \/ eq u origin.
  Proof.
  intros k u Heq. destruct (Rdec k 0%R).
  - now left.
  - right. apply mul_reg_l with k; trivial; []. now rewrite Heq, mul_origin.
  Qed.
  
End MakeRealMetricSpace.

Module Type DiscretSpaceDef <: DecidableType.
  Parameter t : Type.
  Parameter origin : t.
  Parameter eq : t -> t -> t -> Prop.
  Parameter dist : t -> t -> nat.
  Parameter eq_dec : forall x y n, {eq x y n} + {~ eq x y n}.
  
  Parameter add : t -> t -> t -> t.
  Parameter mul : nat -> t -> t -> t.
  Parameter opp : t -> t -> t.
  
  Declare Instance add_compact : Proper (eq ==> eq ==> eq ==> eq) add.
  Declare Instance mul_compact : Proper (Logic.eq ==> eq ==> eq ==> eq) mul.
  Declare Instance opp_compact : Proper (eq ==> eq ==> eq) opp.
  
  Parameter eq_equiv : Equivalence eq.
  Parameter dist_define : forall x y, dist x y = O <-> eq x y origin.
  Parameter dist_sym : forall x y, dist x y = dist y x.
(* there is no triangular inequation in ring-type space.*)

  Parameter add_assoc : forall u v w, eq (add u (add v w origin) origin) (add (add u v origin) w origin).
  Parameter add_comm : forall u v, eq (add u v origin) (add v u origin).
  Parameter add_origin : forall u, eq (add u origin origin) u.
  Parameter add_opp: forall u, eq (add u (opp u origin) origin) origin.
  Parameter mul_distr_add : forall a u v, eq (mul a (add u v origin) origin) (add (mul a u origin) (mul a v origin) origin).
  Parameter mul_morph : forall a b u, eq (mul a (mul b u origin) origin) (mul (a * b) u origin).
  Parameter add_morph : forall a b u, eq (add (mul a u origin) (mul b u origin) origin) (mul (a + b) u origin).
  
  Parameter mul_1 : forall u, eq (mul 1 u origin) u.
  Parameter unit : t. (* TODO: is it really a good name? *)
  Parameter non_trivial : ~eq unit origin.
End DiscretSpaceDef.

Module Type Configuration(Location : DecidableType)(N : Size)(Names : Robots(N)).
  Definition t := Names.ident -> Location.t.
  Definition eq config₁ config₂ := forall id : Names.ident, Location.eq (config₁ id) (config₂ id).
  Declare Instance eq_equiv : Equivalence eq.
  Declare Instance eq_bisim : Bisimulation t.
  Declare Instance eq_subrelation : subrelation eq (Logic.eq ==> Location.eq)%signature.
  
  Parameter neq_equiv : forall config₁ config₂,
    ~eq config₁ config₂ <-> exists id, ~Location.eq (config₁ id) (config₂ id).
  
  Definition map (f : Location.t -> Location.t) (conf : t) := fun id => f (conf id).
  Declare Instance map_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) map.
  
  Parameter Gpos : t -> list Location.t.
  Parameter Bpos : t -> list Location.t.
  Parameter list : t -> list Location.t.
  Declare Instance Gpos_compat : Proper (eq ==> eqlistA Location.eq) Gpos.
  Declare Instance Bpos_compat : Proper (eq ==> eqlistA Location.eq) Bpos.
  Declare Instance list_compat : Proper (eq ==> eqlistA Location.eq) list.
  
  Parameter Gpos_spec : forall conf, Gpos conf = List.map (fun g => conf (Good g)) Names.Gnames.
  Parameter Bpos_spec : forall conf, Bpos conf = List.map (fun g => conf (Byz g)) Names.Bnames.
  Parameter list_spec : forall conf, list conf = List.map conf Names.names.

  Parameter Gpos_InA : forall l conf, InA Location.eq l (Gpos conf) <-> exists g, Location.eq l (conf (Good g)).
  Parameter Bpos_InA : forall l conf, InA Location.eq l (Bpos conf) <-> exists b, Location.eq l (conf (Byz b)).
  Parameter list_InA : forall l conf, InA Location.eq l (list conf) <-> exists id, Location.eq l (conf id).
  
  Parameter Gpos_length : forall conf, length (Gpos conf) = N.nG.
  Parameter Bpos_length : forall conf, length (Bpos conf) = N.nB.
  Parameter list_length : forall conf, length (list conf) = N.nG + N.nB.
  
  Parameter list_map : forall f, Proper (Location.eq ==> Location.eq) f -> 
    forall conf, list (map f conf) = List.map f (list conf).
  Parameter map_merge : forall f g, Proper (Location.eq ==> Location.eq) f ->
    Proper (Location.eq ==> Location.eq) g ->
    forall conf, eq (map g (map f conf)) (map (fun x => g (f x)) conf).
  Parameter map_id : forall conf, eq (map Datatypes.id conf) conf.
End Configuration.


Module Make(Location : DecidableType)(N : Size)(Names : Robots(N)) : Configuration(Location)(N)(Names)
  with Definition t := Names.ident -> Location.t.

(** A configuration is a mapping from identifiers to locations.  Equality is extensional. *)
Definition t := Names.ident -> Location.t.
Definition eq (conf₁ conf₂ : t) : Prop := forall id, Location.eq (conf₁ id) (conf₂ id).

Instance eq_equiv : Equivalence eq.
Proof. split.
+ intros conf x. reflexivity.
+ intros d1 d2 H r. symmetry. apply H.
+ intros d1 d2 d3 H12 H23 x. transitivity (d2 x); auto.
Qed.

Instance eq_bisim : Bisimulation t.
Proof. exists eq. apply eq_equiv. Defined.

Instance eq_subrelation : subrelation eq (Logic.eq ==> Location.eq)%signature.
Proof. intros ? ? Hconf ? id ?. subst. apply Hconf. Qed.

(** Pointwise mapping of a function on a configuration *)
Definition map (f : Location.t -> Location.t) (conf : t) := fun id => f (conf id).

Instance map_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) map.
Proof. intros f g Hfg ? ? Hconf id. unfold map. apply Hfg, Hconf. Qed.

(** Configurations seen as lists *)
Definition Gpos (conf : t) := Names.Internals.fin_map (fun g => conf (Good g)).
Definition Bpos (conf : t) := Names.Internals.fin_map (fun b => conf (Byz b)).
Definition list conf := Gpos conf ++ Bpos conf.

Instance Gpos_compat : Proper (eq ==> eqlistA Location.eq) Gpos.
Proof. repeat intro. unfold Gpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance Bpos_compat : Proper (eq ==> eqlistA Location.eq) Bpos.
Proof. repeat intro. unfold Bpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance list_compat : Proper (eq ==> eqlistA Location.eq) list.
Proof. repeat intro. unfold list. now apply (eqlistA_app _); apply Gpos_compat || apply Bpos_compat. Qed.

Lemma Gpos_spec : forall conf, Gpos conf = List.map (fun g => conf (Good g)) Names.Gnames.
Proof. intros. unfold Gpos, Names.Gnames, Names.Internals.Gnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma Bpos_spec : forall conf, Bpos conf = List.map (fun g => conf (Byz g)) Names.Bnames.
Proof. intros. unfold Bpos, Names.Bnames, Names.Internals.Bnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma list_spec : forall conf, list conf = List.map conf Names.names.
Proof.
intros. unfold list. unfold Names.names, Names.Internals.names.
rewrite map_app, Gpos_spec, Bpos_spec. now do 2 rewrite map_map.
Qed.

Lemma Gpos_InA : forall l conf, InA Location.eq l (Gpos conf) <-> exists g, Location.eq l (conf (Good g)).
Proof. intros. unfold Gpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma Bpos_InA : forall l conf, InA Location.eq l (Bpos conf) <-> exists b, Location.eq l (conf (Byz b)).
Proof. intros. unfold Bpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma list_InA : forall l conf, InA Location.eq l (list conf) <-> exists id, Location.eq l (conf id).
Proof.
intros. unfold list. rewrite (InA_app_iff _). split; intro Hin.
+ destruct Hin as [Hin | Hin]; rewrite Gpos_InA in Hin || rewrite Bpos_InA in Hin; destruct Hin; eauto.
+ rewrite Gpos_InA, Bpos_InA. destruct Hin as [[g | b] Hin]; eauto.
Qed.

Lemma Gpos_length : forall conf, length (Gpos conf) = N.nG.
Proof. intro. unfold Gpos. apply Names.Internals.fin_map_length. Qed.

Lemma Bpos_length : forall conf, length (Bpos conf) = N.nB.
Proof. intro. unfold Bpos. apply Names.Internals.fin_map_length. Qed.

Lemma list_length : forall conf, length (list conf) = N.nG + N.nB.
Proof. intro. unfold list. now rewrite app_length, Gpos_length, Bpos_length. Qed.

Lemma list_map : forall f, Proper (Location.eq ==> Location.eq) f -> 
  forall conf, list (map f conf) = List.map f (list conf).
Proof.
intros f Hf conf. unfold list, map, Gpos, Bpos.
repeat rewrite Names.Internals.map_fin_map. rewrite List.map_app. reflexivity.
Qed.

Lemma map_merge : forall f g, Proper (Location.eq ==> Location.eq) f -> Proper (Location.eq ==> Location.eq) g ->
  forall conf, eq (map g (map f conf)) (map (fun x => g (f x)) conf).
Proof. repeat intro. reflexivity. Qed.

Lemma map_id : forall conf, eq (map Datatypes.id conf) conf.
Proof. repeat intro. reflexivity. Qed.

Lemma neq_equiv : forall config₁ config₂,
  ~eq config₁ config₂ <-> exists id, ~Location.eq (config₁ id) (config₂ id).
Proof.
intros config₁ config₂. split; intro Hneq.
* assert (Hlist : ~eqlistA Location.eq (List.map config₁ Names.names) (List.map config₂ Names.names)).
  { intro Habs. apply Hneq. intro id.
    assert (Hin : List.In id Names.names) by apply Names.In_names.
    induction Names.names as [| id' l].
    - inversion Hin.
    - inversion_clear Habs. inversion_clear Hin; solve [now subst | now apply IHl]. }
  induction Names.names as [| id l].
  + now elim Hlist.
  + cbn in Hlist. destruct (Location.eq_dec (config₁ id) (config₂ id)) as [Hid | Hid].
    - apply IHl. intro Heq. apply Hlist. now constructor.
    - eauto.
* destruct Hneq as [id Hneq]. intro Habs. apply Hneq, Habs.
Qed.

End Make.


(** **  Spectra  **)

Module Type Spectrum(Location : DecidableType)(N : Size). (* <: DecidableType *)
  Module Names := Robots.Make(N).
  Module Config := Make(Location)(N)(Names).
  
  (** Spectra are a decidable type *)
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  Parameter eq_dec : forall x y : t, {eq x y} + {~eq x y}.
  
  (** A predicate characterizing correct spectra for a given local configuration *)
  Parameter from_config : Config.t -> t.
  Declare Instance from_config_compat : Proper (Config.eq ==> eq) from_config.
  Parameter is_ok : t -> Config.t -> Prop.
  Parameter from_config_spec : forall config, is_ok (from_config config) config.
End Spectrum.
