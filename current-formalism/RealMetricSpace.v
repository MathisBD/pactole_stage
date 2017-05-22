Require Import Reals.
Require Import Morphisms.
Require Import Equalities.
Require Import Pactole.Preliminary.


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