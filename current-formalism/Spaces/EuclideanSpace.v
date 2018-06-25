(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import Lra.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Export Pactole.Spaces.RealNormedSpace.
Open Scope R_scope.


Class EuclideanSpace (T : Type) {S : Setoid T} {EQ : @EqDec T S} {VS : RealVectorSpace T} := {
  inner_product : T-> T -> R;
  
  inner_product_compat : Proper (equiv ==> equiv ==> Logic.eq) inner_product;
  
  inner_product_sym : forall u v, inner_product u v = inner_product v u;
  inner_product_add_l : forall u v w, inner_product (add u v) w = inner_product u w + inner_product v w;
  inner_product_mul_l : forall k u v, inner_product (mul k u) v = k * inner_product u v;
  inner_product_nonneg : forall u, 0 <= inner_product u u;
  inner_product_defined : forall u, inner_product u u = 0%R <-> u == origin}.

Existing Instance inner_product_compat.
Arguments inner_product {T%type} {_} {_} {_} {_} u%VS V%VS.
Notation "〈 u , v 〉" := (inner_product u v) (format "'〈' u ,  v '〉'"): VectorSpace_scope.
(* Open Scope VectorSpace_scope. *)

(** *** Results about [inner_product]  **)

Section InnerProductResults.
  Context `{EuclideanSpace}.
  
  Lemma inner_product_add_r : forall u v w, (inner_product u (v + w) = inner_product u v + inner_product u w).
  Proof.
  intros u v w. now rewrite inner_product_sym, inner_product_add_l, inner_product_sym, (inner_product_sym w).
  Qed.
  
  Lemma inner_product_mul_r : forall k u v, inner_product u (k * v) = (k * inner_product u v).
  Proof. intros a u v. now rewrite inner_product_sym, inner_product_mul_l, inner_product_sym. Qed.
  
  Lemma inner_product_origin_l `{EuclideanSpace} : forall u, inner_product 0 u = 0%R.
  Proof. intro. rewrite <- (mul_origin 0), inner_product_mul_l. lra. Qed.
  
  Lemma inner_product_origin_r `{EuclideanSpace} : forall u, inner_product u 0 = 0%R.
  Proof. intro. rewrite inner_product_sym. apply inner_product_origin_l. Qed.
  
  Lemma inner_product_opp_l : forall u v, inner_product (- u) v = - inner_product u v.
  Proof.
  intros u v. apply Rminus_diag_uniq. unfold Rminus. rewrite Ropp_involutive, Rplus_comm.
  rewrite <- inner_product_add_l, add_opp. apply inner_product_origin_l.
  Qed.
  
  Lemma inner_product_opp_r : forall u v, inner_product u (- v) = - inner_product u v.
  Proof. intros u v. setoid_rewrite inner_product_sym. apply inner_product_opp_l. Qed.
  
  Lemma inner_product_opp : forall u v, inner_product (- u) (- v) = inner_product u v.
  Proof. intros u v. now rewrite inner_product_opp_l, inner_product_opp_r, Ropp_involutive. Qed.
  
  Lemma squared_Cauchy_Schwarz : forall u v, (inner_product u v)² <= inner_product u u * inner_product v v.
  Proof.
  intros u v. null v.
  * rewrite 2 inner_product_origin_r, Rsqr_0, Rmult_0_r. reflexivity.
  * rewrite <- inner_product_defined in Hnull.
    cut (0 <= inner_product u u - (inner_product u v)² / inner_product v v).
    + intro Hle. rewrite Rmult_comm, <- (Rmult_1_l _²), <- (Rinv_r _ Hnull), Rmult_assoc.
      apply Rmult_le_compat_l; apply inner_product_nonneg || lra.
    + pose (λ := inner_product u v / inner_product v v).
      rewrite <- Rplus_0_r. rewrite <- (Rminus_diag_eq _ _ (eq_refl (λ² * (inner_product v v)))) at 2.
      replace (〈u, v〉² / 〈v, v〉) with (λ² * 〈v, v〉) by now unfold λ, Rsqr; field.
      assert (Heq : λ² * 〈v, v〉 = λ * 〈u, v〉). { unfold λ, Rsqr. now field. }
      rewrite Heq at 1 3. unfold Rsqr. rewrite (Rmult_assoc λ).
      setoid_rewrite <- inner_product_mul_r. rewrite <- (inner_product_mul_l λ).
      unfold Rminus. rewrite <- inner_product_opp_r, <- (inner_product_opp (λ * v) (λ * v))%VS.
      rewrite <- inner_product_add_l, <- inner_product_add_r.
      rewrite (add_comm _ u), inner_product_sym, <- inner_product_add_r.
      apply inner_product_nonneg.
  Qed.
  
End InnerProductResults.

(** ***  Results about [perpendicular]  **)

Section PerpendicularResults.
  Context `{EuclideanSpace}.

  Definition perpendicular u v := inner_product u v = 0.
(*   Definition colinear `{EuclideanSpace} u v := perpendicular u (orthogonal v). *)
  
  (* could be strenghtened to colinear *)
  Global Instance perpendicular_compat : Proper (equiv ==> equiv ==> iff) perpendicular.
  Proof. intros ? ? Heq1 ? ? Heq2. unfold perpendicular. now rewrite Heq1, Heq2. Qed.
  
  Lemma perpendicular_dec : forall u v, {perpendicular u v} + {~perpendicular u v}.
  Proof. intros u v. unfold perpendicular. apply Rdec. Defined.
  
  Lemma perpendicular_sym : forall u v, perpendicular u v <-> perpendicular v u.
  Proof. intros. unfold perpendicular. now rewrite inner_product_sym. Qed.
  
  Lemma perpendicular_origin_l : forall u, perpendicular origin u.
  Proof. intro. unfold perpendicular. apply inner_product_origin_l. Qed.
  
  Lemma perpendicular_origin_r : forall u, perpendicular u origin.
  Proof. intro. unfold perpendicular. apply inner_product_origin_r. Qed.
  
  Lemma perpendicular_opp_compat_l : forall u v, perpendicular (- u)%VS v <-> perpendicular u v.
  Proof.
  intros u v. unfold perpendicular. split; intro Hperp.
  - rewrite <- mul_1, mul_opp, <- minus_morph, inner_product_mul_l in Hperp. lra.
  - rewrite <- mul_1, mul_opp, <- minus_morph, inner_product_mul_l, Hperp. field.
  Qed.

  Lemma perpendicular_opp_compat_r : forall u v, perpendicular u (- v)%VS <-> perpendicular u v.
  Proof.
  intros u v. unfold perpendicular. split; intro Hperp.
  - setoid_rewrite <- mul_1 in Hperp at 2. rewrite mul_opp, <- minus_morph, inner_product_mul_r in Hperp. lra.
  - setoid_rewrite <- mul_1 at 2. rewrite mul_opp, <- minus_morph, inner_product_mul_r, Hperp. field.
  Qed.

  Lemma perpendicular_mul_compat_l : forall k u v, perpendicular u v -> perpendicular (k * u)%VS v.
  Proof. intros k u v Hperp. unfold perpendicular. rewrite inner_product_mul_l, Hperp. field. Qed.

  Lemma perpendicular_mul_compat_r : forall k u v, perpendicular u v -> perpendicular u (k * v)%VS.
  Proof. intros k u v Hperp. unfold perpendicular. rewrite inner_product_mul_r, Hperp. field. Qed.

  Lemma perpendicular_mul_compat_l_iff : forall k u v, k <> 0 -> (perpendicular (k * u)%VS v <-> perpendicular u v).
  Proof.
  intros k u v Hk. split; intro Hperp.
  - rewrite <- (mul_1 u), <- (Rinv_l k), <- mul_morph; trivial; [].
    now apply perpendicular_mul_compat_l.
  - now apply perpendicular_mul_compat_l.
  Qed.

  Lemma perpendicular_mul_compat_r_iff : forall k u v, k <> 0 -> (perpendicular u (k * v)%VS <-> perpendicular u v).
  Proof.
  intros k u v Hk. split; intro Hperp.
  - rewrite <- (mul_1 v), <- (Rinv_l k), <- mul_morph; trivial; [].
    now apply perpendicular_mul_compat_r.
  - now apply perpendicular_mul_compat_r.
  Qed.
  
End PerpendicularResults.
Arguments perpendicular {T%type} {_} {_} {_} {_} u%VS v%VS.

(** The norm induced by the inner_product. *)
Instance Euclidean2Normed {T} `{EuclideanSpace T} : RealNormedSpace T := {
  norm := fun u => sqrt (inner_product u u) }.
Proof.
+ abstract (intros ? ? Heq; now rewrite Heq).
+ intros a u. rewrite inner_product_mul_l, inner_product_mul_r, <- Rmult_assoc.
  rewrite sqrt_mult_alt, sqrt_square; try reflexivity; []. clear.
  destruct (Rle_dec 0 a); try (now apply Rmult_le_pos); [].
  assert (0 <= -a) by lra. replace (a * a)%R with ((-a) * (-a))%R by lra. now apply Rmult_le_pos.
+ split; intro Heq.
  - apply sqrt_eq_0 in Heq; try apply inner_product_nonneg; [].
    now rewrite <- inner_product_defined.
  - now rewrite Heq, inner_product_origin_l, sqrt_0.
+ intros u v. rewrite <- pos_Rsqr_le.
  - rewrite Rsqr_plus, 3 Rsqr_sqrt; try apply inner_product_nonneg; [].
    rewrite inner_product_add_l, 2 inner_product_add_r, (inner_product_sym v u).
    cut (inner_product u v <= sqrt (inner_product u u) * sqrt (inner_product v v))%R; try lra; [].
    apply pos_Rsqr_le_impl; try (now apply Rmult_le_pos; apply sqrt_pos); [].
    rewrite Rsqr_mult, 2 Rsqr_sqrt; try apply inner_product_nonneg.
    apply squared_Cauchy_Schwarz.
  - apply sqrt_pos.
  - apply Rplus_le_le_0_compat; apply sqrt_pos.
Defined.

Lemma norm_add `{EuclideanSpace} : forall u v, (norm (u + v))² = (norm u)² + 2 * inner_product u v + (norm v)².
Proof.
intros u v. simpl norm.
repeat rewrite Rsqr_sqrt; try apply inner_product_nonneg; [].
rewrite inner_product_add_l, inner_product_add_r, inner_product_add_r. rewrite (inner_product_sym v u). ring.
Qed.

Lemma norm_sub `{EuclideanSpace} : forall u v, (norm (u - v))² = (norm u)² - 2 * inner_product u v + (norm v)².
Proof.
intros u v. simpl norm.
repeat rewrite Rsqr_sqrt; try apply inner_product_nonneg; [].
rewrite inner_product_add_l, inner_product_add_r, inner_product_add_r.
repeat rewrite inner_product_opp_l, inner_product_opp_r. rewrite (inner_product_sym v u). ring.
Qed.

Lemma squared_norm_product `{EuclideanSpace} : forall u, (norm u)² = inner_product u u.
Proof. intro. simpl norm. rewrite Rsqr_sqrt; trivial; []. apply inner_product_nonneg. Qed.

Lemma unitary_product `{EuclideanSpace} : forall u v,
  inner_product u v = norm u * norm v * inner_product (unitary u) (unitary v).
Proof.
intros. setoid_rewrite unitary_id at 1 2.
rewrite inner_product_mul_l, inner_product_mul_r. field.
Qed.

Lemma parallelogram_law `{EuclideanSpace} : forall u v,
  (norm (u + v))² + (norm (u - v))² = 2 * (norm u)² + 2 * (norm v)².
Proof.
intros u v.
repeat rewrite ?squared_norm_product,
               ?inner_product_add_l, ?inner_product_add_r,
               ?inner_product_opp_l, ?inner_product_opp_r.
ring.
Qed.

Lemma polarization_identity  `{EuclideanSpace} : forall u v, 〈u, v〉 = ((norm (u + v))² - (norm (u - v))²) / 4.
Proof.
intros.
rewrite 2 squared_norm_product, 2 inner_product_add_l, 4 inner_product_add_r,
        2 inner_product_opp_l, 2 inner_product_opp_r, (inner_product_sym v u).
field.
Qed.

Lemma polarization_identity1 `{EuclideanSpace} : forall u v, 〈u, v〉 = ((norm (u + v))² - (norm u)² - (norm v)²) / 2.
Proof.
intros.
rewrite 3 squared_norm_product, inner_product_add_l,
        2 inner_product_add_r, (inner_product_sym v u).
field.
Qed.

Lemma polarization_identity2 `{EuclideanSpace} : forall u v, 〈u, v〉 = ((norm u)² + (norm v)² - (norm (u-v))²) / 2.
Proof.
intros.
rewrite 3 squared_norm_product, inner_product_add_l,
        2 inner_product_add_r, inner_product_opp,
        (inner_product_sym (-v)%VS u), inner_product_opp_r.
field.
Qed.

Lemma perpendicular_unitary_compat_l `{EuclideanSpace} :
  forall u v, perpendicular (unitary u) v <-> perpendicular u v.
Proof.
intros u v. null u.
+ now rewrite unitary_origin.
+ unfold perpendicular, unitary. rewrite inner_product_mul_l.
  rewrite <- norm_defined in Hnull. apply Rinv_neq_0_compat in Hnull.
  split; intro Hperp.
  - apply Rmult_integral in Hperp. destruct Hperp; lra.
  - rewrite Hperp. lra.
Qed.

Lemma perpendicular_unitary_compat_r `{EuclideanSpace} :
  forall u v, perpendicular u (unitary v) <-> perpendicular u v.
Proof.
intros u v. null v.
+ now rewrite unitary_origin.
+ unfold perpendicular, unitary. rewrite inner_product_mul_r.
  rewrite <- norm_defined in Hnull. apply Rinv_neq_0_compat in Hnull.
  split; intro Hperp.
  - apply Rmult_integral in Hperp. destruct Hperp; lra.
  - rewrite Hperp. lra.
Qed.

(** Important theorems *)
Theorem Pythagoras `{EuclideanSpace} : forall u v, perpendicular u v <-> (norm (u + v)%VS)² = (norm u)² + (norm v)².
Proof.
intros u v.
repeat rewrite squared_norm_product.
rewrite inner_product_add_l, inner_product_add_r, inner_product_add_r, (inner_product_sym v u).
unfold perpendicular. lra.
Qed.

Theorem Cauchy_Schwarz `{EuclideanSpace} : forall u v, Rabs (inner_product u v) <= (norm u) * norm v.
Proof.
intros u v. apply pos_Rsqr_le.
+ apply Rabs_pos.
+ rewrite <- (Rmult_0_l 0). apply Rmult_le_compat; reflexivity || apply norm_nonneg.
+ rewrite Rsqr_mult, <- Rsqr_abs, 2 squared_norm_product. apply squared_Cauchy_Schwarz.
Qed.

(** Von Neumann-Fréchet theorem: If a norm satisfies the parallelogram law,
    then it arises from an inner product, which can be defined from the polarization identities. *)

(* NB: The difficulty is the proof of [〈k * u, v〉 = k * 〈u, v〉].
       This is usually done by extending a proof for k rational by continuity.
       The proof for k rational is derived from [〈u + v, w〉= 〈u, w〉 + 〈v, w〉] and induction.

       Instead, we try a more algebraic proof (taken from stackexchange):
       1) 〈-u, v〉 = 〈u, -v〉 = -〈u, v〉
       2) 〈k u, k v〉= k² 〈u, v〉
       3) 〈k u, v〉 = 〈u, k v〉
       4) k² 〈u, v〉= k² 〈u, v〉
       5) Distinguish 0 <= k and k < 0 to conclude. *)
Section Normed2Euclidean.
  Context (T : Type).
  Context `{rnsT : RealNormedSpace T}.
  Notation product u v := ((norm (u + v))² - (norm (u - v))²).
  Hypothesis parallelogram_law : forall u v,
    (norm (u + v))² + (norm (u - v))² = 2 * (norm u)² + 2 * (norm v)².
  
  Lemma product_add : forall u v w, product (u + v)%VS w = product u w + product v w.
  Proof.
  intros u v w.
  cut ((norm (u + v + w))² + (norm (u - w))² + (norm (v - w))²
     = (norm (u + v - w))² + (norm (u + w))²  + (norm (v + w))²); try lra; [].
  apply Rmult_eq_reg_l with 4; try lra; []. ring_simplify.
  rewrite double. setoid_rewrite Rmult_plus_distr_r.
  assert (Heq : forall x y z, x + y = z <-> x = z - y) by (intros; lra).
  assert (Heq1 := parallelogram_law u (v + w)%VS).
  assert (Heq2 := parallelogram_law v (u + w)%VS).
  assert (Heq3 := parallelogram_law (u - w)%VS v).
  assert (Heq4 := parallelogram_law (v - w)%VS u).
  assert (Heq5 : (u - v - w == u - w - v)%VS) by now rewrite <- 2 add_assoc, (add_comm (-v)%VS).
  assert (Heq6 : (v - u - w == v - w - u)%VS) by now rewrite <- 2 add_assoc, (add_comm (-u)%VS).
  rewrite Heq in Heq1, Heq2, Heq3, Heq4.
  rewrite add_assoc in Heq1, Heq2. rewrite (add_comm v u) in Heq2.
  rewrite add_comm, add_assoc in Heq3, Heq4. rewrite (add_comm v u) in Heq3.
  rewrite Heq1 at 1. rewrite Heq2. rewrite Heq3 at 1. rewrite Heq4.
  repeat rewrite ?opp_distr_add, ?add_assoc. rewrite Heq5, Heq6.
  ring.
  Qed.
  
  Lemma product_opp : forall u v, product (-u)%VS v = - product u v.
  Proof.
  intros u v.
  cut (product u v + product (-u)%VS v = 0); try lra; [].
  rewrite <- product_add; trivial; [].
  rewrite add_opp.
  do 2 rewrite add_comm, add_origin. rewrite norm_opp. ring.
  Qed.
  
  Lemma product_mul : forall k u v, product (k * u)%VS (k * v)%VS = k² * product u v.
  Proof.
  intros k u v.
  rewrite <- mul_opp, <- 2 mul_distr_add, 2 norm_mul.
  repeat rewrite Rsqr_mult. rewrite <- Rsqr_abs. ring.
  Qed.
  
  Lemma product_mul_switch : forall k u v, product (k * u)%VS v = product u (k * v)%VS.
  Proof.
  intros k u v. cut (product (k * u)%VS v - product u (k * v)%VS = 0); try lra; [].
  unfold product.
  Admitted. (* TODO *)
  
  Lemma product_sqr : forall k u v, product (k² * u)%VS v = k² * product u v.
  Proof. intros k u v. unfold Rsqr at 2 4. now rewrite <- mul_morph, product_mul_switch, product_mul. Qed.
  
Instance Normed2Euclidean : EuclideanSpace T.
simple refine {| inner_product := fun u v => 1/4 * product u v |}; autoclass; simpl.
Proof.
+ abstract (intros u u' Hu v v' Hv; now rewrite Hu, Hv).
+ intros u v. do 2 f_equal.
  - now rewrite add_comm.
  - now rewrite <- norm_opp, opp_distr_add, opp_opp, add_comm.
+ intros u v w. rewrite <- Rmult_plus_distr_l. f_equal.
  apply product_add.
+ intros k u v.
  rewrite <- Rmult_assoc, (Rmult_comm k), Rmult_assoc. f_equal.
  destruct (Rle_dec 0 k) as [Hk | Hk].
  - rewrite <- (Rsqr_sqrt _ Hk). apply product_sqr.
  - rewrite <- (Ropp_involutive k) at 1 2. rewrite minus_morph, product_opp.
    assert (Hk' : 0 <= - k) by lra.
    rewrite <- (Rsqr_sqrt _ Hk'), product_sqr, (Rsqr_sqrt _ Hk').
    ring.
+ intro u. rewrite add_opp, norm_origin. unfold Rsqr. nra.
+ intro u. rewrite add_opp, norm_origin, <- norm_defined.
  assert (Heq : (u + u == 2 * u)%VS) by now rewrite <- add_morph, mul_1.
  rewrite Heq, norm_mul, Rabs_pos_eq; try lra; []. unfold Rsqr. nra.
Defined.
  
End Normed2Euclidean.

(*
Lemma unitary_orthogonal : forall u, unitary (orthogonal u) == orthogonal u.
Proof.
intro u. null u.
- rewrite orthogonal_origin. apply unitary_origin.
- unfold unitary. rewrite R2norm_orthogonal; trivial; []. replace (/1) with 1 by field. now rewrite mul_1.
Qed.

Lemma orthogonal_unitary : forall u, orthogonal (unitary u) == orthogonal u.
Proof.
intro u. null u.
- now rewrite unitary_origin.
- unfold orthogonal. rewrite R2norm_unitary; trivial; []. unfold unitary. simpl.
  rewrite <- R2norm_0 in Hnull. now destruct u; f_equal; simpl; field.
Qed.
*)