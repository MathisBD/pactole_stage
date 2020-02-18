(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Reals.
Require Import Lra.
Require Import SetoidDec.
Require Import RelationPairs.
Require Import Pactole.Util.Coqlib.


Typeclasses eauto := (bfs).
Remove Hints eq_setoid : typeclass_instances.


(** A real vector space *)
Class RealVectorSpace (T : Type) {S : Setoid T} `{@EqDec T S} := {
  origin : T;
  
  add : T -> T -> T;
  mul : R -> T -> T;
  opp : T -> T;
  
  add_compat : Proper (equiv ==> equiv ==> equiv) add;
  mul_compat : Proper (Logic.eq ==> equiv ==> equiv) mul;
  opp_compat : Proper (equiv ==> equiv) opp;
  
  add_assoc : forall u v w, add u (add v w) == add (add u v) w;
  add_comm : forall u v, add u v == add v u;
  add_origin : forall u, add u origin == u;
  add_opp : forall u, add u (opp u) == origin;
  mul_distr_add : forall a u v, mul a (add u v) == add (mul a u) (mul a v);
  mul_morph : forall a b u, mul a (mul b u) == mul (a * b) u;
  add_morph : forall a b u, add (mul a u) (mul b u) == mul (a + b) u;
  
  mul_1 : forall u, mul 1 u == u;
  one : T; (* TODO: is it really a good name? *)
  non_trivial : one =/= origin}.

Global Arguments origin : simpl never.

Global Existing Instance add_compat.
Global Existing Instance mul_compat.
Global Existing Instance opp_compat.

Declare Scope VectorSpace_scope.
Delimit Scope VectorSpace_scope with VS.
Arguments add T%type _ _ _ u%VS v%VS.
Arguments mul T%type _ _ _ k%R u%VS.
Arguments opp T%type _ _ _ u%VS.
Arguments add_assoc {T} {_} {_} {_} u%VS v%VS w%VS.
Arguments add_comm {T} {_} {_} {_} u%VS v%VS.
Arguments add_origin {T} {_} {_} {_} u%VS.
Arguments add_opp {T} {_} {_} {_} u%VS.
Arguments mul_distr_add {T} {_} {_} {_} a%R u%VS v%VS.
Arguments mul_morph {T} {_} {_} {_} a%R b%R u%VS.
Arguments add_morph {T} {_} {_} {_} a%R b%R u%VS.
Arguments mul_1 {T} {_} {_} {_} u%VS.

Notation "0" := (origin) : VectorSpace_scope.
Notation "u + v" := (add u v) : VectorSpace_scope.
Notation "k * u" := (mul k u) : VectorSpace_scope.
Notation "- u" := (opp u) : VectorSpace_scope.
Notation "u - v" := (add u (opp v)) : VectorSpace_scope.

Ltac null x :=
  let Hnull := fresh "Hnull" in
  destruct (x =?= origin) as [Hnull | Hnull]; [try rewrite Hnull in * | change (~x == origin) in Hnull].

Open Scope R_scope.
Open Scope VectorSpace_scope.

(** ***  Proofs of derivable properties  **)

Definition add_origin_r `{RealVectorSpace} := add_origin.

Lemma add_origin_l `{RealVectorSpace} : forall u, 0 + u == u.
Proof. intro. rewrite add_comm. apply add_origin. Qed.

Lemma add_reg_r `{RealVectorSpace} : forall w u v, u + w == v + w -> u == v.
Proof.
intros w u v Heq. setoid_rewrite <- add_origin.
now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
Qed.

Lemma add_reg_l `{RealVectorSpace} : forall w u v, w + u == w + v -> u == v.
Proof. setoid_rewrite add_comm. apply add_reg_r. Qed.

Lemma opp_origin `{RealVectorSpace} : - origin == origin.
Proof. apply (add_reg_r origin). now rewrite add_comm, add_opp, add_origin. Qed.

Lemma opp_reg `{RealVectorSpace} : forall u v, - u == - v -> u == v.
Proof. intros u v Heq. apply (add_reg_r (opp u)). rewrite add_opp, Heq, add_opp. reflexivity. Qed.

Lemma opp_opp `{RealVectorSpace} : forall u, - (- u) == u.
Proof. intro u. apply (add_reg_l (opp u)). now rewrite add_opp, add_comm, add_opp. Qed.

Lemma opp_distr_add `{RealVectorSpace} : forall u v, - (u + v) == (- u) + (- v).
Proof.
intros u v. apply (add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
Qed.

Lemma mul_0 `{RealVectorSpace} : forall u, 0 * u == 0.
Proof.
intro u. apply (add_reg_l u).
rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite add_morph.
ring_simplify (1 + 0)%R. now rewrite mul_1.
Qed.

Lemma minus_morph `{RealVectorSpace} : forall k u, (-k) * u == - (k * u).
Proof.
intros k u. apply (add_reg_l (mul k u)).
rewrite add_opp. rewrite add_morph. ring_simplify (k + - k)%R.
apply mul_0.
Qed.

Lemma mul_origin `{RealVectorSpace} : forall k, k * 0 == 0.
Proof.
intro k. apply add_reg_l with (k * 0).
rewrite <- mul_distr_add. setoid_rewrite add_origin. reflexivity.
Qed.

Lemma mul_opp `{RealVectorSpace} : forall k u, k * (- u) == - (k * u).
Proof.
intros k u. apply (add_reg_l (k * u)). rewrite <- mul_distr_add.
setoid_rewrite add_opp. now rewrite mul_origin.
Qed.

Lemma mul_reg_l `{RealVectorSpace} : forall k u v, k <> 0%R -> k * u == k * v -> u == v.
Proof.
intros k u v Hk Heq. setoid_rewrite <- mul_1.
replace 1%R with (/k * k)%R by now field.
setoid_rewrite <- mul_morph. rewrite Heq.
reflexivity.
Qed.

Lemma mul_reg_r `{RealVectorSpace} : forall k k' u, u =/= 0 -> k * u == k' * u -> k = k'.
Proof.
intros k k' u Hu Heq. destruct (Rdec k k') as [| Hneq]; trivial.
assert (Heq0 : (k - k') * u == 0).
{ unfold Rminus. rewrite <- add_morph, minus_morph, Heq. apply add_opp. }
elim Hu. rewrite <- (mul_1 u). rewrite <- (Rinv_l (k - k')).
- rewrite <- mul_morph. rewrite Heq0. apply mul_origin.
- intro Habs. apply Hneq. now apply Rminus_diag_uniq.
Qed.

Definition middle `{RealVectorSpace} u v := (1/2) * (u + v).

Instance middle_compat `{RealVectorSpace} : Proper (equiv ==> equiv ==> equiv) middle.
Proof. intros u1 u2 Hu v1 v2 Hv. unfold middle. now rewrite Hu, Hv. Qed.

Lemma mul_integral `{RealVectorSpace} : forall k u, k * u == 0 -> k = 0%R \/ u == 0.
Proof.
intros k u Heq. destruct (Rdec k 0%R).
- now left.
- right. apply mul_reg_l with k; trivial; []. now rewrite Heq, mul_origin.
Qed.


(** In a real metric space, we can define straight paths as trajectories. *)
Require Import Pactole.Util.Ratio.

Program Definition straight_path {T} `{RealVectorSpace T} (pt pt' : T) : path T :=
  Build_path _ _ (fun x => pt + (x * (pt' - pt))) _.
Next Obligation.
abstract (intros x y Hxy; apply add_compat; try reflexivity; [];
          apply mul_compat; try apply Hxy; []; apply add_compat, opp_compat; reflexivity).
Defined.

Instance straight_path_compat {T} `{RealVectorSpace T} :
  Proper (equiv ==> equiv ==> equiv) straight_path.
Proof.
intros pt1 pt2 Heq pt1' pt2' Heq' x. simpl.
now apply add_compat, mul_compat, add_compat, opp_compat.
Qed.

Lemma straight_path_1 `{RealVectorSpace} : forall pt pt', straight_path pt pt' ratio_1 == pt'.
Proof. intros. simpl. now rewrite mul_1, add_assoc, (add_comm pt), <- add_assoc, add_opp, add_origin. Qed.

(** We can simplify this definition in the local frame as we start from the origin. *)
Definition local_straight_path {T} `{RVS : RealVectorSpace T} (pt : T) : path T.
Proof.
refine (Build_path _ _ (fun x => @mul _ _ _ RVS x pt) _).
abstract (intros x y Hxy; apply mul_compat; reflexivity || apply Hxy).
Defined.

Instance local_straight_path_compat {T} `{RealVectorSpace T} :
  Proper (equiv ==> equiv) local_straight_path.
Proof. intros pt1 pt2 Heq x. simpl. now apply mul_compat. Qed.

Lemma local_straight_path_1 `{RealVectorSpace} : forall pt, local_straight_path pt ratio_1 == pt.
Proof. intro. simpl. now rewrite mul_1. Qed.

Lemma local_straight_path_global `{RealVectorSpace} :
  forall pt, local_straight_path pt == straight_path origin pt.
Proof. repeat intro. simpl. now rewrite add_origin_l, opp_origin, add_origin. Qed.

(** ***  Weighted barycenter of a list of locations  **)

Section Barycenter.
  Context {T : Type}.
  Context `{RealVectorSpace T}.
  
  Definition barycenter_aux :=
    List.fold_left (fun acc xn => (((snd xn * fst xn) + fst acc), (snd xn + snd acc)%R)).
  
  Definition barycenter E :=
    let '(sum, weight) := barycenter_aux E (origin, 0%R) in ((1 / weight) * sum).
  
  Instance barycenter_aux_compat :
    Proper (PermutationA (equiv * eq) ==> equiv * eq ==> equiv * eq) barycenter_aux.
  Proof.
  apply fold_left_symmetry_PermutationA; autoclass.
  + intros [] [] [Heq1 ?] [] [] [Heq2 ?]. split; hnf in *; simpl in *; subst; trivial; [].
    apply add_compat; trivial; []. now apply mul_compat.
  + intros [u1 k1] [u2 k2] [u3 k3]. simpl.
    split; try (hnf; simpl in *; ring); [].
    unfold RelCompFun; simpl.
    now rewrite add_comm, <- add_assoc, (add_comm _ u3).
  Qed.
  
  Global Instance barycenter_compat : Proper (PermutationA (equiv * eq) ==> equiv) barycenter.
  Proof.
  intros l1 l2 Hperm.
  unfold barycenter.
  apply barycenter_aux_compat in Hperm.
  specialize (Hperm _ _ (reflexivity (origin, 0%R))).
  destruct (barycenter_aux l1 (origin, 0%R)), (barycenter_aux l2 (origin, 0%R)).
  destruct Hperm. hnf in *; simpl in *. subst. now apply mul_compat.
  Qed.
  
  (* The first component of [barycenter_aux] is the weighted sum of all points. *)
  Lemma barycenter_aux_fst : forall E pt sumR,
    fst (barycenter_aux E (pt, sumR)) = List.fold_left (fun acc xn => ((snd xn * fst xn) + acc)) E pt.
  Proof. induction E; intros; simpl; trivial; now rewrite IHE. Qed.
  
  (* The second component of [barycenter_aux] is the sum of all coefficients. *)
  Lemma barycenter_aux_snd : forall E pt sumR,
    snd (barycenter_aux E (pt, sumR)) = List.fold_left (fun acc xn => snd xn + acc)%R E sumR.
  Proof. induction E; intros; simpl; trivial; now rewrite IHE. Qed.
  
  Lemma barycenter_aux_snd_nonneg : forall E init,
    (List.Forall (fun x => 0 <= snd x) E) ->
    snd init <= snd (barycenter_aux E init).
  Proof.
  induction E as [| e E]; intros init HE; simpl.
  + reflexivity.
  + transitivity (snd e + snd init)%R.
    - inv HE. lra.
    - change (snd e + snd init)%R with (snd ((snd e * fst e + fst init)%VS, snd e + snd init))%R.
      apply IHE. now inv HE.
  Qed.
  
  Corollary barycenter_aux_snd_pos : forall E init,
    0 <= snd init ->
    E <> Datatypes.nil ->
    (List.Forall (fun x => 0 < snd x) E) ->
    0 < snd (barycenter_aux E init).
  Proof.
  intros E init Hinit Hnil HE.
  destruct E as [| e E]; try (now elim Hnil); [].
  simpl. apply Rlt_le_trans with (snd e + snd init)%R.
  + inv HE. lra.
  + change (snd e + snd init)%R with (snd ((snd e * fst e + fst init)%VS, snd e + snd init))%R.
    apply barycenter_aux_snd_nonneg.
    rewrite List.Forall_forall in *. intros x Hin. apply Rlt_le, HE. now right.
  Qed.
  
  Lemma barycenter_singleton : forall pt w, w <> 0%R -> barycenter ((pt, w) :: Datatypes.nil) == pt.
  Proof.
  intros pt w Hw. unfold barycenter. simpl.
  rewrite add_origin, Rplus_0_r, mul_morph, Rmult_comm.
  unfold Rdiv. now rewrite Rmult_1_l, Rinv_r, mul_1.
  Qed.
  
  (** Isobarycenter of a list of locations *)
  Lemma fold_add_acc `{RealVectorSpace} : forall E a b,
    List.fold_left add E (a + b) == (List.fold_left add E a) + b.
  Proof.
  induction E as [| x E].
  + reflexivity.
  + intros a b.
    cbn [List.fold_left].
    rewrite <- add_assoc, add_comm with (u := b), add_assoc.
    apply IHE.
  Qed.
  
  Lemma fold_add_permutation : forall l1 l2 a,
    PermutationA equiv l1 l2 ->
    List.fold_left add l1 a == List.fold_left add l2 a.
  Proof.
  intros.
  apply (fold_left_symmetry_PermutationA add_compat); try easy; [].
  intros x y z. now rewrite <- 2 add_assoc, (add_comm x).
  Qed.
  
  Definition isobarycenter (E: list T) : T :=
    (/(INR (List.length E)) * (List.fold_left add E origin))%VS.
  
  Global Instance isobarycenter_compat : Proper (PermutationA equiv ==> equiv) isobarycenter.
  Proof.
  intros l1 l2 Hpermut. unfold isobarycenter.
  assert (Hl: List.length l1 = List.length l2) by apply (PermutationA_length Hpermut).
  rewrite Hl; clear Hl. (* BUG?: f_equiv should find mul_compat *) apply mul_compat; trivial; [].
  apply (fold_left_symmetry_PermutationA add_compat); try easy; [].
  intros x y z. now rewrite <- 2 add_assoc, (add_comm x).
  Qed.
  
  Lemma isobarycenter_singleton : forall pt, isobarycenter (pt :: Datatypes.nil) == pt.
  Proof. intro. unfold isobarycenter. simpl. now rewrite add_origin_l, Rinv_1, mul_1. Qed.
  
  Lemma isobarycenter_barycenter_aux : forall E acc w,
    barycenter_aux (List.map (fun x => (x, 1)) E) (acc, w) == (List.fold_left add E acc, w + INR (length E))%R.
  Proof.
  induction E; intros acc w.
  + simpl. now rewrite Rplus_0_r.
  + cbn -[INR equiv]. rewrite S_INR, IHE.
    split; simpl; try ring; [].
    now rewrite mul_1, add_comm.
  Qed.
(*
  + cbn -[INR equiv]. rewrite S_INR.
    replace (w + (INR (length E) + 1))%R with (w + 1 + (INR (length E)))%R by ring.
    rewrite <- IHE. Print Instances Proper. apply barycenter_aux_compat. f_equiv. rewrite mul_1. f_equiv; try ring; [].
    now rewrite mul_1, add_comm.
*)
  
  Corollary isobarycenter_barycenter : forall E,
    isobarycenter E == barycenter (List.map (fun x => (x, 1)) E).
  Proof.
  unfold isobarycenter, barycenter. intro E.
  destruct (barycenter_aux (List.map (fun x : T => (x, 1)) E) (0, 0%R)) eqn:Heq.
  apply (@eq_subrelation _ equiv _) in Heq.
  rewrite isobarycenter_barycenter_aux in Heq.
  destruct Heq as [Heq1 Heq2]. simpl in Heq1, Heq2. rewrite Rplus_0_l in Heq2.
  rewrite Heq1, Heq2. unfold Rdiv. rewrite Rmult_1_l. reflexivity.
  Qed.
  
End Barycenter.
