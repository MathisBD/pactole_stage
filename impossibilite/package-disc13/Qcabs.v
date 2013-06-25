(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, X. Urbain                                     *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Qabs.
Require Import Qcanon.

Lemma Qceq_spe (x y : Qc) : this x = this y -> x = y.
Proof. intros H; apply Qc_decomp; auto. Qed.

Lemma Qred_abs (x : Q) : Qred (Qabs x) = Qabs (Qred x).
Proof.
  destruct x as [[|a|a] d]; simpl; auto;
  destruct (Pos.ggcd a d) as [x [y z]]; simpl; auto.
Qed.

Lemma Qcabs_aux (x : Q) : Qred x = x -> Qred (Qabs x) = Qabs x.
Proof. now intros H; rewrite (Qred_abs x); rewrite H. Qed.

Definition Qred_morph (x y : Q) : (x <= y)%Q -> (Qred x <= Qred y)%Q.
Proof. now generalize (Qred_compare x y); unfold Qle, Qcompare, Zle; intros [].
Qed.

Definition Qred_comorph (x y : Q) : (Qred x <= Qred y)%Q -> (x <= y)%Q.
Proof. now generalize (Qred_compare x y); unfold Qle, Qcompare, Zle; intros [].
Qed.

Definition Qcabs (x:Qc) : Qc := {| canon := Qcabs_aux x (canon x) |}.
Notation "[ q ]" := (Qcabs q) (q at next level, format "[ q ]") : Qc_scope.

Ltac Qc_unfolds :=
  unfold Qcabs, Qcminus, Qcopp, Qcplus, Qcmult, Qcle, Q2Qc, this.
(******************************************************************************)
Lemma Qcabs_case (x:Qc) (P : Qc -> Type)
: (0 <= x -> P x) -> (x <= 0 -> P (- x)) -> P [x].
Proof.
  intros A B.
  apply (Qabs_case x (fun x => forall Hx, P {|this:=x;canon:=Hx|})).
  intros; case (Qceq_spe x {|canon:=Hx|}); auto.
  intros; case (Qceq_spe (-x) {|canon:=Hx|}); auto.
Qed.

Lemma Qcabs_pos : forall x, 0 <= x -> [x] = x.
Proof.
  intros x Hx; apply Qceq_spe; Qc_unfolds; fold (this x).
  assert (K := canon [x]); simpl in K; case K; clear K.
  set (a := x) at 1; case (canon x); subst a; apply Qred_complete.
  now apply Qabs_pos.
Qed.

Lemma Qcabs_neg : forall x, x <= 0 -> [x] = - x.
Proof.
  intros x Hx; apply Qceq_spe; Qc_unfolds; fold (this x).
  assert (K := canon [x]); simpl in K; case K; clear K.
  now apply Qred_complete; apply Qabs_neg.
Qed.

Lemma Qcabs_nonneg : forall x, 0 <= [x].
Proof. intros; apply Qabs_nonneg. Qed.

(*Lemma Zabs_Qabs : forall n d, (Z.abs n#d)==Qabs (n#d).*)

Lemma Qcabs_opp : forall x, [(-x)] = [x].
Proof.
  intros x; apply Qceq_spe; Qc_unfolds; fold (this x).
  assert (K := canon [x]); simpl in K; case K; clear K.
  case Qred_abs; apply Qred_complete; apply Qabs_opp.
Qed.

Lemma Qcabs_triangle : forall x y, [(x+y)] <= [x] + [y].
Proof.
  intros x y; Qc_unfolds; case Qred_abs; apply Qred_morph; apply Qabs_triangle.
Qed.

Lemma Qcabs_Qcmult : forall a b, [(a*b)] = [a]*[b].
Proof.
  intros x y; apply Qceq_spe; Qc_unfolds; fold (this x) (this y); case Qred_abs.
  apply Qred_complete; apply Qabs_Qmult.
Qed.

Lemma Qcabs_Qcminus x y: [(x - y)] = [(y - x)].
Proof.
  apply Qceq_spe; Qc_unfolds; fold (this x) (this y) (this (-x)) (this (-y)).
  set (a := x) at 2; case (canon x); subst a.
  set (a := y) at 1; case (canon y); subst a.
  repeat rewrite Qred_opp; fold (Qred x - Qred y)%Q (Qred y - Qred x)%Q.
  repeat case Qred_abs; f_equal; apply Qabs_Qminus.
Qed.

Lemma Qcle_Qcabs : forall a, a <= [a].
Proof. intros; apply Qle_Qabs. Qed.

Lemma Qcabs_triangle_reverse : forall x y, [x] - [y] <= [(x - y)].
Proof.
  intros x y.
  unfold Qcle, Qcabs, Qcminus, Qcplus, Qcopp, Q2Qc, this;
  fold (this x) (this y) (this (-x)) (this (-y)).
  case Qred_abs; apply Qred_morph.
  repeat rewrite Qred_opp; rewrite Qred_abs; apply Qabs_triangle_reverse.
Qed.

Lemma Qcabs_Qcle_condition x y : [x] <= y <-> -y <= x <= y.
Proof.
  Qc_unfolds; fold (this x) (this y).
  destruct (Qabs_Qle_condition x y) as [A B].
  split; intros H.
  + destruct (A H) as [X Y]; split; auto.
    now case (canon x); apply Qred_morph.
  + destruct H as [X Y]; apply B; split; auto.
    now case (canon y); case Qred_opp.
Qed.

Lemma Qcabs_diff_Qcle_condition x y r: [(x - y)] <= r <-> x - r <= y <= x + r.
Proof.
  Qc_unfolds; fold (this x) (this y) (this r).
  case Qred_abs; repeat rewrite Qred_opp.
  set (a := y) at 1; case (canon y); subst a.
  set (a := r) at 2; case (canon r); subst a.
  set (a := Qred r) at 2 3;
  assert (K := canon (!!r)); simpl in K; case K; clear K; subst a.
  set (a := Qred y) at 1;
  assert (K := canon (!!y)); simpl in K; case K; clear K; subst a.
  fold (x - Qred y)%Q (x - Qred r)%Q.
  destruct (Qabs_diff_Qle_condition x (Qred y) (Qred r)) as [A B].
  split.
  + clear B; intros H; destruct (A (Qred_comorph _ _ H)) as [X Y]; split;
    apply Qred_morph; auto.
  + clear A; intros H; apply Qred_morph; apply B; destruct H as [X Y]; split;
    apply Qred_comorph; auto.
Qed.

Lemma Qcabs_null (q : Qc) : [q] = 0 -> q = 0.
Proof.
  intros H.
  destruct (proj1 (Qcabs_Qcle_condition q 0)) as [A B].
  + rewrite H; apply Qcle_refl.
  + apply Qcle_antisym; auto.
Qed.

Lemma Qcabs_nonnull (q : Qc) : q <> 0 -> 0 < [q].
Proof.
  intros Hq; destruct (Qclt_le_dec 0 [q]); auto; destruct Hq.
  destruct (proj1 (Qcabs_Qcle_condition _ _) q0); apply Qcle_antisym; auto.
Qed.
