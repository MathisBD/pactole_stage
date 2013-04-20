Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import Qcanon.
(** * Equivalences for both physical positions and
      position seen by good robots *)

(** ** Physical equality. *)
(** Reflexivity *)
Lemma PosEqRefl good bad : forall (p : position good bad), PosEq p p.
Proof. split; split. Qed.

(** Symmetry *)
Lemma PosEqSym good bad
: forall (p q : position good bad), PosEq p q -> PosEq q p.
Proof.
 split.
 + intros n; case (good_ext H); split.
 + intros n; case (bad_ext H); split.
Qed.

(** Transitivity *)
Lemma PosEqTrans good bad
: forall (p q r : position good bad), PosEq p q -> PosEq q r -> PosEq p r.
Proof.
 split.
 + intros n; case (good_ext H0); apply (good_ext H).
 + intros n; case (bad_ext H0); apply (bad_ext H).
Qed.

(** ** k-Implications between positions (as seen by good robots) *)
(* Note: This k-implication implies that good robots have access to the
   number of bad robots, and they can take it into account, though it
   has little impact as a robogram must be defined to be strong against
   a given amount of byzantine robots, and if so, it is automatically
   strong for less byzantine robots (else, the demon could simply
   sacrifice some of its robots to give them the robogram behaviour) *)
(** The null position *)
Definition null good bad : position good bad :=
  {| good_places := fun _ => 0
   ; bad_places := fun _ => 0
   |}.

(** *** The non-null positions form a set with an equivalence
    relation defined by existence of a k such that k-implication
    holds *)

(** Identity *)
Definition id_remap good bad : automorphism (ident good bad).
refine {| section := id; retraction := id |}.
Proof. abstract (split; auto). Defined.

Lemma id_impl good bad (p : position good bad) : PosImpl 1 p p.
Proof.
  split with (id_remap good bad).
  split; simpl; unfold pos_remap_aux; simpl; intros; ring.
Qed.

(** Composition *)
Definition comp_remap good bad (f g : automorphism (ident good bad))
: automorphism (ident good bad).
refine {| section := fun x => section f (section g x)
        ; retraction := fun y => retraction g (retraction f y)
        |}.
Proof.
  abstract (
    intros x y;
    eapply iff_trans; [apply Inversion|];
    eapply iff_trans; [|apply Inversion];
    split; auto
  ).
Defined.

Lemma comp_impl good bad (p q r: position good bad) (l m : Qc)
: PosImpl m q r -> PosImpl l p q -> PosImpl (l*m) p r.
Proof.
  intros [a A] [b B].
  split with (comp_remap b a).
  eapply PosEqTrans; eauto.
  clear - A.
  split; intros n; simpl; unfold pos_remap_aux; simpl.
  + case Qcmult_assoc.
    destruct (retraction b (Good good bad n));
    [generalize (good_ext A n0)|generalize (bad_ext A n0)];
    simpl; unfold pos_remap_aux; simpl; intros []; split.
  + case Qcmult_assoc.
    destruct (retraction b (Bad good bad n));
    [generalize (good_ext A n0)|generalize (bad_ext A n0)];
    simpl; unfold pos_remap_aux; simpl; intros []; split.
Qed.

(** Inversion *)
Definition inv_remap good bad (f : automorphism (ident good bad))
: automorphism (ident good bad).
refine {| section := retraction f; retraction := section f |}.
Proof. abstract (intros; symmetry; apply Inversion). Defined.

Lemma inv_impl good bad (p q : position good bad) (l : Qc)
: l <> 0 -> PosImpl l p q -> PosImpl (/l) q p.
Proof.
  intros Hl [a A]; split with (inv_remap a).
  split; intros n; simpl; unfold pos_remap_aux; simpl.
  + generalize (proj1 (Inversion a (Good good bad n) _) (eq_refl _)).
    destruct (section a (Good good bad n));
    [rewrite (good_ext A)|rewrite (bad_ext A)]; simpl;
    unfold pos_remap_aux; intros H; rewrite H;
    generalize (good_places q n); clear - Hl;
    intros q; rewrite Qcmult_assoc; rewrite Qcmult_inv_l; auto; ring.
  + generalize (proj1 (Inversion a (Bad good bad n) _) (eq_refl _)).
    destruct (section a (Bad good bad n));
    [rewrite (good_ext A)|rewrite (bad_ext A)]; simpl;
    unfold pos_remap_aux; intros H; rewrite H;
    generalize (bad_places q n); clear - Hl;
    intros q; rewrite Qcmult_assoc; rewrite Qcmult_inv_l; auto; ring.
Qed.

(* To be done:
forall x, (x 0-implies y <=> y is a position where every one is at 0)
*)
(** *** The null position is an initial object of k-implications *)
Lemma null_terminal good bad (x y : position good bad)
: (PosImpl 0 x y) <-> (PosEq x (null good bad)).
Proof.
  split; intros.
  + destruct H; destruct good_remap; split; simpl in *; intros;
    [rewrite good_ext|rewrite bad_ext]; ring.
  + split with (id_remap good bad).
    destruct H; split; simpl in *; intros;
    [rewrite good_ext|rewrite bad_ext]; ring.
Qed.