Set Implicit Arguments.
Require Import byzance.
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

(** ** Equivalence between positions (as seen by good robots) *)
(* Note: This equivalence implies that good robots have access to the
   number of bad robots, and they can take it into account, though it
   has little impact as a robogram must be defined to be strong against
   a given amount of byzantine robots, and if so, it is automatically
   strong for less byzantine robots (else, the demon could simply
   sacrifice some of its robots to give them the robogram behaviour) *)
(** Reflexivity *)
Definition refl_auto good bad : automorphism (ident good bad) :=
 {| section := fun x => x
  ; retraction := fun x => x
  ; Inversion := fun x y => conj (fun H => eq_sym H) (fun H => eq_sym H)
  |}.
Lemma PosEquivRefl good bad : forall (p : position good bad), PosEquiv p p.
Proof. split with (refl_auto good bad); split; split. Qed.
 
(** Symmetry *)
Definition sym_auto good bad (s:automorphism (ident good bad))
: automorphism (ident good bad) :=
 {| section := retraction s
  ; retraction := section s
  ; Inversion := fun x y => conj (proj2 (Inversion s y x))
                                 (proj1 (Inversion s y x))
  |}.
Lemma PosEquivSym good bad
: forall (p q : position good bad), PosEquiv p q -> PosEquiv q p.
Proof.
 intros p q [remap Hremap].
 split with (sym_auto remap); split; simpl.
 + intros n.
   generalize (proj1 (Inversion remap (Good good bad n) _) (eq_refl _)).
   destruct (section remap (Good good bad n)); simpl;
   intros; [rewrite (good_ext Hremap)|rewrite (bad_ext Hremap)];
   simpl; rewrite H; split.
 + intros n.
   generalize (proj1 (Inversion remap (Bad good bad n) _) (eq_refl _)).
   destruct (section remap (Bad good bad n)); simpl;
   intros; [rewrite (good_ext Hremap)|rewrite (bad_ext Hremap)];
   simpl; rewrite H; split.
Qed.

(** Transitivity *)
Definition trans_auto good bad (s t:automorphism (ident good bad))
: automorphism (ident good bad) :=
 {| section := fun x => section t (section s x)
  ; retraction := fun x => retraction s (retraction t x)
  ; Inversion := fun x y => conj
    (fun H => proj1 (Inversion s _ _) (sym_equal (proj1 (Inversion t _ _ ) H)))
    (fun H => proj2 (Inversion t _ _) (sym_equal (proj2 (Inversion s _ _ ) H)))
  |}.
Lemma PosEquivTrans good bad
: forall (p q r : position good bad),
  PosEquiv p q -> PosEquiv q r -> PosEquiv p r.
Proof.
 intros p q r [remap_p_q Hremap_p_q] [remap_q_r Hremap_q_r].
 split with (trans_auto remap_q_r remap_p_q).
 apply PosEqTrans with (pos_remap remap_p_q q); auto.
 clear p Hremap_p_q.
 apply PosEqTrans with (pos_remap remap_p_q (pos_remap remap_q_r r)).
 split; simpl in *; intros.
 + destruct (retraction remap_p_q (Good good bad n)); simpl.
   - apply (good_ext Hremap_q_r n0).
   - apply (bad_ext Hremap_q_r n0).
 + destruct (retraction remap_p_q (Bad good bad n)); simpl.
   - apply (good_ext Hremap_q_r n0).
   - apply (bad_ext Hremap_q_r n0).
 + split; simpl; intros.
   - destruct (retraction remap_p_q (Good good bad n)); split.
   - destruct (retraction remap_p_q (Bad good bad n)); split.
Qed.
