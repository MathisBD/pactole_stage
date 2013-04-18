Set Implicit Arguments.
Require Import ConvergentFormalism.
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
(* To be done:
k<>0 => x k-implies y => y 1/k-implies x
x 1-implies x
x k-implies y => y l-implies z => x kl-implies z
forall x, (x 0-implies y <=> y is a position where every one is at 0)
*)