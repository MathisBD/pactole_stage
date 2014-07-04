Require Import Reals.
Require Import Morphisms.
Require Import FiniteSumR.
Require Import ConvergentFormalismR.
Import Permutation.

Set Implicit Arguments.


(* ********************************************************* *)
(** *  General results about equality in the robot model **)
(* ******************************************************** *)

(** This module contains definitions and properties about the notions
    of equality we need for proofs. In particular it contains
    technical lemmas (introduced by <<Instance: Proper...>>) making
    these equality relations proper rewriting relations (i.e. that
    some constants are morphisms for these relations). *)

Class Bisimulation (T : Type) := {
  bisim : T -> T -> Prop;
  bisim_equiv : Equivalence bisim}.
Infix "≈" := bisim (at level 30).

(* We do not want this one because it will instantiate all bisim with Lein=bnie equality.
Instance equiv_bisim (T : Type) (R : T -> T -> Prop) `{eqR : Equivalence T R} : Bisimulation T := {
  bisim := R;
  bisim_equiv := eqR}.
*)

(** **  Equality of positions  **)

(** ***  On good robots only  **)

Instance ExtEq_equiv T U : Equivalence (@ExtEq T U).
Proof. split.
+ now intros ? ?.
+ intros f g Heq x. now rewrite Heq.
+ intros f g h Hfg Hgh x. now rewrite Hfg, Hgh.
Qed.

Instance ExtEq_bisim T U : Bisimulation (T -> U).
Proof. exists (@ExtEq T U). apply ExtEq_equiv. Qed.

(** ***  On full positions  **)

Instance pos_eq_equiv G B : Equivalence (@PosEq G B).
Proof. split.
+ split; intuition.
+ intros d1 d2 [H1 H2]. split; intro; now rewrite H1 || rewrite H2.
+ intros d1 d2 d3 [H1 H2] [H3 H4]. now split; intro; rewrite H1, H3 || rewrite H2, H4.
Qed.

Instance gp_compat G B : Proper (@PosEq G B ==> (eq ==> eq)) (@gp G B).
Proof. intros [] [] [Hpos _] x1 x2 Hx. subst. now rewrite Hpos. Qed.

Instance bp_compat G B : Proper (@PosEq G B ==> (eq ==> eq)) (@bp G B).
Proof. intros [] [] [_ Hpos] x1 x2 Hx. subst. now rewrite Hpos. Qed.

Instance poseq_bisim G B : Bisimulation (position G B).
Proof. exists (@PosEq G B). apply pos_eq_equiv. Defined.

Instance locate_compat G B : Proper (@PosEq G B ==> eq ==> eq) (@locate G B).
Proof. intros p q Hpq n [m | m] Hnm; subst; simpl; rewrite Hpq; reflexivity. Qed.

Instance subst_pos_compat G B : Proper (ExtEq ==> @PosEq G B ==> @PosEq G B) (@subst_pos G B).
Proof. intros σ σ' Hσ p q Hpq. split; intro n; simpl; now rewrite Hpq, Hσ. Qed.

(** ***  On spectra  **)

Definition spec_eq (s1 s2 : spectrum) := Permutation s1 s2.

Instance spec_eq_equiv : Equivalence spec_eq.
Proof. apply Permutation_Equivalence. 
Qed.

Instance spec_eq_bisim : Bisimulation spectrum.
Proof. exists spec_eq. exact spec_eq_equiv. Qed.

Instance fold_left_compat X Y : Proper ((eq ==> eq ==> eq) ==> eq ==> eq) (@fold_left X Y).
Proof.
intros f g Hfg.
unfold fold_left. destruct (X.(next) None); try reflexivity. 
pattern n. apply (well_founded_induction X.(RecPrev)). 
intros n1 Hn. case_eq (X.(next) (Some n1)).
  intros n0 Hn0 acc1 acc2 Hacc. subst. setoid_rewrite fold_left_from_equation. rewrite Hn0.
  apply Hn. unfold PrevRel. now rewrite <- X.(NextPrev). now apply Hfg.
  intros Hn0 acc1 acc2 Hacc. subst. setoid_rewrite fold_left_from_equation. rewrite Hn0. now apply Hfg.
Qed.

Instance nominal_spectrum_compat G B : Proper (@PosEq G B ==> spec_eq) (@nominal_spectrum G B).
Proof.
intros p1 p2 Hp.
unfold nominal_spectrum. destruct Hp.
assert (Hcompat := @fold_left_compat (G ⊎ B) spectrum
  (fun (acc : list R) (id : G ⊎ B) =>
    match id with
      | inl g => gp p1 g
      | inr b => bp p1 b
    end :: acc)
  (fun (acc : list R) (id : G ⊎ B) =>
    match id with
      | inl g => gp p2 g
      | inr b => bp p2 b
    end :: acc)).
replace (fold_left (G ⊎ B)
        (fun (acc : list R) (id : G ⊎ B) =>
         match id with
         | inl g => gp p1 g
         | inr b => bp p1 b
         end :: acc) Datatypes.nil)
  with (fold_left (G ⊎ B)
       (fun (acc : list R) (id : G ⊎ B) =>
         match id with
         | inl g => gp p2 g
         | inr b => bp p2 b
         end :: acc) Datatypes.nil).
  setoid_rewrite (good_ext. Qed.

(** **  Equality of demons  **)

(** ***  Equality of demonic_actions  **)
Definition da_eq {G B} (da1 da2 : demonic_action G B) :=
  (forall g, da1.(frame) g = da2.(frame) g) /\ (forall b, da1.(locate_byz) b = da2.(locate_byz) b).

Instance da_eq_equiv G B : Equivalence (@da_eq G B).
Proof. split.
+ split; intuition.
+ intros d1 d2 [H1 H2]. split; intro; now rewrite H1 || rewrite H2.
+ intros d1 d2 d3 [H1 H2] [H3 H4]. now split; intro; rewrite H1, H3 || rewrite H2, H4.
Qed.

Instance locate_byz_compat G B : Proper (@da_eq G B ==> eq ==> eq) (@locate_byz G B).
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd. simpl in *. apply (H0 p2). Qed.

Instance frame_compat G B : Proper (@da_eq G B ==> eq ==> eq) (@frame G B).
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd. simpl in *. apply (H p2). Qed.

Instance spectrum_of_compat {G B} : Proper (@da_eq G B ==> eq ==> @PosEq G B ==> spec_eq) (@spectrum_of G B). 
Proof.
intros [? ? da1 ?] [? ? da2 ?] Hda g1 g2 Hg p1 p2 Hp. simpl. unfold da_eq in Hda. simpl in Hda.
unfold spec_eq. subst. Print is_spectrum.
apply (Permutation_trans (l' := nominal_spectrum p1)).
apply (spectrum_ok g2 p1).
Qed.

(** ***  Equality of demons  **)
CoInductive deq {G B} (d1 d2 : demon G B) : Prop :=
  | Cdeq : da_eq (demon_head d1) (demon_head d2) -> deq (demon_tail d1) (demon_tail d2) -> deq d1 d2.

Instance deq_equiv G B : Equivalence (@deq G B).
Proof. split.
+ coinduction deq_refl. split; intuition.
+ coinduction deq_sym. symmetry. now inversion H. now inversion H.
+ coinduction deq_trans.
    inversion H. inversion H0. now transitivity (demon_head y).
    apply (deq_trans (demon_tail x) (demon_tail y) (demon_tail z)).
      now inversion H. now inversion H0.
Qed.

Instance deq_bisim G B : Bisimulation (demon G B).
Proof. exists deq. apply deq_equiv. Qed.

(** **  Equality of robograms  **)

Print robogram.

Definition req (r1 r2 : robogram) := ExtEq r1 r2.

Instance similarity_compat G B :
  Proper (eq ==> eq ==> (@PosEq G B) ==> (@PosEq G B)) (@similarity G B).
Proof.
intros k1 k2 Hk t1 t2 Ht p1 p2 [Hp1 Hp2]. subst.
split; intro; simpl; now rewrite Hp1 || rewrite Hp2.
Qed.

Print round.
Instance round_compat G B :
  Proper (req ==> da_eq ==> (eq ==> eq) ==> eq ==> eq) (@round G B).
Proof.
intros r1 r2 Hr d1 d2 Hd gp1 gp2 Hgp p1 p2 Hp.
unfold req in Hr. unfold round. simpl in *.
rewrite (frame_compat Hd Hp). destruct (Rdec (frame d2 p2) 0).
  now apply Hgp.
  f_equal. now apply Hgp. f_equal. simpl. rewrite Hr.
  subst. rewrite Hd. , Hgp. apply Hr. apply Hr2 with (id_perm G B). apply similarity_compat; trivial.
  split; intro; simpl. symmetry. now apply Hgp.
  symmetry. apply Hd.
Qed.

Instance round_compat_bis G B :
  Proper  (req ==> da_eq ==> ExtEq ==> ExtEq) (@round G B).
Proof.
intros [r1 Hr1] [r2 Hr2] Hr da1 da2 Hda gp1 gp2 Hgp p.
unfold req in Hr. unfold round. simpl in *.
rewrite (frame_compat Hda (eq_refl p)). destruct (Rdec (frame da2 p) 0).
  now apply Hgp.
  f_equal. now apply Hgp. f_equal. simpl. rewrite Hr.
  subst. rewrite Hgp.
  apply Hr2 with (id_perm G B). apply similarity_compat; trivial.
  split; intro; simpl. symmetry. now apply Hgp.
  symmetry. apply Hda.
Qed.


(** **  Equality of execution  **)

CoInductive eeq {G} (e1 e2 : execution G) : Prop :=
  | Ceeq : (forall p, (execution_head e1) p =  (execution_head e2) p) ->
           eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.

Instance eeq_equiv G : Equivalence (@eeq G).
Proof. split.
+ coinduction eeq_refl. split; intuition.
+ coinduction eeq_sym. symmetry. now inversion H. now inversion H.
+ coinduction eeq_trans. intro.
    inversion H. inversion H0. now transitivity (execution_head y p).
    apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
      now inversion H. now inversion H0.
Qed.

Instance eeq_bisim G : Bisimulation (execution G).
Proof. exists eeq. apply eeq_equiv. Qed.


Instance execution_head_compat (G : finite) : Proper (eeq ==> eq ==> eq) (@execution_head G).
Proof. intros e1 e2 He ? ? ?. subst. inversion He. intuition. Qed.

Instance execution_tail_compat (G : finite) : Proper (eeq ==> eeq) (@execution_tail G).
Proof. intros e1 e2 He. now inversion He. Qed.

Theorem execute_compat G B : Proper (req ==> deq ==> (eq ==> eq) ==> eeq) (@execute G B).
Proof.
intros r1 r2 Hr.
cofix proof. constructor. simpl. intro. now apply (H0 p p).
apply proof; clear proof. now inversion H. intros gp1 gp2 Heq.
inversion H. simpl. destruct x, y. simpl in *.
inversion H. simpl in *. now apply round_compat.
Qed.
