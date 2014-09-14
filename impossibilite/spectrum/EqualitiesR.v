Require Import Reals.
Require Import Morphisms.
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

Instance pos_eq_equiv nG nB : Equivalence (@PosEq nG nB).
Proof. split.
+ split; intuition.
+ intros d1 d2 [H1 H2]. split; intro; now rewrite H1 || rewrite H2.
+ intros d1 d2 d3 [H1 H2] [H3 H4]. now split; intro; rewrite H1, H3 || rewrite H2, H4.
Qed.

Instance gp_compat nG nB : Proper (@PosEq nG nB ==> (eq ==> eq)) (@gp nG nB).
Proof. intros [] [] [Hpos _] x1 x2 Hx. subst. now rewrite Hpos. Qed.

Instance bp_compat nG nB : Proper (@PosEq nG nB ==> (eq ==> eq)) (@bp nG nB).
Proof. intros [] [] [_ Hpos] x1 x2 Hx. subst. now rewrite Hpos. Qed.

Instance poseq_bisim nG nB : Bisimulation (position nG nB).
Proof. exists (@PosEq nG nB). apply pos_eq_equiv. Defined.

Instance poseq_extensional nG nB : Proper (ExtEq ==> ExtEq ==> @PosEq nG nB) (@Build_position nG nB).
Proof. intros gp1 gp2 Hgp bp1 bp2 Hbp. now split; intro n; rewrite Hgp || rewrite Hbp. Qed.

Instance poseq_respectful nG nB : Proper ((eq ==> eq) ==> (eq ==> eq) ==> @PosEq nG nB) (@Build_position nG nB).
Proof. intros gp1 gp2 Hgp bp1 bp2 Hbp. now split; intro n; simpl; rewrite (Hgp n n) || rewrite (Hbp n n). Qed.

Instance locate_compat nG nB : Proper (@PosEq nG nB ==> eq ==> eq) (@locate nG nB).
Proof. intros p q Hpq n [m | m] Hnm; subst; simpl; rewrite Hpq; reflexivity. Qed.

Instance subst_pos_compat nG nB : Proper (ExtEq ==> @PosEq nG nB ==> @PosEq nG nB) (@subst_pos nG nB).
Proof. intros σ σ' Hσ p q Hpq. split; intro n; simpl; now rewrite Hpq, Hσ. Qed.

(** ***  On spectra  **)
(*
Definition spec_eq (s1 s2 : spectrum) := Permutation s1 s2.

Instance spec_eq_equiv : Equivalence spec_eq.
Proof. apply Permutation_Equivalence. Qed.

Instance spec_eq_bisim : nBisimulation spectrum.
Proof. exists spec_eq. exact spec_eq_equiv. Qed.
*)
Instance fin_map_compat n X : Proper ((eq ==> eq) ==> eq) (@fin_map n X).
Proof.
intros f g Hfg. induction n.
  reflexivity.
  simpl. f_equiv. now apply Hfg.
  apply IHn. now repeat intro; subst; apply Hfg.
Qed.

Instance nominal_spectrum_compat nG nB : Proper (@PosEq nG nB ==> eq) (@nominal_spectrum nG nB).
Proof.
intros p1 p2 [? ?]. unfold nominal_spectrum. f_equal; apply fin_map_compat.
- repeat intro. subst. apply good_ext.
- repeat intro. subst. apply byz_ext.
Qed.

(** **  Equality of demons  **)

(** ***  Equality of demonic_actions  **)

Definition da_eq {nG nB} (da1 da2 : demonic_action nG nB) :=
  (forall g, da1.(frame) g = da2.(frame) g) /\
  (forall b, da1.(locate_byz) b = da2.(locate_byz) b) /\
  (forall g pos1 pos2, PosEq pos1 pos2 -> da1.(spectrum_of) g pos1 = da2.(spectrum_of) g pos2).

Instance da_eq_equiv nG nB : Equivalence (@da_eq nG nB).
Proof. split.
+ split; intuition. now apply spectrum_exteq.
+ intros d1 d2 [H1 [H2 H3]]. now repeat split; intros; rewrite H1 || rewrite H2 || rewrite (H3 _ pos2 pos1).
+ intros d1 d2 d3 [H1 [H2 H3]] [H4 [H5 H6]]. repeat split; intros; try solve [now rewrite H1, H4 | now rewrite H2, H5].
 rewrite (H3 _ pos1 pos2), (H6 _ pos2 pos1); trivial. now rewrite (spectrum_exteq d3 _ H). now symmetry.
Qed.

Instance frame_compat nG nB : Proper (@da_eq nG nB ==> eq ==> eq) (@frame nG nB).
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H1 p2). Qed.

Instance locate_byz_compat nG nB : Proper (@da_eq nG nB ==> eq ==> eq) (@locate_byz nG nB).
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 [H2 H3]]. simpl in *. apply (H2 p2). Qed.

Instance spectrum_of_compat_perm {nG nB} : Proper (@da_eq nG nB ==> eq ==> @PosEq nG nB ==> @Permutation R) (@spectrum_of nG nB). 
Proof.
intros [? ? da1 ?] [? ? da2 ?] Hda g1 g2 Hg p1 p2 Hp. unfold da_eq in Hda. simpl in *. subst.
apply (Permutation_trans (l' := nominal_spectrum p1)).
apply (spectrum_ok g2 p1). rewrite Hp. symmetry. apply spectrum_ok0.
Qed.

Instance spectrum_of_compat {nG nB} : Proper (@da_eq nG nB ==> eq ==> @PosEq nG nB ==> eq) (@spectrum_of nG nB). 
Proof.
intros [? ? da1 ?] [? ? da2 ?] Hda g1 g2 Hg p1 p2 Hp. unfold da_eq in Hda. simpl in *. subst.
rewrite (spectrum_exteq g2 p1 p2 Hp). now apply Hda.
Qed.
(*
Definition da_eq {nG nB} (da1 da2 : demonic_action nG nB) :=
  (forall g, da1.(frame) g = da2.(frame) g) /\
  (forall b, da1.(locate_byz) b = da2.(locate_byz) b).

Instance da_eq_trans nG nB : Transitive (@da_eq nG nB).
Proof.
intros d1 d2 d3 [H1 [H2 H3]] [H4 [H5 H6]].
repeat split; intros; try solve [now rewrite H1, H4 | now rewrite H2, H5].
rewrite (H3 _ _ _ H). now rewrite (H6 _ _ pos2).
Qed.

Instance da_eq_sym nG nB : Symmetric (@da_eq nG nB).
Proof.
intros d1 d2 [H1 [H2 H3]]. repeat split; intros; try solve [now rewrite H1 | now rewrite H2].
symmetry in H. now rewrite (H3 _ _ _ H).
Qed.

Instance frame_compat nG nB : Proper (@da_eq nG nB ==> eq ==> eq) (@frame nG nB).
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 [H2 H3]]. simpl in *. apply (H1 p2). Qed.

Instance locate_byz_compat nG nB : Proper (@da_eq nG nB ==> eq ==> eq) (@locate_byz nG nB).
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 [H2 H3]]. simpl in *. apply (H2 p2). Qed.

Instance spectrum_of_compat nG nB : Proper (@da_eq nG nB ==> eq ==> @PosEq nG nB ==> eq) (@spectrum_of nG nB).
Proof.
intros [] [] Hd p1 p2 Hp g1 g2 Hg. subst. destruct Hd as [H1 [H2 H3]].
simpl in *. now rewrite (H3 _ _ _ Hg).
Qed.
*)
(** ***  Equality of demons  **)
CoInductive deq {nG nB} (d1 d2 : demon nG nB) : Prop :=
  | Cdeq : da_eq (demon_head d1) (demon_head d2) -> deq (demon_tail d1) (demon_tail d2) -> deq d1 d2.

Instance deq_equiv nG nB : Equivalence (@deq nG nB).
Proof. split.
+ coinduction deq_refl. split; intuition. now rewrite H.
+ coinduction deq_sym. symmetry. now inversion H. now inversion H.
+ coinduction deq_trans.
    inversion H. inversion H0. now transitivity (demon_head y).
    apply (deq_trans (demon_tail x) (demon_tail y) (demon_tail z)).
      now inversion H. now inversion H0.
Qed.

Instance deq_bisim nG nB : Bisimulation (demon nG nB).
Proof. exists deq. apply deq_equiv. Qed.

(** **  Equality of robograms  **)

Definition req (r1 r2 : robogram) := ExtEq r1 r2.

Instance req_equiv : Equivalence req.
Proof. split.
+ split; intuition.
+ intros d1 d2 H x. now rewrite H.
+ intros d1 d2 d3 H1 H2 x. now rewrite H1, H2.
Qed.

Instance similarity_compat nG nB :
  Proper (eq ==> eq ==> (@PosEq nG nB) ==> (@PosEq nG nB)) (@similarity nG nB).
Proof.
intros k1 k2 Hk t1 t2 Ht p1 p2 [Hp1 Hp2]. subst.
split; intro; simpl; now rewrite Hp1 || rewrite Hp2.
Qed.

Instance round_compat nG nB :
  Proper (req ==> da_eq ==> (eq ==> eq) ==> eq ==> eq) (@round nG nB).
Proof.
intros r1 r2 Hr da1 da2 Hd gp1 gp2 Hgp p1 p2 Hp.
unfold req in Hr. unfold round. simpl in *.
rewrite (frame_compat Hd Hp). destruct (Rdec (frame da2 p2) 0).
  now apply Hgp.
  f_equal. now apply Hgp. f_equal. rewrite Hr.
  subst. now rewrite (Hgp p2 p2 eq_refl), Hd, Hgp.
Qed.

Instance round_compat_bis nG nB :
  Proper  (req ==> da_eq ==> ExtEq ==> ExtEq) (@round nG nB).
Proof. intros ? ? ? ? ? ? ? ? Hgp p. apply round_compat; trivial. intros ? ? ?. now subst; rewrite Hgp. Qed.


(** **  Equality of execution  **)

CoInductive eeq {nG} (e1 e2 : execution nG) : Prop :=
  | Ceeq : (forall p, (execution_head e1) p =  (execution_head e2) p) ->
           eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.

Instance eeq_equiv nG : Equivalence (@eeq nG).
Proof. split.
+ coinduction eeq_refl. split; intuition.
+ coinduction eeq_sym. symmetry. now inversion H. now inversion H.
+ coinduction eeq_trans. intro.
    inversion H. inversion H0. now transitivity (execution_head y p).
    apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
      now inversion H. now inversion H0.
Qed.

Instance eeq_bisim nG : Bisimulation (execution nG).
Proof. exists eeq. apply eeq_equiv. Qed.


Instance execution_head_compat nG : Proper (eeq ==> eq ==> eq) (@execution_head nG).
Proof. intros e1 e2 He ? ? ?. subst. inversion He. intuition. Qed.

Instance execution_tail_compat nG : Proper (eeq ==> eeq) (@execution_tail nG).
Proof. intros e1 e2 He. now inversion He. Qed.

Theorem execute_compat nG nB : Proper (req ==> deq ==> (eq ==> eq) ==> eeq) (@execute nG nB).
Proof.
intros r1 r2 Hr.
cofix proof. constructor. simpl. intro. now apply (H0 p p).
apply proof; clear proof. now inversion H. intros gp1 gp2 Heq.
inversion H. simpl. destruct x, y. simpl in *.
inversion H. simpl in *. now apply round_compat.
Qed.
