Require Import Reals.
Require Import Morphisms.
Require Import ConvergentFormalismR.

Set Implicit Arguments.


(****************************************)
(** *  General results about equality  **)
(****************************************)

Class Bisimulation (T : Type) := {
  bisim : T -> T -> Prop;
  bisim_equiv : Equivalence bisim}.
Infix "≈" := bisim (at level 0).


(** **  Equality of demons  **)

(** ***  Equality of demonic_actions  **)
Definition da_eq G B (da1 da2 : demonic_action G B) :=
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

Definition req G B (r1 r2 : robogram G B) := forall p, algo r1 p = algo r2 p.

Instance req_equiv G B : Equivalence (@req G B).
Proof. split.
+ split; intuition.
+ intros d1 d2 H x. now rewrite H.
+ intros d1 d2 d3 H1 H2 x. now rewrite H1, H2.
Qed.

Instance algo_compat G B : Proper (@req G B ==> @PosEq G B ==> eq) (@algo G B).
Proof.
intros r1 r2 Hr p1 p2 Hp. rewrite Hr. apply AlgoMorph with (id_perm G B).
simpl. unfold subst_pos. now destruct Hp; split; simpl.
Qed.

Instance similarity_compat G B :
  Proper (eq ==> eq ==> (@PosEq G B) ==> (@PosEq G B)) (@similarity G B).
Proof.
intros k1 k2 Hk t1 t2 Ht p1 p2 [Hp1 Hp2]. subst.
split; intro; simpl; now rewrite Hp1 || rewrite Hp2.
Qed.

(* Duplicate from MeetingTheorem_Fair *)
Definition id_perm g b : automorphism (ident g b).
refine {| section := fun x => x
        ; retraction := fun x => x
        |}.
abstract (unfold id; split; auto).
Defined.

Instance round_compat G B :
  Proper (@req G B ==> @da_eq G B ==> (eq ==> eq) ==> eq ==> eq) (@round G B).
Proof.
intros [r1 Hr1] [r2 Hr2] Hr d1 d2 Hd gp1 gp2 Hgp p1 p2 Hp.
unfold req in Hr. simpl in Hr. unfold round.
rewrite (frame_compat Hd Hp). destruct (Rdec (frame d2 p2) 0).
  now apply Hgp.
  f_equal. now apply Hgp. f_equal. simpl. rewrite Hr.
  subst. rewrite (Hgp p2 p2 refl_equal).
  apply Hr2 with (id_perm G B). apply similarity_compat; trivial.
  split; intro; simpl. symmetry. now apply Hgp.
  symmetry. apply Hd.
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

Theorem execute_compat G B : Proper ((@req G B) ==> deq ==> (eq ==> eq) ==> eeq) (@execute G B).
Proof.
intros r1 r2 Hr.
cofix proof. constructor. simpl. intro. now apply (H0 p p).
apply proof; clear proof. now inversion H. intros gp1 gp2 Heq.
inversion H. simpl. destruct x, y. simpl in *.
inversion H. simpl in *. now apply round_compat.
Qed.
