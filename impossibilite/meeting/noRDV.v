Require Import QArith.
Require Import Qcanon.
Require Import Qcabs.
Require Import ConvergentFormalism.
Require Import Morphisms.
Require Import Field.


Set Implicit Arguments.

(** *  Lemmas about Qc  **)

Lemma H01 : 1 <> 0.
Proof. now compute. Qed.

Lemma Qcinv_1 : / 1 = 1.
Proof. now compute. Qed.

Lemma Qcinv_involutive : forall q, //q = q.
Proof. intro. unfold Qcinv. qc. apply Qinv_involutive. Qed.

Lemma Qcopp_distr_plus : forall q₁ q₂, - (q₁ + q₂) = -q₁ + -q₂.
Proof. intros. ring. Qed.

Lemma Qcopp_non_0 : forall q, q <> 0 -> -q <> 0.
Proof. intros q Hq Habs. apply Hq. rewrite <- Qcopp_involutive at 1. now rewrite Habs. Qed.

Lemma Qceq_minus_iff : forall q₁ q₂, q₁ = q₂ <-> q₁ - q₂ = 0.
Proof.
intros. split; intro. subst. ring.
replace (q₂) with (0 + q₂). replace q₁ with (q₁ - q₂ + q₂) by ring.
now f_equal. ring.
Qed.

Lemma Qcmult_reg_l : forall q₁ q₂ q₃, q₃ <> 0 -> (q₃ * q₁ = q₃ * q₂ <-> q₁ = q₂).
Proof.
intros q₁ q₂ q₃ Hq₃. split; intro H. replace (q₁) with (q₁ * q₃ * /q₃).
setoid_rewrite Qcmult_comm at 2. rewrite H. setoid_rewrite Qcmult_comm at 2. 
rewrite <- Qcmult_assoc. rewrite Qcmult_inv_r. now rewrite Qcmult_1_r. assumption.
rewrite <- Qcmult_assoc. rewrite Qcmult_inv_r. now rewrite Qcmult_1_r. assumption.
now subst.
Qed.

Lemma Qcmult_reg_r : forall q₁ q₂ q₃, q₃ <> 0 -> (q₁ * q₃ = q₂ * q₃ <-> q₁ = q₂).
Proof. intros. setoid_rewrite Qcmult_comm. now apply Qcmult_reg_l. Qed.

Lemma neq_sym A : forall x y : A, x <> y -> y <> x.
Proof. auto. Qed.


Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

Lemma execute_tail : forall G B (r : robogram G B) (d : demon G B) gp,
  execution_tail (execute r d gp) = execute r (demon_tail d) (round r (demon_head d) gp).
Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.


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

Instance similarity_compat G B :
  Proper (eq ==> eq ==> (@PosEq G B) ==> (@PosEq G B)) (@similarity G B).
Proof.
intros k1 k2 Hk t1 t2 Ht p1 p2 [Hp1 Hp2]. subst.
split; intro; simpl; now rewrite Hp1 || rewrite Hp2.
Qed.

Instance round_compat G B :
  Proper (@req G B ==> @da_eq G B ==> (eq ==> eq) ==> eq ==> eq) (@round G B).
Proof.
intros [r1 Hr1] [r2 Hr2] Hr d1 d2 Hd gp1 gp2 Hgp p1 p2 Hp.
unfold req in Hr. simpl in Hr. unfold round.
rewrite (frame_compat Hd Hp). destruct (Qc_eq_dec (frame d2 p2) 0).
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


(*****************************)
(** *  The Meeting Problem  **)
(*****************************)

(** **  Definition of the Meeting problem  **)

CoInductive Together G (pt: location) (e : execution G) : Prop :=
  CTogether : (forall p, execution_head e p = pt) -> Together pt (execution_tail e) -> Together pt e.

Inductive Meeting G (pt : location) (e : execution G) : Prop :=
  | MeetNow : Together pt e -> Meeting pt e
  | MeetLater : Meeting pt (execution_tail e) -> Meeting pt e.

Definition solMeeting G B (r : robogram G B) :=
  forall (gp : G -> location) (d : demon G B), Fair d -> exists pt : location, Meeting pt (execute r d gp).

(** **  Framework for two robots  **)

Definition Zero : finite.
refine {|
  name := False;
  next := fun fo => match fo with | None => None | Some f => match f with end end;
  prev := fun fo => match fo with | None => None | Some f => match f with end end |}.
Proof.
abstract (now intros [ [] | ] [ [] | ]).
abstract (intros []).
abstract (intros []).
Defined.

Definition Zero_fun {X} : Zero -> X := fun fo => match fo with end.

Definition lift_function {G H I J : finite} (f : G -> H) (g : I -> J) (id : ident G I) : ident H J :=
  match id with
    | Good g => Good H J (f g)
    | Byz b => Byz H J (g b)
  end.

Definition lift_with_Zero {G H : finite} (f : G -> H) := lift_function f (@Zero_fun Zero).

Definition lift_automorphism {G} (σ : automorphism (name G)) : automorphism (ident G Zero).
refine {| section := lift_with_Zero σ.(section);
retraction := lift_with_Zero σ.(retraction);
Inversion := _ |}.
Proof.
abstract (intros [x | []] [y | []]; simpl; split; intro H; f_equal; injection H; apply σ.(Inversion)).
Defined.

Definition Two : finite.
refine {|
  name := bool;
  next := fun b => match b with Some true => Some false | Some false => None | None => Some true end;
  prev := fun b => match b with Some true => None | Some false => Some true | None => Some false end|}.
Proof.
abstract (destruct x as [[ | ] | ], y as [[ | ] | ]; split; intro H; reflexivity || discriminate H).
abstract (intros []; repeat (clear; apply Acc_intro; intros [] ?; try discriminate H)).
abstract (intros []; repeat (clear; apply Acc_intro; intros [] ?; try discriminate H)).
Defined.

(** Permutation of two robots **)
Definition swap : automorphism Two.
refine ({|
  section := fun b => (negb b);
  retraction := negb;
  Inversion := _ |}).
abstract (intros [] []; simpl; intuition).
Defined.

Definition swap0 : automorphism (ident Two Zero) := lift_automorphism swap.

(** A global position is defined by its position on good robots **)
Definition lift_pos {G} (pos : name G -> Qc) := {| gp := pos; bp := Zero_fun|}.

Lemma lift_pos_equiv G : forall pos : position G Zero, PosEq pos (lift_pos pos.(gp)).
Proof. intro; split; intro x; reflexivity || destruct x. Qed.

(** The reference position **)
Definition gpos : Two -> location := fun b => if b then 1 else 0.
Definition pos0 := lift_pos gpos.


Section MeetingTwo.

Variable r : robogram Two Zero.

(* The movement of robots *)
Definition move := algo r pos0.

(** Movements are always the same **)
Lemma always_same_move_true : forall (pos : name Two -> Qc) k, pos true <> pos false -> k <> 0 ->
  algo r (similarity k (pos true) (lift_pos pos)) = move * k * (pos false - pos true).
Proof.
intros pos k Hpos Hk.
assert (/ (k * (pos false - pos true)) <> 0) as Hzoom.
  apply Qcinv_non_0. intro Heq. apply Qcmult_integral in Heq.
  apply neq_sym in Hpos. rewrite Qceq_minus_iff in Hpos. destruct Heq; contradiction.
rewrite (AlgoZoom r Hzoom). unfold lift_pos, similarity, homothecy; simpl.
rewrite Qcinv_involutive. rewrite (AlgoMorph r (q := pos0) swap0). fold move. ring.
split; intros []; simpl.
  rewrite Qcmult_inv_l. reflexivity. intro Heq. apply Hzoom. now rewrite Heq.
  ring.
Qed.

Theorem always_same_move : forall (pos : name Two -> Qc) k b, pos true <> pos false -> k <> 0 ->
  algo r (similarity k (pos b) (lift_pos pos)) = move * k * (pos (negb b) - pos b).
Proof.
intros pos k [] Hpos Hk.
  now apply always_same_move_true.
  assert (- (1) <> 0) as H1 by now compute.
  rewrite (AlgoZoom r H1).
  rewrite (@AlgoMorph _ _ r _ (similarity k (pos true) (lift_pos pos)) swap0).
    simpl. rewrite always_same_move_true. field. now compute. assumption. assumption.
    split; intros []; simpl; ring.
Qed.


(** We will prove that with bad_demon, robots are always apart,
    which is enough to prove the impossibility of meeting. **)
CoInductive Always_Differ (e : execution Two) :=
  CAD : (execution_head e true <> execution_head e false) -> Always_Differ (execution_tail e) -> Always_Differ e.

Theorem different_no_meeting : forall e, Always_Differ e -> forall pt, ~Meeting pt e.
Proof.
intros e He pt Habs. induction Habs.
  inversion H. inversion He. elim H2. now do 2 rewrite H0.
  inversion He. now apply IHHabs.
Qed.
Section Ratio1.

Hypothesis Hratio : move = 1.

(** If robots go on the position of the other one (symmetrical by definition of robogram), 
    activate both and they swap position.  **)

Definition da1 : demonic_action Two Zero := {|
  locate_byz := Zero_fun;
  frame := fun _ => 1 |}.

CoFixpoint bad_demon1 : demon Two Zero := NextDemon da1 bad_demon1.

Lemma bad_demon_head1 : demon_head bad_demon1 = da1.
Proof. reflexivity. Qed.

Lemma bad_demon_tail1 : demon_tail bad_demon1 = bad_demon1.
Proof. reflexivity. Qed.

(** bad_demon1 is fair **)
Lemma Fair_bad_demon1 : Fair bad_demon1.
Proof. coinduction bad_fair1. intro g. constructor. now compute. Qed.

(** The distance is preserved between rounds **)
Lemma round_dist1 : forall pos, pos true <> pos false ->
  round r da1 pos true - round r da1 pos false = -(pos true - pos false).
Proof.
intros pos Hpos. unfold round. simpl. rewrite Qcinv_1. do 2 rewrite Qcmult_1_l.
repeat rewrite always_same_move; try (assumption || apply H01).
simpl. rewrite Hratio. ring.
Qed.

Corollary round_differ1 : forall pos, pos true <> pos false -> round r da1 pos true <> round r da1 pos false.
Proof.
intros pos Hpos Habs. rewrite Qceq_minus_iff in Habs.
apply Hpos. symmetry. rewrite Qceq_minus_iff.
replace (pos false - pos true) with (-(pos true - pos false)) by ring.
rewrite <- round_dist1. apply Habs. assumption.
Qed.

Theorem Always_Differ1 : forall pos, pos true <> pos false -> Always_Differ (execute r bad_demon1 pos).
Proof.
cofix differs. intros pos0 Hpos0. constructor. simpl. assumption.
rewrite execute_tail, bad_demon_head1, bad_demon_tail1.
apply differs. now apply round_differ1.
Qed.

End Ratio1.

Section RatioNot1.

Hypothesis Hratio : move <> 1.

Definition da2_1 : demonic_action Two Zero := {|
  locate_byz := Zero_fun;
  frame := fun b : name Two => if b then 1 else 0 |}.

Definition da2_2 : demonic_action Two Zero := {|
  locate_byz := Zero_fun;
  frame := fun b : name Two => if b then 0 else 1 |}.

CoFixpoint bad_demon2 : demon Two Zero := NextDemon da2_1 (NextDemon da2_2 bad_demon2).

Lemma bad_demon_head2_1 : demon_head bad_demon2 = da2_1.
Proof. reflexivity. Qed.

Lemma bad_demon_head2_2 : demon_head (demon_tail bad_demon2) = da2_2.
Proof. reflexivity. Qed.

Lemma bad_demon_tail2 : demon_tail (demon_tail bad_demon2) = bad_demon2.
Proof. reflexivity. Qed.

(** bad_demon2 is fair **)
Theorem Fair_bad_demon2 : Fair bad_demon2.
Proof.
cofix fair_demon. constructor.
+ intros [].
    constructor 1. rewrite bad_demon_head2_1. now simpl.
    constructor 2.
      rewrite bad_demon_head2_1. now simpl.
      constructor 1. rewrite bad_demon_head2_2. simpl. apply H01.
+ constructor. intros [].
    constructor 2.
      rewrite bad_demon_head2_2. now simpl.
      rewrite bad_demon_tail2. constructor 1. rewrite bad_demon_head2_1. simpl. apply H01.
    constructor 1. rewrite bad_demon_head2_2. simpl. apply H01.
  rewrite bad_demon_tail2. apply fair_demon.
Qed.

(** The distance is multiplied by a constant factor during a round **)
Lemma round_dist2_1 : forall ρ pos, ρ <> 0 -> pos false - pos true = ρ ->
  round r da2_1 pos false - round r da2_1 pos true = (1 - move) * ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl.
rewrite (AlgoZoom r (Qcinv_non_0 Hρ)).
rewrite Qcinv_involutive. rewrite Qcinv_1. unfold Qcminus in *.
rewrite Qcopp_distr_plus. rewrite Qcplus_assoc. rewrite Hpos.
rewrite Qcmult_plus_distr_l. do 2 rewrite Qcmult_1_l. f_equal. f_equal.
ring_simplify. f_equal.
erewrite (@AlgoMorph _ _ r _ pos0 swap0). reflexivity.
split; intros []; simpl; unfold Qcminus. rewrite Hpos. now field. ring.
Qed.

Corollary round_differ2_1 : forall pos, pos true <> pos false -> round r da2_1 pos true <> round r da2_1 pos false.
Proof.
intros pos Hpos Habs.
assert (pos false - pos true <> 0) as Hρ. intro. apply Hpos. symmetry. now rewrite Qceq_minus_iff.
symmetry in Habs. rewrite Qceq_minus_iff in Habs. apply Hρ.
rewrite (round_dist2_1 pos Hρ (refl_equal _)) in Habs.
apply Qcmult_integral in Habs. destruct Habs as [Habs | Habs].
  rewrite <- Qceq_minus_iff in Habs. symmetry in Habs. contradiction.
  contradiction.
Qed.

Lemma round_dist2_2 :  forall ρ pos, ρ <> 0 -> pos false - pos true = ρ ->
  round r da2_2 pos false - round r da2_2 pos true = (1 - move) * ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl.
rewrite (AlgoZoom r (Qcinv_non_0 Hρ)).
rewrite Qcinv_involutive. rewrite Qcinv_1. unfold Qcminus in *. 
rewrite Qcmult_plus_distr_l. do 2 rewrite Qcmult_1_l.
rewrite Qcplus_comm. rewrite Qcplus_assoc. setoid_rewrite Qcplus_comm at 2.
f_equal. assumption. rewrite Qcmult_comm. f_equal.
assert (- (1) <> 0) as H1. now compute.
rewrite (AlgoZoom r H1).
erewrite (@AlgoMorph _ _ r _ pos0 (id_perm Two Zero)). reflexivity.
split; intros []; simpl; unfold Qcminus.
replace (- (1) * (/ ρ * (1 * (pos true + - pos false)))) with (/ ρ * (pos false + - pos true)) by ring.
rewrite Hpos. now field. ring.
Qed.

Corollary round_differ2_2 : forall pos, pos true <> pos false -> round r da2_2 pos true <> round r da2_2 pos false.
Proof.
intros pos Hpos Habs.
assert (pos false - pos true <> 0) as Hρ. intro. apply Hpos. symmetry. now rewrite Qceq_minus_iff.
symmetry in Habs. rewrite Qceq_minus_iff in Habs. apply Hρ.
rewrite (round_dist2_2 pos Hρ (refl_equal _)) in Habs.
apply Qcmult_integral in Habs. destruct Habs as [Habs | Habs].
  rewrite <- Qceq_minus_iff in Habs. symmetry in Habs. contradiction.
  contradiction.
Qed.

Theorem Always_Differ2 : forall pos, pos true <> pos false -> Always_Differ (execute r bad_demon2 pos).
Proof.
cofix differs. intros pos Hpos. constructor. simpl. assumption.
constructor.
  simpl. now apply round_differ2_1.
  do 2 rewrite execute_tail. rewrite bad_demon_tail2, bad_demon_head2_1, bad_demon_head2_2.
  apply differs. apply round_differ2_2. apply round_differ2_1. assumption.
Qed.

End RatioNot1.

(** The demon that fails the robogram :
    - if robots go on the position of the other one (symmetrical by definition of robogram), 
      activate both and they swap position;
    - otherwise, just activate one and the distance between them does not become zero
      and you can scale it back on the next round.  **)
Definition bad_demon : demon Two Zero.
destruct (Qc_eq_dec move 1).
  (* Robots exchange positions *)
  exact bad_demon1.
  (* Robots do no exchange positions *)
  exact bad_demon2.
Defined.

Theorem Fair_bad_demon : Fair bad_demon.
Proof.
unfold bad_demon. destruct (Qc_eq_dec move 1).
  apply Fair_bad_demon1.
  apply Fair_bad_demon2.
Qed.

Theorem Always_Different : forall pos, pos true <> pos false ->
  Always_Differ (execute r bad_demon pos).
Proof.
intros. unfold bad_demon. destruct (Qc_eq_dec move 1).
  now apply Always_Differ1.
  now apply Always_Differ2.
Qed.


Theorem noMeeting : ~(solMeeting r).
Proof.
intro Habs. specialize (Habs gpos bad_demon Fair_bad_demon). destruct Habs as [pt Habs].
revert Habs. apply different_no_meeting.
assert (gpos false - gpos true = Qcopp 1). simpl. reflexivity.
replace (- (1)) with (/ (gpos false - gpos true)).
apply Always_Different; now compute.
Qed.

End MeetingTwo.

Check noMeeting.
Print Assumptions noMeeting.