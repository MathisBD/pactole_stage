Require Import QArith.
Require Import Qcanon.
Require Import Qcabs.
Require Import ConvergentFormalism.
Require Import Equalities.
Require Import Morphisms.
Require Import Field.


Set Implicit Arguments.

(** *  Lemmas about Qc  **)

Lemma Qcinv_1 : / 1 = 1.
Proof. now compute. Qed.

Lemma Qcinv_involutive : forall q, //q = q.
Proof. intro. unfold Qcinv. qc. apply Qinv_involutive. Qed.

Lemma Qcopp_distr_plus : forall q₁ q₂, - (q₁ + q₂) = -q₁ + -q₂.
Proof. intros. ring. Qed.

Lemma Qcopp_neq_0_compat : forall q, q <> 0 -> -q <> 0.
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


(*****************************)
(** *  The Meeting Problem  **)
(*****************************)

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

Definition Zero_fun X : Zero -> X := fun fo => match fo with end.

Definition lift_function {G H I J : finite} (f : G -> H) (g : I -> J) (id : ident G I) : ident H J :=
  match id with
    | Good g => Good H J (f g)
    | Byz b => Byz H J (g b)
  end.

Definition lift_with_Zero {G H : finite} (f : G -> H) := lift_function f (Zero_fun Zero).

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

Definition lift_pos (pos : Two -> Qc) := {| gp := pos; bp := Zero_fun Qc |}.

Lemma pos_equiv : forall (pos : position Two Zero), PosEq pos (lift_pos pos.(gp)).
Proof. intro. split; intros []; now simpl. Qed.

Lemma symmetry : forall b r pos k, algo r (similarity k (pos b) (lift_pos pos))
  = algo r (similarity (- (k)) (pos (negb b)) (lift_pos pos)).
Proof. intros [] ? ? ?; apply (AlgoMorph r swap0); split; intros []; simpl; ring. Qed.

Definition Posopp (pos : Two -> location) : Two -> location := fun n => - pos n.

Lemma clotilde : forall b pos k,
 PosEq (similarity (- (k)) (- pos b) (lift_pos (Posopp pos)))
       (similarity k (pos b) (lift_pos pos)).
Proof.
intros. unfold similarity. split; simpl.
intro. unfold Posopp. unfold Qcminus. rewrite Qcopp_involutive. do 2 rewrite Qcmult_plus_distr_r.
f_equal; ring.
intros [].
Qed.

CoInductive Meet G (pt: location) (e : execution G) : Prop :=
  Meeting : (forall p, execution_head e p = pt) -> Meet pt (execution_tail e) -> Meet pt e.

Inductive WillMeet G (pt : location) (e : execution G) : Prop :=
  | Now : Meet pt e -> WillMeet pt e
  | Later : WillMeet pt (execution_tail e) -> WillMeet pt e.

Definition solMeeting G B (r : robogram G B) := forall (gp : G -> location) (d : demon G B),
  Fair d -> exists pt : location, WillMeet pt (execute r d gp).

Section MeetingTwo.

Variable r : robogram Two Zero.

(* A demon that fails the robogram :
   - if robots go on the position of the other one (symmetrical by definition of robogram), 
     activate both and they swap position;
   - otherwise, just activate one and the distance between them does not become zero
     and you can scale it back on the next round.  *)

Definition gpos : Two -> location := fun b => if b then 1 else 0.
Definition pos0 := {| gp := gpos; bp := Zero_fun Qc |}.

(* The movement of robots in the reference position *)
Definition move := algo r pos0.


(* We will prove that with bad_demon, robots are always apart. *)
CoInductive Always_Differ (e : execution Two) :=
  CAD : (execution_head e true <> execution_head e false) -> Always_Differ (execution_tail e) -> Always_Differ e.

Section Move1.

Hypothesis Hmove : move = 1.

Definition da1_1 : demonic_action Two Zero := {|
  locate_byz := Zero_fun Qc;
  frame := fun b : name Two => if b then - (1) else 1 |}.

Definition da1_2 : demonic_action Two Zero := {|
  locate_byz := Zero_fun Qc;
  frame := fun b : name Two => if b then 1 else - (1) |}.

CoFixpoint bad_demon1 : demon Two Zero := NextDemon da1_1 (NextDemon da1_2 bad_demon1).

Lemma bad_demon_tail1 : demon_tail (demon_tail bad_demon1) = bad_demon1.
Proof. reflexivity. Qed.

Lemma bad_demon_head1_1 : demon_head bad_demon1 = da1_1.
Proof. reflexivity. Qed.

Lemma bad_demon_head1_2 : demon_head (demon_tail bad_demon1) = da1_2.
Proof. reflexivity. Qed.

Lemma Fair_bad_demon1 : Fair bad_demon1.
Proof.
cofix bad_fair1. constructor.
  intro. constructor. simpl. now destruct g; compute.
  constructor.
    intro. constructor. simpl. now destruct g; compute.
    rewrite bad_demon_tail1. apply bad_fair1.
Qed.

Lemma round_dist1_1 : forall pos, pos true - pos false = 1 -> round r da1_1 pos true - round r da1_1 pos false = - (1).
Proof.
intros pos Hpos. unfold round. simpl. replace (/ - (1)) with (- / 1) by (now field; compute; split).
unfold Qcminus in *. rewrite Qcopp_distr_plus. rewrite <- Qcplus_assoc. setoid_rewrite Qcplus_comm at 2.
rewrite <- Qcplus_assoc. setoid_rewrite Qcplus_comm at 3. rewrite Qcplus_assoc.
rewrite symmetry. rewrite Qcopp_involutive. unfold similarity. simpl. rewrite pos_equiv. simpl.
rewrite Qcinv_1. rewrite Qcmult_1_l. rewrite Hpos.
cut (algo r (lift_pos (fun n : bool => 1 * (pos n - pos false))) = 1). intro Heq. rewrite Heq. ring.
assert (PosEq pos0 (lift_pos (fun n : bool => 1 * (pos n - pos false)))) as Heq.
  split; intros []; simpl; unfold Qcminus; try rewrite Hpos; ring.
rewrite <- Heq. apply Hmove.
Qed.

Lemma round_dist1_2 : forall pos, pos true - pos false = - (1) -> round r da1_2 pos true - round r da1_2 pos false = 1.
Proof.
intros pos Hpos. unfold round. simpl. replace (/ - (1)) with (- / 1) by (now field; compute; split).
unfold Qcminus in *. rewrite Qcopp_distr_plus. rewrite <- Qcplus_assoc. setoid_rewrite Qcplus_comm at 2.
rewrite <- Qcplus_assoc. setoid_rewrite Qcplus_comm at 3. rewrite Qcplus_assoc.
rewrite symmetry. rewrite Qcopp_involutive. unfold similarity. simpl. rewrite pos_equiv. simpl.
rewrite Qcinv_1. rewrite Qcmult_1_l. rewrite Hpos.
cut (algo r (lift_pos (fun n : bool => - (1) * (pos n - pos false))) = 1). intro Heq. rewrite Heq. ring.
assert (PosEq pos0 (lift_pos (fun n : bool => - (1) * (pos n - pos false)))) as Heq.
  split; intros []; simpl; unfold Qcminus; try rewrite Hpos; ring.
rewrite <- Heq. apply Hmove.
Qed.

Theorem Always_Differ1 : forall pos, pos true - pos false = 1 -> Always_Differ (execute r bad_demon1 pos).
Proof.
cofix differs. intros pos0 Hpos0. constructor.
  simpl. intro Habs. rewrite Habs in Hpos0. ring_simplify in Hpos0. discriminate Hpos0.
  rewrite execute_tail. constructor.
    simpl. apply round_dist1_1 in Hpos0. intro Habs. rewrite Habs in Hpos0. ring_simplify in Hpos0. discriminate Hpos0.
    rewrite execute_tail. rewrite bad_demon_head1_1, bad_demon_head1_2, bad_demon_tail1.
  apply differs. clear differs. apply round_dist1_2. now apply round_dist1_1.
Qed.

End Move1.

Section MoveNot1.

Hypothesis Hmove : move <> 1.

Lemma ratio_inv : forall ρ, ρ <> 0 -> ρ / (1 - move) <> 0.
Proof.
intros ρ Hρ Habs. apply Hρ. rewrite <- Qcmult_reg_r. rewrite Qcmult_0_l. apply Habs.
apply Qcinv_non_0. intro. apply Hmove. symmetry. rewrite Qceq_minus_iff. assumption.
Qed.

Definition da2_1 ρ : demonic_action Two Zero := {|
  locate_byz := Zero_fun Qc;
  frame := fun b : name Two => if b then ρ else 0 |}.

Definition da2_2 ρ : demonic_action Two Zero := {|
  locate_byz := Zero_fun Qc;
  frame := fun b : name Two => if b then 0 else -ρ |}.

CoFixpoint bad_demon2 ρ : demon Two Zero :=
  NextDemon (da2_1 ρ) 
  (NextDemon (da2_2 (ρ / (1 - move)))
  (bad_demon2 (ρ / (1 - move) / (1 - move)))). (* ρ updated *)

Lemma bad_demon_head2_1 : forall ρ, demon_head (bad_demon2 ρ) = da2_1 ρ.
Proof. reflexivity. Qed.

Lemma bad_demon_head2_2 : forall ρ, demon_head (demon_tail (bad_demon2 ρ)) = da2_2 (ρ / (1 - move)).
Proof. reflexivity. Qed.

Lemma bad_demon_tail2 :
  forall ρ, demon_tail (demon_tail (bad_demon2 ρ)) = bad_demon2 (ρ / (1 - move) / (1 - move)).
Proof. reflexivity. Qed.

Theorem Fair_bad_demon2 : forall ρ, ρ <> 0 -> Fair (bad_demon2 ρ).
Proof.
cofix fair_demon. intros ρ Hρ. constructor.
  intros [].
    constructor 1. rewrite bad_demon_head2_1. now simpl.
    constructor 2.
      rewrite bad_demon_head2_1. now simpl.
      constructor 1. rewrite bad_demon_head2_2. simpl. apply Qcopp_neq_0_compat. now apply ratio_inv.
  constructor. intros [].
    constructor 2.
      rewrite bad_demon_head2_2. now simpl.
      rewrite bad_demon_tail2. constructor 1. rewrite bad_demon_head2_1. simpl. now do 2 apply ratio_inv.
    constructor 1. rewrite bad_demon_head2_2. simpl. apply Qcopp_neq_0_compat. now apply ratio_inv.
  rewrite bad_demon_tail2. apply fair_demon. now do 2 apply ratio_inv.
Qed.

Lemma round_dist2_1 : forall ρ pos, ρ <> 0 -> pos false - pos true = /ρ ->
  round r (da2_1 ρ) pos false - round r (da2_1 ρ) pos true = (1 - move) / ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl. destruct (Qc_eq_dec ρ 0) as [| _]. contradiction.
erewrite (@AlgoMorph _ _ r _ pos0 swap0).
fold move. unfold Qcminus. ring_simplify. rewrite Hpos. now field.
split; intros []; simpl. rewrite Hpos. now rewrite Qcmult_inv_r. ring.
Qed.

Corollary round_differ2_1 : forall pos, pos true <> pos false ->
  round r (da2_1 (/(pos false - pos true))) pos true <> round r (da2_1 (/(pos false - pos true))) pos false.
Proof.
intros pos Hpos Habs.
assert (pos false - pos true <> 0) as Hρ. intro. apply Hpos. symmetry. now rewrite Qceq_minus_iff.
symmetry in Habs. rewrite Qceq_minus_iff in Habs.
rewrite (round_dist2_1 _ (Qcinv_non_0 Hρ) (eq_sym (Qcinv_involutive _))) in Habs.
unfold Qcdiv in Habs. rewrite Qcinv_involutive in Habs.
apply Qcmult_integral in Habs. destruct Habs as [Habs | Habs].
  rewrite <- Qceq_minus_iff in Habs. symmetry in Habs. contradiction.
  contradiction.
Qed.

Lemma round_dist2_2 : forall ρ pos, ρ <> 0 -> pos false - pos true = /ρ ->
  round r (da2_2 ρ) pos false - round r (da2_2 ρ) pos true = (1 - move) / ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl. destruct (Qc_eq_dec (-ρ) 0) as [Heq | _]. elim (Qcopp_neq_0_compat Hρ Heq).
erewrite (@AlgoMorph _ _ r _ pos0 (id_perm Two Zero)).
Focus 2. split; intros []; simpl. replace (- ρ * (pos true - pos false)) with (ρ * (pos false - pos true)) by ring.
rewrite Hpos. now rewrite Qcmult_inv_r. ring.
fold move. replace (pos false + / - ρ * move - pos true) with (pos false - pos true + / - ρ * move) by ring.
rewrite Hpos. field. split. assumption. now apply Qcopp_neq_0_compat.
Qed.

Corollary round_differ2_2 : forall pos, pos true <> pos false ->
  round r (da2_2 (/ (pos false - pos true))) pos true <> round r (da2_2 (/ (pos false - pos true))) pos false.
Proof.
intros pos Hpos Habs.
assert (pos false - pos true <> 0) as Hρ. intro. apply Hpos. symmetry. now rewrite Qceq_minus_iff.
symmetry in Habs. rewrite Qceq_minus_iff in Habs.
rewrite (round_dist2_2 _ (Qcinv_non_0 Hρ) (eq_sym (Qcinv_involutive _))) in Habs.
unfold Qcdiv in Habs. rewrite Qcinv_involutive in Habs.
apply Qcmult_integral in Habs. destruct Habs as [Habs | Habs].
  rewrite <- Qceq_minus_iff in Habs. symmetry in Habs. contradiction.
  contradiction.
Qed.

Theorem Always_Differ2 :
  forall pos, pos true <> pos false -> Always_Differ (execute r (bad_demon2 (/ (pos false - pos true))) pos).
Proof.
cofix differs. intros pos Hpos. constructor. simpl. assumption.
constructor.
  simpl. now apply round_differ2_1.
  do 2 rewrite execute_tail. rewrite bad_demon_tail2, bad_demon_head2_1, bad_demon_head2_2.
  pose (pos1 := round r (da2_1 (/ (pos false - pos true))) pos).
  pose (pos2 := round r (da2_2 (/ (pos false - pos true) / (1 - move))) pos1).
  fold pos1. fold pos2.
  assert ((/ (pos1 false - pos1 true) = / (pos false - pos true) / (1 - move))) as Hpos1.
    unfold pos1. unfold Qcdiv. rewrite <- Qcinv_mult_distr. f_equal.
    apply neq_sym in Hpos. rewrite Qceq_minus_iff in Hpos.
    rewrite (round_dist2_1 _ (Qcinv_non_0 Hpos) (eq_sym (Qcinv_involutive _))).
    unfold Qcdiv. rewrite Qcinv_involutive. ring.
  assert ((/ (pos2 false - pos2 true) = / (pos1 false - pos1 true) / (1 - move))) as Hpos2.
    unfold pos2. rewrite <- Hpos1. unfold Qcdiv. rewrite <- Qcinv_mult_distr. f_equal.
    rewrite round_dist2_2.
      unfold Qcdiv. rewrite Qcinv_involutive. ring.
      apply Qcinv_non_0. rewrite <- Qceq_minus_iff. apply neq_sym. apply round_differ2_1. assumption.
      rewrite Qcinv_involutive. reflexivity.
    rewrite <- Hpos1. rewrite <- Hpos2. apply differs. clear differs.
    unfold pos2. rewrite <- Hpos1. apply round_differ2_2.
    unfold pos1. apply round_differ2_1. assumption.
Qed.

End MoveNot1.

Definition bad_demon : Qc -> demon Two Zero.
destruct (Qc_eq_dec move 1).
  (* Robots exchange positions *)
  intros _. exact bad_demon1.
  (* Robots do no exchange positions *)
  exact bad_demon2.
Defined.

Theorem Fair_bad_demon : forall ρ, ρ <> 0 -> Fair (bad_demon ρ).
Proof.
intros. unfold bad_demon. destruct (Qc_eq_dec move 1).
  exact Fair_bad_demon1.
  now apply Fair_bad_demon2.
Qed.

Theorem Always_Different : forall pos, pos true - pos false = 1 ->
  Always_Differ (execute r (bad_demon (/ (pos false - pos true))) pos).
Proof.
intros pos Hpos. unfold bad_demon. destruct (Qc_eq_dec move 1).
  now apply Always_Differ1.
  apply Always_Differ2. assumption. intro Habs. rewrite Habs in Hpos. ring_simplify in Hpos. discriminate Hpos.
Qed.

Theorem different_no_meeting : forall e, Always_Differ e -> forall pt, ~WillMeet pt e.
Proof.
intros e He pt Habs. induction Habs.
  inversion H. inversion He. elim H2. now do 2 rewrite H0.
  inversion He. now apply IHHabs.
Qed.

Theorem noMeeting : ~(solMeeting r).
Proof.
assert (- (1) <> 0) as H10. now compute.
intro Habs. specialize (Habs gpos (bad_demon (- (1))) (Fair_bad_demon H10)). destruct Habs as [pt Habs].
revert Habs. apply different_no_meeting.
assert (gpos false - gpos true = Qcopp 1). simpl. reflexivity.
replace (- (1)) with (/ (gpos false - gpos true)).
apply Always_Different; now compute.
Qed.

End MeetingTwo.

Check noMeeting.
Print Assumptions noMeeting.