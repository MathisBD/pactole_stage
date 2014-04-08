Require Import Reals.
Require Import ConvergentFormalismR.
Require Import EqualitiesR.
Require Import Morphisms.


Set Implicit Arguments.


Lemma Rminus1 : -1 <> 0.
Proof.
intro Habs. apply Ropp_eq_compat in Habs.
rewrite Ropp_involutive, Ropp_0 in Habs. now apply R1_neq_R0.
Qed.

Ltac Rdec := repeat
  match goal with
    | |- context[Rdec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (Rdec x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[Rdec 1 0] => 
        let Heq := fresh "Heq" in destruct (Rdec 1 0) as [Heq | Heq];
        [now elim R1_neq_R0 | clear Heq]
    | |- context[Rdec (-1) 0] => 
        let Heq := fresh "Heq" in destruct (Rdec (-1) 0) as [Heq | Heq];
        [now elim Rminus1 | clear Heq]
  end.


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

Definition lift_pos (pos : Two -> R) := {| gp := pos; bp := Zero_fun R |}.

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
intro. unfold Posopp. unfold Rminus. rewrite Ropp_involutive. do 2 rewrite Rmult_plus_distr_l.
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
Definition pos0 := {| gp := gpos; bp := Zero_fun R |}.

(* The movement of robots in the reference position *)
Definition move := algo r pos0.


(* We will prove that with bad_demon, robots are always apart. *)
CoInductive Always_Differ (e : execution Two) :=
  CAD : (execution_head e true <> execution_head e false) -> Always_Differ (execution_tail e) -> Always_Differ e.

Section Move1.

Hypothesis Hmove : move = 1.

Definition da1_1 : demonic_action Two Zero := {|
  locate_byz := Zero_fun R;
  frame := fun b : name Two => if b then - (1) else 1 |}.

Definition da1_2 : demonic_action Two Zero := {|
  locate_byz := Zero_fun R;
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
  intro. constructor. simpl. destruct g; exact Rminus1 || exact R1_neq_R0.
  constructor.
    intro. constructor. simpl. destruct g; exact Rminus1 || exact R1_neq_R0.
    rewrite bad_demon_tail1. apply bad_fair1.
Qed.

Lemma round_dist1_1 : forall pos, pos true - pos false = 1 -> round r da1_1 pos true - round r da1_1 pos false = - (1).
Proof.
intros pos Hpos. unfold round. simpl. replace (/ - (1)) with (- / 1) by (now field; compute; split).
Rdec. field_simplify. unfold Rdiv. rewrite Rinv_1. repeat rewrite Rmult_1_r.
rewrite symmetry. rewrite Ropp_involutive. unfold similarity. simpl. rewrite pos_equiv. simpl.
cut (algo r (lift_pos (fun n : bool => 1 * (pos n - pos false))) = 1).
intro Heq. rewrite Heq. ring_simplify. rewrite Hpos. ring.
assert (PosEq pos0 (lift_pos (fun n : bool => 1 * (pos n - pos false)))) as Heq.
  split; intros []; simpl; try rewrite Hpos; ring.
rewrite <- Heq. apply Hmove.
Qed.

Lemma round_dist1_2 : forall pos, pos true - pos false = - (1) -> round r da1_2 pos true - round r da1_2 pos false = 1.
Proof.
intros pos Hpos. unfold round. simpl. replace (/ - (1)) with (- / 1) by (now field; compute; split).
Rdec. field_simplify. unfold Rdiv. repeat rewrite Rinv_1 || rewrite Rmult_1_r.
rewrite symmetry. unfold similarity. simpl. rewrite pos_equiv. simpl.
cut (algo r (lift_pos (fun n : bool => - (1) * (pos n - pos false))) = 1).
  intro Heq. rewrite Heq. ring_simplify. rewrite Hpos. ring.
assert (PosEq pos0 (lift_pos (fun n : bool => - (1) * (pos n - pos false)))) as Heq.
  split; intros []; simpl; try rewrite Hpos; ring.
rewrite <- Heq. apply Hmove.
Qed.

Theorem Always_Differ1 : forall pos, pos true - pos false = 1 -> Always_Differ (execute r bad_demon1 pos).
Proof.
cofix differs. intros pos0 Hpos0. constructor.
  simpl. intro Habs. rewrite Habs in Hpos0. ring_simplify in Hpos0.
  symmetry in Hpos0. revert Hpos0. exact R1_neq_R0.
  rewrite execute_tail. constructor.
    simpl. apply round_dist1_1 in Hpos0. apply Ropp_eq_compat in Hpos0. intro Habs.
    rewrite Habs in Hpos0. ring_simplify in Hpos0.
    symmetry in Hpos0. revert Hpos0. exact R1_neq_R0.
  apply differs. clear differs. apply round_dist1_2. now apply round_dist1_1.
Qed.

End Move1.

Section MoveNot1.

Hypothesis Hmove : move <> 1.

Lemma ratio_inv : forall ρ, ρ <> 0 -> ρ / (1 - move) <> 0.
Proof.
intros ρ Hρ Habs. apply Hρ. apply (Rmult_eq_compat_l (1 - move)) in Habs.
unfold Rdiv in Habs. replace ( (1 - move) * (ρ * / (1 - move))) with (ρ * ((1 - move) * / (1 - move))) in Habs by ring.
rewrite Rinv_r in Habs. now ring_simplify in Habs. intro Heq. apply Hmove. symmetry. now apply Rminus_diag_uniq.
Qed.

Definition da2_1 ρ : demonic_action Two Zero := {|
  locate_byz := Zero_fun R;
  frame := fun b : name Two => if b then ρ else 0 |}.

Definition da2_2 ρ : demonic_action Two Zero := {|
  locate_byz := Zero_fun R;
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
      constructor 1. rewrite bad_demon_head2_2. simpl. apply Ropp_neq_0_compat. now apply ratio_inv.
  constructor. intros [].
    constructor 2.
      rewrite bad_demon_head2_2. now simpl.
      rewrite bad_demon_tail2. constructor 1. rewrite bad_demon_head2_1. simpl. now do 2 apply ratio_inv.
    constructor 1. rewrite bad_demon_head2_2. simpl. apply Ropp_neq_0_compat. now apply ratio_inv.
  rewrite bad_demon_tail2. apply fair_demon. now do 2 apply ratio_inv.
Qed.

Lemma round_dist2_1 : forall ρ pos, ρ <> 0 -> pos false - pos true = /ρ ->
  round r (da2_1 ρ) pos false - round r (da2_1 ρ) pos true = (1 - move) / ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl. Rdec. destruct (Rdec ρ 0) as [| _]. contradiction.
erewrite (@AlgoMorph _ _ r _ pos0 swap0).
fold move. unfold Rminus. ring_simplify. rewrite Hpos. now field.
split; intros []; simpl. rewrite Hpos. now rewrite Rinv_r. ring.
Qed.

Corollary round_differ2_1 : forall pos, pos true <> pos false ->
  round r (da2_1 (/(pos false - pos true))) pos true <> round r (da2_1 (/(pos false - pos true))) pos false.
Proof.
intros pos Hpos Habs.
assert (pos false - pos true <> 0) as Hρ. intro. apply Hpos. symmetry. now apply Rminus_diag_uniq.
symmetry in Habs. apply Rminus_diag_eq in Habs.
rewrite (round_dist2_1 _ (Rinv_neq_0_compat _ Hρ) (eq_sym (Rinv_involutive _ Hρ))) in Habs.
unfold Rdiv in Habs. rewrite Rinv_involutive in Habs; trivial.
apply Rmult_integral in Habs. destruct Habs as [Habs | Habs].
  apply Rminus_diag_uniq in Habs. symmetry in Habs. contradiction.
  contradiction.
Qed.

Lemma round_dist2_2 : forall ρ pos, ρ <> 0 -> pos false - pos true = /ρ ->
  round r (da2_2 ρ) pos false - round r (da2_2 ρ) pos true = (1 - move) / ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl. Rdec.
destruct (Rdec (-ρ) 0) as [Heq | _]. elim (Ropp_neq_0_compat ρ Hρ Heq).
erewrite (@AlgoMorph _ _ r _ pos0 (id_perm Two Zero)).
fold move. replace (pos false + / - ρ * move - pos true) with (pos false - pos true + / - ρ * move) by ring.
rewrite Hpos. now field.
split; intros []; simpl. replace (- ρ * (pos true - pos false)) with (ρ * (pos false - pos true)) by ring.
rewrite Hpos. now rewrite Rinv_r. ring.
Qed.

Corollary round_differ2_2 : forall pos, pos true <> pos false ->
  round r (da2_2 (/ (pos false - pos true))) pos true <> round r (da2_2 (/ (pos false - pos true))) pos false.
Proof.
intros pos Hpos Habs.
assert (pos false - pos true <> 0) as Hρ. intro. apply Hpos. symmetry. now apply Rminus_diag_uniq.
symmetry in Habs. apply Rminus_diag_eq in Habs.
rewrite (round_dist2_2 _ (Rinv_neq_0_compat _ Hρ) (eq_sym (Rinv_involutive _ Hρ))) in Habs.
unfold Rdiv in Habs. rewrite Rinv_involutive in Habs; trivial.
apply Rmult_integral in Habs. destruct Habs as [Habs | Habs].
  apply Rminus_diag_uniq in Habs. symmetry in Habs. contradiction.
  contradiction.
Qed.

Ltac shift := let Hm := fresh "Hm" in intro Hm; apply Rminus_diag_uniq in Hm;
  try (contradiction || symmetry in Hm; contradiction).

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
  assert (pos false - pos true <> 0) as Hneq. shift.
  assert ((/ (pos1 false - pos1 true) = / (pos false - pos true) / (1 - move))) as Hpos1.
    unfold pos1. unfold Rdiv. rewrite <- Rinv_mult_distr. f_equal.
    rewrite (round_dist2_1 _ (Rinv_neq_0_compat _ Hneq) (eq_sym (Rinv_involutive _ Hneq))).
    now field. assumption. shift.
  assert (pos1 false <> pos1 true). apply not_eq_sym. now apply round_differ2_1.
  assert ((/ (pos2 false - pos2 true) = / (pos1 false - pos1 true) / (1 - move))) as Hpos2.
    unfold pos2. rewrite <- Hpos1. unfold Rdiv. rewrite <- Rinv_mult_distr. f_equal.
    rewrite round_dist2_2.
      field. shift.
      apply Rinv_neq_0_compat. shift.
      rewrite Rinv_involutive. reflexivity. shift. shift. shift.
    rewrite <- Hpos1. rewrite <- Hpos2. apply differs. clear differs.
    unfold pos2. rewrite <- Hpos1. apply round_differ2_2.
    unfold pos1. apply round_differ2_1. assumption.
Qed.

End MoveNot1.

Definition bad_demon : R -> demon Two Zero.
destruct (Rdec move 1).
  (* Robots exchange positions *)
  intros _. exact bad_demon1.
  (* Robots do no exchange positions *)
  exact bad_demon2.
Defined.

Theorem Fair_bad_demon : forall ρ, ρ <> 0 -> Fair (bad_demon ρ).
Proof.
intros. unfold bad_demon. destruct (Rdec move 1).
  exact Fair_bad_demon1.
  now apply Fair_bad_demon2.
Qed.

Theorem Always_Different : forall pos, pos true - pos false = 1 ->
  Always_Differ (execute r (bad_demon (/ (pos false - pos true))) pos).
Proof.
intros pos Hpos. unfold bad_demon. destruct (Rdec move 1).
  now apply Always_Differ1.
  apply Always_Differ2. assumption. intro Habs. rewrite Habs in Hpos.
  ring_simplify in Hpos. symmetry in Hpos. revert Hpos. exact R1_neq_R0.
Qed.

Theorem different_no_meeting : forall e, Always_Differ e -> forall pt, ~WillMeet pt e.
Proof.
intros e He pt Habs. induction Habs.
  inversion H. inversion He. elim H2. now do 2 rewrite H0.
  inversion He. now apply IHHabs.
Qed.

Theorem noMeeting : ~(solMeeting r).
Proof.
assert (- (1) <> 0) as H10. exact Rminus1.
intro Habs. specialize (Habs gpos (bad_demon (- (1))) (Fair_bad_demon H10)). destruct Habs as [pt Habs].
revert Habs. apply different_no_meeting.
replace (- (1)) with (/ (gpos false - gpos true)) by (simpl; field).
apply Always_Different; simpl; field.
Qed.

End MeetingTwo.

Check noMeeting.
Print Assumptions noMeeting.