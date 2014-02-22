Require Import Reals.
Require Import ConvergentFormalismR.
Require Import EqualitiesR.
Require Import FiniteSumR.
Require Import Morphisms.


Set Implicit Arguments.

Lemma neq_sym A : forall x y : A, x <> y -> y <> x.
Proof. auto. Qed.

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


(********************************)
(** *  Fair and k-Fair demons  **)
(********************************)

(* g will be activated in at most k steps *)
Inductive AtMost {G B} g (d : demon G B) : nat -> Prop :=
  | kNow : forall k, frame (demon_head d) g <> 0 -> AtMost g d k
  | kLater : forall k, frame (demon_head d) g = 0 ->
            AtMost g (demon_tail d) k -> AtMost g d (S k).

(* k-fair: every robot is activated at most every k steps *)
CoInductive kFair {G B} k (d : demon G B) :=
  AlwayskFair : (forall g, AtMost g d k) -> kFair k (demon_tail d) ->
                kFair k d.

Lemma AtMost_LocallyFair {G B} : forall g (d : demon G B) k,
  AtMost g d k -> LocallyFairForOne g d.
Proof.
intros g d k Hg. induction Hg.
  now constructor 1.
  now constructor 2.
Qed.

Theorem kFair_Fair {G B} : forall k (d : demon G B), kFair k d -> Fair d.
Proof.
coinduction kfair_is_fair.
  destruct H. intro. now apply AtMost_LocallyFair with k.
  apply (kfair_is_fair k). now destruct H.
Qed.

Lemma AtMost_trans {G B} : forall g (d : demon G B) k,
  AtMost g d k -> forall k', (k <= k')%nat -> AtMost g d k'.
Proof.
intros g d k Hd. induction Hd; intros k' Hk.
  now constructor 1.
  destruct k'.
    now inversion Hk.
    constructor 2.
      assumption.
      apply IHHd. omega.
Qed.

Theorem kFair_trans {G B} : forall k (d: demon G B),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
coinduction fair; destruct H.
  intro. now apply AtMost_trans with k.
  now apply (fair k).
Qed.


(*****************************)
(** *  The Meeting Problem  **)
(*****************************)

CoInductive Meet G (pt: location) (e : execution G) : Prop :=
  Meeting : (forall p, execution_head e p = pt) -> Meet pt (execution_tail e) -> Meet pt e.

Inductive WillMeet G (pt : location) (e : execution G) : Prop :=
  | Now : Meet pt e -> WillMeet pt e
  | Later : WillMeet pt (execution_tail e) -> WillMeet pt e.

Definition solMeeting G B (r : robogram G B) := forall (gp : G -> location) (d : demon G B) k,
  kFair k d -> exists pt : location, WillMeet pt (execute r d gp).


(* We will prove that with [bad_demon], robots are always apart. *)
CoInductive Always_Differ G (e : execution (fplus G G)) :=
  CAD : (forall x y, execution_head e (inl x) <> execution_head e (inr y)) ->
        Always_Differ (execution_tail e) -> Always_Differ e.

Theorem different_no_meeting : forall (G : finite) e,
  inhabited G -> @Always_Differ G e -> forall pt, ~WillMeet pt e.
Proof.
intros G e [g] He pt Habs. induction Habs.
  inversion H. inversion He. elim (H2 g g). now do 2 rewrite H0.
  inversion He. now apply IHHabs.
Qed.

Lemma Always_Differ_compat G : forall e1 e2,
  eeq e1 e2 -> @Always_Differ G e1 -> Always_Differ e2.
Proof.
coinduction diff.
  intros. rewrite <- H. now destruct H0.
  destruct H. apply (diff _ _ H1). now destruct H0.
Qed.

Lemma Always_Differ_compat_iff G : Proper (eeq ==> iff) (@Always_Differ G).
Proof.
intros e1 e2 He; split; intro.
  now apply (Always_Differ_compat He).
  now apply (Always_Differ_compat (symmetry He)).
Qed.


(***********************************************************************)
(** *  Framework for an even number of robots without byzantine ones  **)
(***********************************************************************)

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

(** Permutation of two robots **)
Definition swap (G : finite) : automorphism (fplus G G).
refine ({|
  section := fun x => match x with inl a => inr a | inr b => inl b end;
  retraction := fun x => match x with inl a => inr a | inr b => inl b end;
  Inversion := _ |}).
abstract (intros [? | ?] [? | ?]; simpl; intuition; congruence).
Defined.

Definition swap0 G : automorphism (ident (fplus G G) Zero) := lift_automorphism (swap G).

Lemma swap0_involutive : forall G pos, PosEq (pos ∘ swap0 G ∘ swap0 G) pos.
Proof. split; intros []; intro; reflexivity. Qed.


Definition lift_pos G (pos : (fplus G G) -> R) := {| gp := pos; bp := Zero_fun R |}.

Lemma pos_equiv : forall G (pos : position (fplus G G) Zero), PosEq pos (lift_pos pos.(gp)).
Proof. intro. split; intros []; now simpl. Qed.


(*************************************************************)
(** *  Proof of the impossiblity of meeting for two robots  **)
(*************************************************************)

Section MeetingEven.

Variable G : finite.
Variable r : robogram (fplus G G) Zero.

(* A demon that fails the robogram :
   - if robots go on the position of the other one (symmetrical by definition of robogram), 
     activate both and they swap position;
   - otherwise, just activate one and the distance between them does not become zero
     and you can scale it back on the next round. *)

(** The reference starting position **)
Definition gpos1 : (fplus G G) -> location := fun x => match x with inl a => 0 | inr b => 1 end.
Definition pos1 := lift_pos gpos1.

(** The symmetrical position of the starting position **)
Definition gpos2 : (fplus G G) -> location := fun x => match x with inl a => 1 | inr b => 0 end.
Definition pos2 := lift_pos gpos2.

Lemma pos1_pos2_equiv : PosEq (pos1 ∘ swap0 G) pos2.
Proof. split; intros []; intro; reflexivity. Qed.

Lemma pos2_pos1_equiv : PosEq (pos2 ∘ swap0 G) pos1.
Proof. split; intros []; intro; reflexivity. Qed.

(** Relative positions in the reference positions. **)
(* The last two digits denotes the operation perfomed :
   - first  : 0 -> same scale; 1 -> inverse scale 
   - second : 0 -> same place; 1 -> shifted place *)
Lemma pos1_similarity_00 : PosEq (⟦1, 0⟧ pos1) pos1.
Proof. split; intros[]; intro x; simpl; ring. Qed.

Lemma pos2_similarity_00 : PosEq (⟦1, 0⟧ pos2) pos2.
Proof. split; intros[]; intro x; simpl; ring. Qed.

Lemma pos1_similarity_10 : PosEq (⟦- (1), 0⟧ pos1) (⟦1, 1⟧ pos2).
Proof. split; intros[]; intro x; simpl; ring. Qed.

Lemma pos2_similarity_10 : PosEq (⟦- (1), 0⟧ pos2) (⟦1, 1⟧ pos1).
Proof. split; intros[]; intro x; simpl; ring. Qed.

Lemma pos1_similarity_01 : PosEq (⟦1, 1⟧ pos1) (⟦- (1), 0⟧ pos2).
Proof. split; intros[]; intro x; simpl; ring. Qed.

Lemma pos2_similarity_01 : PosEq (⟦1, 1⟧ pos2) (⟦- (1), 0⟧ pos1).
Proof. split; intros[]; intro x; simpl; ring. Qed.

Lemma pos1_similarity_11 : PosEq (⟦- (1), 1⟧ pos1) pos2.
Proof. split; intros[]; intro x; simpl; ring. Qed.

Lemma pos2_similarity_11 : PosEq (⟦- (1), 1⟧ pos2) pos1.
Proof. split; intros[]; intro x; simpl; ring. Qed.


(** The movement of robots in the reference position **)
Definition move := algo r pos1.

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : move = 1.

Definition da1_1 : demonic_action (fplus G G) Zero := {|
  locate_byz := Zero_fun R;
  frame := fun x : fplus G G => match x with inl _ => 1 | inr _ => - (1) end |}.

Definition da1_2 : demonic_action (fplus G G) Zero := {|
  locate_byz := Zero_fun R;
  frame := fun x : fplus G G => match x with inl _ => - (1) | inr _ => 1 end |}.

CoFixpoint bad_demon1 : demon (fplus G G) Zero := NextDemon da1_1 (NextDemon da1_2 bad_demon1).

Lemma bad_demon_tail1 : demon_tail (demon_tail bad_demon1) = bad_demon1.
Proof. reflexivity. Qed.

Lemma bad_demon_head1_1 : demon_head bad_demon1 = da1_1.
Proof. reflexivity. Qed.

Lemma bad_demon_head1_2 : demon_head (demon_tail bad_demon1) = da1_2.
Proof. reflexivity. Qed.

Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof.
cofix bad_fair1. constructor.
  intro. constructor. simpl. destruct g; exact Rminus1 || exact R1_neq_R0.
  constructor.
    intro. constructor. simpl. destruct g; exact Rminus1 || exact R1_neq_R0.
    rewrite bad_demon_tail1. apply bad_fair1.
Qed.

Lemma round_dist1_1 : ExtEq (round r da1_1 gpos1) gpos2.
Proof.
intros [x | x]; unfold round; simpl; Rdec; ring_simplify.
rewrite pos1_similarity_00. fold move. rewrite Hmove. field.
rewrite pos1_similarity_11. rewrite (AlgoMorph r (swap0 G) (q:=pos1)). fold move. rewrite Hmove. field.
symmetry. apply pos2_pos1_equiv.
Qed.

Lemma round_dist1_2 : ExtEq (round r da1_2 gpos2) gpos1.
Proof.
intros [x | x]; unfold round; simpl; Rdec; ring_simplify.
rewrite pos2_similarity_11. fold move. rewrite Hmove. field.
rewrite pos2_similarity_00. rewrite (AlgoMorph r (swap0 G) (q:=pos1)). fold move. rewrite Hmove. field.
symmetry. apply pos2_pos1_equiv.
Qed.

Theorem Always_Differ1_aux : forall e, (ExtEq e gpos1) -> Always_Differ (execute r bad_demon1 e).
Proof.
cofix differs. intros e He. constructor.
  simpl. intros. subst. apply neq_sym. do 2 rewrite He. exact R1_neq_R0.
  rewrite execute_tail, bad_demon_head1_1. constructor.
    intros. subst. simpl. do 2 rewrite (round_compat_bis (reflexivity r) (reflexivity da1_1) He).
    do 2 rewrite round_dist1_1. simpl. exact R1_neq_R0.
    rewrite execute_tail, bad_demon_tail1, bad_demon_head1_2.
  apply differs. rewrite He. intro x.
  rewrite (round_compat_bis (reflexivity r) (reflexivity da1_2) (round_dist1_1)).
  apply round_dist1_2.
Qed.

Theorem Always_Differ1 : Always_Differ (execute r bad_demon1 gpos1).
Proof. apply Always_Differ1_aux. reflexivity. Qed.

End Move1.

(** **  Second case: Only one robot is activated at a time **)

Section MoveNot1.

Hypothesis Hmove : move <> 1.

Lemma ratio_inv : forall ρ, ρ <> 0 -> ρ / (1 - move) <> 0.
Proof.
intros ρ Hρ Habs. apply Hρ. apply (Rmult_eq_compat_l (1 - move)) in Habs.
unfold Rdiv in Habs. 
replace ( (1 - move) * (ρ * / (1 - move))) with (ρ * ((1 - move) * / (1 - move))) in Habs by ring.
rewrite Rinv_r in Habs. now ring_simplify in Habs. intro Heq. apply Hmove. symmetry. now apply Rminus_diag_uniq.
Qed.

Definition da2_1 ρ : demonic_action (fplus G G) Zero := {|
  locate_byz := Zero_fun R;
  frame := fun x : name (fplus G G) => match x with inl _ => ρ | inr _ => 0 end |}.

Definition da2_2 ρ : demonic_action (fplus G G) Zero := {|
  locate_byz := Zero_fun R;
  frame := fun x : name (fplus G G) => match x with inl _ => 0 | inr _ => -ρ end |}.

CoFixpoint bad_demon2 ρ : demon (fplus G G) Zero :=
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

Theorem kFair_bad_demon2 : forall ρ, ρ <> 0 -> kFair 1 (bad_demon2 ρ).
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

Lemma round_dist2_1 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall x y, round r (da2_1 ρ) pos (inr x) - round r (da2_1 ρ) pos (inl y) = (1 - move) / ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl. Rdec. destruct (Rdec ρ 0) as [| _]. contradiction.
intros x y. erewrite (@AlgoMorph _ _ r _ pos1 (id_perm (fplus G G) Zero)).
fold move. unfold Rminus. ring_simplify. rewrite Hpos. now field.
clear x; split; intros []; intro x; simpl.
  assert (forall x y, pos (inl x) = pos (inl y)) as Heq.
    intros. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
    apply Rplus_eq_reg_l with (pos (inr x)).
    unfold Rminus in Hpos. now do 2 rewrite Hpos.
  rewrite (Heq x y). ring.
  rewrite Hpos. now rewrite Rinv_r.
Qed.

Corollary round_sameX2_1 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall x x', round r (da2_1 ρ) pos (inr x) = round r (da2_1 ρ) pos (inr x').
Proof.
intros. apply Rplus_eq_reg_l with (- round r (da2_1 ρ) pos (inl x)).
setoid_rewrite Rplus_comm.
change (round r (da2_1 ρ) pos (inr x) - round r (da2_1 ρ) pos (inl x)
  = round r (da2_1 ρ) pos (inr x') - round r (da2_1 ρ) pos (inl x)).
now setoid_rewrite round_dist2_1.
Qed.

Corollary round_sameY2_1 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall y y', round r (da2_1 ρ) pos (inl y) = round r (da2_1 ρ) pos (inl y').
Proof.
intros. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
apply Rplus_eq_reg_l with (round r (da2_1 ρ) pos (inr y)).
change (round r (da2_1 ρ) pos (inr y) - round r (da2_1 ρ) pos (inl y) =
round r (da2_1 ρ) pos (inr y) - round r (da2_1 ρ) pos (inl y')).
now setoid_rewrite round_dist2_1.
Qed.

Corollary round_differ2_1 : forall pos,
  (forall x x', pos (inr x) = pos (inr x')) ->
  (forall y y', pos (inl y) = pos (inl y')) ->
  (forall x y, pos (inr x) <> pos (inl y)) ->
  forall x y x' y', round r (da2_1 (/(pos(inr x)-pos(inl y)))) pos (inr x')
                 <> round r (da2_1 (/(pos(inr x)-pos(inl y)))) pos (inl y').
Proof.
intros pos Hx Hy Hpos x y x' y' Habs.
assert (pos (inr x) - pos (inl y) <> 0) as Hρ. intro. apply (Hpos x y). now apply Rminus_diag_uniq.
apply Rminus_diag_eq in Habs. rewrite (@round_dist2_1 _ pos (Rinv_neq_0_compat _ Hρ)) in Habs.
  unfold Rdiv in Habs. rewrite Rinv_involutive in Habs; trivial.
  apply Rmult_integral in Habs. destruct Habs as [Habs | Habs].
    apply Rminus_diag_uniq in Habs. symmetry in Habs. contradiction.
    contradiction.
  intros. rewrite Rinv_involutive; trivial. now rewrite (Hx x0 x), (Hy y0 y).
Qed.

Lemma round_dist2_2 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall x y, round r (da2_2 ρ) pos (inr x) - round r (da2_2 ρ) pos (inl y) = (1 - move) / ρ.
Proof.
intros ρ pos Hρ Hpos. unfold round. simpl. Rdec.
destruct (Rdec (-ρ) 0) as [Heq | _]. elim (Ropp_neq_0_compat ρ Hρ Heq).
intros x y. erewrite (@AlgoMorph _ _ r _ pos1 (swap0 G)).
  fold move.
  replace (pos (inr x) + / - ρ * move - pos (inl y)) with (pos (inr x) - pos (inl y) + / - ρ * move) by ring.
  rewrite Hpos. now field.
split; intros []; intro n; simpl.
  assert (forall x y, pos (inr x) = pos (inr y)) as Heq.
    intros. apply Rplus_eq_reg_l with (- (pos (inl x))).
    setoid_rewrite Rplus_comm. unfold Rminus in Hpos. now do 2 rewrite Hpos.
  rewrite (Heq n x). ring.
  replace (- ρ * (pos (inl n) - pos (inr x))) with (ρ * (pos (inr x) - pos (inl n))) by ring.
  rewrite Hpos. now rewrite Rinv_r.
Qed.

Corollary round_sameX2_2 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall x x', round r (da2_2 ρ) pos (inr x) = round r (da2_2 ρ) pos (inr x').
Proof.
intros. apply Rplus_eq_reg_l with (- round r (da2_2 ρ) pos (inl x)).
setoid_rewrite Rplus_comm.
change (round r (da2_2 ρ) pos (inr x) - round r (da2_2 ρ) pos (inl x)
  = round r (da2_2 ρ) pos (inr x') - round r (da2_2 ρ) pos (inl x)).
now setoid_rewrite round_dist2_2.
Qed.

Corollary round_sameY2_2 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall y y', round r (da2_2 ρ) pos (inl y) = round r (da2_2 ρ) pos (inl y').
Proof.
intros. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
apply Rplus_eq_reg_l with (round r (da2_2 ρ) pos (inr y)).
change (round r (da2_2 ρ) pos (inr y) - round r (da2_2 ρ) pos (inl y) =
round r (da2_2 ρ) pos (inr y) - round r (da2_2 ρ) pos (inl y')).
now setoid_rewrite round_dist2_2.
Qed.

Corollary round_differ2_2 : forall pos,
  (forall x x', pos (inr x) = pos (inr x')) ->
  (forall y y', pos (inl y) = pos (inl y')) ->
  (forall x y, pos (inr x) <> pos (inl y)) ->
  forall x y x' y', round r (da2_2 (/(pos(inr x)-pos(inl y)))) pos (inr x')
                 <> round r (da2_2 (/(pos(inr x)-pos(inl y)))) pos (inl y').
Proof.
intros pos Hx Hy Hpos x y x' y' Habs.
assert (pos (inr x) - pos (inl y) <> 0) as Hρ. intro. apply (Hpos x y). now apply Rminus_diag_uniq.
apply Rminus_diag_eq in Habs. rewrite (@round_dist2_2 _ pos (Rinv_neq_0_compat _ Hρ)) in Habs.
  unfold Rdiv in Habs. rewrite Rinv_involutive in Habs; trivial.
  apply Rmult_integral in Habs. destruct Habs as [Habs | Habs].
    apply Rminus_diag_uniq in Habs. symmetry in Habs. contradiction.
    contradiction.
  intros. rewrite Rinv_involutive; trivial. now rewrite (Hx x0 x), (Hy y0 y).
Qed.

Ltac shift := let Hm := fresh "Hm" in intro Hm; apply Rminus_diag_uniq in Hm;
  try (contradiction || symmetry in Hm; contradiction).


Theorem Always_Differ2 : forall pos,
  (forall x x', pos (inr x) = pos (inr x')) ->
  (forall y y', pos (inl y) = pos (inl y')) ->
  (forall x y, pos (inr x) <> pos (inl y)) ->
  forall x y, Always_Differ (execute r (bad_demon2 (/ (pos (inr x) - pos (inl y)))) pos).
Proof.
cofix differs. intros pos Hx Hy Hpos x y. constructor; [| constructor].
(* Inital state *)
  simpl. intros. apply neq_sym. now apply Hpos.
(* State after one step *)
  simpl. intros. apply neq_sym. now apply round_differ2_1.
(* State after two steps *)
  do 2 rewrite execute_tail. rewrite bad_demon_tail2, bad_demon_head2_1, bad_demon_head2_2.
  pose (ρ := / (pos (inr x) - pos (inl y))). fold ρ.
  pose (pos1 := round r (da2_1 ρ) pos). fold pos1.
  pose (pos2 := round r (da2_2 (ρ / (1 - move))) pos1). fold pos2.
  (* properties of pos *)
  assert (pos (inr x) - pos (inl y) <> 0) as Hneq. shift. apply (Hpos _ _ Hm).
  assert (ρ <> 0) as Hρ. now apply Rinv_neq_0_compat.
  (* properties of pos1 *)
  assert (pos1 (inr x) <> pos1 (inl y)). now apply round_differ2_1.
  assert (forall x x', pos1 (inr x) = pos1 (inr x')) as Hx1.
    unfold pos1. apply round_sameX2_1. assumption. intros. unfold ρ.
    rewrite Rinv_involutive; trivial. now rewrite (Hx x0 x), (Hy y0 y).
  assert (forall y y', pos1 (inl y) = pos1 (inl y')) as Hy1.
    unfold pos1. apply round_sameY2_1. assumption. intros. unfold ρ.
    rewrite Rinv_involutive; trivial. now rewrite (Hx x0 x), (Hy y0 y).
  assert ((/ (pos1 (inr x) - pos1 (inl y)) = / (pos (inr x) - pos (inl y)) / (1 - move))) as Hpos1.
    unfold pos1. unfold Rdiv. rewrite <- Rinv_mult_distr. f_equal.
    rewrite (round_dist2_1 _ (Rinv_neq_0_compat _ Hneq)).
      now field.
      intros x' y'. rewrite Rinv_involutive; trivial. now rewrite (Hx x' x), (Hy y' y). 
      assumption.
      shift.
  (* properties of pos2 *)
  assert (forall x x', pos2 (inr x) = pos2 (inr x')) as Hx2.
    unfold pos1. apply round_sameX2_2. now apply ratio_inv. intros x' y'.
    rewrite (Hx1 x' x), (Hy1 y' y). rewrite <- Rinv_involutive at 1; trivial. f_equal. exact Hpos1. shift.
  assert (forall y y', pos2 (inl y) = pos2 (inl y')) as Hy2.
    unfold pos1. apply round_sameY2_2. now apply ratio_inv. intros x' y'.
    rewrite (Hx1 x' x), (Hy1 y' y). rewrite <- Rinv_involutive at 1; trivial. f_equal. exact Hpos1. shift.
  assert ((/ (pos2 (inr x) - pos2 (inl y)) = / (pos1 (inr x) - pos1 (inl y)) / (1 - move))) as Hpos2.
    unfold pos2. rewrite Hpos1. unfold Rdiv. repeat rewrite <- Rinv_mult_distr; try assumption || now shift.
      f_equal. rewrite round_dist2_2.
        unfold ρ. field. split; shift. now apply (Hpos x y).
        now apply ratio_inv.
        intros x' y'. rewrite (Hx1 x' x),(Hy1 y' y). rewrite <- Rinv_involutive at 1; try now shift.
        f_equal. now rewrite Hpos1.
      intro Habs. apply Rmult_integral in Habs. destruct Habs as [? | Habs]. contradiction. revert Habs. shift.
  (* final proof *)
  unfold ρ. rewrite <- Hpos1. rewrite <- Hpos2. apply differs; clear differs; try assumption.
  intros x' y'. unfold pos2, ρ. rewrite <- Hpos1. apply round_differ2_2; try assumption.
  apply round_differ2_1; assumption.
Qed.

End MoveNot1.

(** **  Merging both cases  **)

Definition bad_demon : R -> demon (fplus G G) Zero.
destruct (Rdec move 1).
  (** Robots exchange positions **)
  intros _. exact bad_demon1.
  (** Robots do no exchange positions **)
  exact bad_demon2.
Defined.

Theorem kFair_bad_demon : forall ρ, ρ <> 0 -> kFair 1 (bad_demon ρ).
Proof.
intros. unfold bad_demon. destruct (Rdec move 1).
  apply kFair_trans with 0%nat. exact kFair_bad_demon1. omega.
  now apply kFair_bad_demon2.
Qed.

Theorem noMeeting : inhabited G -> ~(solMeeting r).
Proof.
intros HG Habs. specialize (Habs gpos1 (bad_demon 1) 1%nat (kFair_bad_demon R1_neq_R0)).
destruct Habs as [pt Habs]. revert Habs. apply different_no_meeting. assumption.
destruct HG as [g]. unfold bad_demon.
destruct (Rdec move 1) as [Hmove | Hmove].
  now apply Always_Differ1.
  replace 1 with (/ (gpos1 (inr g) - (gpos1 (inl g)))) by (simpl; field).
  apply (Always_Differ2 Hmove gpos1); try reflexivity. intros. simpl. apply R1_neq_R0.
Qed.

End MeetingEven.

Check noMeeting.
Print Assumptions noMeeting.
