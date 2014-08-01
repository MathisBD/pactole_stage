Require Import Bool.
Require Import Reals.
Require Import List.
Require Import ConvergentFormalismR.
Require Import EqualitiesR.
Import FiniteSumR.
Require Import Morphisms.
Require Import Psatz.
Import Permutation.
Import Datatypes. (* to overshadow Rlist and its constructors [nil] and [cons] *)
Set Implicit Arguments.



(* ************************************ *)
(** * Some necessary results on Lists.  *)
(* ************************************ *)

Section List_results.
Context (A : Type).
(*Context (eqdec : SetoidDec.EqDec (SetoidDec.eq_setoid A)).*)

Instance In_perm_compat : Proper (eq ==> @Permutation A ==> iff) (@In A).
Proof. intros x y ? l l' Hl. subst. split; apply Permutation_in; assumption || now symmetry. Qed.

Lemma last_In : forall l (x : A), l <> List.nil -> List.In (List.last l x) l.
Proof.
induction l; intros x Hx. now elim Hx.
destruct l. now left. 
change (List.In (List.last (a0 :: l) x) (a :: a0 :: l)).
right. apply IHl. discriminate.
Qed.

Fixpoint alls (x : A) n :=
  match n with
    | 0 => Datatypes.nil
    | S m => x :: alls x m
  end.

Lemma alls_length : forall (x : A) n, length (alls x n) = n.
Proof. intros x n. induction n; simpl; auto. Qed.

Lemma alls_In : forall (x y : A) n, In y (alls x n) -> y = x.
Proof.
intros x y n Hin. induction n.
  contradiction Hin.
  destruct Hin. now symmetry. now apply IHn.
Qed.

Corollary alls_not_In : forall (x y : A) n, x <> y -> ~In y (alls x n).
Proof. intros x y n Hxy Habs. apply Hxy. symmetry. apply (alls_In _ _ _ Habs). Qed.

Lemma alls_inj1 : forall x1 x2 n1 n2, alls x1 (S n1) = alls x2 n2 -> x1 = x2.
Proof. intros x1 x2 n1 [] Heq; simpl in *. discriminate Heq. now inversion Heq. Qed.

Lemma alls_inj2 : forall x1 x2 n1 n2, alls x1 n1 = alls x2 n2 -> n1 = n2.
Proof.
intros x1 x2 n1. induction n1; intros [] Heq; try reflexivity || discriminate Heq.
f_equal. apply IHn1. now inversion Heq.
Qed.

Lemma alls_carac : forall x l, (forall y, In y l -> y = x) <-> l = alls x (length l).
Proof.
intros x l. split; intro H.
  induction l. reflexivity. simpl. f_equal.
    apply H. now left.
    apply IHl. intros y Hy. apply H. now right.
  rewrite H. intro. apply alls_In.
Qed. 

Lemma Forall_Perm_trans : forall (l1 l2 : list A) (P Q : A -> Prop),
  (eq ==> iff)%signature P Q -> Permutation l1 l2 -> List.Forall P l1 -> List.Forall Q l2.
Proof.
intros l1 l2 P Q HPQ Hperm Hfor. 
rewrite List.Forall_forall in *. intros. rewrite <- (HPQ _ _ eq_refl). 
apply Hfor. revert H. apply Permutation_in. now symmetry.
Qed.

Lemma Forall_Permutation_compat : Proper ((eq ==> iff) ==> @Permutation A ==> iff) List.Forall.
Proof. intros f g Hfg l1 l2 Hl. split; apply Forall_Perm_trans; easy || now symmetry. Qed.

Lemma Permutation_alls : forall (x : A) n l,
  Permutation l (alls x n) -> l = alls x n.
Proof.
intros x n. induction n; intros l Hl.
  simpl in *. apply Permutation_nil. now symmetry.
  destruct l.
    apply Permutation_nil in Hl. discriminate Hl.
    assert (a = x). { apply alls_In with (S n). simpl alls. rewrite <- Hl. now left. }
    subst. simpl in *. f_equal. apply IHn. apply (Permutation_cons_inv Hl).
Qed.

Lemma map_alls : forall f pt n, map f (alls pt n) = alls (f pt) n.
Proof. intros f pt n. induction n. reflexivity. simpl. now rewrite IHn. Qed.

Lemma In_nth : forall d x (l : list A), In x l -> exists n, (n < length l)%nat /\ nth n l d = x.
Proof.
intros x d l Hin. induction l.
- inversion Hin.
- destruct Hin.
    subst. exists 0%nat. split. simpl. now auto with arith. reflexivity.
    destruct (IHl H) as [n [Hn Hl]]. apply lt_n_S in Hn. exists (S n). now split.
Qed.

Lemma In_split_first : forall (x : A) l, In x l -> exists l1, exists l2, ~List.In x l1 /\ l = l1 ++ x :: l2.
Proof.
intros x l. induction l as [| a l]; intro Hin.
  now elim (List.in_nil Hin).
  destruct Hin.
    subst. exists nil. exists l. intuition.
    destruct (IHl H) as [l1 [l2 [Hnin Heq]]].
    exists (a :: l1). exists l2. subst. intuition.
Abort. (* require decidability of equality *)

Lemma Permutation_in_inside : forall (x : A) l l',
  Permutation l l' -> In x l -> exists l1 l2, l' = l1 ++ x :: l2.
Proof.
intros x l l' Hperm Hin. rewrite Hperm in Hin.
destruct (in_split _ _ Hin) as [l1 [l2 Heq]]. exists l1. exists l2. now subst l'.
Qed.
(*
Proof.
intros x l l' perm Hin. induction perm using Permutation_ind_bis.
+ inversion Hin. SearchAbout In.
+ destruct Hin.
  - subst. exists nil. exists l'. simpl. repeat split. now apply Permutation_cons.
  - destruct (IHperm H) as [l1 [l2 [Hperm Heq]]]. subst l'. exists (x0 :: l1). exists l2.
    split; trivial. simpl. etransitivity; try constructor 3. now apply Permutation_cons.
+ destruct Hin as [? | [? | Hin]]; try subst.
  - exists (cons x0 nil). exists l'. simpl. split. now do 2 constructor. reflexivity.
  - exists nil. exists (cons y l'). simpl. split. etransitivity. constructor 3. now do 2 constructor. reflexivity.
  - destruct (IHperm Hin) as [l1 [l2 [Hperm Heq]]]. subst l'.
    exists (x0 :: y :: l1). exists l2. split; trivial. simpl.
    transitivity (x0 :: y :: l). constructor. transitivity (x0 :: x :: y :: l1 ++ l2). constructor.
    transitivity (y :: x :: l1 ++ l2); constructor. assumption. constructor.
+ rewrite perm1 in Hin. destruct (IHperm2 Hin) as [l1 [l2 [Hperm Heq]]].
  subst l''. exists l1. exists l2. split. now transitivity l'. reflexivity.
Qed.
*)

Corollary Permutation_cons_inside : forall (x : A) l l',
  Permutation (x :: l) l' -> exists l1 l2, Permutation l (l1 ++ l2) /\ l' = l1 ++ x :: l2.
Proof.
intros x l l' Hperm. destruct (Permutation_in_inside x Hperm) as [l1 [l2 Heql]]. now left.
exists l1. exists l2. split.
- apply Permutation_cons_inv with x. transitivity l'. assumption. subst. symmetry. apply Permutation_middle.
- assumption.
Qed.

Lemma Permutation_NoDup : forall l l' : list A, Permutation l l' -> NoDup l -> NoDup l'.
Proof.
intros l l' Hperm. induction Hperm; intro Hdup.
+ trivial.
+ inversion_clear Hdup. constructor.
    intro Habs. apply H. now rewrite Hperm.
    auto.
+ inversion_clear Hdup. inversion_clear H0. constructor.
    intros [Habs | Habs]. subst. apply H. now left. contradiction.
    constructor. intro Habs. apply H. now right. assumption.
+ auto.
Qed.

Lemma remove_in_out eq_dec : forall (x y : A) l, y <> x -> (In x (remove eq_dec y l) <-> In x l).
Proof.
intros x y l Hxy. induction l. reflexivity.
simpl. destruct (eq_dec y a).
  subst. rewrite IHl. split; intro H. now right. now destruct H.
  simpl. now rewrite IHl.
Qed.
Global Arguments remove_in_out eq_dec [x] y l _.

Lemma remove_alls eq_dec : forall x n, remove eq_dec x (alls x n) = nil.
Proof.
intros x n. induction n.
  reflexivity.
  simpl. destruct (eq_dec x x) as [_ | Hneq]; assumption || now elim Hneq.
Qed.

Lemma remove_nil eq_dec : forall x l, remove eq_dec x l = nil -> exists n, l = alls x n.
Proof.
intros x l Hl. induction l.
  now exists 0%nat.
  simpl in Hl. destruct (eq_dec x a).
    destruct (IHl Hl) as [n ?]. subst. now exists (S n).
    discriminate Hl.
Qed.

Instance remove_Perm_proper eq_dec : Proper (eq ==> @Permutation A ==> @Permutation A) (@remove A eq_dec).
Proof.
intros x y ? l1 l2 Hl. subst. induction Hl.
- apply Permutation_refl.
- simpl. destruct (eq_dec y x). assumption. now constructor.
- simpl. destruct (eq_dec y y0), (eq_dec y x); apply Permutation_refl || now constructor.
- now constructor 4 with (remove eq_dec y l').
Qed.

Lemma remove_app eq_dec : forall (x : A) l1 l2,
  remove eq_dec x (l1 ++ l2) = remove eq_dec x l1 ++ remove eq_dec x l2.
Proof.
intros x l1 l2. induction l1. reflexivity. simpl.
destruct (eq_dec x a). apply IHl1. simpl. f_equal. apply IHl1.
Qed.

Corollary remove_inside_in eq_dec :
  forall (x : A) l1 l2, remove eq_dec x (l1 ++ x :: l2) = remove eq_dec x l1 ++ remove eq_dec x l2.
Proof. intros x ? ?. rewrite remove_app. simpl. destruct (eq_dec x x) as [| Hneq]. reflexivity. now elim Hneq. Qed.

Corollary remove_inside_out eq_dec : forall (x y : A) l1 l2,
  x <> y -> remove eq_dec x (l1 ++ y :: l2) = remove eq_dec x l1 ++ y :: remove eq_dec x l2.
Proof. intros x y ? ? ?. rewrite remove_app. simpl. destruct (eq_dec x y). contradiction. reflexivity. Qed.

Lemma remove_idempotent eq_dec : forall (x : A) l, remove eq_dec x (remove eq_dec x l) = remove eq_dec x l.
Proof.
intros x l. induction l.
  reflexivity.
  simpl. destruct (eq_dec x a) eqn:Hx.
    assumption.
    simpl. rewrite Hx. now rewrite IHl.
Qed.

Lemma remove_comm eq_dec : forall (x y : A) l,
  remove eq_dec x (remove eq_dec y l) = remove eq_dec y (remove eq_dec x l).
Proof.
intros x y l. induction l.
  reflexivity.
  simpl. destruct (eq_dec y a) eqn:Hy, (eq_dec x a) eqn:Hx; simpl;
  try rewrite Hx; try rewrite Hy; simpl; now rewrite IHl.
Qed.


Lemma count_occ_app eq_dec : forall l1 l2 (x : A),
  count_occ eq_dec (l1 ++ l2) x = (count_occ eq_dec l1 x + count_occ eq_dec l2 x)%nat.
Proof.
intros l1. induction l1; intros l2 x; simpl.
  reflexivity.
  destruct (eq_dec a x); now rewrite IHl1.
Qed.

Instance count_occ_proper eq_dec : Proper (@Permutation A ==> eq ==> eq) (@count_occ A eq_dec).
Proof.
intro l. induction l as [| x l]; intros [| x' l'] Hl ? ? ?; subst.
  reflexivity.
  apply Permutation_nil in Hl. discriminate Hl.
  symmetry in Hl. apply Permutation_nil in Hl. discriminate Hl.
  destruct (eq_dec x x') as [? | Hx].
  + subst x'. apply Permutation_cons_inv in Hl. apply IHl in Hl.
    simpl. now rewrite (Hl _ _ (eq_refl y)).
  + destruct (Permutation_cons_inside Hl) as [l1 [l2 [Hperm Heql]]].
    rewrite Heql. simpl. rewrite (IHl _ Hperm _ _ (eq_refl y)). do 2 rewrite count_occ_app.
    simpl. destruct (eq_dec x y). now apply plus_n_Sm. reflexivity.
Qed.

Lemma count_occ_remove_in eq_dec : forall (x : A) l, count_occ eq_dec (remove eq_dec x l) x = 0%nat.
Proof.
intros x l. induction l. reflexivity. simpl.
destruct (eq_dec x a) as [| Hneq]. assumption. simpl.
destruct (eq_dec a x). now elim Hneq. assumption. 
Qed.

Lemma count_occ_remove_out eq_dec :
  forall (x y : A) l, x <> y -> count_occ eq_dec (remove eq_dec x l) y = count_occ eq_dec l y.
Proof.
intros x y l Hxy. induction l. reflexivity. simpl.
destruct (eq_dec x a); simpl; destruct (eq_dec a y).
  subst. now elim Hxy.
  assumption.
  now f_equal.
  assumption.
Qed.
Global Arguments count_occ_remove_out [eq_dec] x [y] [l] _.

Lemma count_occ_alls_in eq_dec : forall x n, count_occ eq_dec (alls x n) x = n.
Proof.
intros x n. induction n; simpl.
  reflexivity.
  destruct (eq_dec x x) as [| Hneq]. now rewrite IHn. now elim Hneq. 
Qed.

Lemma count_occ_alls_out eq_dec : forall x y n, x <> y -> count_occ eq_dec (alls x n) y = 0%nat.
Proof. intros x y n Hxy. induction n; simpl; trivial; now destruct (eq_dec x y). Qed.

Theorem remove_count_occ_restore eq_dec : forall x l,
  Permutation l (alls x (count_occ eq_dec l x) ++ (remove eq_dec x l)).
Proof.
intros x l. induction l.
+ reflexivity.
+ simpl. destruct (eq_dec a x) as [| Hneq]. subst.
  - simpl. apply Permutation_cons. destruct (eq_dec x x) as [| Hneq]. assumption. now elim Hneq.
  - destruct (eq_dec x a). subst. now elim Hneq. etransitivity.
      now apply Permutation_cons, IHl.
      now apply Permutation_cons_app.
Qed.

End List_results.

Definition count_occ_properR := count_occ_proper Rdec.
Definition remove_Perm_properR := remove_Perm_proper Rdec.
Existing Instance count_occ_properR.
Existing Instance remove_Perm_properR.
Existing Instance In_perm_compat.


(** **  The same for real unumbers. **)

(** Small dedicated decision tactic for reals handling 1<>0 and r=r *)
Ltac Rdec := repeat
  match goal with
    | |- context[Rdec ?x ?x] =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
    | |- context[Rdec 1 0] => 
        let Heq := fresh "Heq" in destruct (Rdec 1 0) as [Heq | Heq];
        [now elim R1_neq_R0 | clear Heq]
    | H : context[Rdec ?x ?x] |- _ =>
        let Heq := fresh "Heq" in destruct (Rdec x x) as [Heq | Heq];
        [clear Heq | exfalso; elim Heq; reflexivity]
  end.


Lemma le_neq_lt : forall m n : nat, (n <= m -> n <> m -> n < m)%nat.
Proof. intros n m Hle Hneq. now destruct (le_lt_or_eq _ _ Hle). Qed.

Lemma Rle_neq_lt : forall x y : R, x <= y -> x <> y -> x < y.
Proof. intros ? ? Hle ?. now destruct (Rle_lt_or_eq_dec _ _ Hle). Qed.

Lemma Rdiv_reg : forall x y z, z <> 0 -> x / z = y / z -> x = y.
Proof.
intros x y z Hneq Heq. setoid_rewrite <- Rmult_1_r. rewrite <- Rinv_r with z.
setoid_rewrite <- Rmult_comm at 2 4. do 2 rewrite <- Rmult_assoc.
unfold Rdiv in Heq. now rewrite Heq. assumption.
Qed.

Lemma local_invert : forall k t x y, k <> 0 -> (k * (x - t) = k * (y - t) <-> x = y).
Proof.
intros. split; intro.
  SearchAbout Rplus eq. psatz R.
  now subst.
Qed.

(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot. We
    call a [position] a function from robots to position. An
    [execution] is an infinite (coinductive) stream of [position]s. A
    [demon] is an infinite stream of [demonic_action]s. *)

(** ** Framework for the empty set of byzantine robots **)

(** [Zero] is the (finite) empty set.  *)
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

(** This is the unique function from [Zero] to anything. *)
Definition Zero_fun X : Zero -> X := fun fo => match fo with end.

Lemma Zero_fun_equiv X : forall f : Zero -> X, ExtEq f (Zero_fun X).
Proof. intros f []. Qed.

Lemma ExtEq_Zero_PosEq {G} : forall pos1 pos2 : position G Zero, ExtEq pos1.(gp) pos2.(gp) -> PosEq pos1 pos2.
Proof. intros pos1 pos2 Hext. split; intro n. apply Hext. destruct n. Qed.

(** *** Lifting notions from good robots to (good,∅). *)

(** [lift_function f g] lifts two renaming functions, one for good and
    one for bad robots, into a renaming function for any robot. *)
Definition lift_gp {G : finite} (f : G -> R) := {| gp := f; bp := Zero_fun R |}.
(* It would be great to have it as a coercion between G → location and position,
   but I do not know how to make it work. *)

Instance lift_gp_proper {G : finite} : Proper (ExtEq ==> @PosEq G Zero) lift_gp.
Proof. intros f g Hfg. split. apply Hfg. intros []. Qed.

(** As there is no byzantine robots, a position is caracterized by the locations of good robots only. *)
Lemma lift_gp_equiv  {G} : forall pos : position G Zero, PosEq pos (lift_gp pos.(gp)).
Proof. intros [gp bp]. split; simpl. now intro. now intros []. Qed.


(** ** Some properties related to the gathering problem *)

(** [gathered_at pos pt] means that in position [pos] all robots
    are at the same location [pt] (exactly). *)
Definition gathered_at {G} (pos:G -> location) (pt:location) := forall r:G, pos r = pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive Gather {G} (pt: location) (e : execution G) : Prop :=
  Gathering : gathered_at (execution_head e) pt -> Gather pt (execution_tail e) -> Gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is
    *eventually* [Gather]ed. *)
Inductive WillGather {G} (pt : location) (e : execution G) : Prop :=
  | Now : Gather pt e -> WillGather pt e
  | Later : WillGather pt (execution_tail e) -> WillGather pt e.

(** When all robots are on two piles od the same height,
    there is no solution to the gathering problem.
    Therefore, we define these positions as [forbidden]. *)
Definition forbidden {G B} (pos : position G B) :=
  exists p1, exists p2, exists n, p1 <> p2 /\ Permutation (nominal_spectrum pos) (alls p1 n ++ alls p2 n).

(** [solGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position not [forbidden], will *eventually* be [Gather]ed. *)
Definition solGathering {G} (r : robogram) (d : demon G Zero) :=
  forall (gp : G -> location), ~forbidden (lift_gp gp) -> exists pt : location, WillGather pt (execute r d gp).

(** [Split p] means that position [p] contains to bijective sets of
    robots that do not share positions. *)
Definition Split {G} (p: (G ⊎ G) -> R) :=
  forall x y:G, p (inl x) <> p (inr y).

(** [Always_Split e] means that (infinite) execution [e] is [Split]
    forever. We will prove that with [bad_demon], robots are always
    apart. *)
CoInductive Always_Split {G} (e : execution (G ⊎ G)) :=
  CAD : Split (execution_head e) ->
        Always_Split (execution_tail e) -> Always_Split e.

(** ** Linking the different properties *)

Theorem different_no_gathering : forall (G : finite) (e:execution (G ⊎ G)),
  inhabited G -> Always_Split e -> forall pt, ~WillGather pt e.
Proof.
  intros G e [g] He pt Habs.
  induction Habs.
  - inversion H. inversion He. elim (H2 g g). now do 2 rewrite H0.
  - inversion He. now apply IHHabs.
Qed.

Lemma Always_Split_compat G : forall e1 e2,
  eeq e1 e2 -> @Always_Split G e1 -> Always_Split e2.
Proof.
  coinduction diff.
  - unfold Split in *. intros. rewrite <- H. now destruct H0.
  - destruct H. apply (diff _ _ H1). now destruct H0.
Qed.

Lemma Always_Split_compat_iff G : Proper (eeq ==> iff) (@Always_Split G).
Proof.
  intros e1 e2 He; split; intro.
  - now apply (Always_Split_compat He).
  - now apply (Always_Split_compat (symmetry He)).
Qed.


(** * Framework of the impossibility proof  **)

(** [Four] is a finite set of size four.  *)

Inductive Four_state :=
  | One4 : Four_state
  | Two4 : Four_state
  | Three4 : Four_state
  | Four4 : Four_state.

Definition Four_next fo := 
  match fo with
    | None => Some One4
    | Some One4 => Some Two4
    | Some Two4 => Some Three4
    | Some Three4 => Some Four4
    | Some Four4 => None
  end.

Definition Four_prev fo := 
  match fo with
    | None => Some Four4
    | Some Four4 => Some Three4
    | Some Three4 => Some Two4
    | Some Two4 => Some One4
    | Some One4 => None
  end.

Lemma Four_NextPrev :
  forall x y : option Four_state, Four_next x = y <-> Four_prev y = x.
Proof. intros [[] |] [[] |]; split; intro H; reflexivity || discriminate H. Qed.

(*Lemma RecNext : forall z : name, Acc NextRel z;
    RecPrev : forall z : name, Acc PrevRel z*)
Lemma Acc_next_1 : Acc (fun x y => Four_next (Some x) = Some y) One4.
Proof. apply Acc_intro. intros [] H; discriminate H. Qed.

Lemma Acc_next_2 : Acc (fun x y => Four_next (Some x) = Some y) Two4.
Proof.
apply Acc_intro. intros [] H; try discriminate H.
exact Acc_next_1.
Qed.

Lemma Acc_next_3 : Acc (fun x y => Four_next (Some x) = Some y) Three4.
Proof.
apply Acc_intro. intros [] H; try discriminate H.
exact Acc_next_2.
Qed.

Lemma Acc_next_4 : Acc (fun x y => Four_next (Some x) = Some y) Four4.
Proof.
apply Acc_intro. intros [] H; try discriminate H.
exact Acc_next_3.
Qed.

Theorem Acc_next : forall f : Four_state, Acc (fun x y => Four_next (Some x) = Some y) f.
Proof.
intros [];
solve[apply Acc_next_1
     | apply Acc_next_2
     | apply Acc_next_3
     | apply Acc_next_4].
Qed.

Lemma Acc_prev_4 : Acc (fun x y => Four_prev (Some x) = Some y) Four4.
Proof. apply Acc_intro. intros [] H; discriminate H. Qed.

Lemma Acc_prev_3 : Acc (fun x y => Four_prev (Some x) = Some y) Three4.
Proof.
apply Acc_intro. intros [] H; try discriminate H.
exact Acc_prev_4.
Qed.

Lemma Acc_prev_2 : Acc (fun x y => Four_prev (Some x) = Some y) Two4.
Proof.
apply Acc_intro. intros [] H; try discriminate H.
exact Acc_prev_3.
Qed.

Lemma Acc_prev_1 : Acc (fun x y => Four_prev (Some x) = Some y) One4.
Proof.
apply Acc_intro. intros [] H; try discriminate H.
exact Acc_prev_2.
Qed.

Theorem Acc_prev : forall f : Four_state, Acc (fun x y => Four_prev (Some x) = Some y) f.
Proof.
intros [];
solve[apply Acc_prev_1
     | apply Acc_prev_2
     | apply Acc_prev_3
     | apply Acc_prev_4].
Qed.

Definition Four : finite := {|
  name := Four_state;
  next := Four_next;
  prev := Four_prev;
  NextPrev := Four_NextPrev;
  RecNext := Acc_next;
  RecPrev := Acc_prev
  |}.

Theorem Four_dec : forall x y : Four, {x = y} + {x <> y}.
Proof. decide equality. Defined.


(** *  Some result about sorting  *)

Import Mergesort.
Print Module Mergesort.
Print Module Type Orders.TotalLeBool.

Definition Rleb (x y : R) := if Rle_lt_dec x y then true else false.

Lemma Rleb_spec : forall x y, Rleb x y = true <-> Rle x y.
Proof.
intros x y; unfold Rleb; destruct (Rle_lt_dec x y); split; intro H; trivial. inversion H. elim (Rlt_not_le _ _ r H).
Qed.

Corollary Rleb_total : forall x y, Rleb x y = true \/ Rleb y x = true.
Proof.
intros x y. unfold Rleb. destruct (Rle_lt_dec x y).
  now left.
  right. destruct (Rle_lt_dec y x). reflexivity. elim (Rlt_irrefl x). now apply Rlt_trans with y.
Qed.
Local Coercion is_true : bool >-> Sortclass.

Corollary Rleb_trans : Transitive Rleb.
Proof. intros ? ? ?. unfold is_true. setoid_rewrite Rleb_spec. apply Rle_trans. Qed.

Module Rletot : Orders.TotalLeBool with Definition t := R
                                   with Definition leb := Rleb.
  Definition t := R.
  Definition leb := Rleb.
  Definition leb_total := Rleb_total.
End Rletot.

Import Sorted.
Module Rsort := Mergesort.Sort(Rletot).
Print Module Rsort.
Import Rsort.

Ltac Rle_dec :=
  match goal with
    | |- context[Rle_lt_dec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rle_lt_dec x y) as [Heq | Hneq]
    | _ => fail
  end.

Theorem StronglySorted_uniq :
  forall l l', StronglySorted Rleb l -> StronglySorted Rleb l' -> Permutation l l' -> l = l'.
Proof.
intros l l' Hl. revert l Hl l'.
apply (StronglySorted_ind (fun l => forall l' : list R, StronglySorted Rleb l' -> Permutation l l' -> l = l')).
+ intros l' _ Hperm. symmetry. now apply Permutation_nil.
+ intros a l Hl IHl Hle l' Hl' Hperm. destruct l' as [| b l'].
  - apply Permutation_nil. now symmetry.
  - assert (a = b). 
    { destruct (Req_dec a b); trivial. apply Rle_antisym.
      - rewrite List.Forall_forall in Hle. rewrite <- Rleb_spec. apply Hle.
        cut (List.In b (a :: l)). now intros [|].
        rewrite Hperm. now left.
      - apply StronglySorted_inv in Hl'. destruct Hl' as [_ Hl'].
        rewrite List.Forall_forall in Hl'. rewrite <- Rleb_spec. apply Hl'.
        cut (List.In a (b :: l')). now intros [Hin | Hin]; try symmetry in Hin.
        rewrite <- Hperm. now left. }
    subst. f_equal. apply IHl. now apply StronglySorted_inv in Hl'.
    now apply Permutation_cons_inv with b.
Qed.

Instance sort_uniq : Proper (@Permutation R ==> eq) sort.
Proof.
intros l l' Hl. apply StronglySorted_uniq.
- apply StronglySorted_sort. exact Rleb_trans.
- apply StronglySorted_sort. exact Rleb_trans.
- transitivity l. symmetry. apply Permuted_sort. transitivity l'. assumption. apply Permuted_sort.
Qed.


Corollary StronglySorted_sort_identity : forall l, StronglySorted Rleb l -> sort l = l.
Proof.
intros l Hl. apply StronglySorted_uniq.
apply StronglySorted_sort. apply Rleb_trans.
assumption.
symmetry. apply Permuted_sort.
Qed.

Corollary sort_idempotent : forall l, sort (sort l) = sort l.
Proof. intros l. apply StronglySorted_sort_identity. apply StronglySorted_sort. apply Rleb_trans. Qed.

Lemma StronglySorted_alls : forall x n, StronglySorted Rleb (alls x n).
Proof.
intros x n. induction n. constructor.
apply SSorted_cons. assumption.
rewrite List.Forall_forall. intros e Hin. apply alls_In in Hin. subst.
unfold is_true. rewrite Rleb_spec. apply Rle_refl.
Qed.

Lemma sort_alls : forall pt n, sort (alls pt n) = alls pt n.
Proof. intros. apply StronglySorted_sort_identity. apply StronglySorted_alls. Qed.

Theorem sort_min : forall (s : spectrum) (d x : R), List.In x s ->
  List.hd d (sort s) <= x.
Proof.
intros s d x Hin.
assert (Hsort := StronglySorted_sort s Rleb_trans).
assert (Hperm := Permuted_sort s).
destruct (sort s).
- symmetry in Hperm. apply Permutation_nil in Hperm. subst. now inversion Hin.
- simpl. rewrite Hperm in Hin. destruct Hin. subst. apply Rle_refl.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort Hmin].
  rewrite List.Forall_forall in Hmin. rewrite <- Rleb_spec. now apply Hmin.
Qed.

Theorem sort_max : forall (s : spectrum) (d x : R), List.In x s ->
  x <= List.last (sort s) d.
Proof.
intros s d x Hin.
assert (Hsort := StronglySorted_sort s Rleb_trans).
assert (Hperm := Permuted_sort s).
rewrite Hperm in Hin. revert Hsort x Hin. clear Hperm. generalize (sort s).
apply (@StronglySorted_ind R _ (fun l => forall x : R, List.In x l -> x <= List.last l d)).
now intros ? [].
intros a l Hsorted HP Hle x Hin. destruct Hin.
- subst. destruct l. simpl. apply Rle_refl.
  apply Rle_trans with r. inversion_clear Hle. now rewrite <- Rleb_spec. apply HP. now left.
- destruct l. inversion H. now apply HP.
Qed.


(** *  Definitions for 4 robots **)

Implicit Type pos : position Four Zero.

(* Will not scale! *)
Theorem nominal_spectrum4 : forall pos,
  nominal_spectrum pos = (pos.(gp) Four4) :: (pos.(gp) Three4) :: (pos.(gp) Two4) :: (pos.(gp) One4) :: Datatypes.nil.
Proof.
intros [gp bp]. unfold nominal_spectrum, FiniteSumR.fold_left. simpl.
repeat (rewrite fold_left_from_equation; simpl). now compute.
Qed.

(* It needs to be defined on positions and not only on spectra.
   It is more natural and does not depend on a demon. *)

Instance forbidden_invariant : Proper (@PosEq Four Zero ==> iff) forbidden.
Proof.
intros p1 p2 Heq. split; intros [pt1 [pt2 [n [Hneq Hpt]]]]; 
exists pt1; exists pt2; exists n; split; trivial; now rewrite <- Hpt, Heq.
Qed.

(* Both Stack and has_dups should be changed to output the position of the highest stack, *if it is unique*.
   This probably requires multisets to define it propertly. *)
Definition Stack pos :=
  exists n1 : Four, exists n2 : Four, n1 <> n2 /\ pos.(gp) n1 = pos.(gp) n2.

Definition center4 (s : spectrum) := List.fold_left Rplus s 0.

(** Are robots on a stack **)
Function has_dups (l : list R) : option R :=
  match l with
    | List.nil => None
    | h :: t => if List.in_dec Rdec h t then Some h else has_dups t
  end.

(* can be proved with the correct definition *)
Hypothesis Stack_proper : Proper (@PosEq Four Zero ==> iff) Stack.
Hypothesis has_dups_invariant : Proper (@Permutation R ==> eq) has_dups.

(** Two stack of robots of the same size. **)
Definition is_forbidden (s : spectrum) :=
  match s with
    | nil => false
    | x :: l =>
      match remove Rdec x l with
        | nil => false
        | y :: l' =>
          match remove Rdec y l' with
            | nil => beq_nat (count_occ Rdec s x) (count_occ Rdec s y)
            | _ => false
          end
      end
  end.

Ltac Rdec_full :=
  match goal with
    | |- context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.

Lemma has_dups_spec : forall l x, has_dups l = Some x
  <-> (exists l1 l2, ~List.In x l1 /\ NoDup l1 /\ (forall y, In y l1 -> ~In y l2) /\ In x l2 /\ l = l1 ++ x :: l2).
Proof.
induction l; intro x; split; intro H.
+ discriminate H.
+ destruct H as [[] [l2 [_ [_ [_ [_ Habs]]]]]]; discriminate Habs.
+ simpl in H. destruct (List.in_dec Rdec a l) as [Hin | Hnin].
  - inversion H. subst. clear H. exists nil. exists l. intuition. constructor.
  - rewrite IHl in H. destruct H as [l1 [l2 [H1 [H2 [H3 [H4 H5]]]]]]. clear IHl. subst. destruct (Rdec a x).
      subst. elim Hnin. apply in_or_app. now right; left.
      exists (a :: l1). exists l2. intuition.
        destruct H; contradiction.
        constructor. intro Habs. apply Hnin. apply in_or_app. now left. assumption.
        destruct H.
          subst. apply Hnin. apply in_or_app. now do 2 right.
          now apply (H3 y).
+ destruct H as [l1 [l2 [H1 [H2 [H3 [H4 H5]]]]]]. rewrite H5. destruct l1.
    simpl in *. destruct (in_dec Rdec x l2). reflexivity. contradiction.
    rewrite <- app_comm_cons. simpl. destruct (in_dec Rdec r (l1 ++ x :: l2)) as [Hin | Hnin].
    - inversion_clear H2. elim (H3 r). now left. apply in_app_or in Hin. destruct Hin. contradiction.
      destruct H2. subst. elim H1. now left. assumption.
    - rewrite <- app_comm_cons in H5. inversion H5. subst. rewrite IHl. clear IHl H5.
      exists l1. exists l2. intuition. now inversion H2.
      now apply (H3 y); try right.
Qed.

(* PC: j'ai mis des inférieurs stricts ici, sans quoi le lemme
   has_dups_spec2 est faux pour une valeur par défaut mal choisie. Il
   y avait une raison pour mettre des <= ?
   LR: Juste une erreur de définition
       De toute façon, je pars actuellement sur utiliser la position pour 
       définir les propriétés absolues (ie ne dépendant pas d'un robot)
       et le spectre pour les versions locales utilisées par les robots *)

Definition Stack2 (s : spectrum) :=
  exists n1 n2, (n1 < List.length s)%nat /\ (n2 < List.length s)%nat /\
                n1 <> n2 /\ List.nth n1 s 0 = List.nth n2 s 0.

(* Stack does not exhibit the first repeated occurrence of a location,
   so this is not trivial to prove. *)
Lemma has_dups_spec2 : forall (s : spectrum),
  (exists r, has_dups s = Some r) -> Stack2 s.
Proof.
induction s.
+ intro Habs. 
  exfalso. destruct Habs as [? Habs]. now inversion Habs.
+ intros h.
  destruct h as [x h].
  simpl in h.
  destruct s.
    { inversion h. }
    { destruct (List.in_dec Rdec a (r :: s)).
      - unfold Stack.
        exists 0%nat.
        assert (hInnth:exists n, (n < List.length (r::s))%nat
                          /\ forall default, List.nth n (r::s) default = a).
        { admit. }
        destruct hInnth as [y hInnth].
        destruct hInnth as [hInnth1 hInnth2].
        exists (S y);intuition;auto.
        + simpl in hInnth1.
          simpl.
          omega.
        + simpl in hInnth1.
          simpl.
          omega.
        + simpl.
          simpl in hInnth2.
          symmetry.
          apply hInnth2.
      - assert (hstack:Stack2 (r::s)).
        { apply IHs.
          exists x.
          assumption. }
        unfold Stack2 in hstack.
        decompose [ex and] hstack.
        clear hstack.
        exists (S x0).
        exists (S x1).
        intuition;auto.
        + simpl in H,H0.
          simpl.
          omega.
        + simpl in H,H0.
          simpl.
          omega. }
Qed.


Lemma Stack_nonempty : forall s, Stack2 s -> s <> List.nil.
Proof. intros s [n [_ [H _]]]. intro Habs. subst. inversion H. Qed.

Lemma No_Stack_nil : ~ Stack2 Datatypes.nil.
Proof.
  intro abs.
  apply Stack_nonempty with Datatypes.nil;auto.
Qed.

(* Stack does not exhibit the first repeated occurrence of a location,
   so this is not trivial to prove. *)
Lemma has_dups_spec2bis : forall (s : spectrum),
  Stack2 s -> exists r, has_dups s = Some r.
Proof.
  intros s.
  induction s.
  - intro.
    exfalso.
    apply No_Stack_nil;auto.
  - intros has.
    destruct (List.in_dec Rdec a s) eqn:heq.
    + exists a.
      simpl.
      destruct s.
      * inversion i.
      * rewrite heq.
        reflexivity.
    + assert (hstacks:Stack2 s).
      { unfold Stack2 in has.
        decompose [and ex] has.
        clear has.
        (* x cannot be 0 since a is not repeated in s. *)
        destruct x.
        { exfalso.
          simpl List.nth in H3 at 1.
          destruct x0.
          { omega. }
          simpl in H3.
          apply n.
          rewrite H3.
          apply List.nth_In.
          simpl in H0.
          omega. }
        (* x0 cannot be 0 since a is not repeated in s. *)
        destruct x0.
        { exfalso.
          simpl List.nth in H3 at 1.
          simpl in H3.
          apply n.
          rewrite <- H3.
          apply List.nth_In.
          simpl in H.
          omega. }
        simpl in H3.
        exists x.
        exists x0.
        intuition;auto. }
      specialize (IHs hstacks).
      destruct IHs.
      exists x.
      simpl.
      destruct s.
      * exfalso.
        apply No_Stack_nil;auto.
      * rewrite heq.
        assumption.
Qed.


Lemma has_dups_NoDup_None : forall l, has_dups l = None <-> NoDup l.
Proof.
induction l.
+ split; intro. constructor. reflexivity.
+ simpl. destruct (in_dec Rdec a l).
  - split; intro H. discriminate H. inversion H. contradiction.
  - split; intro H; rewrite IHl in *. now constructor. now inversion H.
Qed.

Lemma has_dups_NoDup_Some : forall l, (exists pt, has_dups l = Some pt) <-> ~NoDup l.
Proof.
intro l. split; intro H.
  intro Hl. rewrite <- has_dups_NoDup_None in Hl. rewrite Hl in H. destruct H as [pt H]. discriminate H.
  rewrite <- has_dups_NoDup_None in H. destruct (has_dups l). now exists r. now elim H.
Qed.

Theorem has_dups_Stack : forall pos, Stack pos <-> exists pt, has_dups (nominal_spectrum pos) = Some pt.
Proof.
intro pos. rewrite nominal_spectrum4. split.
- intros [n1 [n2 [Hneq Heq]]]. unfold has_dups. simpl. repeat Rdec_full; try
  match goal with |- exists pt : R, Some ?n = Some pt => now exists n end.
  destruct n1, n2; (now elim Hneq) || contradiction || (symmetry in Heq; contradiction).
- intros [pt Hpt]. revert Hpt. unfold has_dups. simpl. repeat Rdec_full; intro Hpt; try discriminate Hpt;
  match goal with H : gp pos ?n = gp pos ?m |- _ => exists n; exists m end; split; discriminate || assumption.
Qed.

Corollary Stack_NoDup : forall pos, Stack pos <-> ~NoDup (nominal_spectrum pos).
Proof. intro. rewrite has_dups_Stack. apply has_dups_NoDup_Some. Qed.
(*
Proof.
intro pos. split; intro H.
+ intro Habs. rewrite nominal_spectrum4 in Habs. inversion_clear Habs.
  inversion_clear H1. inversion_clear H3. inversion_clear H4. clear H5.
  destruct H as [[] [[] [Hneq Heq]]]; (now elim Hneq) || rewrite Heq in *; intuition.
+ rewrite <- has_dups_NoDup in H. SearchAbout None Some.
  case_eq (has_dups (nominal_spectrum pos)); intros r Hr || intro; try contradiction.
  rewrite has_dups_spec in Hr. destruct Hr as [l1 [l2 [Hl1 [Hn1 [Hin [Hl2 Heq]]]]]].
  assert (Hlength : length (l1 ++ r :: l2) = 4%nat). { rewrite <- Heq. now rewrite nominal_spectrum4. }
  rewrite app_length in Hlength. simpl in *.
  destruct l1 as [| a [| b [| c [|]]]]; destruct l2 as [| a' [| b' [| c' [|]]]];
  simpl in *; try discriminate Hlength; try (rewrite plus_comm in Hlength; discriminate Hlength); clear Hlength;
  repeat (destruct Hl2 as [Hl2 | Hl2]); ((now elim Hl2) || subst);
    rewrite nominal_spectrum4 in Heq; inversion Heq;
    match goal with
      | H : gp pos ?n = gp pos ?m |- _ => exists n; exists m
    end; split; discriminate || assumption.
Qed.
*)

(* If the position is forbidden, we have two possible stacks. *)
Lemma has_dups_None_invariant :
  forall (s s' : spectrum), Permutation s s' -> (has_dups s = None <-> has_dups s' = None).
Proof. intros. do 2 rewrite has_dups_NoDup_None. split; apply Permutation_NoDup; assumption || now symmetry. Qed.

Lemma has_dups_map : forall pt f s, has_dups s = Some pt -> has_dups (map f s) = Some (f pt).
Proof. Admitted.
(* can be proven with a correct definition for has_dups *)

Corollary has_dups_similarity : forall pt k t pos,
  has_dups (nominal_spectrum pos) = Some pt -> has_dups (nominal_spectrum (⟦ k, t⟧ pos)) = Some (k * (pt - t)).
Proof. intros. rewrite nominal_spectrum_similarity. now rewrite (@has_dups_map pt). Qed.

Lemma has_dups_similarity_None : forall k t pos, k <> 0 ->
  has_dups (nominal_spectrum pos) = None -> has_dups (nominal_spectrum (⟦ k, t⟧ pos)) = None.
Proof.
intros k t pos Hk. do 2 rewrite nominal_spectrum4.
simpl; repeat Rdec_full; intros Hnone; discriminate Hnone ||
  now (rewrite local_invert in Heq) || idtac.
Qed.

Ltac Rdec_aux H :=
  match type of H with
    | context[Rdec ?x ?y] =>
      let Heq := fresh "Heq" in let Hneq := fresh "Hneq" in
      destruct (Rdec x y) as [Heq | Hneq]
    | _ => fail
  end.


(**  Back to the proof  **)

Lemma remove_alls_2 : forall x y l n, remove Rdec x l = alls y (S n) -> forall z, In z (x :: l) <-> z = x \/ z = y.
Proof.
intros x y l n Hl z. split; intro Hin.
- destruct (Rdec z x). now left. right.
  rewrite <- (remove_in_out Rdec x) in Hin.
  simpl in Hin. Rdec. rewrite Hl in Hin.
  now apply alls_In with (S n). auto.
- destruct (Rdec z x). subst. now left. destruct Hin. contradiction. subst.
  right. rewrite <- (remove_in_out Rdec x). rewrite Hl. now left. auto.
Qed.

Theorem is_forbidden_correct : forall pos,
  is_forbidden (nominal_spectrum pos) = true -> forbidden pos.
Proof.
unfold is_forbidden. intros pos H.
destruct (nominal_spectrum pos) eqn:Hnom; try discriminate H.
destruct (remove Rdec r s) as [| r' s'] eqn:Hs; try discriminate H.
destruct (remove Rdec r' s') eqn:Hs'; try discriminate H.
apply remove_nil in Hs'. destruct Hs' as [n Hs']. subst s'.
assert (Hin : forall x, In x (r :: s) <-> x = r \/ x = r'). { intro. now apply remove_alls_2 with n. }
assert (Hneq : r <> r'). { intro. subst r'. apply (remove_In Rdec s r). rewrite Hs. now left. }
assert (Hr : count_occ Rdec (r :: s) r = S n).
{ symmetry in H. apply beq_nat_eq in H. rewrite H. rewrite <- (count_occ_remove_out r Hneq).
  simpl. Rdec. rewrite Hs. simpl. Rdec. now rewrite count_occ_alls_in. }
exists r. exists r'. exists (S n). split; trivial.
rewrite Hnom. clear Hnom. rewrite (remove_count_occ_restore Rdec r). simpl remove. Rdec. now rewrite Hr, Hs.
Qed.

(* In the general case, we also need the hypothesis that G contains at least 2 elements. *)
Theorem is_forbidden_complete : forall pos, @forbidden Four Zero pos -> is_forbidden (nominal_spectrum pos) = true.
Proof.
unfold is_forbidden. intros pos H.
destruct H as [pt1 [pt2 [n [Hneq Hperm]]]].
destruct (nominal_spectrum pos) as [| r [| r' s]] eqn:Hnom.
(* the hypothesis on G is used in the next 2 lines *)
+ rewrite nominal_spectrum4 in Hnom. discriminate Hnom.
+ rewrite nominal_spectrum4 in Hnom. discriminate Hnom.
+ destruct n. simpl in Hperm. symmetry in Hperm. apply Permutation_nil in Hperm. discriminate Hperm.
  assert (Hin : forall x, In x (nominal_spectrum pos) <-> x = pt1 \/ x = pt2).
  { intro x. rewrite Hnom, Hperm, in_app_iff. split; intros [Hin | Hin]; subst.
      left. now apply (alls_In pt1 x (S n)).
      right. now apply (alls_In pt2 x (S n)).
      now do 2 left.
      now right; left. }
  assert (Heqr : r = pt1 \/ r = pt2). { rewrite <- Hin, Hnom. now left. }
  assert (Heqr' : r' = pt1 \/ r' = pt2). { rewrite <- Hin, Hnom. now right; left. }
  { destruct Heqr, Heqr'; subst r r'; simpl remove at 1; Rdec.
  (* Four main cases *)
  * destruct (remove Rdec pt1 s) eqn:Hrem1.
    + elim (@in_nil _ pt2). rewrite <- Hrem1.
      replace (remove Rdec pt1 s) with (remove Rdec pt1 (pt1 :: pt1 :: s)) by now simpl; Rdec.
      rewrite Hperm. rewrite remove_app. apply in_or_app. right. rewrite remove_in_out. now left. assumption.
    + assert (Heqr : r = pt2).
      { assert (Hr : r <> pt1). { intro. subst r. apply (remove_In Rdec s pt1). rewrite Hrem1. now left. }
        assert (Hrin : In r (nominal_spectrum pos)).
        { rewrite Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt1). rewrite Hrem1. now left. auto. }
        rewrite Hin in Hrin. now destruct Hrin. }
      subst r. destruct (remove Rdec pt2 l) eqn:Hrem2.
      - rewrite Hperm. do 2 rewrite count_occ_app. repeat rewrite count_occ_alls_in, count_occ_alls_out.
        rewrite beq_nat_true_iff. now auto.
        assumption. auto.
      - assert (r <> pt2). { intro. subst r. apply (remove_In Rdec l pt2). rewrite Hrem2. now left. }
        assert (r <> pt1).
        { intro. subst r. apply (remove_In Rdec s pt1). rewrite Hrem1. right.
          rewrite <- (remove_in_out Rdec pt2). rewrite Hrem2. now left. auto. }
        assert (Habs : r = pt1 \/ r = pt2).
        { rewrite <- Hin, Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt1); auto. rewrite Hrem1. right.
          rewrite <- (remove_in_out Rdec pt2); auto. rewrite Hrem2. now left. }
        now destruct Habs.
  * destruct (Rdec pt1 pt2) eqn:Hpt; try contradiction.
    assert (Hc1 : count_occ Rdec (pt1 :: pt2 :: s) pt1 = S n).
    { rewrite Hperm. rewrite count_occ_app. rewrite count_occ_alls_in, count_occ_alls_out. auto. auto. }
    assert (Hc2 : count_occ Rdec (pt1 :: pt2 :: s) pt2 = S n).
    { rewrite Hperm. rewrite count_occ_app. rewrite count_occ_alls_in, count_occ_alls_out. auto. auto. }
    destruct (remove Rdec pt1 s) eqn:Hrem1.
    + simpl. Rdec. rewrite Hpt. destruct (Rdec pt2 pt1) eqn:Htp. now elim Hneq.
      simpl in Hc1, Hc2. Rdec. rewrite Htp in Hc1. rewrite Hpt in Hc2. rewrite Hc1, Hc2. now rewrite <- beq_nat_refl.
    + simpl remove. destruct (Rdec pt2 r).
      - subst r. destruct (remove Rdec pt2 l) eqn:Hrem2.
          rewrite Hc1, Hc2. now rewrite <- beq_nat_refl.
          assert (r <> pt2). { intro. subst r. apply (remove_In Rdec l pt2). rewrite Hrem2. now left. }
          assert (r <> pt1).
          { intro. subst r. apply (remove_In Rdec s pt1). rewrite Hrem1. right.
            rewrite <- (remove_in_out Rdec pt2). rewrite Hrem2. now left. auto. }
          assert (Habs : r = pt1 \/ r = pt2).
          { rewrite <- Hin, Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt1); auto. rewrite Hrem1. right.
            rewrite <- (remove_in_out Rdec pt2); auto. rewrite Hrem2. now left. }
          now destruct Habs.
      - assert (r <> pt1). { intro. subst r. apply (remove_In Rdec s pt1). rewrite Hrem1. now left. }
        assert (Habs : r = pt1 \/ r = pt2).
        { rewrite <- Hin, Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt1); auto. rewrite Hrem1. now left. }
        destruct Habs; auto.
  * destruct (Rdec pt2 pt1) eqn:Htp; try now elim Hneq.
    assert (Hc1 : count_occ Rdec (pt2 :: pt1 :: s) pt1 = S n).
    { rewrite Hperm. rewrite count_occ_app. rewrite count_occ_alls_in, count_occ_alls_out. auto. auto. }
    assert (Hc2 : count_occ Rdec (pt2 :: pt1 :: s) pt2 = S n).
    { rewrite Hperm. rewrite count_occ_app. rewrite count_occ_alls_in, count_occ_alls_out. auto. auto. }
    destruct (remove Rdec pt2 s) eqn:Hrem1.
    + simpl. Rdec. rewrite Htp. destruct (Rdec pt1 pt2) eqn:Hpt. now elim Hneq.
      simpl in Hc1, Hc2. Rdec. rewrite Htp in Hc1. rewrite Hpt in Hc2. rewrite Hc1, Hc2. now rewrite <- beq_nat_refl.
    + simpl remove. destruct (Rdec pt1 r).
      - subst r. destruct (remove Rdec pt1 l) eqn:Hrem2.
          rewrite Hc1, Hc2. now rewrite <- beq_nat_refl.
          assert (r <> pt1). { intro. subst r. apply (remove_In Rdec l pt1). rewrite Hrem2. now left. }
          assert (r <> pt2).
          { intro. subst r. apply (remove_In Rdec s pt2). rewrite Hrem1. right.
            rewrite <- (remove_in_out Rdec pt1). rewrite Hrem2. now left. auto. }
          assert (Habs : r = pt1 \/ r = pt2).
          { rewrite <- Hin, Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt2); auto. rewrite Hrem1. right.
            rewrite <- (remove_in_out Rdec pt1); auto. rewrite Hrem2. now left. }
          now destruct Habs.
      - assert (r <> pt2). { intro. subst r. apply (remove_In Rdec s pt2). rewrite Hrem1. now left. }
        assert (Habs : r = pt1 \/ r = pt2).
        { rewrite <- Hin, Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt2); auto. rewrite Hrem1. now left. }
        destruct Habs; auto.
  * destruct (remove Rdec pt2 s) eqn:Hrem1.
    + elim (@in_nil _ pt1). rewrite <- Hrem1.
      replace (remove Rdec pt2 s) with (remove Rdec pt2 (pt2 :: pt2 :: s)) by now simpl; Rdec.
      rewrite Hperm. rewrite remove_app. apply in_or_app. left. rewrite remove_in_out. now left. auto.
    + assert (Heqr : r = pt1).
      { assert (Hr : r <> pt2). { intro. subst r. apply (remove_In Rdec s pt2). rewrite Hrem1. now left. }
        assert (Hrin : In r (nominal_spectrum pos)).
        { rewrite Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt2). rewrite Hrem1. now left. auto. }
        rewrite Hin in Hrin. now destruct Hrin. }
      subst r. destruct (remove Rdec pt1 l) eqn:Hrem2.
      - rewrite Hperm. do 2 rewrite count_occ_app. repeat rewrite count_occ_alls_in, count_occ_alls_out.
        rewrite beq_nat_true_iff. now auto.
        auto. assumption.
      - assert (r <> pt1). { intro. subst r. apply (remove_In Rdec l pt1). rewrite Hrem2. now left. }
        assert (r <> pt2).
        { intro. subst r. apply (remove_In Rdec s pt2). rewrite Hrem1. right.
          rewrite <- (remove_in_out Rdec pt1). rewrite Hrem2. now left. auto. }
        assert (Habs : r = pt1 \/ r = pt2).
        { rewrite <- Hin, Hnom. do 2 right. rewrite <- (remove_in_out Rdec pt2); auto. rewrite Hrem1. right.
          rewrite <- (remove_in_out Rdec pt1); auto. rewrite Hrem2. now left. }
        now destruct Habs. }
Qed.

Corollary is_forbidden_true : forall pos, is_forbidden (@nominal_spectrum Four Zero pos) = true <-> forbidden pos.
Proof. intro pos. split; intro H. now apply is_forbidden_correct. now apply is_forbidden_complete. Qed.

Corollary is_forbidden_false : forall pos, is_forbidden (nominal_spectrum pos) = false <-> ~forbidden pos.
Proof.
intro pos. assert (Hp := is_forbidden_true pos).
destruct (is_forbidden (nominal_spectrum pos)); rewrite <- Hp; intuition.
Qed.

Lemma is_forbidden_alls : forall pt n, is_forbidden (alls pt n) = false.
Proof. intros pt [| n]. reflexivity. unfold is_forbidden. simpl. Rdec. now rewrite remove_alls. Qed.

Instance is_forbidden_Permutation_proper : Proper (@Permutation R ==> eq) is_forbidden.
Proof.
intros [| r l] [| r' l'] Hperm.
reflexivity. apply Permutation_nil in Hperm. discriminate Hperm.
symmetry in Hperm. apply Permutation_nil in Hperm. discriminate Hperm.
unfold is_forbidden at 1. simpl remove. Rdec. destruct (remove Rdec r l) as [| r1 l1] eqn:Hrem.
+ unfold is_forbidden. apply remove_nil in Hrem. destruct Hrem as [n Hn].
  rewrite Hn in Hperm. symmetry in Hperm. change (r :: alls r n) with (alls r (S n)) in Hperm.
  apply Permutation_alls in Hperm. rewrite Hperm. inversion Hperm. subst. now rewrite remove_alls.
+ simpl count_occ. Rdec. destruct (Permutation_cons_inside Hperm) as [l2 [l3 [H1 H2]]].
  destruct (Rdec r r1) as [| Hneq]. subst r. exfalso. elim (remove_In Rdec l r1). rewrite Hrem. now left.
  destruct (remove Rdec r1 l1) as [| r4 l4] eqn:Hrem2.
  - apply remove_nil in Hrem2. destruct Hrem2 as [n Hn]. subst l1.
     assert (Heq : count_occ Rdec l r1 = S n).
    { rewrite <- (count_occ_remove_out r Hneq). rewrite Hrem. simpl. Rdec. now rewrite count_occ_alls_in. }
    rewrite Heq.
    (* there are only two differents elements inside l *)
    assert (Hl : forall x, In x (r :: l) <-> x = r \/ x = r1).
    { apply remove_alls_2 with n. simpl in Hrem. Rdec. apply Hrem. }
    (* the same goes for l' as it is a permutation of l *)
    assert (Hl' : forall x, In x (r' :: l') <-> x = r \/ x = r1). { intro x. rewrite <- Hl. now rewrite Hperm. }
    assert (Hr' : r' = r \/ r' = r1). { rewrite <- Hl'. now left. }
    destruct (Rdec r' r) as [| Hrr'].
    (* the first elements in both lists are the same *)
    * subst r'. unfold is_forbidden.
      assert (Hr : remove Rdec r l' = alls r1 (S n)).
      { apply Permutation_alls. simpl alls. rewrite <- Hrem. apply Permutation_cons_inv in Hperm. now rewrite Hperm. }
      rewrite Hr. simpl. rewrite remove_alls. Rdec. destruct (Rdec r r1) as [| _]; try contradiction.
      rewrite <- (count_occ_remove_out r Hneq).
      assert (Hr2 : remove Rdec r l' = alls r1 (S n)). { revert Hr. simpl. Rdec. auto. }
      rewrite Hr2. rewrite count_occ_alls_in. simpl.
      apply Permutation_cons_inv in Hperm. f_equal. now rewrite Hperm.
    (* the first elements in both lists are differents *)
    * destruct Hr'. contradiction. subst r'. unfold is_forbidden. simpl remove. Rdec.
      destruct (remove Rdec r1 l') eqn:Hrem2.
        apply remove_nil in Hrem2. destruct Hrem2  as [m ?]. subst l'.
        elim Hrr'. symmetry. SearchAbout In alls. apply alls_In with (S m).
        simpl alls. rewrite <- Hperm. now left.
        destruct (Rdec r1 r0). subst. elim (remove_In Rdec l' r0). rewrite Hrem2. now left.
        assert (r0 = r).
        { cut (r0 = r \/ r0 = r1). intro H. destruct H; assumption || (symmetry in H; contradiction).
          rewrite <- Hl'. right. rewrite  <- (remove_in_out Rdec r1). rewrite Hrem2. now left. assumption. }
        subst r0.
        simpl in Hrem. Rdec. destruct (remove Rdec r l0) eqn:Hrem1.
          rewrite H2, H1. repeat rewrite count_occ_app. simpl. Rdec.
          destruct l2. inversion H2. contradiction. simpl in H2. inversion H2. subst. simpl. Rdec.
          destruct (Rdec r0 r). contradiction. destruct (Rdec r r0). now elim Hrr'.
          rewrite <- plus_n_Sm. simpl. rewrite NPeano.Nat.eqb_sym. f_equal.
          apply eq_add_S. rewrite <- count_occ_app.
          transitivity (count_occ Rdec ((r0 :: l2) ++ l3) r0). rewrite <- H1.
          rewrite <- (count_occ_remove_out r).
          rewrite Hrem. simpl. Rdec. now rewrite count_occ_alls_in. assumption. simpl. now Rdec.
          assert (r0 <> r /\ r0 <> r1).
          { split; intro; subst r0.
              apply (remove_In Rdec l0 r). rewrite Hrem1. now left.
              apply (remove_In Rdec l' r1). rewrite Hrem2. right.
              rewrite <- (remove_in_out Rdec r). rewrite Hrem1. now left. assumption. }
          exfalso. apply (Classical_Prop.and_not_or _ _ H). rewrite <- Hl'. destruct H. right.
          rewrite <- (remove_in_out Rdec r1). rewrite Hrem2. right.
          rewrite <- (remove_in_out Rdec r). rewrite Hrem1. now left. auto. auto.
  - unfold is_forbidden. simpl. Rdec.
    destruct (remove Rdec r' l') eqn:Hrem3; try reflexivity.
    destruct (remove Rdec r0 l0) eqn:Hrem4; try reflexivity.
    apply remove_nil in Hrem4. destruct Hrem4 as [n Hn]. subst l0. exfalso.
    (* 3 differents elements (r, r1, r4) are in l, whereas only two are possible for l' *)
    assert (r4 <> r1). { intro. subst. apply (remove_In Rdec l1 r1). rewrite Hrem2. now left. }
    assert (r4 <> r).
    { intro. subst. apply (remove_In Rdec l r). rewrite Hrem.
      right. rewrite <- (remove_in_out Rdec r1). rewrite Hrem2. now left. auto. }
    assert (Heq : r0 = r /\ r1 = r' \/ r' = r /\ r1 = r0).
    { destruct (Rdec r0 r) as [| Hr0r].
      + subst r0. left. split. reflexivity.
        assert (Hr1 : In r1 (r :: l)).
        { right. rewrite <- (remove_in_out Rdec r). rewrite Hrem. now left. assumption. }
        change (r :: alls r n) with (alls r (S n)) in Hrem3. rewrite Hperm in Hr1.
        rewrite (@remove_alls_2 r' r _ n) in Hr1. destruct Hr1. assumption. now elim Hneq. assumption.
      + right. assert (r' = r). 
        { assert (Hr1 : In r (r' :: l')). { rewrite <- Hperm. now left. }
          destruct (Rdec r r'). now symmetry. destruct Hr1 as [| Hr]. assumption.
          rewrite <- (remove_in_out Rdec r') in Hr. rewrite Hrem3 in Hr.
          destruct Hr as [| Hr]. contradiction. apply alls_In in Hr. now elim Hr0r. auto. }
        subst r'. apply Permutation_cons_inv in Hperm. split; trivial.
        apply (alls_In _ _ (S n)). simpl alls. rewrite <- Hrem3.
        rewrite <- Hperm. rewrite Hrem. now left. }
    destruct Heq as [[] | []]; subst.
      assert (Habs : r4 = r' \/ r4 = r).
      { rewrite <- (remove_alls_2 _ _ Hrem3). rewrite <- Hperm. right.
        rewrite <- (remove_in_out Rdec r). rewrite Hrem. right.
        rewrite <- (remove_in_out Rdec r'). rewrite Hrem2. now left.
        auto. auto. }
      destruct Habs; auto.
      apply Permutation_cons_inv in Hperm.
      assert (Habs : r4 = r \/ r4 = r0).
      { rewrite <- (remove_alls_2 _ _ Hrem3). rewrite <- Hperm. right.
        rewrite <- (remove_in_out Rdec r). rewrite Hrem. right.
        rewrite <- (remove_in_out Rdec r0). rewrite Hrem2. now left.
        auto. auto. }
      destruct Habs; auto.
Qed.


Definition range b1 b2 (s : spectrum) :=
  List.Forall (fun x => b1 <= x <= b2) s.

Lemma range_compat : Proper (eq ==> eq ==> @Permutation R ==> iff) range.
Proof.
intros inf1 inf2 ? sup1 sup2 ? s1 s2 Hs. subst.
unfold range. split; apply Forall_Perm_trans; trivial. reflexivity. reflexivity. now symmetry.
Qed.

Lemma range_split : forall b1 b2 s,
  range b1 b2 s <-> (List.Forall (fun x => b1 <= x) s /\ List.Forall (fun x => x <= b2) s).
Proof.
intros b1 b2 s. unfold range. setoid_rewrite List.Forall_forall.
intuition; apply (H _ H0).
Qed.

Definition extremal r (s : spectrum) :=
  exists b, range b r s \/ range r b s.

(*
Parameter is_extremal : ident Four Zero -> position Four Zero -> bool.
Hypothesis is_extremal_correct : forall r pos, is_extremal r pos = true <-> extremal r pos.
*)

Definition is_extremal r (s : spectrum) :=
  if Rdec r (List.hd r (sort s)) then true else
  if Rdec r (List.last (sort s) r) then true else false.

Theorem is_extremal_correct : forall r (s : spectrum),
  List.In r s -> (is_extremal r s = true <-> extremal r s).
Proof.
unfold is_extremal,extremal. intros r s Hin.
repeat Rdec_full; split; intro H; try (reflexivity || discriminate H);
try solve [reflexivity | discriminate H | right; now intros [] | left; now intros []].
+ clear H. rewrite Heq. exists (List.last (sort s) r). right.
  rewrite range_split. split;
  rewrite List.Forall_forall; apply sort_min || apply sort_max.
+ clear H. exists (List.hd r (sort s)). left. rewrite Heq.
  rewrite range_split. split;
  rewrite List.Forall_forall; apply sort_min || apply sort_max.
+ exfalso. destruct H as [b [Hb | Hb]].
  - elim (Rlt_irrefl r). apply Rlt_le_trans with (List.last (sort s) r).
      revert Hneq0. generalize (sort_max s r r Hin). apply Rle_neq_lt.
      apply range_split in Hb. destruct Hb as [_ Hb]. rewrite List.Forall_forall in Hb.
      apply Hb. rewrite (Permuted_sort s) at 2. apply last_In.
      rewrite (Permuted_sort s) in Hin. destruct (sort s).
      inversion Hin. discriminate.
  - elim (Rlt_irrefl r). apply Rle_lt_trans with (List.hd r (sort s)).
      apply range_split in Hb. destruct Hb as [Hb _]. rewrite List.Forall_forall in Hb.
      apply Hb. rewrite (Permuted_sort s) at 2.
      rewrite (Permuted_sort s) in Hin. destruct (sort s).
      inversion Hin. now left.
      assert (Hneq' : List.hd r (sort s) <> r). { intro. apply Hneq. now symmetry. }
      revert Hneq'. generalize (sort_min s r r Hin). apply Rle_neq_lt.
Qed.

Instance is_extremal_perm_invariant : Proper (eq ==> @Permutation R ==> eq) is_extremal.
Proof.
intros x y ? s s' Hs. subst. unfold is_extremal. 
assert (Heq : sort s = sort s'). now rewrite Hs. now rewrite Heq.
Qed.

Lemma is_extremal_similarity_invariant : forall k t pos r, k <> 0 ->
  is_extremal (k * (r - t)) (nominal_spectrum (⟦k, t⟧ pos)) = is_extremal r (nominal_spectrum pos).
Proof.
intros k t pos r Hk. unfold is_extremal.
Admitted.
(* it requires to notice that similairty is monotonous and therefore may only reverse the order *)


Definition extreme_center (s : spectrum) :=
  (List.hd 0 (sort s) + List.last (sort s) 0) / 2.
(* When there is no robot (s is empty), the center is 0. *)

Instance extreme_center_perm_invariant : Proper (@Permutation R ==> eq) extreme_center.
Proof. intros s s' Hs. unfold extreme_center. now rewrite Hs. Qed.

Lemma extreme_center_similarity_invariant : forall k t pos, k <> 0 ->
  extreme_center (nominal_spectrum (⟦k, t⟧ pos)) = k * (extreme_center (nominal_spectrum pos) - t).
Proof.
intros k t pos Hk. unfold extreme_center.
Admitted.
(* it requires to notice that similairty is monotonous and therefore may only reverse the order *)


Definition robogram (s : spectrum) : location :=
  if is_forbidden s then 0 else
  match has_dups s with
    | Some p => p
    | None => if is_extremal 0 s then 0 else extreme_center s end.

Print Assumptions robogram.

(** The robogram is invariant by permutation of spectra. *)
Instance robogram_invariant : Proper (@Permutation R ==> eq) robogram.
Proof.
unfold robogram. intros s s' Hperm. rewrite Hperm.
destruct (is_forbidden s') eqn:Hforbidden.
- reflexivity.
- rewrite (has_dups_invariant (symmetry Hperm)). destruct (has_dups s).
    reflexivity.
    now do 2 rewrite Hperm.
Qed.
Print Assumptions robogram_invariant.


Lemma nominal_spectrum_alls : forall pt,
  nominal_spectrum (@lift_gp Four (fun _ => pt)) = alls pt 4.
Proof.
intro pt. unfold lift_gp, nominal_spectrum, fold_left. simpl.
now repeat (rewrite fold_left_from_equation; simpl).
Qed.

Lemma forbidden_similarity_invariant : forall pos k t, forbidden ((⟦k, t⟧) pos) -> forbidden pos.
Proof.
intros [gp bp] k t [p1 [p2 [n [Hneq Hperm]]]]. destruct (Rdec k 0).
+ subst. assert (Heq : PosEq (lift_gp (fun _ => 0)) (⟦0, t⟧ {| gp := gp; bp := bp |})).
  { split; simpl. intro. now rewrite Rmult_0_l. intros []. }
  rewrite <- Heq in Hperm. clear Heq. rewrite nominal_spectrum_alls in Hperm.
  symmetry in Hperm. apply Permutation_alls in Hperm.
  destruct n as [| [| [| [| [| n]]]]]; simpl in Hperm; inversion Hperm. subst. now elim Hneq.
+ exists (p1 / k + t). exists (p2 / k + t). exists n. split.
  clear -Hneq n0. intro Habs. apply Hneq. apply Rdiv_reg with k. assumption.
  apply Rplus_eq_reg_l with t. now setoid_rewrite Rplus_comm.
  clear Hneq. rewrite <- (@similarity_inverse _ _ k t); trivial. unfold similarity at 1.
  replace (p1 / k + t) with (/k * (p1 - - k * t)) by now field.
  change (/k * (p1 - - k * t)) with ((fun x => /k * (x - - k * t)) p1). rewrite <- map_alls.
  replace (p2 / k + t) with (/k * (p2 - - k * t)) by now field.
  change (/k * (p2 - - k * t)) with ((fun x => /k * (x - - k * t)) p2). rewrite <- map_alls.
  rewrite nominal_spectrum_map. rewrite <- map_app. now apply Permutation_map.
Qed.

Corollary forbidden_similarity_iff : forall k t pos, k <> 0 -> (forbidden (⟦k, t⟧ pos) <-> forbidden pos).
Proof.
intros k t pos Hk. split.
+ apply forbidden_similarity_invariant.
+ rewrite <- is_forbidden_true. rewrite <- (similarity_inverse t pos Hk) at 1.
  rewrite is_forbidden_true. apply forbidden_similarity_invariant.
Qed.

Corollary is_forbidden_similarity_invariant : forall k t pos, k <> 0 ->
  is_forbidden (nominal_spectrum (⟦k, t⟧ pos)) = is_forbidden (nominal_spectrum pos).
Proof.
intros k t pos Hk. destruct (is_forbidden (nominal_spectrum pos)) eqn:Hpos.
  now rewrite is_forbidden_true, forbidden_similarity_iff, <- is_forbidden_true.
  now rewrite is_forbidden_false, forbidden_similarity_iff, <- is_forbidden_false.
Qed.

(** If [k = 0], then all robots are collapsed on a single location and any position ⟦k, t⟧ pos is not fobidden. **)

Lemma forbidden_still : forall (da : demonic_action Four Zero) pos,
  forbidden pos -> PosEq (lift_gp (round robogram da pos.(gp))) pos.
Proof.
intros [] pos Hforbidden. assert (Hdes := Hforbidden). destruct Hdes as [p1 [p2 [Hneq Hperm]]].
split; intro n; try now destruct n. unfold round. simpl.
destruct (Rdec (frame n) 0). reflexivity.
rewrite <- Rplus_0_r. f_equal. erewrite <- Rmult_0_r. f_equal.
unfold robogram.
rewrite spectrum_ok.
assert (is_forbidden (nominal_spectrum ((⟦frame n, gp pos n⟧) {| gp := gp pos; bp := locate_byz |}))
        = is_forbidden (nominal_spectrum {| gp := gp pos; bp := locate_byz |})) as Heq.
{ case_eq (is_forbidden (nominal_spectrum ((⟦frame n, gp pos n⟧) {| gp := gp pos; bp := locate_byz |}))); intro Heq.
  - rewrite is_forbidden_true in Heq. rewrite forbidden_similarity_iff in Heq; trivial.
    now rewrite <- is_forbidden_true in Heq.
  - rewrite is_forbidden_false in Heq. rewrite forbidden_similarity_iff in Heq; trivial.
    now rewrite <- is_forbidden_false in Heq. }
rewrite Heq. clear Heq. rewrite <- is_forbidden_true in Hforbidden.
assert (Hpos : PosEq ({| gp := gp pos; bp := locate_byz |}) pos). { split; now intros || now intros []. }
rewrite Hpos. clear Hpos. now rewrite Hforbidden.
Qed.

(*
Theorem forbidden_round : forall (da : demonic_action Four Zero) pos,
  forbidden (lift_gp (round robogram da pos.(gp))) <-> forbidden pos.
Proof.
intros da pos. split; intro Hpos.
+ destruct Hpos as [p1 [p2 [n [Hneq Hp]]]]. unfold robogram in *.
  
+ rewrite <- is_forbidden_true. rewrite (forbidden_still da Hpos). now rewrite is_forbidden_true.
Qed.
*)
Theorem never_forbidden : forall (da : demonic_action Four Zero) pos,
  ~forbidden pos -> ~forbidden (lift_gp (round robogram da pos.(gp))).
Proof.
intros da pos Hpos.
assert (ExtEq (round robogram da (gp pos)) 
              (fun g : Four =>
              if Rdec (frame da g) 0 then gp pos g
              else gp pos g + / frame da g * robogram (nominal_spectrum
            ((⟦frame da g, gp pos g⟧) {| gp := gp pos; bp := locate_byz da |})))).
{ intro n. unfold round. destruct (Rdec (frame da n) 0). reflexivity. now rewrite spectrum_ok. }
rewrite H.
Admitted.

(*
Theorem robogram_similarity_invariant : forall k t pos, k <> 0 ->
  robogram (nominal_spectrum (⟦k, t⟧ pos)) = k * (robogram (nominal_spectrum pos) - t).
Proof.
intros k t pos Hk. unfold robogram.
rewrite is_forbidden_similarity_invariant; trivial.
destruct (has_dups (nominal_spectrum pos)) eqn:Hdup.
  apply (has_dups_similarity k t) in Hdup. rewrite Hdup.
Qed.
*)

(*
(* This inductive expresses that there will be a stack (in the sense of [Stack] and [has_dups]).
   It does not express that all robots are stacked (it is the purpose of Gather). *)
Inductive Will_stack (e : execution Four) :=
  | AlreadyStacked : Stack (lift_gp (execution_head e)) -> Will_stack e
  | After :  Will_stack (execution_tail e) -> Will_stack e.
*)

(* To simplify proofs in a first pass. *)
Axiom active : forall da n, @frame Four Zero da n <> 0. 

Theorem Will_stack : forall da pos, ~forbidden pos -> ~Stack pos ->
  Stack (lift_gp (round (B:=Zero) robogram da pos.(gp))).
Proof.
intros da pos Hok Hyet.
destruct (has_dups (nominal_spectrum (lift_gp (round robogram da (gp pos))))) as [pt |] eqn:Hnom.
+ rewrite nominal_spectrum4 in Hnom. revert Hnom. simpl. repeat Rdec_full; intro Hnom.
  - exists Three4. exists Four4. simpl. now split.
  - exists Two4. exists Four4. simpl. now split.
  - exists One4. exists Four4. simpl. now split.
  - exists Two4. exists Three4. simpl. now split.
  - exists One4. exists Three4. simpl. now split.
  - exists One4. exists Two4. simpl. now split.
  - discriminate Hnom.
+ rewrite nominal_spectrum4 in Hnom. revert Hnom. simpl. repeat Rdec_full; intro Hnom; try discriminate Hnom.
  pose (s := nominal_spectrum pos).
  assert (Hext : ExtEq (round robogram da (gp pos))
                       (fun n => if is_extremal (gp pos n) s then gp pos n else extreme_center s)).
  { intro n. 
    rewrite <- is_forbidden_false, <- (@is_forbidden_similarity_invariant (frame da n) (gp pos n)) in Hok.
    assert (Hdup : has_dups (nominal_spectrum ((⟦frame da n, gp pos n⟧) pos)) = None).
    { rewrite has_dups_Stack in Hyet. destruct (has_dups (nominal_spectrum pos)) eqn:Hdups.
      elim Hyet. now exists r. apply has_dups_similarity_None. now apply active. assumption. }
    assert (Hpos : PosEq {| gp := gp pos; bp := locate_byz da |} pos) by (split; now intros []).
    unfold round. destruct (Rdec (frame da n) 0) as [Habs | _]. now elim (active _ _ Habs).
    rewrite spectrum_ok, Hpos. unfold robogram. rewrite Hok, Hdup.
    replace 0 with (frame da n * (gp pos n - gp pos n)) by ring.
    rewrite is_extremal_similarity_invariant, extreme_center_similarity_invariant.
    fold s. destruct (is_extremal (gp pos n) s). field. now apply active. field. now apply active.
    now apply active. now apply active. now apply active. }
  rewrite Hext. unfold is_extremal, extreme_center. assert (Hperm := Permuted_sort s).
  assert (Hl : length (sort s) = 4%nat).
  { replace 4%nat with (length s). apply Permutation_length. now symmetry. unfold s. now rewrite nominal_spectrum4. }
  assert (Hs := LocallySorted_sort s).
  destruct (sort s) as [| a [| b [| c [| d [| ? ?]]]]]; try discriminate Hl. clear Hl.
  assert (Hsort : a <= b /\ b <= c /\ c <= d).
  { inversion_clear Hs. split. inversion_clear H0. now rewrite <- Rleb_spec.
    inversion_clear H. split. inversion_clear H2. now rewrite <- Rleb_spec.
    inversion_clear H1. inversion_clear H3. now rewrite <- Rleb_spec. }
  (* We need to give the position of the minimum in s, therefore to consider the 24 possible permutations... *)
Admitted.

Lemma gathered_at_PosEq : forall (gp : Four -> R) pt, gathered_at gp pt -> ExtEq gp (fun _ => pt).
Proof. intros gp pt Hgather. intro n. apply Hgather. Qed.

Theorem gathered_at_round : forall pt gp (da : demonic_action Four Zero),
  gathered_at gp pt -> gathered_at (round robogram da gp) pt.
Proof.
intros pt gp [] Hgather. unfold round. simpl.
intro g. destruct (Rdec (frame g) 0). now apply Hgather.
rewrite Hgather. rewrite <- Rplus_0_r. f_equal. rewrite <- (Rmult_0_r (/ frame g)). f_equal.
unfold similarity. simpl. rewrite (spectrum_exteq g _ (lift_gp (fun _ => 0))). unfold robogram.
assert (spectrum_of g (lift_gp (fun _ => 0)) = alls 0 4) as Heq.
{ apply Permutation_alls.
  transitivity (nominal_spectrum (lift_gp (fun _ : Four => 0))).
    apply spectrum_ok.
    now rewrite nominal_spectrum_alls. }
rewrite Heq. rewrite is_forbidden_alls. simpl. now Rdec.
split; (now intros []) || intro x; simpl. rewrite Hgather, Rminus_diag_eq. now rewrite Rmult_0_r. reflexivity.
Qed.

Lemma gathered_at_Gather : forall pt (d : demon Four Zero) gp, gathered_at gp pt ->
  Gather pt (execute robogram d gp).
Proof.
intro pt. cofix gather. intros d gp Hgather. constructor. apply Hgather.
rewrite execute_tail. apply gather. now apply gathered_at_round.
Qed.

Theorem stack_sol : forall k (d : demon Four Zero), kFair k d ->
  forall gp : Four -> R, ~forbidden (lift_gp gp) ->
  Stack (lift_gp gp) ->
  exists pt, WillGather pt (execute robogram d gp).
Proof.
intros k [da d] Hfair gp Hok Hstack.
assert (Hs := Hstack). rewrite has_dups_Stack in Hs. destruct Hs as [pt Hpt].
exists pt. constructor 2. constructor 1.
rewrite execute_tail. cofix gathered. constructor. clear gathered. simpl. unfold gathered_at.
intro n. unfold round.
pose (s := spectrum_of da n ((⟦frame da n, gp n⟧) {| gp := gp; bp := locate_byz da |})). fold s.
destruct (Rdec (frame da n) 0).
  admit. (* Stalling case *)
  unfold robogram.
  assert (Hfor : is_forbidden s = false).
  { unfold s. rewrite spectrum_ok. rewrite is_forbidden_false. intro Habs. apply Hok.
    revert Habs. setoid_rewrite lift_gp_equiv at 2. simpl. apply forbidden_similarity_invariant. }
  rewrite Hfor. clear Hfor.
  assert (Hperm : Permutation s (nominal_spectrum (⟦frame da n, gp n⟧ {| gp := gp; bp := locate_byz da |})))
  by apply da.(spectrum_ok).
  SearchAbout has_dups.
  SearchAbout forbidden. rewrite <- is_forbidden_false in Hok. rewrite Hperm.
  setoid_rewrite lift_gp_equiv at 2. simpl. rewrite (has_dups_similarity _ _ _ Hpt). now field.
(* back to coinduction *)
apply gathered. (* je comprends toujours pas comment ça marche... ill-formed recursive definition *)
Admitted.

Theorem meeting4 :
  forall d : demon Four Zero, forall k, kFair k d -> solGathering robogram d.
Proof.
intros d k Hfair gp Hok.
destruct (has_dups (nominal_spectrum (lift_gp gp))) eqn:Hdup.
  (* there is a stack *)
  apply (stack_sol Hfair Hok). rewrite has_dups_Stack. now exists r.
  (* there is not stack, it will be created at the next step *)
  inversion_clear Hfair as [_ Htfair].
  destruct (stack_sol Htfair (@never_forbidden (demon_head d) _ Hok)) as [pt Hpt].
    apply Will_stack. assumption. rewrite has_dups_Stack. rewrite Hdup. intros [? Habs]. discriminate Habs.
    exists pt. constructor 2. rewrite execute_tail. exact Hpt.
Qed.
