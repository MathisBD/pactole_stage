(* Order of import is important here, Equivalence.equiv must be hidden by SetoidClass.equiv. *)
Require Import Coq.Classes.Equivalence Morphisms.
Require Import SetoidList SetoidPermutation SetoidDec.
Require Import Bool Program.Basics.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.FSets.FSetInterface.


Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.
Local Open Scope set_scope.
Local Open Scope equiv_scope.


(** This file corresponds to [FSetFacts.v] in the standard library.
   There are additional specifications, for boolean functions in particular,
   in the [InductiveSpec] section at the end of the file.
   *)
Hint Extern 1 (Equivalence _) => constructor; congruence : core.
Hint Extern 1 (equiv ?x ?x) => reflexivity : core.
Hint Extern 2 (equiv ?y ?x) => now symmetry : core.
Hint Extern 2 (Equivalence.equiv ?y ?x) => now symmetry : core.

Notation Leibniz := (@eq _) (only parsing).

(** * Specifications written using equivalences *)
Section IffSpec.
  Context `{HF : @FSetSpecs elt St Helt F}.

  Let t := set elt.
  Definition eq_b x y := x == y.
  Variable s s' s'' : t.
  Variable x y z : elt.

  Lemma In_eq_iff : x == y -> (In x s <-> In y s).
  Proof using HF.
    split; apply In_1;intros; auto.
  Qed.

  Lemma mem_spec : mem x s = true <-> In x s.
  Proof using HF. split; [apply mem_2 | apply mem_1]. Qed.

  Lemma mem_false : mem x s = false <-> ~In x s.
  Proof using HF. intros; rewrite <- mem_spec; destruct (mem x s); intuition. Qed.

  Lemma equal_spec : equal s s' = true <-> s == s'.
  Proof using HF. split; [apply equal_2 | apply equal_1]. Qed.

  Lemma subset_spec : subset s s' = true <-> s [<=] s'.
  Proof using HF. split; [apply subset_2 | apply subset_1]. Qed.

  Lemma empty_spec : forall x, In x empty <-> False.
  Proof using HF. intuition; apply (empty_1 H). Qed.

  Lemma is_empty_spec : is_empty s = true <-> s == empty.
  Proof using HF.
  split.
  - intros H e. apply is_empty_2 in H. specialize (H e). rewrite empty_spec. tauto.
  - intro Heq. apply is_empty_1. intro e. rewrite (Heq e), empty_spec. tauto.
  Qed.

  Lemma singleton_spec : In y (singleton x) <-> x == y.
  Proof using HF. split; [apply singleton_1|apply singleton_2]. Qed.

  Lemma add_spec : In y (add x s) <-> x == y \/ In y s.
  Proof using HF.
    split; [| destruct 1; [apply add_1 | apply add_2]]; auto.
    destruct (Helt x y) as [E|E].
    - intro. auto.
    - intro H; right. eauto using add_3.
  Qed.

  Lemma add_other : x =/= y -> (In y (add x s) <-> In y s).
  Proof using HF. split; [apply add_3 | apply add_2]; auto. Qed.

  Lemma remove_spec : In y (remove x s) <-> In y s /\ x =/= y.
  Proof using HF.
    split; [split;
      [apply remove_3 with x |] | destruct 1; apply remove_2]; auto.
    intro.
    apply (remove_1 H0 H).
  Qed.

  Lemma remove_other : x =/= y -> (In y (remove x s) <-> In y s).
  Proof using HF. split; [apply remove_3 | apply remove_2]; auto. Qed.

  Lemma union_spec : In x (union s s') <-> In x s \/ In x s'.
  Proof using HF. split; [apply union_1 | destruct 1; [apply union_2 | apply union_3]]; auto. Qed.

  Lemma inter_spec : In x (inter s s') <-> In x s /\ In x s'.
  Proof using HF.
    split; [split; [apply inter_1 with s' |
      apply inter_2 with s] | destruct 1; apply inter_3]; auto.
  Qed.

  Lemma diff_spec : In x (diff s s') <-> In x s /\ ~ In x s'.
  Proof using HF.
    split; [split; [apply diff_1 with s' |
      apply diff_2 with s] | destruct 1; apply diff_3]; auto.
  Qed.

  Lemma elements_spec : InA equiv x (elements s) <-> In x s.
  Proof using HF. split; [apply elements_2 | apply elements_1]. Qed.

  Section ForFilter.
    Variable f : elt -> bool.
    Context {Hf : Proper (equiv ==> @eq bool) f}.

    Lemma filter_spec : (In x (filter f s) <-> In x s /\ f x = true).
    Proof using HF Hf.
      split.
      - split.
        + eapply filter_1; eauto.
        + eapply filter_2; eauto.
      - destruct 1; eapply filter_3; eauto.
    Qed.

    Lemma for_all_spec : for_all f s = true <-> For_all (fun x => f x = true) s.
    Proof using HF Hf. split; [eapply for_all_2; eauto | eapply for_all_1; eauto]; auto. Qed.

    Lemma exists_spec : exists_ f s = true <-> Exists (fun x => f x = true) s.
    Proof using HF Hf. split; [eapply exists_2 | eapply exists_1]; eauto. Qed.
  End ForFilter.
  Arguments InA {A%type_scope} _ _ _.

End IffSpec.

(** Useful tactic for simplifying expressions like [In y (add x (union s s'))]*)
Ltac set_iff :=
 repeat (progress (
  rewrite add_spec || rewrite remove_spec || rewrite singleton_spec
  || rewrite union_spec || rewrite inter_spec || rewrite diff_spec
  || rewrite empty_spec)).

(**  * Specifications written using boolean predicates *)

Section BoolSpec.
  Context `{HF : @FSetSpecs elt St Helt F}.

  Let t := set elt.
  Variable s s' s'' : t.
  Variable x y z : elt.

  Lemma mem_b : x == y -> mem x s = mem y s.
  Proof using HF.
    intros.
    generalize (mem_spec s x) (mem_spec s y) (In_eq_iff s H).
    destruct (mem x s); destruct (mem y s); intuition.
  Qed.

  Lemma empty_b : mem y empty = false.
  Proof using HF.
    generalize (empty_spec y)(mem_spec empty y).
    destruct (mem y empty); intuition.
  Qed.

  Lemma add_b : mem y (add x s) = (x ==b y) || mem y s.
  Proof using HF.
    generalize (mem_spec (add x s) y)(mem_spec s y)(add_spec s x y); unfold eqb.
    unfold equiv_decb.
    destruct (equiv_dec x y) ; destruct (mem y s);
      destruct (mem y (add x s)); simpl; intuition.
  Qed.

  Lemma add_neq_b : x =/= y -> mem y (add x s) = mem y s.
  Proof using HF.
    intros; generalize (mem_spec (add x s) y)(mem_spec s y)(add_other s H).
    destruct (mem y s); destruct (mem y (add x s)); intuition.
  Qed.

  Lemma remove_b : mem y (remove x s) = mem y s && negb (x ==b y).
  Proof using HF.
    generalize (mem_spec (remove x s) y)(mem_spec s y)(remove_spec s x y).
    unfold equiv_decb;destruct (equiv_dec x y); destruct (mem y s); destruct (mem y (remove x s));
      simpl; intuition ; contradiction.
  Qed.

  Lemma remove_neq_b : x =/= y -> mem y (remove x s) = mem y s.
  Proof using HF.
    intros; generalize (mem_spec (remove x s) y) (mem_spec s y)
      (remove_other s H).
    destruct (mem y s); destruct (mem y (remove x s)); intuition.
  Qed.

  Lemma singleton_b : mem y (singleton x) = (x ==b y).
  Proof using HF.
    generalize (mem_spec (singleton x) y)(singleton_spec x y); unfold eqb.
    unfold equiv_decb;destruct (equiv_dec x y); destruct (mem y (singleton x)); intuition.
  Qed.

  Lemma union_b : mem x (union s s') = mem x s || mem x s'.
  Proof using HF.
    generalize (mem_spec (union s s') x)(mem_spec s x)(mem_spec s' x)
      (union_spec s s' x).
    destruct (mem x s); destruct (mem x s');
      destruct (mem x (union s s')); intuition.
  Qed.

  Lemma inter_b : mem x (inter s s') = mem x s && mem x s'.
  Proof using HF.
    generalize (mem_spec (inter s s') x)(mem_spec s x)
      (mem_spec s' x)(inter_spec s s' x).
    destruct (mem x s); destruct (mem x s');
      destruct (mem x (inter s s')); intuition.
  Qed.

  Lemma diff_b : mem x (diff s s') = mem x s && negb (mem x s').
  Proof using HF.
    generalize (mem_spec (diff s s') x)(mem_spec s x)
      (mem_spec s' x)(diff_spec s s' x).
    destruct (mem x s); destruct (mem x s');
      destruct (mem x (diff s s')); simpl; intuition.
  Qed.

  Lemma elements_b : mem x s = existsb (fun y => x ==b y) (elements s).
  Proof using HF.
    generalize (mem_spec s x)(elements_spec s x)
      (existsb_exists (fun y => x ==b y) (elements s)).
    rewrite InA_alt.
    destruct (mem x s); destruct (existsb (fun y => x ==b y)
      (elements s)); auto; intros.
    symmetry.
    rewrite H1.
    destruct H0 as (_, H0).
    destruct H0 as (a,(Ha1,Ha2)); [ intuition |].
    exists a; intuition.
    unfold equiv_decb; destruct (equiv_dec x a); auto.
    rewrite H, <- H0.
    destruct H1 as (H1,_).
    destruct H1 as (a,(Ha1,Ha2)); [intuition|].
    exists a; intuition.
    unfold equiv_decb in *; destruct (equiv_dec x a); auto; discriminate.
  Qed.

  Variable f : elt->bool.

  Lemma filter_b `{Proper _ (equiv ==> @eq bool) f} :
    mem x (filter f s) = mem x s && f x.
  Proof using HF.
    intros.
    generalize (mem_spec (filter f s) x)(mem_spec s x)(filter_spec (f:=f) s x).
    destruct (mem x s); destruct (mem x (filter f s));
      destruct (f x); simpl; intuition.
  Qed.

  Lemma for_all_b `{Proper _ (equiv ==> @eq bool) f} :
    for_all f s = forallb f (elements s).
  Proof using HF.
    intros.
    generalize (forallb_forall f (elements s))
      (for_all_spec (f:=f) s)(elements_spec s).
    unfold For_all.
    destruct (forallb f (elements s)); destruct (for_all f s); auto; intros.
    rewrite H1; intros.
    destruct H0 as (H0, _).
    rewrite <- (H2 x0) in H3.
    rewrite (InA_alt equiv x0 (elements s)) in H3.
    destruct H3 as (a,(Ha1,Ha2)).
    rewrite (H _ _ Ha1).
    apply H0; auto.
    symmetry.
    rewrite H0; intros.
    destruct H1 as (H1, _).
    apply H1; auto.
    rewrite <- H2.
    rewrite InA_alt; eauto.
  Qed.

  Lemma exists_b `{Proper _ (equiv ==> @eq bool) f} :
    exists_ f s = existsb f (elements s).
  Proof using HF.
    intros.
    generalize (existsb_exists f (elements s))
      (exists_spec (f:=f) s)(elements_spec s).
    unfold Exists.
    destruct (existsb f (elements s)); destruct (exists_ f s); auto; intros.
    rewrite H1; intros.
    destruct H0 as (H0,_).
    destruct H0 as (a,(Ha1,Ha2)); auto.
    exists a; split; auto.
    rewrite <- H2; rewrite InA_alt; eauto.
    symmetry.
    rewrite H0.
    destruct H1 as (H1, _).
    destruct H1 as (a,(Ha1,Ha2)); auto.
    rewrite <- (H2 a) in Ha1.
    rewrite (InA_alt equiv a (elements s)) in Ha1.
    destruct Ha1 as (b,(Hb1,Hb2)).
    exists b; auto.
    rewrite <- (H _ _ Hb1); auto.
  Qed.
End BoolSpec.


Instance In_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> iff) In.
Proof using .
  intros x y H s s' H0.
  rewrite (In_eq_iff s H); auto.
Qed.

Instance is_empty_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> @eq bool)  is_empty.
Proof using .
  intros s s' H.
  generalize (is_empty_spec s)(is_empty_spec s').
  destruct (is_empty s); destruct (is_empty s');
  unfold Empty; auto; intros.
  - symmetry. now rewrite H1, <- H, <- H0.
  - now rewrite H0, H, <- H1.
Qed.

Instance Empty_m `{HF : @FSetSpecs A St HA F} : Proper (equiv ==> iff) Empty.
Proof using . unfold Empty. intros ? ? H. now setoid_rewrite H. Qed.

Instance mem_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> @eq bool) mem.
Proof using .
  intros x y H s s' H0.
  generalize (H0 x); clear H0; rewrite (In_eq_iff s' H).
  generalize (mem_spec s x)(mem_spec s' y).
  destruct (mem x s); destruct (mem y s'); intuition.
Qed.

Instance singleton_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv) singleton.
Proof using .
  intros x y H a.
  do 2 rewrite singleton_spec.
  split; intros.
  - transitivity x; auto.
  - transitivity y; auto.
Qed.

Instance add_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> equiv) add.
Proof using .
  intros x y H s s' H0 a.
  do 2 rewrite add_spec; rewrite H; rewrite H0; intuition.
Qed.

Instance remove_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> equiv) remove.
Proof using .
  intros x y H s s' H0 a.
  do 2 rewrite remove_spec; rewrite H; rewrite H0; intuition.
Qed.

Instance union_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> equiv) union.
Proof using .
  intros s s' H s'' s''' H0 a.
  do 2 rewrite union_spec; rewrite H; rewrite H0; intuition.
Qed.

Instance inter_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> equiv) inter.
Proof using .
  intros s s' H s'' s''' H0 a.
  do 2 rewrite inter_spec; rewrite H; rewrite H0; intuition.
Qed.

Instance diff_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> equiv) diff.
Proof using .
  intros s s' H s'' s''' H0 a.
  do 2 rewrite diff_spec; rewrite H; rewrite H0; intuition.
Qed.

Instance elements_compat `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> PermutationA equiv) elements.
Proof using .
intros s s' Heq. apply NoDupA_equivlistA_PermutationA.
+ auto with typeclass_instances.
+ apply elements_NoDupA.
+ apply elements_NoDupA.
+ intro x. rewrite 2 elements_spec. apply Heq.
Qed.

Instance PermutationA_length {elt} `{Setoid elt} : Proper (PermutationA equiv ==> Logic.eq) (@length elt).
Proof using . clear. intros l1 l2 perm. induction perm; simpl; auto; congruence. Qed.

Instance cardinal_compat `{HF : @FSetSpecs A St HA F} : Proper (equiv ==> Logic.eq) cardinal.
Proof using . intros ? ? Heq. rewrite 2 cardinal_spec. now do 2 f_equiv. Qed.

Instance Subset_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> iff) Subset.
Proof using .
  unfold Subset; intros s s' H u u' H'; split; intros.
  rewrite <- H'; apply H0; rewrite H; assumption.
  rewrite H'; apply H0; rewrite <- H; assumption.
Qed.

Instance subset_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> @eq bool) subset.
Proof using .
  intros s s' H s'' s''' H0.
  generalize (subset_spec s s'') (subset_spec s' s''').
  destruct (subset s s''); destruct (subset s' s'''); auto; intros.
  rewrite H in H1; rewrite H0 in H1; intuition.
  rewrite H in H1; rewrite H0 in H1; intuition.
Qed.

Instance equal_m `{HF : @FSetSpecs A St HA F} :
  Proper (equiv ==> equiv ==> @eq bool) equal.
Proof using .
  intros s s' H s'' s''' H0.
  generalize (equal_spec s s'') (equal_spec s' s''').
  destruct (equal s s''); destruct (equal s' s'''); auto; intros.
  rewrite H in H1; rewrite H0 in H1; intuition.
  rewrite H in H1; rewrite H0 in H1; intuition.
Qed.

(** * [Subset] is a setoid order *)
Lemma Subset_refl `{HF : @FSetSpecs A St HA F} :
  forall s, s[<=]s.
Proof using . red; auto. Qed.

Lemma Subset_trans `{HF : @FSetSpecs A St HA F} :
  forall s s' s'', s[<=]s'->s'[<=]s''->s[<=]s''.
Proof using . unfold Subset; eauto. Qed.

Instance SubsetSetoid `{@FSetSpecs A St HA F} :
  PreOrder Subset := {
    PreOrder_Reflexive := Subset_refl;
    PreOrder_Transitive := Subset_trans
}.

(** * Set operations and morphisms *)
Instance In_s_m `{F : FSet A, @FSetSpecs _ _ _ F} :
  Proper (equiv ==> Subset ++> impl) In | 1.
Proof using .
  simpl_relation; apply H2; rewrite <- H1; auto.
Qed.

Instance Empty_s_m `{F : FSet A, @FSetSpecs _ _ _ F} :
  Proper (Subset --> impl) Empty.
Proof using .
  simpl_relation; unfold Subset, Empty, impl; intros.
  exact (H2 a (H1 a H3)).
Qed.

Instance add_s_m `{F : FSet A, @FSetSpecs _ _ _ F} :
  Proper (equiv ==> Subset ++> Subset) add.
Proof using .
  unfold Subset; intros x y H1 s s' H2 a.
  do 2 rewrite add_spec; rewrite H1; intuition.
Qed.

Instance remove_s_m `{F : FSet A, @FSetSpecs _ _ _ F} :
  Proper (equiv ==> Subset ++> Subset) remove.
Proof using .
  unfold Subset; intros x y H1 s s' H2 a.
  do 2 rewrite remove_spec; rewrite H1; intuition.
Qed.

Instance union_s_m `{F : FSet A, @FSetSpecs _ _ _  F} :
  Proper (Subset ++> Subset ++> Subset) union.
Proof using .
  intros s s' H1 s'' s''' H2 a.
  do 2 rewrite union_spec; intuition.
Qed.

Instance inter_s_m `{F : FSet A, @FSetSpecs _ _ _ F} :
  Proper (Subset ++> Subset ++> Subset) inter.
Proof using .
  intros s s' H1 s'' s''' H2 a.
  do 2 rewrite inter_spec; intuition.
Qed.

Instance diff_s_m `{F : FSet A, @FSetSpecs _ _ _ F} :
  Proper (Subset ++> Subset --> Subset) diff.
Proof using .
  unfold Subset; intros s s' H1 s'' s''' H2 a.
  do 2 rewrite diff_spec; intuition.
Qed.

(** [fold], [filter], [for_all], [exists_] and [partition] require
   the  additional hypothesis on [f]. *)
Instance filter_m  `{F : FSet A, @FSetSpecs _ _ _ F} :
  forall f `{Proper _ (equiv ==> @eq bool) f},
    Proper (equiv ==> equiv) (filter f).
Proof using .
  intros f Hf s s' H' x.
  repeat rewrite filter_spec; auto. rewrite H'; reflexivity.
Qed.

Lemma filter_ext  `{F : FSet A, @FSetSpecs _ _ _ F} :
  forall f f' `{Proper _ (equiv ==> @eq bool) f}, (forall x, f x = f' x) ->
    forall s s', s==s' -> filter f s == filter f' s'.
Proof using .
  intros f f' Hf Hff' s s' Hss' x. do 2 (rewrite filter_spec; auto).
  rewrite Hff', Hss'; intuition.
  red; repeat intro; rewrite <- 2 Hff'; auto.
Qed.

Instance filter_s_m  `{F : FSet A, @FSetSpecs _ _ _ F} :
  forall f `{Proper _ (equiv ==> @eq bool) f},
    Proper (Subset ==> Subset) (filter f).
Proof using .
  unfold Subset; intros f Hf s s' H' x.
  repeat rewrite filter_spec; auto; intro; intuition.
Qed.

(** * Inductive specifications of boolean functions *)
CoInductive reflects (P : Prop) : bool -> Prop :=
| reflects_true : forall (Htrue : P), reflects P true
| reflects_false : forall (Hfalse : ~P), reflects P false.

Section InductiveSpec.
  Context `{HF : @FSetSpecs elt St Helt F}.
  Variables s s' s'' : set elt.
  Variables x y z : elt.

  Property In_dec : reflects (In x s) (mem x s).
  Proof using HF.
    case_eq (mem x s); intro H; constructor.
    apply mem_2; exact H.
    intro abs; rewrite (mem_1 abs) in H; discriminate.
  Qed.

  Property is_empty_dec : reflects (Empty s) (is_empty s).
  Proof using HF.
    case_eq (is_empty s); intro H; constructor.
    apply is_empty_2; exact H.
    intro abs; rewrite (is_empty_1 abs) in H; discriminate.
  Qed.
  Corollary is_empty_dec2 : reflects (s == empty) (is_empty s).
  Proof using HF.
    destruct is_empty_dec; constructor.
    intro a; rewrite empty_spec; intuition; contradiction (Htrue a).
    intro R; rewrite R in Hfalse; contradiction Hfalse.
    auto with set typeclass_instances.
  Qed.

  Property equal_dec : reflects (s == s') (equal s s').
  Proof using HF.
    case_eq (equal s s'); intro H; constructor.
    apply equal_2; exact H.
    intro abs; rewrite (equal_1 abs) in H; discriminate.
  Qed.

  Property subset_dec : reflects (s [<=] s') (subset s s').
  Proof using HF.
    case_eq (subset s s'); intro H; constructor.
    apply subset_2; exact H.
    intro abs; rewrite (subset_1 abs) in H; discriminate.
  Qed.

  Section Compat.
    Variable f : elt -> bool.
    Context `{Comp : Proper _ (equiv ==> @eq bool) f}.

    Property for_all_dec :
      reflects (For_all (fun x => f x = true) s) (for_all f s).
    Proof using Comp HF.
      case_eq (for_all f s); intro H; constructor.
      - eapply for_all_2; eauto.
      - intro abs; rewrite for_all_1 in H; trivial; discriminate.
    Qed.

    Property exists_dec :
      reflects (Exists (fun x => f x = true) s) (exists_ f s).
    Proof using Comp HF.
      case_eq (exists_ f s); intro H; constructor.
      eapply exists_2; eauto.
      intro abs; rewrite exists_1 in H; trivial; discriminate.
    Qed.
  End Compat.

  CoInductive choose_spec : option elt -> Prop :=
  | choose_spec_Some : forall x (Hin : In x s), choose_spec (Some x)
  | choose_Spec_None : forall (Hempty : Empty s), choose_spec None.
  Property choose_dec : choose_spec (choose s).
  Proof using HF.
    case_eq (choose s); intros; constructor.
    apply choose_1; auto.
    apply choose_2; auto.
  Qed.

(*  CoInductive min_elt_spec : option elt -> Prop :=
  | min_elt_spec_Some :
    forall x (Hin : In x s) (Hmin : forall y, In y s -> ~y <<< x),
      min_elt_spec (Some x)
  | min_elt_spec_None :
    forall (Hempty : Empty s), min_elt_spec None.
  Property min_elt_dec : min_elt_spec (min_elt s).
  Proof.
    case_eq (min_elt s); intros; constructor.
    apply min_elt_1; auto.
    intro; apply min_elt_2; auto.
    apply min_elt_3; auto.
  Qed.

  Inductive max_elt_spec : option elt -> Prop :=
  | max_elt_spec_Some :
    forall x (Hin : In x s) (Hmin : forall y, In y s -> ~y >>> x),
      max_elt_spec (Some x)
  | max_elt_spec_None :
    forall (Hempty : Empty s), max_elt_spec None.
  Property max_elt_dec : max_elt_spec (max_elt s).
  Proof.
    case_eq (max_elt s); intros; constructor.
    apply max_elt_1; auto.
    intro; apply max_elt_2; auto.
    apply max_elt_3; auto.
  Qed.*)
End InductiveSpec.

Lemma elements_empty `{F : FSet A, @FSetSpecs _ _ _ F} : elements empty = nil.
Proof using .
assert (Hspec := empty_spec). setoid_rewrite <- elements_spec in Hspec.
destruct (elements empty) as [| e l]; trivial; [].
exfalso. rewrite <- (Hspec e). now left.
Qed.

Lemma PermutationA_nil : forall A (eqA : relation A), Equivalence eqA ->
  forall l, PermutationA eqA nil l -> l = nil.
Proof using .
intros A eqA HeqA l Hl. destruct l.
+ reflexivity.
+ exfalso. rewrite <- InA_nil. rewrite (Coq.Lists.SetoidPermutation.PermutationA_equivlistA HeqA).
  - now left.
  - eassumption.
Qed.

Lemma elements_nil `{F : FSet A, @FSetSpecs _ _ _ F} : forall s, elements s = nil <-> s == empty.
Proof using .
intro s. split; intro Heq.
+ intro x. rewrite <- elements_spec, Heq, empty_spec, InA_nil. tauto.
+ apply (@PermutationA_nil _ equiv); auto with typeclass_instances.
  rewrite <- elements_empty, Heq. reflexivity.
Qed.

Lemma cardinal_empty `{F : FSet A, @FSetSpecs _ _ _ F} : cardinal empty = 0.
Proof using . now rewrite cardinal_spec, length_zero_iff_nil, elements_empty. Qed.

Lemma elements_add_incl `{F : FSet A, @FSetSpecs _ _ _ F} :
  forall x s, inclA equiv (elements (add x s)) (x :: elements s).
Proof using .
intros x s y. rewrite elements_spec. set_iff. intros [Heq | Hin].
- now left.
- right. now rewrite elements_spec.
Qed.

Lemma elements_add `{F : FSet A, @FSetSpecs _ _ _ F} : forall x s,
  ~In x s -> PermutationA equiv (elements (add x s)) (x :: elements s).
Proof using .
intros x s Hx. apply NoDupA_equivlistA_PermutationA.
+ auto with typeclass_instances.
+ apply elements_NoDupA.
+ constructor.
  - now rewrite elements_spec.
  - apply elements_NoDupA.
+ intro y. rewrite elements_spec. set_iff.
  split; intro Hin.
  - destruct Hin; (now left) || now right; rewrite elements_spec.
  - inversion_clear Hin; auto; []. right. now rewrite <- elements_spec.
Qed.

Lemma cardinal_add `{F : FSet A, @FSetSpecs _ _ _ F} : forall x s,
  ~In x s -> cardinal (add x s) = S (cardinal s).
Proof using . intros. now rewrite 2 cardinal_spec, elements_add. Qed.

Global Instance Set_EqDec elt `{F : FSet elt, @FSetSpecs _ _ _ F} : @EqDec (set elt) _.
Proof.
intros s1 s2. destruct (equal s1 s2) eqn:Heq.
- left. now rewrite <- equal_spec.
- right. intro Habs. rewrite <- equal_spec, Heq in Habs. discriminate.
Defined.


(** *  Map  **)

Instance fold_compat {A B} `{FSetSpecs A} `{Setoid B} :
  forall f : A -> B -> B, Proper (equiv ==> equiv ==> equiv) f -> transpose equiv f ->
  forall a, Proper (equiv ==> equiv) (fun x => fold f x a).
Proof using .
intros f Hf Ht a m1 m2 Heq. do 2 rewrite fold_spec.
rewrite fold_left_symmetry_PermutationA; autoclass; [|].
- repeat intro. now apply Hf.
- now rewrite Heq.
Qed.

Lemma fold_left_add_acc {A B} `{FSet A} `{FSetSpecs B} : forall (f : A -> B), Proper (equiv ==> equiv) f ->
  forall x l acc, In x (fold_left (fun acc y => add (f y) acc) l acc)
                  <-> In x acc \/ exists y, InA equiv y l /\ x == f y.
Proof using .
intros f Hf x l. induction l as [| e l]; intro acc; simpl.
+ intuition.
  match goal with H : exists _, InA _ _ nil /\ _ |- _ =>
    destruct H as [? [H _]]; now rewrite InA_nil in H end.
+ rewrite IHl. set_iff. split; intro Hin.
  - destruct Hin as [[? | ?] | [? [? ?]]]; try tauto; eauto.
  - destruct Hin as [Heq | [? [Hin Heq]]]; tauto || inv Hin; eauto.
    do 2 left. match goal with H : _ == e |- _ => now rewrite <- H end.
Qed.

(* Instance elements_compat : Proper (equiv ==> PermutationA equiv) elements := elements_compat. *)
Definition map {A B} `{FSet A} `{FSet B} (f : A -> B) s :=
  fold (fun x acc => add (f x) acc) s empty.

Instance map_compat {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  Proper (equiv ==> equiv) (map f).
Proof using .
intros f Hf m₁ m₂ Hm. unfold map. apply fold_compat; autoclass; [|].
- repeat intro. now repeat f_equiv.
- repeat intro. set_iff. tauto.
Qed.

Lemma map_empty {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, map f empty == empty.
Proof using . intro. unfold map. rewrite fold_spec, elements_empty. simpl. reflexivity. Qed.

Lemma map_spec {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall y s, In y (map f s) <-> exists x, In x s /\ y == (f x).
Proof using .
intros f Hf y s. unfold map.
rewrite fold_spec, fold_left_add_acc, empty_spec; trivial; [].
setoid_rewrite elements_spec. intuition.
Qed.

Corollary map_In {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall x m, In x m -> In (f x) (map f m).
Proof using . repeat intro. rewrite map_spec; eauto. Qed.

Corollary map_add {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall x m, map f (add x m) == add (f x) (map f m).
Proof using .
intros f Hf x m y. set_iff. rewrite 2 map_spec; trivial; [].
split; intro Hin.
+ destruct Hin as [? [Hin Hy]]. revert Hin. set_iff. intros [Hx | Hin].
  - rewrite Hy, Hx. now left.
  - right. eauto.
+ destruct Hin as [Hy | [? [Hin Hx]]]; eexists; set_iff; eauto.
Qed.

Lemma map_injective_elements {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f,
  Proper (equiv ==> equiv) f ->
  injective equiv equiv f ->
  forall s, PermutationA equiv (elements (map f s)) (List.map f (elements s)).
Proof using .
intros f Hf Hf2 s.
apply NoDupA_equivlistA_PermutationA; autoclass.
+ apply elements_NoDupA.
+ eapply map_injective_NoDupA, elements_NoDupA; autoclass.
+ intro y.
  rewrite elements_spec, map_spec, InA_map_iff; autoclass; [].
  split; intros [x [Hx1 Hx2]].
  - exists x. rewrite elements_spec. auto.
  - exists x. rewrite <- elements_spec. now symmetry in Hx1.
Qed.
