(******************************************)
(*   Finite multiset library              *)
(*   Developped for the PACTOLE project   *)
(*   L. Rieg                              *)
(*                                        *)
(*   This file is distributed under       *)
(*   the terms of the CeCILL-C licence    *)
(*                                        *)
(******************************************)


Require Import Bool.
Require Import Lia PeanoNat.
Require Import PArith.
Require Import RelationPairs.
(* Require Import Equalities. *)
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.MMultiset.Preliminary.
Require Import Pactole.Util.MMultiset.MMultisetInterface.


Set Implicit Arguments.
Notation " x == y " := (equiv x y) (at level 70, no associativity).
Notation " x =/= y " := (complement equiv x y) (at level 70, no associativity).


Section MMultisetFacts.
  
  Context {elt : Type}.
  Context {elt_Setoid : Setoid elt}.
  Context {elt_EqDec : EqDec elt_Setoid}.
  Context {FMultisetsOps : FMOps elt elt_EqDec}.
  Context {FMultisetsSpec : FMultisetsOn elt FMultisetsOps}.
  
  Instance eq_pair_equiv : Equivalence eq_pair.
  Proof using . split.
  intros [x n]. now split; hnf.
  intros [x n] [y m] [? ?]; split; hnf in *; now auto.
  intros ? ? ? [? ?] [? ?]. split. hnf in *. now transitivity (fst y). now transitivity (snd y).
  Qed.
  
  Instance eq_pair_Setoid : Setoid (elt * nat) := {| equiv := eq_pair |}.
  
  (** An experimental tactic that superficially ressembles [fsetdec].  It is by no mean as general. **)
  Hint Rewrite empty_spec add_same remove_same diff_spec union_spec inter_spec lub_spec singleton_same : FMsetdec.
  Hint Rewrite is_empty_spec nfilter_spec filter_spec npartition_spec_fst npartition_spec_snd : FMsetdec.
  Hint Rewrite partition_spec_fst partition_spec_snd for_all_spec exists_spec : FMsetdec.
  Hint Unfold In : FMsetdec.
  
  Lemma neq_is_neq : forall x y, ~x == y -> x =/= y.
  Proof using . now repeat intro. Qed.
  
  Lemma neq_sym : forall x y, x =/= y -> y =/= x.
  Proof using . intros x y Hxy Heq. apply Hxy. now symmetry. Qed.
  
  Ltac saturate_Einequalities :=
    repeat match goal with
      (* change ~ == for =/= *)
      | H : ~?x == ?y |- _ => apply neq_is_neq in H
      (* remove duplicates *)
      | H1 : ?x =/= ?y, H2 : ?x =/= ?y |- _ => clear H2
      (* avoid reflexive inequalities *)
      | H : ?x =/= ?x |- _ => change (id (x =/= x)) in H
      (* avoid already saturated inequalities *)
      | H1 : ?x =/= ?y, H2 : ?y =/= ?x |- _ => change (id (x =/= y)) in H1; change (id (y =/= x)) in H2
      (* saturate the remaining ones *)
      | H : ?x =/= ?y |- _ => let Hneq := fresh "Hneq" in assert (Hneq := neq_sym H)
    end;
    (* remove the markers (id) *)
    repeat match goal with
      | H : id (?x =/= ?y) |- _ => change (x =/= y) in H
    end.
  
  Ltac msetdec_step := 
    match goal with
      (* Simplifying equalities *)
      | H : ?x = ?x |- _ => clear H
      | H : ?x == ?x |- _ => clear H
      | H : ?x = ?y |- _ => subst x || rewrite H in *
      | Hneq : ?x =/= ?x |- _ => now elim Hneq
      | Heq : @equiv elt _ ?x ?y |- _ => clear x Heq || rewrite Heq in *
      | Heq : @equiv (multiset _) _ ?x ?y, Hin : context[?x] |- _ => rewrite Heq in Hin
      | Heq : @equiv (multiset _) _ ?x ?y |- context[?x] => rewrite Heq
      | Heq : @equiv (multiset _) _ ?x ?y |- _ => clear x Heq
      (* Simplifying [singleton], [add] and [remove] *)
      | Hneq : ?y =/= ?x |- context[multiplicity ?y (singleton ?x ?n)] => rewrite singleton_other; trivial
      | Hneq : ?y =/= ?x |- context[multiplicity ?y (add ?x ?n ?m)] => rewrite add_other; trivial
      | Hneq : ?y =/= ?x |- context[multiplicity ?y (remove ?x ?n ?m)] => rewrite remove_other; trivial
      | Hneq : ?y =/= ?x, H : context[multiplicity ?y (singleton ?x ?n)] |- _ =>
          rewrite singleton_other in H; trivial
      | Hneq : ?y =/= ?x, H : context[multiplicity ?y (add ?x ?n ?m)] |- _ => rewrite add_other in H; trivial
      | Hneq : ?y =/= ?x, H : context[multiplicity ?y (remove ?x ?n ?m)] |- _ =>
          rewrite remove_other in H; trivial
      (* Destructing equalities *)
      | H : ?x =/= ?y |- context[?x == ?y] => destruct (equiv_dec x y) as [| _]; try contradiction
      | |- context[?x == ?y] => destruct (equiv_dec x y); trivial
      | |- context[multiplicity ?y (singleton ?x ?n)] => destruct (equiv_dec y x)
      | |- context[multiplicity ?y (add ?x ?n ?m)] => destruct (equiv_dec y x)
      | |- context[multiplicity ?y (remove ?x ?n ?m)] => destruct (equiv_dec y x)
      | H : context[multiplicity ?y (singleton ?x ?n)] |- _ => destruct (equiv_dec y x)
      | H : context[multiplicity ?y (add ?x ?n ?m)] |- _ => destruct (equiv_dec y x)
      | H : context[multiplicity ?y (remove ?x ?n ?m)] |- _ => destruct (equiv_dec y x)
      | |- context[equiv_dec ?x ?y] => destruct (equiv_dec x y)
      | Heq : context[equiv_dec ?x ?y] |- _ => destruct (equiv_dec x y)
      | _ => idtac
    end.
  
  Ltac msetdec :=
    repeat (saturate_Einequalities; autorewrite with FMsetdec in *; unfold In in *; trivial;
            msetdec_step; easy || (try lia)).
  
  Tactic Notation "msetdec_n" integer(n) :=
    do n (saturate_Einequalities; autorewrite with FMsetdec in *; unfold In in *; trivial;
            msetdec_step; easy || (try lia)).
  
  Lemma subrelation_pair_elt : subrelation eq_pair eq_elt.
  Proof using . now intros [x n] [y p] [Heq _]. Qed.
  
  Lemma InA_pair_elt : forall x n p l, InA eq_pair (x, n) l -> InA eq_elt (x, p) l.
  Proof using .
  intros x n p l Hin. induction l as [| [y q] l].
  + rewrite InA_nil in Hin. elim Hin.
  + inversion_clear Hin.
    - destruct H as [Heq ?]. now left.
    - right. now apply IHl.
  Qed.
  
  Lemma InA_elt_pair : forall x n l, InA eq_elt (x, n) l -> exists n', InA eq_pair (x, n') l.
  Proof using .
  intros x n l Hin. induction l as [| [y p] l].
  + rewrite InA_nil in Hin. elim Hin.
  + inversion_clear Hin.
    - compute in H. exists p. left. now rewrite H.
    - apply IHl in H. destruct H as [k Hin]. exists k. now right.
  Qed.
  
  Lemma pair_dec : forall xn yp, {eq_pair xn yp} + {~eq_pair xn yp}.
  Proof using .
  intros [x n] [y p]. destruct (equiv_dec x y).
  + destruct (Nat.eq_dec n p).
    - left. split; assumption.
    - right. intros [_ Habs]. contradiction.
  + right. intros [Habs _]. contradiction.
  Qed.
  
  Lemma elt_dec : forall xn yp, {eq_elt xn yp} + {~eq_elt xn yp}.
  Proof using . intros [? ?] [? ?]. apply equiv_dec. Qed.
  
  
  (** *  Instances for rewriting  **)
  
  Global Existing Instance multiplicity_compat.
  Global Existing Instance fold_compat.
  
  (** **  [Subset] and [equiv] are an order relation and the corresponding equivalence relation  **)
  
  Global Instance Subset_PreOrder : PreOrder Subset.
  Proof using . split; repeat intro. msetdec. etransitivity; eauto. Qed.
  
  Global Instance Subset_PartialOrder : PartialOrder equiv Subset.
  Proof using FMultisetsSpec.
  intros m1 m2. split; intro Hm.
  - now split; intro x; rewrite Hm.
  - destruct Hm. intro. now apply Nat.le_antisymm.
  Qed.
  
  (** **  Compatibility with respect to [equiv]  **)
  
  Global Instance InA_elt_compat : Proper (eq_elt ==> PermutationA eq_pair ==> iff) (InA eq_elt).
  Proof using .
  intros ? ? ? ? ? Hperm. apply (InA_perm_compat _). assumption.
  revert Hperm. apply PermutationA_subrelation_compat; trivial. apply subrelation_pair_elt.
  Qed.
  
  Global Instance In_compat : Proper (equiv ==> equiv ==> iff) In.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance is_empty_compat : Proper (equiv ==> Logic.eq) is_empty.
  Proof using FMultisetsSpec.
  intros s1 s2 Heq. destruct (is_empty s2) eqn:Hs2.
  + msetdec.
  + destruct (is_empty s1) eqn:Hs1.
    - rewrite <- Hs2. symmetry. msetdec.
    - reflexivity.
  Qed.
  
  Global Instance add_compat : Proper (equiv ==> Logic.eq ==> equiv ==> equiv) add.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance singleton_compat : Proper (equiv ==> Logic.eq ==> equiv) singleton.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance remove_compat : Proper (equiv ==> Logic.eq ==> equiv ==> equiv) remove.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance union_compat : Proper (equiv ==> equiv ==> equiv) union.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance inter_compat : Proper (equiv ==> equiv ==> equiv) inter.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance diff_compat : Proper (equiv ==> equiv ==> equiv) diff.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance lub_compat : Proper (equiv ==> equiv ==> equiv) lub.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
(*  Global Instance subset_compat : Proper (eq ==> eq ==> iff) Subset.
  Proof. intros m1 m1' Heq1 m2 m2' Heq2. now rewrite Heq1, Heq2. Qed.*)
  
  Global Instance nfilter_compat f : compatb f -> Proper (equiv ==> equiv) (nfilter f).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance filter_compat f : Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> equiv) (filter f).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance npartition_compat f : compatb f -> Proper (equiv ==> equiv * equiv) (npartition f).
  Proof using FMultisetsSpec.
  intros Hf s1 s2 Hs. split; intro x.
  - msetdec.
  - msetdec; repeat intro; now rewrite Hf.
  Qed.
  
  Global Instance partition_compat f : Proper (equiv ==> Logic.eq) f ->
    Proper (equiv ==> equiv * equiv) (partition f).
  Proof using FMultisetsSpec.
  intros Hf s1 s2 Hs. split; intro x.
  - msetdec.
  - msetdec; repeat intro; now rewrite Hf.
  Qed.
  
  Global Instance elements_compat : Proper (equiv ==> PermutationA eq_pair) elements.
  Proof using FMultisetsSpec.
  intros s1 s2 Hs. apply NoDupA_equivlistA_PermutationA.
  - now apply eq_pair_equiv.
  - generalize (elements_NoDupA s1). apply NoDupA_strengthen. now intros [? ?] [? ?] [? _].
  - generalize (elements_NoDupA s2). apply NoDupA_strengthen. now intros [? ?] [? ?] [? _].
  - intros [x n]. do 2 rewrite elements_spec. now rewrite Hs.
  Qed.
  
  Global Instance support_compat : Proper (equiv ==> PermutationA equiv) support.
  Proof using FMultisetsSpec.
  intros s1 s2 Hs.
  apply NoDupA_equivlistA_PermutationA; autoclass; try (now apply support_NoDupA); [].
  intro x. do 2 rewrite support_spec. unfold In. now rewrite Hs.
  Qed.
  
  Global Instance size_compat : Proper (equiv ==> Logic.eq) size.
  Proof using FMultisetsSpec. intros s1 s2 Hs. do 2 rewrite size_spec. now rewrite Hs. Qed.
  
  Global Instance for_all_compat : forall f, compatb f -> Proper (equiv ==> Logic.eq) (for_all f).
  Proof using FMultisetsSpec.
  intros f Hf s1 s2 Hs. destruct (for_all f s2) eqn:Hs2.
  + rewrite for_all_spec in Hs2 |-  *; trivial. intros x Hin. rewrite Hs. apply Hs2. now rewrite <- Hs.
  + destruct (for_all f s1) eqn:Hs1.
    - rewrite <- Hs2. symmetry. rewrite for_all_spec in Hs1 |- *; trivial.
      intros x Hin. rewrite <- Hs. apply Hs1. now rewrite Hs.
    - reflexivity.
  Qed.
  
  Global Instance exists_compat : forall f, compatb f -> Proper (equiv ==> Logic.eq) (exists_ f).
  Proof using FMultisetsSpec.
  intros f Hf s1 s2 Hs. destruct (exists_ f s2) eqn:Hs2.
  + rewrite exists_spec in Hs2 |- *; trivial. destruct Hs2 as [x [Hin Hfx]]. exists x. now split; rewrite Hs.
  + destruct (exists_ f s1) eqn:Hs1.
    - rewrite <- Hs2. symmetry. rewrite exists_spec in Hs1 |-  *; trivial.
      destruct Hs1 as [x [Hin Hfx]]. exists x. now split; rewrite <- Hs.
    - reflexivity.
  Qed.
  
  Global Instance For_all_compat : forall f, Proper (equiv ==> Logic.eq ==> iff) f ->
    Proper (equiv ==> iff) (For_all f).
  Proof using FMultisetsSpec.
  intros f Hf s1 s2 Hs. split; intros Hall x Hin.
  - rewrite <- Hs. apply Hall. now rewrite Hs.
  - rewrite Hs. apply Hall. now rewrite <- Hs.
  Qed.
  
  Global Instance Exists_compat : forall f, Proper (equiv ==> Logic.eq ==> iff) f ->
    Proper (equiv ==> iff) (Exists f).
  Proof using FMultisetsSpec.
  intros f Hf s1 s2 Hs. split; intros [x [Hin Hfx]].
  - exists x. now split; rewrite <- Hs.
  - exists x. now split; rewrite Hs.
  Qed.
  
  Global Instance cardinal_compat : Proper (equiv ==> Logic.eq) cardinal.
  Proof using FMultisetsSpec.
  intros s1 s2 Hs. do 2 rewrite cardinal_spec, fold_spec. rewrite (fold_left_symmetry_PermutationA _ _).
  - reflexivity.
  - intros x ? ? [? ?] [? ?] [? Heq]. hnf in *. simpl in *. now subst.
  - intros [? ?] [? ?] ?. cbn. lia.
  - now rewrite Hs.
  - reflexivity.
  Qed.
  
  (** **  Compatibility with respect to [Subset]  **)
  
  Global Instance multiplicity_sub_compat : Proper (equiv ==> Subset ==> le) multiplicity.
  Proof using FMultisetsSpec. intros ? ? Heq ? ? Hle. rewrite Heq. apply Hle. Qed.
  
  Global Instance In_sub_compat : Proper (equiv ==> Subset ==> impl) In.
  Proof using FMultisetsSpec. intros ? y ? ? ? Hs H. msetdec. specialize (Hs y). lia. Qed.
  
  Global Instance add_sub_compat : Proper (equiv ==> le ==> Subset ==> Subset) add.
  Proof using FMultisetsSpec. repeat intro. msetdec. now apply Plus.plus_le_compat. Qed.
  
  Global Instance singleton_sub_compat : Proper (equiv ==> le ==> Subset) singleton.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Global Instance remove_sub_compat : Proper (equiv ==> le --> Subset ==> Subset) remove.
  Proof using FMultisetsSpec. intros ? y ? ? ? Hle ? ? Hsub ?. msetdec. specialize (Hsub y). compute in Hle. lia. Qed.
  
  Global Instance union_sub_compat : Proper (Subset ==> Subset ==> Subset) union.
  Proof using FMultisetsSpec. intros ? ? Hsub1 ? ? Hsub2 x. specialize (Hsub1 x). specialize (Hsub2 x). msetdec. Qed.
  
  Global Instance inter_sub_compat : Proper (Subset ==> Subset ==> Subset) inter.
  Proof using FMultisetsSpec.
  intros ? ? Hsub1 ? ? Hsub2 x. specialize (Hsub1 x). specialize (Hsub2 x). msetdec.
  Qed.
  
  Global Instance diff_sub_compat : Proper (Subset ==> Subset --> Subset) diff.
  Proof using FMultisetsSpec. intros ? ? Hsub1 ? ? Hsub2 x. specialize (Hsub1 x). specialize (Hsub2 x). msetdec. Qed.
  
  Global Instance lub_sub_compat : Proper (Subset ==> Subset ==> Subset) lub.
  Proof using FMultisetsSpec.
  intros ? ? Hsub1 ? ? Hsub2 x. specialize (Hsub1 x). specialize (Hsub2 x).
  msetdec.
  Qed.
  
  Global Instance subset_sub_compat : Proper (Subset --> Subset ==> impl) Subset.
  Proof using . intros m1 m1' Heq1 m2 m2' Heq2 ?. hnf in Heq1. repeat (etransitivity; try eassumption). Qed.
  
  Global Instance support_sub_compat : Proper (Subset ==> inclA equiv) support.
  Proof using FMultisetsSpec. intros ? ? Hsub ? Hin. rewrite support_spec in Hin |- *. now rewrite <- Hsub. Qed.
  
  Global Instance size_sub_compat : Proper (Subset ==> le) size.
  Proof using FMultisetsSpec.
  intros m1 m2 Hsub. do 2 rewrite size_spec. apply support_sub_compat in Hsub.
  apply (inclA_length _); trivial. apply support_NoDupA.
  Qed.

  (*
  (* Wrong if [f] is not monotonous in its second argument *)
  Global Instance filter_sub_compat f : compatb f -> Proper (Subset ==> Subset) (filter f).
  Proof. repeat intro. msetdec. Abort.
  
  Global Instance partition_compat f : compatb f -> Proper (eq ==> eq * eq) (partition f).
  Proof.
  intros Hf s1 s2 Hs. split; intro x.
    msetdec.
    repeat rewrite partition_spec_snd; trivial. rewrite filter_compat; trivial. repeat intro. now rewrite Hf.
  Qed.
  
  Global Instance elements_compat : Proper (Subset ==> inclA eq_pair) elements.
  Proof.
  intros s1 s2 Hs. apply NoDupA_equivlistA_PermutationA.
    now apply eq_pair_equiv.
    generalize (elements_NoDupA s1). apply NoDupA_strengthen. now intros [? ?] [? ?] [? _].
    generalize (elements_NoDupA s2). apply NoDupA_strengthen. now intros [? ?] [? ?] [? _].
    intro x. do 2 rewrite elements_spec. now rewrite Hs.
  Qed.
  
  Global Instance for_all_sub_compat : forall f, compatb f -> Proper (Subset --> Bool.le) (for_all f).
  Proof.
  intros f Hf s1 s2 Hs. destruct (for_all f s2) eqn:Hs2.
    rewrite for_all_spec in *; trivial. intros x Hin. rewrite Hs. apply Hs2. now rewrite <- Hs.
    destruct (for_all f s1) eqn:Hs1.
      rewrite <- Hs2. symmetry. rewrite for_all_spec in *; trivial.
      intros x Hin. rewrite <- Hs. apply Hs1. now rewrite Hs.
      reflexivity.
  Qed.
  
  Global Instance exists_compat : forall f, compatb f -> Proper (eq ==> Logic.eq) (exists_ f).
  Proof.
  intros f Hf s1 s2 Hs. destruct (exists_ f s2) eqn:Hs2.
    rewrite exists_spec in *; trivial. destruct Hs2 as [x [Hin Hfx]]. exists x. now split; rewrite Hs.
    destruct (exists_ f s1) eqn:Hs1.
      rewrite <- Hs2. symmetry. rewrite exists_spec in *; trivial.
       destruct Hs1 as [x [Hin Hfx]]. exists x. now split; rewrite <- Hs.
      reflexivity.
  Qed.
  
  Global Instance For_all_sub_compat : forall f, compatb f -> Proper (Subset --> impl) (For_all f).
  Proof.
  intros f Hf s1 s2 Hs H x Hin.
    rewrite <- Hs. apply H. now rewrite Hs.
    rewrite Hs. apply H. now rewrite <- Hs.
  Qed.
  
  Global Instance Exists_compat : forall f, compatb f -> Proper (Subset ==> impl) (Exists f).
  Proof.
  intros f Hf s1 s2 Hs. split; intros [x [Hin Hfx]].
    exists x. now split; rewrite <- Hs.
    exists x. now split; rewrite Hs.
  Qed.
  *)
  
  (** *  Complementary results  **)
  
(*   Lemma eq_dec : forall m1 m2, {m1 == m2} + {~m1 == m2}. *)
  Global Instance MMultisetEqDec : @EqDec (multiset elt) _.
  Proof.
  intros m1 m2. destruct (equal m1 m2) eqn:Heq.
  - left. now rewrite <- equal_spec.
  - right. intro Habs. rewrite <- equal_spec, Heq in Habs. discriminate.
  Defined.
  
  (** **  Results about [In]  **)

  Lemma not_In : forall x m, ~In x m <-> m[x] = 0.
  Proof using . intros. msetdec. Qed.
  
  Lemma In_dec : forall x m, {In x m} + {~In x m}.
  Proof using .
  intros x m. destruct (m[x]) eqn:Hn.
  - right. msetdec.
  - left. msetdec.
  Qed.
  
  (** **  Results about [empty]  **)
  
  Lemma empty_is_empty : is_empty empty = true.
  Proof using FMultisetsSpec. rewrite is_empty_spec. reflexivity. Qed.
  
  Lemma In_empty : forall x, ~In x empty.
  Proof using FMultisetsSpec. intro. msetdec. Qed.
  
  Lemma subset_empty_l : forall m, empty [<=] m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma subset_empty_r : forall m, m [<=] empty <-> m == empty.
  Proof using FMultisetsSpec.
  repeat intro. split; intro Hm.
  - apply antisymmetry. assumption. apply subset_empty_l.
  - now rewrite Hm.
  Qed.
  
  Lemma add_empty : forall x n, add x n empty == singleton x n.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_empty : forall x n, remove x n empty == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma elements_empty : elements empty = nil.
  Proof using FMultisetsSpec.
  destruct (elements empty) as [| [x n] l] eqn:Habs. reflexivity.
  assert (Hin : InA eq_pair (x, n) ((x, n) :: l)) by now left.
  rewrite <- Habs, elements_spec, empty_spec in Hin. lia.
  Qed.
  
  Corollary fold_empty : forall A f (i : A), fold f empty i = i.
  Proof using FMultisetsSpec. intros A f i. now rewrite fold_spec, elements_empty. Qed.
  
  Corollary cardinal_empty : cardinal empty = 0.
  Proof using FMultisetsSpec. now rewrite cardinal_spec, fold_empty. Qed.
  
  Corollary support_empty : support empty = nil.
  Proof using FMultisetsSpec.
  destruct (support empty) as [| e l] eqn:Habs. reflexivity.
  cut (InA equiv e (e :: l)). rewrite <- Habs, support_spec. unfold In. rewrite empty_spec. lia. now left.
  Qed.
  
  Corollary size_empty : size empty = 0.
  Proof using FMultisetsSpec. now rewrite size_spec, support_empty. Qed.
  
  Lemma nfilter_empty : forall f, compatb f -> nfilter f empty == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. now destruct (f x 0). Qed.
  
  Lemma filter_empty : forall f, Proper (equiv ==> Logic.eq) f -> filter f empty == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. now destruct (f x). Qed.
  
  Lemma for_all_empty : forall f, compatb f -> for_all f empty = true.
  Proof using FMultisetsSpec. repeat intro. msetdec. intro. msetdec. Qed.
  
  Lemma exists_empty : forall f, compatb f -> exists_ f empty = false.
  Proof using FMultisetsSpec.
  intros. destruct (exists_ f empty) eqn:Habs; trivial.
  rewrite exists_spec in Habs; trivial. destruct Habs. msetdec.
  Qed.
  
  Lemma npartition_empty_fst : forall f, compatb f -> fst (npartition f empty) == empty.
  Proof using FMultisetsSpec. intros. msetdec. now apply nfilter_empty. Qed.
  
  Lemma npartition_empty_snd : forall f, compatb f -> snd (npartition f empty) == empty.
  Proof using FMultisetsSpec. intros f Hf. msetdec. apply nfilter_empty. repeat intro. now rewrite Hf. Qed.
  
  Lemma partition_empty_fst : forall f, Proper (equiv ==> Logic.eq) f -> fst (partition f empty) == empty.
  Proof using FMultisetsSpec. intros. msetdec. now apply filter_empty. Qed.
  
  Lemma partition_empty_snd : forall f, Proper (equiv ==> Logic.eq) f -> snd (partition f empty) == empty.
  Proof using FMultisetsSpec. intros f Hf. msetdec. apply filter_empty. repeat intro. now rewrite Hf. Qed.
  
  Lemma choose_empty : choose empty = None.
  Proof using FMultisetsSpec. rewrite choose_None. reflexivity. Qed.
  
  (** **  Results about [singleton]  **)
  
  Lemma singleton_spec : forall x y n, (singleton x n)[y] = if equiv_dec y x then n else 0.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma singleton_0 : forall x, singleton x 0 == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma subset_singleton_l : forall x n m, n <= m[x] -> singleton x n [<=] m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma subset_singleton_r : forall x n m, 
    m [<=] singleton x n <-> m[x] <= n /\ m == singleton x (m[x]).
  Proof using FMultisetsSpec.
  repeat intro. split; intro Hm.
  + split.
    - specialize (Hm x). msetdec.
    - intro y. specialize (Hm y). msetdec.
  + intro y. destruct Hm as [Hm1 Hm2]. rewrite Hm2. clear Hm2. msetdec.
  Qed.
  
  Lemma singleton_empty : forall x n, singleton x n == empty <-> n = 0.
  Proof using FMultisetsSpec.
  intros x n. split; intro Heq.
  + destruct n. reflexivity. symmetry. rewrite <- (empty_spec x), <- Heq. msetdec.
  + subst. apply singleton_0.
  Qed.
  
  Lemma In_singleton : forall x n y, In y (singleton x n) <-> equiv y x /\ n > 0.
  Proof using FMultisetsSpec. intros. unfold In. rewrite singleton_spec. destruct (equiv_dec y x); intuition. Qed.
  
  Lemma add_singleton_same : forall x n p, add x p (singleton x n) == singleton x (n + p).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_singleton_comm : forall x y n p, add y p (singleton x n) == add x n (singleton y p).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_singleton_same : forall x n p, remove x n (singleton x p) == singleton x (p - n).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_singleton_other : forall x y n p, ~y == x -> remove y n (singleton x p) == singleton x p.
  Proof using FMultisetsSpec. repeat intro. msetdec. (* BUG?: saturate_Einequalities should work! *) now elim H. Qed.
  
  Theorem elements_singleton : forall x n, n > 0 -> eqlistA eq_pair (elements (singleton x n)) ((x, n) :: nil).
  Proof using FMultisetsSpec.
  intros x n Hn. apply (PermutationA_length1 _). apply (NoDupA_equivlistA_PermutationA _).
  + apply (NoDupA_strengthen (eqA' := eq_elt) _). apply elements_NoDupA.
  + apply NoDupA_singleton.
  + intros [y p]. rewrite elements_spec. simpl. split; intro Hin.
    - destruct Hin as [Hin1 Hin2]. msetdec. now left.
    - inversion_clear Hin.
        compute in H. destruct H. msetdec.
        now rewrite InA_nil in H.
  Qed.
  
  Lemma singleton_injective : forall x y n p, n > 0 -> singleton x n == singleton y p -> equiv x y /\ n = p.
  Proof using FMultisetsSpec.
  intros x y n p Hn Heq.
  assert (p > 0) by (destruct p; try rewrite singleton_0, singleton_empty in Heq; lia).
  assert (Hel := elements_singleton x Hn). apply eqlistA_PermutationA_subrelation in Hel.
  rewrite Heq in Hel. apply (PermutationA_length1 _) in Hel. rewrite elements_singleton in Hel; trivial.
  inversion_clear Hel. now destruct H0.
  Qed.
  
  Lemma fold_singleton : forall A eqA, Reflexive eqA -> forall f, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f ->
   forall (acc : A) x n, n > 0 -> eqA (fold f (singleton x n) acc) (f x n acc).
  Proof using FMultisetsSpec.
  intros A eqA HeqA f Hf acc x n Hn. rewrite fold_spec.
  change (f x n acc) with (fold_left (fun acc xn => f (fst xn) (snd xn) acc) ((x, n) :: nil) acc).
  assert (Hf2 : Proper (eqA ==> eq_pair ==> eqA) (fun acc xn => f (fst xn) (snd xn) acc)).
  { intros ? ? Heq [y p] [z q] [Hxy Hnp]. simpl. apply Hf; assumption. }
  apply (fold_left_compat Hf2); trivial. now apply elements_singleton.
  Qed.
  
  Lemma cardinal_singleton : forall x n, cardinal (singleton x n) = n.
  Proof using FMultisetsSpec.
  intros. destruct n.
  - rewrite singleton_0. apply cardinal_empty.
  - rewrite cardinal_spec, fold_singleton; lia || now repeat intro; subst.
  Qed.
  
  Lemma support_singleton : forall x n, n > 0 -> PermutationA equiv (support (singleton x n)) (x :: nil).
  Proof using FMultisetsSpec.
  intros x n Hn. apply (NoDupA_equivlistA_PermutationA _).
  + apply support_NoDupA. 
  + apply NoDupA_singleton.
  + intro. rewrite support_spec. unfold In. split; intro Hin.
    - left. msetdec.
    - inversion_clear Hin. msetdec. inversion H.
  Qed.
  
  Corollary size_singleton : forall x n, n > 0 -> size (singleton x n) = 1.
  Proof using FMultisetsSpec. intros. now rewrite size_spec, support_singleton. Qed.
  
  Lemma nfilter_singleton_true : forall f x n, compatb f -> n > 0 ->
    (nfilter f (singleton x n) == singleton x n <-> f x n = true).
  Proof using FMultisetsSpec.
  intros f x n Hf Hn. split; intro Heq.
  - specialize (Heq x). msetdec. destruct (f x n); reflexivity || lia.
  - intro y. msetdec. now destruct (f y 0).
  Qed.
  
  Lemma nfilter_singleton_false : forall f x n, compatb f -> n > 0 -> 
    (nfilter f (singleton x n) == empty <-> f x n = false).
  Proof using FMultisetsSpec.
  intros f x n Hf Hn. split; intro Heq.
  - specialize (Heq x). msetdec. destruct (f x n); reflexivity || lia.
  - intro y. msetdec. now destruct (f y 0).
  Qed.
  
  Lemma filter_singleton_true : forall f x n, Proper (equiv ==> Logic.eq) f -> n > 0 ->
    (filter f (singleton x n) == singleton x n <-> f x = true).
  Proof using FMultisetsSpec.
  intros f x n Hf Hn. split; intro Heq.
  - specialize (Heq x). msetdec. destruct (f x); reflexivity || lia.
  - intro y. msetdec. now destruct (f y).
  Qed.
  
  Lemma filter_singleton_false : forall f x n, Proper (equiv ==> Logic.eq) f -> n > 0 -> 
    (filter f (singleton x n) == empty <-> f x = false).
  Proof using FMultisetsSpec.
  intros f x n Hf Hn. split; intro Heq.
  - specialize (Heq x). msetdec. destruct (f x); reflexivity || lia.
  - intro y. msetdec. now destruct (f y).
  Qed.
  
  Lemma for_all_singleton_true : forall f x n, compatb f -> n > 0 ->
    (for_all f (singleton x n) = true <-> f x n = true).
  Proof using FMultisetsSpec.
  intros f x n Hf Hn. rewrite for_all_spec; trivial. split; intro Hall.
  - unfold For_all in Hall. setoid_rewrite In_singleton in Hall. specialize (Hall x). msetdec. now apply Hall.
  - intro. msetdec.
  Qed.
  
  Lemma for_all_singleton_false : forall f x n, compatb f -> n > 0 -> 
    (for_all f (singleton x n) = false <-> f x n = false).
  Proof using FMultisetsSpec.
  intros. destruct (f x n) eqn:Hfxn.
  - rewrite <- for_all_singleton_true in Hfxn; trivial. now rewrite Hfxn.
  - destruct (for_all f (singleton x n)) eqn:Habs; try reflexivity.
    rewrite for_all_singleton_true, Hfxn in Habs; trivial. discriminate Habs.
  Qed.
  
  Lemma for_all_exists_singleton : forall f x n, compatb f -> n > 0 ->
    exists_ f (singleton x n) = for_all f (singleton x n).
  Proof using FMultisetsSpec.
  intros f x n Hf Hn. destruct (for_all f (singleton x n)) eqn:Hall.
  + rewrite for_all_singleton_true in Hall; trivial. rewrite exists_spec; trivial. exists x. msetdec.
  + rewrite for_all_singleton_false in Hall; trivial. destruct (exists_ f (singleton x n)) eqn:Hex; trivial.
    rewrite exists_spec in Hex; trivial. destruct Hex as [y [Hin Hy]]. rewrite In_singleton in Hin.
    destruct Hin. msetdec.
  Qed.
  
  Corollary exists_singleton_true : forall f x n, compatb f -> n > 0 ->
    (exists_ f (singleton x n) = true <-> f x n = true).
  Proof using FMultisetsSpec. intros. now rewrite for_all_exists_singleton, for_all_singleton_true. Qed.
  
  Corollary exists_singleton_false : forall f x n, compatb f -> n > 0 ->
  (exists_ f (singleton x n) = false <-> f x n = false).
  Proof using FMultisetsSpec. intros. now rewrite for_all_exists_singleton, for_all_singleton_false. Qed.
  
  Lemma npartition_singleton_true_fst : forall f x n, compatb f -> n > 0 ->
    (fst (npartition f (singleton x n)) == singleton x n <-> f x n = true).
  Proof using FMultisetsSpec. intros. autorewrite with FMsetdec; trivial; []. now rewrite nfilter_singleton_true. Qed.
  
  Lemma npartition_singleton_true_snd : forall f x n, compatb f -> n > 0 ->
    (snd (npartition f (singleton x n)) == empty <-> f x n = true).
  Proof using FMultisetsSpec.
  intros. autorewrite with FMsetdec; trivial; []. rewrite nfilter_singleton_false; trivial; [|].
  - apply negb_false_iff.
  - intros ? ? Heq1 ? ? Heq2. now rewrite Heq1, Heq2.
  Qed.
  
  Lemma npartition_singleton_false_fst : forall f x n, compatb f -> n > 0 ->
    (fst (npartition f (singleton x n)) == empty <-> f x n = false).
  Proof using FMultisetsSpec. intros. autorewrite with FMsetdec; trivial; []. now rewrite nfilter_singleton_false. Qed.
  
  Lemma npartition_singleton_false_snd : forall f x n, compatb f -> n > 0 ->
    (snd (npartition f (singleton x n)) == singleton x n <-> f x n = false).
  Proof using FMultisetsSpec.
  intros. autorewrite with FMsetdec; trivial; []. rewrite nfilter_singleton_true; trivial; [|].
  - apply negb_true_iff.
  - intros ? ? Heq1 ? ? Heq2. now rewrite Heq1, Heq2.
  Qed.
  
  Lemma partition_singleton_true_fst : forall f x n, Proper (equiv ==> Logic.eq) f -> n > 0 ->
    (fst (partition f (singleton x n)) == singleton x n <-> f x = true).
  Proof using FMultisetsSpec. intros. autorewrite with FMsetdec; trivial; []. now rewrite filter_singleton_true. Qed.
  
  Lemma partition_singleton_true_snd : forall f x n, Proper (equiv ==> Logic.eq) f -> n > 0 ->
    (snd (partition f (singleton x n)) == empty <-> f x = true).
  Proof using FMultisetsSpec.
  intros. autorewrite with FMsetdec; trivial; []. rewrite filter_singleton_false; trivial; [|].
  - apply negb_false_iff.
  - intros ? ? Heq. now rewrite Heq.
  Qed.
  
  Lemma partition_singleton_false_fst : forall f x n, Proper (equiv ==> Logic.eq) f -> n > 0 ->
    (fst (partition f (singleton x n)) == empty <-> f x = false).
  Proof using FMultisetsSpec. intros. autorewrite with FMsetdec; trivial; []. now rewrite filter_singleton_false. Qed.
  
  Lemma partition_singleton_false_snd : forall f x n, Proper (equiv ==> Logic.eq) f -> n > 0 ->
    (snd (partition f (singleton x n)) == singleton x n <-> f x = false).
  Proof using FMultisetsSpec.
  intros. autorewrite with FMsetdec; trivial; []. rewrite filter_singleton_true; trivial; [|].
  - apply negb_true_iff.
  - intros ? ? Heq. now rewrite Heq.
  Qed.
  
  Lemma choose_singleton : forall x n, n > 0 -> exists y, equiv x y /\ choose (singleton x n) = Some y.
  Proof using FMultisetsSpec.
  intros x n Hn. destruct (choose (singleton x n)) eqn:Hx.
  + exists e. repeat split. apply choose_Some in Hx. rewrite In_singleton in Hx. now destruct Hx as [Hx _].
  + rewrite choose_None, singleton_empty in Hx. lia.
  Qed.
  
  (** **  Results about [add]  **)
  
  Lemma add_spec : forall x y n m,
    (add x n m)[y] = if equiv_dec y x then m[y] + n else m[y].
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_0 : forall x m, add x 0 m == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_comm : forall x1 x2 n1 n2 m, add x1 n1 (add x2 n2 m) == add x2 n2 (add x1 n1 m).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_multiplicity_inf_bound : forall x n m, n <= (add x n m)[x].
  Proof using FMultisetsSpec. intros. msetdec. Qed.
  
  Lemma add_disjoint : forall x n m, add x n m == add x (m[x] + n) (remove x m[x] m).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_merge : forall x n p m, add x n (add x p m) == add x (n + p) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_is_empty : forall x n m, add x n m == empty <-> n = 0 /\ m == empty.
  Proof using FMultisetsSpec.
  intros x n m. split; intro Heq.
  + split.
    - specialize (Heq x). msetdec.
    - intro y. specialize (Heq y). msetdec.
  + intro y. destruct Heq as [Heq1 Heq2]. specialize (Heq2 y). msetdec.
  Qed.
  
  Lemma add_is_singleton : forall x y n p m, add x n m == singleton y p -> m == singleton y (p - n).
  Proof using FMultisetsSpec.
  intros x y n p m Hadd z. destruct n.
  + rewrite add_0 in Hadd. now rewrite Hadd, <- Minus.minus_n_O.
  + assert (Heq := Hadd x). msetdec. rewrite <- (add_other y z (S n)), Hadd; trivial. msetdec.
  Qed.
  
  Lemma add_subset : forall x n m, m [<=] add x n m.
  Proof using FMultisetsSpec. repeat intro. msetdec.  Qed.
  
  Lemma add_subset_remove : forall x n m1 m2, add x n m1 [<=] m2 -> m1 [<=] remove x n m2.
  Proof using FMultisetsSpec. intros x n m1 m2 Hsub y. specialize (Hsub y). msetdec. Qed.

  Lemma add_In : forall x y n m, In x (add y n m) <-> equiv x y /\ n > 0 \/ In x m.
  Proof using FMultisetsSpec.
  intros x y n m. unfold In. destruct (equiv_dec x y) as [Heq | Heq].
  - repeat rewrite (multiplicity_compat _ _ Heq _ _ (reflexivity _)). rewrite add_same. destruct n; intuition.
  - rewrite add_other; trivial. intuition.
  Qed.
  
  Lemma add_injective : forall x n, injective equiv equiv (add x n).
  Proof using FMultisetsSpec. intros ? ? ? ? Heq y. specialize (Heq y). msetdec. Qed.
  
  (** ** Results about [remove] **)
  
  Lemma remove_spec : forall x y n m, (remove x n m)[y] = if equiv_dec y x then m[y] - n else m[y].
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_0 : forall x m, remove x 0 m == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_out : forall x n m, ~In x m -> remove x n m == m.
  Proof using FMultisetsSpec. unfold In. repeat intro. msetdec. Qed.
  
  Lemma remove_comm : forall x1 x2 n1 n2 m, remove x1 n1 (remove x2 n2 m) == remove x2 n2 (remove x1 n1 m).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_merge : forall x n p m, remove x n (remove x p m) == remove x (n + p) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_cap : forall x n m, m[x] <= n -> remove x n m == remove x (m[x]) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_add_comm : forall x1 x2 n1 n2 m, x1 =/= x2 ->
    remove x1 n1 (add x2 n2 m) == add x2 n2 (remove x1 n1 m).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_add1 : forall x n p m, n <= p -> remove x n (add x p m) == add x (p - n) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_add2 : forall x n p m, p <= n -> remove x n (add x p m) == remove x (n - p) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Corollary remove_add_cancel : forall x n m, remove x n (add x n m) == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_remove1 : forall x n p m, p <= m[x] -> p <= n -> add x n (remove x p m) == add x (n - p) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_remove2 : forall x n p m, m[x] <= p -> m[x] <= n -> add x n (remove x p m) == add x (n - m[x]) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_remove3 : forall x n p m, n <= m[x] <= p -> add x n (remove x p m) == remove x (m[x] - n) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_remove4 : forall x n p m, n <= p <= m[x] -> add x n (remove x p m) == remove x (p - n) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Corollary add_remove_cancel : forall x n m, n <= m[x] -> add x n (remove x n m) == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  Arguments add_remove_cancel [x] [n] [m] _ _.
  (* PB: The arguments are not strict because of equiv.  We could instead [Unset Strict Implicit]. *)
  
  Lemma add_remove_id : forall x n m, m[x] <= n -> add x (m[x]) (remove x n m) == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_is_empty : forall x n m,
    remove x n m == empty <-> m == singleton x (m[x]) /\ m[x] <= n.
  Proof using FMultisetsSpec.
  intros x n m. split; intro Heq.
  + split.
    - intro y. specialize (Heq y). msetdec.
    - specialize (Heq x). msetdec.
  + destruct Heq as [Heq1 Heq2]. rewrite Heq1. intro y. destruct (equiv_dec y x) as [Heq | Hneq].
    - rewrite Heq, remove_same, singleton_spec, empty_spec. destruct (equiv_dec x x); lia.
    - rewrite remove_other, singleton_spec, empty_spec; trivial. now destruct (equiv_dec y x).
  Qed.
  
  Lemma remove_is_singleton : forall n x m,
    (exists p, remove x n m == singleton x p) <-> m == singleton x (m[x]).
  Proof using FMultisetsSpec.
  intros n x m. split; intro Heq.
  + destruct Heq as [p Heq]. intro y. msetdec. erewrite <- remove_other. rewrite Heq. msetdec. assumption.
  + exists (m[x] - n). intro y. rewrite Heq at 1. clear Heq. msetdec.
  Qed.
  
  Lemma remove_subset : forall x n m, remove x n m [<=] m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_subset_add : forall x n m1 m2, remove x n m1 [<=] m2 <-> m1 [<=] add x n m2.
  Proof using FMultisetsSpec. intros x n m1 m2. split; intros Hsub y; specialize (Hsub y); msetdec. Qed.
  
  Lemma remove_In : forall x y n m,
    In x (remove y n m) <-> equiv x y /\ n < m[x] \/ ~equiv x y /\ In x m.
  Proof using FMultisetsSpec.
  intros x y n m. unfold In. destruct (equiv_dec x y) as [Heq | Heq].
  + repeat rewrite (multiplicity_compat _ _ Heq _ _ (reflexivity _)). rewrite remove_same. intuition.
  + rewrite remove_other; trivial. split; intro; try right; intuition.
  Qed.
  
  Lemma remove_injective : forall x n m1 m2, n <= m1[x] -> n <= m2[x] ->
    remove x n m1 == remove x n m2 -> m1 == m2.
  Proof using FMultisetsSpec. intros x n m1 m2 Hm1 Hm2 Heq y. specialize (Heq y). msetdec. Qed.
  
  (** ** Results about [union]. **)
  
  Lemma union_empty_l : forall m, union empty m == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_empty_r : forall m, union m empty == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_comm : forall m1 m2, union m1 m2 == union m2 m1.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_assoc : forall m1 m2 m3, union m1 (union m2 m3) == union (union m1 m2) m3.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_union_singleton_l : forall x n m, union (singleton x n) m == add x n m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_union_singleton_r : forall x n m, union m (singleton x n) == add x n m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_add_comm_l : forall x n m1 m2, union (add x n m1) m2 == add x n (union m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_add_comm_r : forall x n m1 m2, union m1 (add x n m2) == add x n (union m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_remove_comm_l1 : forall x n m1 m2, n <= m1[x] ->
    union (remove x n m1) m2 == remove x n (union m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.

  Lemma union_remove_comm_l2 : forall x n m1 m2, m1[x] <= n ->
    union (remove x n m1) m2 == remove x (m1[x]) (union m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_remove_comm_r1 : forall x n m1 m2, n <= m2[x] ->
    union m1 (remove x n m2) == remove x n (union m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_remove_comm_r2 : forall x n m1 m2, m2[x] <= n ->
    union m1 (remove x n m2) == remove x (m2[x]) (union m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma empty_union : forall m1 m2, union m1 m2 == empty <-> m1 == empty /\ m2 == empty.
  Proof using FMultisetsSpec.
  intros m1 m2. split; intro Heq.
  + split; intro x; specialize (Heq x); msetdec.
  + intro. destruct Heq. msetdec.
  Qed.
  
  Lemma union_singleton : forall x n m1 m2, union m1 m2 == singleton x n <->
    m1 == singleton x (m1[x]) /\ m2 == singleton x (m2[x])
    /\ n = m1[x] + m2[x].
  Proof using FMultisetsSpec.
  intros x n m1 m2. split; intro Heq.
  + repeat split.
    - intro y. specialize (Heq y). msetdec.
    - intro y. specialize (Heq y). msetdec.
    - specialize (Heq x). msetdec.
  + destruct Heq as [Heq1 [Heq2 Heq3]]. intro y. subst n.
    rewrite union_spec, Heq1, Heq2 at 1. repeat rewrite singleton_spec.
    now destruct (equiv_dec y x).
  Qed.
  
  Lemma union_In : forall x m1 m2, In x (union m1 m2) <-> In x m1 \/ In x m2.
  Proof using FMultisetsSpec. intros. unfold In. rewrite union_spec. lia. Qed.
  
  Lemma union_out : forall x m1 m2, ~In x (union m1 m2) <-> ~In x m1 /\ ~In x m2.
  Proof using FMultisetsSpec. intros x m1 m2. rewrite union_In. tauto. Qed.
  
  Lemma union_subset_l : forall m1 m2, m1 [<=] union m1 m2.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_subset_r : forall m1 m2, m2 [<=] union m1 m2.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_injective_l : forall m, injective equiv equiv (union m).
  Proof using FMultisetsSpec. intros m1 m2 m3 Heq x. specialize (Heq x). msetdec. Qed.
  
  Lemma union_injective_r : forall m, injective equiv equiv (fun m' => union m' m).
  Proof using FMultisetsSpec. intros m1 m2 m3 Heq x. specialize (Heq x). msetdec. Qed.
  
  (** **  Results about [inter]  **)
  
  Lemma inter_empty_l : forall m, inter empty m == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_empty_r : forall m, inter m empty == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_comm : forall m1 m2, inter m1 m2 == inter m2 m1.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_assoc : forall m1 m2 m3, inter m1 (inter m2 m3) == inter (inter m1 m2) m3.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma add_inter_distr : forall x n m1 m2, add x n (inter m1 m2) == inter (add x n m1) (add x n m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma remove_inter_distr : forall x n m1 m2, remove x n (inter m1 m2) == inter (remove x n m1) (remove x n m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_singleton_l : forall x n m, inter (singleton x n) m == singleton x (min n m[x]).
  Proof using FMultisetsSpec. intros x n m y. msetdec. Qed.
  
  Lemma inter_singleton_r : forall x n m, inter m (singleton x n) == singleton x (min n m[x]).
  Proof using FMultisetsSpec. intros. rewrite inter_comm. apply inter_singleton_l. Qed.
  
  Lemma inter_is_singleton : forall x m1 m2,
    (exists n, inter m1 m2 == singleton x n) <-> forall y, y =/= x -> ~In y m1 \/ ~In y m2.
  Proof using FMultisetsSpec.
  intros x m1 m2. split; intro Hin.
  * intros y Hy. destruct Hin as [n Hin]. destruct (m1[y]) eqn:Hm1.
    + msetdec.
    + right. specialize (Hin y). msetdec.
  * exists (min m1[x] m2[x]).
    intro y. msetdec. apply Hin in c. destruct (m1[y]) as [| n].
    + msetdec.
    + destruct (m2[y]); trivial. destruct n; lia.
  Qed.
  
  Lemma inter_In : forall x m1 m2, In x (inter m1 m2) <-> In x m1 /\ In x m2.
  Proof using FMultisetsSpec. intros. unfold In. rewrite inter_spec. unfold gt. rewrite Nat.min_glb_lt_iff. lia. Qed.
  
  Lemma inter_out : forall x m1 m2, ~In x (inter m1 m2) <-> ~In x m1 \/ ~In x m2.
  Proof using FMultisetsSpec. intros x m1 m2. rewrite inter_In. destruct (In_dec x m1); intuition. Qed.
  
  Lemma empty_inter : forall m1 m2, inter m1 m2 == empty <->
    forall x, ~In x m1 /\ ~In x m2 \/ In x m1 /\ ~In x m2 \/ ~In x m1 /\ In x m2.
  Proof using FMultisetsSpec.
  intros m1 m2. split; intro Hin.
  + intro x. destruct (In_dec x m1) as [Hin1 | Hin1], (In_dec x m2) as [Hin2 | Hin2]; auto.
    assert (Habs : In x (inter m1 m2)). { rewrite inter_In. auto. }
    rewrite Hin in Habs. apply In_empty in Habs. elim Habs.
  + intro x. rewrite empty_spec, inter_spec. destruct (Hin x) as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]];
    rewrite not_In in *; try rewrite Hin1; try rewrite Hin2; auto with arith.
  Qed.
  
  Lemma inter_add_l1 : forall x n m1 m2, n <= m2[x] ->
    inter (add x n m1) m2 == add x n (inter m1 (remove x n m2)).
  Proof using FMultisetsSpec. intros x n m1 m2 Hn. rewrite <- (add_remove_cancel Hn) at 1. symmetry. apply add_inter_distr. Qed.
  
  Lemma inter_add_l2 : forall x n m1 m2, m2[x] <= n ->
    inter (add x n m1) m2 == add x (m2[x]) (inter m1 (remove x n m2)).
  Proof using FMultisetsSpec.
  intros x n m1 m2 Hn. assert (Heq : n = m2[x] + (n - m2[x])) by lia.
  rewrite <- (add_remove_cancel (reflexivity (m2[x]))) at 1.
  rewrite Heq, <- add_merge, <- add_inter_distr. f_equiv. clear Heq. intro. msetdec. Qed.
  
  Corollary inter_add_r1 : forall x n m1 m2, n <= m1[x] ->
    inter m1 (add x n m2) == add x n (inter (remove x n m1) m2).
  Proof using FMultisetsSpec. intros. setoid_rewrite inter_comm. now apply inter_add_l1. Qed.
  
  Corollary inter_add_r2 : forall x n m1 m2, m1[x] <= n ->
    inter m1 (add x n m2) == add x (m1[x]) (inter (remove x n m1) m2).
  Proof using FMultisetsSpec. intros. setoid_rewrite inter_comm. now apply inter_add_l2. Qed.
  
  Lemma remove_inter_add_l : forall x n m1 m2, inter (remove x n m1) m2 == remove x n (inter m1 (add x n m2)).
  Proof using FMultisetsSpec.
  repeat intro. msetdec.
  Qed.
  
  Lemma remove_inter_add_r : forall x n m1 m2, inter m1 (remove x n m2) == remove x n (inter (add x n m1) m2).
  Proof using FMultisetsSpec.
  repeat intro. msetdec.
  Qed.
  
  Lemma inter_subset_l : forall m1 m2, inter m1 m2 [<=] m1.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_subset_r : forall m1 m2, inter m1 m2 [<=] m2.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_eq_subset_l : forall m1 m2, inter m1 m2 == m1 <-> m1 [<=] m2.
  Proof using FMultisetsSpec.
  intros. split; intros Hm y; specialize (Hm y); msetdec.
  Qed.
  
  Lemma inter_eq_subset_r : forall m1 m2, inter m1 m2 == m2 <-> m2 [<=] m1.
  Proof using FMultisetsSpec. intros. rewrite inter_comm. apply inter_eq_subset_l. Qed.
  
  (** **  Results about [diff]  **)
  
  Lemma diff_In : forall x m1 m2, In x (diff m1 m2) <-> m1[x] > m2[x].
  Proof using FMultisetsSpec. intros. unfold In. rewrite diff_spec. lia. Qed.
  
  Lemma diff_empty_l : forall m, diff empty m == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_empty_r : forall m, diff m empty == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_empty_subset : forall m1 m2, diff m1 m2 == empty <-> m1 [<=] m2.
  Proof using FMultisetsSpec. intros. split; intros Hm y; specialize (Hm y); msetdec. Qed.
  
  Corollary diff_refl : forall m, diff m m == empty.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_subset : forall m1 m2, diff m1 m2 [<=] m1.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_singleton_l : forall x n m, diff (singleton x n) m == singleton x (n - m[x]).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_singleton_r : forall x n m, diff m (singleton x n) == remove x n m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_singleton_subset : forall x n m1 m2, diff m1 m2 == singleton x n -> m1 [<=] add x n m2.
  Proof using FMultisetsSpec. intros x n m1 m2 Heq y. specialize (Heq y). msetdec. Qed.
  
  Lemma diff_add_r : forall x n m1 m2, n <= m2[x] -> m1[x] <= m2[x] ->
    diff m1 (add x n m2) == remove x n (diff m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_add_l1 : forall x n m1 m2, n <= m2[x] -> diff (add x n m1) m2 == diff m1 (remove x n m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_add_l2 : forall x n m1 m2, m2[x] <= n ->
    diff (add x n m1) m2 == add x (n - m2[x]) (diff m1 (remove x (m2[x]) m2)).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_remove_l : forall x n m1 m2, diff (remove x n m1) m2 == remove x n (diff m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_remove_r1 : forall x n m1 m2, m1[x] <= n -> m2[x] <= n ->
    diff m1 (remove x n m2) == add x (min (m1[x]) (m2[x])) (diff m1 m2).
  Proof using FMultisetsSpec.
  repeat intro. msetdec.
  Qed.
  
  Lemma diff_remove_r2 : forall x n m1 m2, n <= m1[x] -> m2[x] <= m1[x] ->
    diff m1 (remove x n m2) == add x (min n (m2[x])) (diff m1 m2).
  Proof using FMultisetsSpec.
  repeat intro. msetdec.
  Qed.
  
  Lemma diff_remove_r3 : forall x n m1 m2, n <= m2[x] -> m1[x] <= m2[x] ->
    diff m1 (remove x n m2) == add x (n + m1[x] - m2[x]) (diff m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_union_comm_l : forall m1 m2 m3, m3 [<=] m1 -> union (diff m1 m3) m2 == diff (union m1 m2) m3.
  Proof using FMultisetsSpec. intros ? ? ? Hle x. specialize (Hle x). msetdec. Qed.
  
  Lemma diff_union_comm_r : forall m1 m2 m3, m3 [<=] m2 -> union m1 (diff m2 m3) == diff (union m1 m2) m3.
  Proof using FMultisetsSpec. intros ? ? ? Hle x. specialize (Hle x). msetdec. Qed.
  
  Lemma inter_diff_l : forall m1 m2 m3, inter (diff m1 m2) m3 == diff (inter m1 (union m2 m3)) m2.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_diff_r : forall m1 m2 m3, inter m1 (diff m2 m3) == diff (inter m2 (union m1 m3)) m3.
  Proof using FMultisetsSpec. intros. rewrite inter_comm, union_comm. apply inter_diff_l. Qed.
  
  Lemma diff_inter_distr_l : forall m1 m2 m3, diff (inter m1 m2) m3 == inter (diff m1 m3) (diff m2 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_inter_r : forall m1 m2 m3, diff m1 (inter m2 m3) == lub (diff m1 m2) (diff m1 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_inter : forall m1 m2, diff m1 m2 == diff m1 (inter m1 m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Corollary diff_disjoint : forall m1 m2, inter m1 m2 == empty -> diff m1 m2 == m1.
  Proof using FMultisetsSpec. intros m1 m2 Hm. rewrite diff_inter, Hm. apply diff_empty_r. Qed.
  
  Lemma diff_injective : forall m1 m2 m3, m3 [<=] m1 -> m3 [<=] m2 -> diff m1 m3 == diff m2 m3 -> m1 == m2.
  Proof using FMultisetsSpec. intros ? ? ? Hle1 Hle2 Heq x. specialize (Heq x). specialize (Hle1 x). specialize (Hle2 x). msetdec. Qed.
  
  Lemma inter_as_diff : forall m1 m2, inter m1 m2 == diff m1 (diff m1 m2).
  Proof using FMultisetsSpec. intros ? ? ?. msetdec. Qed.
  
  Lemma subset_split : forall m1 m2, m1 [<=] m2 <-> union (diff m2 m1) m1 == m2.
  Proof using FMultisetsSpec. intros. split; intros Hle x; specialize (Hle x); msetdec. Qed.
  
  (** **  Results about [lub]  **)
  
  Lemma lub_In : forall x m1 m2, In x (lub m1 m2) <-> In x m1 \/ In x m2.
  Proof using FMultisetsSpec. intros. unfold In, gt. rewrite lub_spec. apply Nat.max_lt_iff. Qed.
  
  Lemma lub_comm : forall m1 m2, lub m1 m2 == lub m2 m1.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_assoc : forall m1 m2 m3, lub m1 (lub m2 m3) == lub (lub m1 m2) m3.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_empty_l : forall m, lub empty m == m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_empty_r : forall m, lub m empty == m.
  Proof using FMultisetsSpec. intros. rewrite lub_comm. apply lub_empty_l. Qed.
  
  Lemma lub_subset_l : forall m1 m2, m1 [<=] lub m1 m2.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_subset_r : forall m1 m2, m2 [<=] lub m1 m2.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_is_empty : forall m1 m2, lub m1 m2 == empty <-> m1 == empty /\ m2 == empty.
  Proof using FMultisetsSpec.
  intros m1 m2. split; intro Heq.
  + split; intro x; specialize (Heq x); msetdec;
    destruct (m1[x]), (m2[x]); trivial; discriminate.
  + intro. destruct Heq. msetdec.
  Qed.
  
  Lemma lub_eq_l : forall m1 m2, lub m1 m2 == m2 <-> m1 [<=] m2.
  Proof using FMultisetsSpec.
  intros m1 m2. split; intro Heq.
  - rewrite <- Heq. apply lub_subset_l.
  - intro x. msetdec. apply Nat.max_r, Heq.
  Qed.
  
  Lemma subset_lub_r : forall m1 m2, m2 [<=] m1 <-> lub m1 m2 == m1.
  Proof using FMultisetsSpec. intros. now rewrite lub_comm, lub_eq_l. Qed.
  
  Lemma add_lub_distr : forall x n m1 m2, add x n (lub m1 m2) == lub (add x n m1) (add x n m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_add_l : forall x n m1 m2, lub (add x n m1) m2 == add x n (lub m1 (remove x n m2)).
  Proof using FMultisetsSpec.
  intros x n m1 m2 y. msetdec.
  Qed.
  
  Lemma lub_add_r : forall x n m1 m2, lub m1 (add x n m2) == add x n (lub (remove x n m1) m2).
  Proof using FMultisetsSpec. intros. setoid_rewrite lub_comm. apply lub_add_l. Qed.
  
  Lemma lub_singleton_l : forall x n m, lub (singleton x n) m == add x (n - m[x]) m.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_singleton_r : forall x n m, lub m (singleton x n) == add x (n - m[x]) m.
  Proof using FMultisetsSpec. intros. rewrite lub_comm. apply lub_singleton_l. Qed.
  
  Lemma lub_is_singleton : forall x n m1 m2, lub m1 m2 == singleton x n
    <-> m1 == singleton x (m1[x]) /\ m2 == singleton x (m2[x])
        /\ n = max (m1[x]) (m2[x]).
  Proof using FMultisetsSpec.
  intros x n m1 m2. split; intro Heq.
  + repeat split; try intro y.
    - specialize (Heq y). msetdec.
    - specialize (Heq y). msetdec.
    - specialize (Heq x). msetdec.
  + destruct Heq as [Hm1 [Hm2 Hn]]. rewrite Hm1, Hm2, lub_singleton_l, add_singleton_same. f_equiv. subst.
    rewrite singleton_same. apply Max.max_case_strong; lia.
  Qed.
  
  Lemma remove_lub : forall x n m1 m2, remove x n (lub m1 m2) == lub (remove x n m1) (remove x n m2).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_remove_l : forall x n m1 m2, lub (remove x n m1) m2 == remove x n (lub m1 (add x n m2)).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_remove_r : forall x n m1 m2, lub m1 (remove x n m2) == remove x n (lub (add x n m1) m2).
  Proof using FMultisetsSpec. intros. setoid_rewrite lub_comm. apply lub_remove_l. Qed.
  
  Lemma union_lub_distr_l : forall m1 m2 m3, union (lub m1 m2) m3 == lub (union m1 m3) (union m2 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma union_lub_distr_r : forall m1 m2 m3, union m1 (lub m2 m3) == lub (union m1 m2) (union m1 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_union_l : forall m1 m2 m3, lub (union m1 m2) m3 == union m1 (lub m2 (diff m3 m1)).
  Proof using FMultisetsSpec.
  repeat intro. msetdec. Qed.
  
  Lemma lub_union_r : forall m1 m2 m3, lub m1 (union m2 m3) == union (lub m3 (diff m1 m2)) m2.
  Proof using FMultisetsSpec. intros. rewrite lub_comm. setoid_rewrite union_comm at 2. apply lub_union_l. Qed.
  
  Lemma lub_inter_distr_l : forall m1 m2 m3, lub m1 (inter m2 m3) == inter (lub m1 m2) (lub m1 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_inter_distr_r : forall m1 m2 m3, lub (inter m1 m2) m3 == inter (lub m1 m3) (lub m2 m3).
  Proof using FMultisetsSpec. intros. setoid_rewrite lub_comm. apply lub_inter_distr_l. Qed.
  
  Lemma inter_lub_distr_l : forall m1 m2 m3, inter m1 (lub m2 m3) == lub (inter m1 m2) (inter m1 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma inter_lub_distr_r : forall m1 m2 m3, inter (lub m1 m2) m3 == lub (inter m1 m3) (inter m2 m3).
  Proof using FMultisetsSpec. intros. setoid_rewrite inter_comm. apply inter_lub_distr_l. Qed.
  
  Lemma lub_diff_l : forall m1 m2 m3, lub (diff m1 m2) m3 == diff (lub m1 (union m2 m3)) m2.
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_diff_r : forall m1 m2 m3, lub m1 (diff m2 m3) == diff (lub (union m1 m3) m2) m3.
  Proof using FMultisetsSpec. intros. setoid_rewrite lub_comm. rewrite union_comm. apply lub_diff_l. Qed.
  
  Lemma diff_lub_distr_r : forall m1 m2 m3, diff (lub m1 m2) m3 == lub (diff m1 m3) (diff m2 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma diff_lub_l : forall m1 m2 m3, diff m1 (lub m2 m3) == inter (diff m1 m2) (diff m1 m3).
  Proof using FMultisetsSpec. repeat intro. msetdec. Qed.
  
  Lemma lub_subset_union : forall m1 m2, lub m1 m2 [<=] union m1 m2.
  Proof using FMultisetsSpec. intros m1 m2 ?. msetdec. Qed.
  
  (** **  Results about [elements]  **)
  
  Lemma elements_pos : forall x n m, InA eq_pair (x, n) (elements m) -> n > 0.
  Proof using FMultisetsSpec. intros x n m Hin. now rewrite elements_spec in Hin. Qed.
  
  Theorem elements_In : forall x n m, InA eq_elt (x, n) (elements m) <-> In x m.
  Proof using FMultisetsSpec.
  intros x n m. split; intro Hin.
  + apply InA_elt_pair in Hin. destruct Hin as [p Hp]. simpl in Hp. rewrite elements_spec in Hp.
    destruct Hp as [Heq Hpos]. unfold In. simpl in *. now subst.
  + apply InA_pair_elt with (m[x]). rewrite elements_spec. split; trivial.
  Qed.
  
  Lemma elements_elt_strengthen : forall x n m,
    InA eq_elt (x, n) (elements m) -> InA eq_pair (x, m[x]) (elements m).
  Proof using FMultisetsSpec. intros ? ? ? Hin. rewrite elements_spec. simpl. rewrite elements_In in Hin. intuition. Qed.
  
  Theorem elements_eq_equiv : forall m₁ m₂, equivlistA eq_pair (elements m₁) (elements m₂) <-> m₁ == m₂.
  Proof using FMultisetsSpec.
  intros m₁ m₂. split; intro Heq.
  + assert (Hdup₁ := NoDupA_strengthen subrelation_pair_elt (elements_NoDupA m₁)).
    assert (Hdup₂ := NoDupA_strengthen subrelation_pair_elt (elements_NoDupA m₂)).
    apply (NoDupA_equivlistA_PermutationA _) in Heq; trivial. clear Hdup₁ Hdup₂.
    intro x. destruct (m₂[x]) eqn:Hm₂.
    - assert (Hin : forall n, ~InA eq_pair (x, n) (elements m₂)).
      { intros n Habs. rewrite elements_spec in Habs. destruct Habs. simpl in *. lia. }
      destruct (m₁[x]) eqn:Hm₁. reflexivity.
      specialize (Hin (S n)). rewrite <- Heq in Hin. rewrite elements_spec in Hin.
      elim Hin. split; simpl. assumption. lia.
    - assert (Hin : InA eq_pair (x, S n) (elements m₂)). { rewrite elements_spec. split; simpl. assumption. lia. }
      rewrite <- Heq in Hin. rewrite elements_spec in Hin. now destruct Hin.
  + intros [x n]. now rewrite Heq.
  Qed.
  
  Corollary elements_eq : forall m₁ m₂, PermutationA eq_pair (elements m₁) (elements m₂) <-> m₁ == m₂.
  Proof using FMultisetsSpec.
  intros m₁ m₂. rewrite <- elements_eq_equiv. split; intro.
  - now apply (PermutationA_equivlistA _).
  - apply (NoDupA_equivlistA_PermutationA _); trivial; apply (NoDupA_strengthen _ (elements_NoDupA _)).
  Qed.
  
  Lemma elements_pair_subset : forall x n m₁ m₂,
    m₁ [<=] m₂ -> InA eq_pair (x, n) (elements m₁) -> exists n', n <= n' /\ InA eq_pair (x, n') (elements m₂).
  Proof using FMultisetsSpec.
  intros x n m₁ m₂ Hm. setoid_rewrite elements_spec. simpl. intros [Heq Hpos].
  exists (m₂[x]); repeat split.
  - rewrite <- Heq. apply Hm.
  - specialize (Hm x). lia.
  Qed.
  
  Lemma elements_elt_subset : forall xn m₁ m₂,
    m₁ [<=] m₂ -> InA eq_elt xn (elements m₁) -> InA eq_elt xn (elements m₂).
  Proof using FMultisetsSpec. intros [? ?] * ?. do 2 rewrite elements_In. now apply In_sub_compat. Qed.
  
  Lemma elements_nil : forall m, elements m = nil <-> m == empty.
  Proof using FMultisetsSpec.
  intro m. split; intro Heq.
  - intro x.
    assert (~m[x] > 0).
    { intro Habs. apply (conj (eq_refl (m[x]))) in Habs.
      change x with (fst (x, m[x])) in Habs at 1.
      change (m[x]) with (snd (x, m[x])) in Habs at 2 3.
      rewrite <- elements_spec in Habs. rewrite Heq in Habs. now rewrite InA_nil in Habs. }
    rewrite empty_spec. lia.
  - apply (@PermutationA_nil _ eq_pair _). now rewrite Heq, elements_empty.
  Qed.
  
  Lemma elements_add_In : forall x y n p m, InA eq_pair (x, n) (elements (add y p m))
    <-> equiv x y /\ n = p + m[y] /\ n > 0
        \/ ~equiv x y /\ InA eq_pair (x, n) (elements m).
  Proof using FMultisetsSpec.
  intros x y n p m. rewrite elements_spec. simpl. split; intro Hx.
  + destruct Hx as [Hx1 Hx2]. destruct (equiv_dec x y) as [Heq | Hneq].
    - left. repeat split; try assumption. subst n. rewrite <- Heq. rewrite add_same. apply Nat.add_comm.
    - right. split. assumption. rewrite elements_spec. rewrite add_other in Hx1. simpl. now split. auto.
  + destruct Hx as [[Hx1 [Hx2 Hx3]] | [Hx1 Hx2]].
    - rewrite Hx1, add_same. split; lia.
    - rewrite elements_spec in Hx2. destruct Hx2. simpl in *. rewrite add_other. now split. auto.
  Qed.
  
  Lemma elements_remove : forall x y n p m, InA eq_pair (x, n) (elements (remove y p m))
    <-> equiv x y /\ n = m[y] - p /\ n > 0
        \/ ~equiv x y /\ InA eq_pair (x, n) (elements m).
  Proof using FMultisetsSpec.
  intros x y n p m. rewrite elements_spec. simpl. split; intro Hx.
  + destruct Hx as [Hx1 Hx2]. destruct (equiv_dec x y) as [Heq | Hneq].
    - left. repeat split; try assumption. now rewrite Heq, remove_same in Hx1.
    - right. split. assumption. rewrite elements_spec. rewrite remove_other in Hx1; auto.
  + destruct Hx as [[Hx1 [Hx2 Hx3]] | [Hx1 Hx2]].
    - rewrite Hx1, remove_same. now split.
    - rewrite elements_spec in Hx2. destruct Hx2. simpl in *. rewrite remove_other; trivial. now split.
  Qed.
  
  Lemma elements_union : forall x n m₁ m₂, InA eq_pair (x, n) (elements (union m₁ m₂))
    <-> (In x m₁ \/ In x m₂) /\ n = m₁[x] + m₂[x].
  Proof using FMultisetsSpec.
  intros x n m₁ m₂. rewrite elements_spec, union_spec. simpl. unfold In.
  split; intros [Heq Hpos]; split; now symmetry || lia.
  Qed.
  
  Lemma elements_inter : forall x n m₁ m₂, InA eq_pair (x, n) (elements (inter m₁ m₂))
    <-> (In x m₁ /\ In x m₂) /\ n = min (m₁[x]) (m₂[x]).
  Proof using FMultisetsSpec.
  intros x n m₁ m₂. rewrite elements_spec, inter_spec. unfold In. simpl.
  split; intros [Heq Hpos]; split; try (now symmetry).
  - rewrite <- Heq in *. unfold gt in *. now rewrite Nat.min_glb_lt_iff in *.
  - rewrite Hpos. unfold gt in *. now rewrite Nat.min_glb_lt_iff in *.
  Qed.
  
  Lemma elements_diff : forall x n m₁ m₂, InA eq_pair (x, n) (elements (diff m₁ m₂))
    <-> n = m₁[x] - m₂[x] /\ n > 0.
  Proof using FMultisetsSpec. intros. rewrite elements_spec, diff_spec. intuition. Qed.
  
  Lemma elements_lub : forall x n m₁ m₂, InA eq_pair (x, n) (elements (lub m₁ m₂))
    <-> (In x m₁ \/ In x m₂) /\ n = max (m₁[x]) (m₂[x]).
  Proof using FMultisetsSpec.
  intros x n m₁ m₂. rewrite elements_spec, lub_spec. unfold In. simpl.
  split; intros [Heq Hpos]; split; try (now symmetry).
  - rewrite <- Heq in *. unfold gt in *. now rewrite Nat.max_lt_iff in *.
  - rewrite Hpos. unfold gt in *. now rewrite Nat.max_lt_iff in *.
  Qed.
  
  Lemma support_elements : forall x m, InA equiv x (support m) <-> InA eq_pair (x, m[x]) (elements m).
  Proof using FMultisetsSpec. intros. rewrite support_spec, elements_spec. simpl. msetdec. Qed.
  
  Lemma elements_add_out : forall x n m, n > 0 -> ~In x m ->
    PermutationA eq_pair (elements (add x n m)) ((x, n) :: elements m).
  Proof using FMultisetsSpec.
  intros x n m Hn Hin. apply (NoDupA_equivlistA_PermutationA _).
  * apply (NoDupA_strengthen _ (elements_NoDupA _)).
  * constructor.
    + rewrite elements_spec. simpl. intros [? _]. apply Hin. unfold In. lia.
    + apply (NoDupA_strengthen _ (elements_NoDupA _)).
  * intros [y p]. rewrite elements_add_In. split; intro Hm.
    + destruct Hm as [[Hm1 [Hm2 Hpos]] | [Hm1 Hm2]]; simpl in *.
      - unfold In in Hin. left. split. assumption. compute. lia.
      - now right.
    + simpl. inversion_clear Hm.
      - destruct H as [Hy Hp]. compute in Hy, Hp. left. subst. unfold In in Hin. repeat split; trivial. lia.
      - right. split; trivial. intro Habs. apply Hin. rewrite <- Habs. rewrite <- support_spec, support_elements.
        assert (Hy := H). rewrite elements_spec in Hy. destruct Hy as [Hy _]. simpl in Hy. now subst.
  Qed.
  
  Lemma elements_remove1 : forall x n m, m[x] <= n ->
    PermutationA eq_pair (elements (remove x n m)) (removeA pair_dec (x, m[x]) (elements m)).
  Proof using FMultisetsSpec.
  intros x n m Hn. apply (NoDupA_equivlistA_PermutationA _).
  + apply (NoDupA_strengthen _ (elements_NoDupA _)).
  + apply removeA_NoDupA; refine _. apply (NoDupA_strengthen _ (elements_NoDupA _)).
  + intros [y p]. rewrite removeA_InA_iff; refine _. rewrite elements_remove, elements_spec. simpl. intuition.
    - destruct H1. contradiction.
    - destruct (equiv_dec y x) as [Heq | Heq]; auto. elim H1. split; msetdec.
  Qed.
  
  Lemma elements_remove2 : forall x n m, n < m[x] ->
    PermutationA eq_pair (elements (remove x n m))
                         ((x, m[x] - n) :: removeA elt_dec (x, m[x]) (elements m)).
  Proof using FMultisetsSpec.
  intros x n m Hn. apply (NoDupA_equivlistA_PermutationA _).
  + apply (NoDupA_strengthen _ (elements_NoDupA _)).
  + constructor.
    - intro Habs. eapply InA_pair_elt in Habs. rewrite removeA_InA_iff in Habs; refine _.
      destruct Habs as [_ Habs]. now elim Habs.
    - eapply (NoDupA_strengthen subrelation_pair_elt). apply removeA_NoDupA, elements_NoDupA; refine _.
  + intros [y p]. rewrite elements_remove, elements_spec. simpl. intuition.
    - rewrite H. left. split. compute. reflexivity. assumption.
    - right. rewrite removeA_InA_iff_strong; refine _. split; trivial.
      rewrite elements_spec. auto.
    - { destruct (equiv_dec y x) as [Heq | Heq].
        + inversion_clear H.
          - left. destruct H0. repeat split; auto. hnf in *. simpl in *. lia.
          - apply (InA_pair_elt (m[x])) in H0. rewrite Heq, removeA_InA in H0; refine _.
            destruct H0 as [_ Habs]. elim Habs. reflexivity.
        + right. split; trivial. inversion_clear H.
          - elim Heq. destruct H0. auto.
          - apply removeA_InA_weak in H0. rewrite elements_spec in H0. assumption. }
  Qed.
  
  (** [is_elements] tests wether a given list can be the elements of a multiset **)
  Definition is_elements l := NoDupA eq_elt l /\ Forall (fun xn => snd xn > 0) l.
  
  Lemma is_elements_nil : is_elements nil.
  Proof using . split; constructor. Qed.
  
  Lemma is_elements_cons : forall xn l, is_elements l -> ~InA eq_elt xn l -> snd xn > 0 -> is_elements (xn :: l).
  Proof using .
  unfold is_elements. setoid_rewrite Forall_forall. intros xn l [Hdup Hpos] Hx Hn. split.
  - now constructor.
  - intros [y p] Hin. inversion_clear Hin; now subst || apply Hpos.
  Qed.
  
  Lemma is_elements_cons_inv : forall xn l, is_elements (xn :: l) -> is_elements l.
  Proof using . intros xn l [Hdup Hpos]. inversion_clear Hpos. inversion_clear Hdup. now split. Qed.
  
  Lemma elements_is_elements : forall m, is_elements (elements m).
  Proof using FMultisetsSpec.
  intro m. split.
  - now apply elements_NoDupA.
  - rewrite Forall_forall. intros [x n] Hx. apply (@elements_pos x n m). now apply (In_InA _).
  Qed.
  
  Global Instance is_elements_compat : Proper (PermutationA eq_pair ==> iff) is_elements.
  Proof using .
  intros l1 l2 perm. induction perm as [| [x n] [y p] ? ? [Heq1 Heq2] | x y l | l1 l2 l3].
  + reflexivity.
  + compute in Heq1, Heq2. subst p. split; intros [Hdup Hpos]; inversion_clear Hdup; inversion_clear Hpos.
    - apply is_elements_cons.
        apply IHperm. now split.
        now rewrite perm, Heq1 in H.
        assumption.
    - apply is_elements_cons.
        apply IHperm. now split.
        now rewrite perm, Heq1.
        assumption.
  + split; intros [Hdup Hpos]; inversion_clear Hdup; inversion_clear Hpos;
    inversion_clear H0; inversion_clear H2; repeat apply is_elements_cons; trivial.
    - now split.
    - intro Habs. apply H. now right.
    - intros Habs. inversion_clear Habs.
        apply H. now left.
        contradiction.
    - now split.
    - intro Habs. apply H. now right.
    - intros Habs. inversion_clear Habs.
        apply H. now left.
        contradiction.
  + now rewrite IHperm1.
  Qed.
  
  Theorem is_elements_spec : forall l, is_elements l <-> exists m, PermutationA eq_pair l (elements m).
  Proof using FMultisetsSpec.
  induction l as [| [x n] l].
  + split; intro Hl.
    - exists empty. now rewrite elements_empty.
    - apply is_elements_nil.
  + split; intro Hl.
    - destruct Hl as [Hdup Hpos].
      assert (Hel : is_elements l). { split. now inversion_clear Hdup. now inversion_clear Hpos. }
      rewrite IHl in Hel. destruct Hel as [m Hm]. exists (add x n m). symmetry. rewrite Hm. apply elements_add_out.
        now inversion_clear Hpos.
        inversion_clear Hdup. rewrite <- support_spec, support_elements. intro Habs. apply H.
        rewrite <- Hm in Habs. eapply InA_pair_elt. apply Habs.
    - destruct Hl as [m Hperm]. rewrite Hperm. apply elements_is_elements.
  Qed.
  
  (** A variant of the previous theorem, but with conclusion in [Type] rather than [Prop]. **)
  Theorem is_elements_build : forall l, is_elements l -> {m | PermutationA eq_pair l (elements m)}.
  Proof.
  induction l as [| [x n] l]; intro Hl.
  + exists empty. now rewrite elements_empty.
  + destruct Hl as [Hdup Hpos].
    assert (Hel : is_elements l). { split. now inversion_clear Hdup. now inversion_clear Hpos. }
    apply IHl in Hel. destruct Hel as [m Hm]. exists (add x n m). symmetry. rewrite Hm. apply elements_add_out.
    - now inversion_clear Hpos.
    - inversion_clear Hdup. rewrite <- support_spec, support_elements. intro Habs. apply H.
      rewrite <- Hm in Habs. eapply InA_pair_elt. apply Habs.
  Defined.
  
  (** [from_elements] builds back a multiset from its elements **)
  Fixpoint from_elements l := (* List.fold_left (fun acc xn => add (fst xn) (snd xn) acc) l empty. *)
    match l with
      | nil => empty
      | (x, n) :: l => add x n (from_elements l)
    end.
  
  Global Instance from_elements_compat : Proper (PermutationA eq_pair ==> equiv) from_elements.
  Proof using FMultisetsSpec.
  intros l1 l2 perm. induction perm as [| [x n] [y p] ? ? [Hxy Hnp] | [x n] [y p] |]; simpl.
  + reflexivity.
  + intro z. compute in Hxy, Hnp. now rewrite Hxy, Hnp, IHperm.
  + apply add_comm.
  + intro x. now transitivity ((from_elements l₂)[x]).
  Qed.
  
  Lemma from_elements_nil : from_elements nil = empty.
  Proof using . reflexivity. Qed.
  
  Lemma from_elements_cons : forall x n l, from_elements ((x, n) :: l) = add x n (from_elements l).
  Proof using . reflexivity. Qed.
  
  Lemma from_elements_valid_empty : forall l, is_elements l -> from_elements l == empty <-> l = nil.
  Proof using FMultisetsSpec.
  intros [| [x n] l] Hl.
  - simpl. intuition.
  - destruct Hl as [_ Hl]. inversion_clear Hl. simpl from_elements.
    rewrite add_is_empty. cbn in *. intuition (lia || discriminate).
  Qed.
  
  Lemma from_elements_empty : forall l, from_elements l == empty <-> Forall (fun xn => snd xn = 0) l.
  Proof using FMultisetsSpec.
  induction l as [| [x n] l].
  + simpl. intuition.
  + simpl from_elements. split; intro Hl; rewrite add_is_empty, IHl in *; inversion_clear Hl; intuition.
  Qed.
  
  Lemma from_elements_singleton : forall x n l, is_elements l -> n > 0 ->
    from_elements l == singleton x n <-> eqlistA eq_pair l ((x, n) :: nil).
  Proof using FMultisetsSpec.
  intros x n l Hl Hn. destruct l as [| [y p] [| [z q] l]].
  + split; intro Hin.
    - symmetry in Hin. rewrite singleton_empty in Hin. lia.
    - inversion_clear Hin.
  + simpl from_elements. rewrite add_empty. split; intro Heq.
    - symmetry in Heq. apply singleton_injective in Heq; trivial. destruct Heq. now repeat constructor.
    - inversion_clear Heq. destruct H as [Heq1 Heq2]. compute in Heq1, Heq2. now rewrite Heq1, Heq2.
  + split; intro Hin.
    - assert (Heq : equiv y x /\ equiv z x).
      { simpl in *. split.
        + specialize (Hin y). msetdec. destruct Hl as [_ Hl]. inversion_clear Hl. cbn in *. lia.
        + apply add_is_singleton in Hin. specialize (Hin z). msetdec. destruct Hl as [_ Hl].
          inversion_clear Hl. inversion_clear H0. simpl in *. lia. }
      destruct Heq as [Heq1 Heq2]. destruct Hl as [Hl _]. inversion_clear Hl.
      elim H. left. compute. now transitivity x.
    - inversion_clear Hin. inversion_clear H0.
  Qed.
  
  Lemma from_elements_out : forall x n l, ~InA eq_elt (x, n) l -> (from_elements l)[x] = 0.
  Proof using FMultisetsSpec.
  intros x n l Hin. induction l as [| [y p] l]; simpl.
  + apply empty_spec.
  + rewrite add_other.
    - apply IHl. intro Habs. apply Hin. now right.
    - intro Habs. apply Hin. now left.
  Qed.
  
  Lemma from_elements_in : forall x n l, NoDupA eq_elt l -> InA eq_pair (x, n) l -> (from_elements l)[x] = n.
  Proof using FMultisetsSpec.
  intros x n l Hl Hin. induction l as [| [y p] l].
  + rewrite InA_nil in Hin. elim Hin.
  + simpl. inversion_clear Hin.
    - destruct H as [Hx Hn]. compute in Hx, Hn. inversion Hl. now rewrite Hx, add_same, (@from_elements_out y p).
    - inversion_clear Hl. rewrite add_other. now apply IHl.
      intro Habs. apply H0. apply InA_pair_elt with n. now rewrite <- Habs.
  Qed.
  
  Lemma from_elements_elements : forall m, from_elements (elements m) == m.
  Proof using FMultisetsSpec.
  intros m x. destruct (m[x]) eqn:Hn.
  - apply from_elements_out with 0. intro Habs. apply InA_elt_pair in Habs.
    destruct Habs as [n Habs]. rewrite elements_spec in Habs. simpl in Habs. lia.
  - apply from_elements_in. apply elements_NoDupA. rewrite elements_spec. simpl. lia.
  Qed.
  
  Lemma elements_from_elements : forall l, is_elements l -> PermutationA eq_pair (elements (from_elements l)) l.
  Proof using FMultisetsSpec.
  intros l Hl. rewrite is_elements_spec in Hl. destruct Hl as [m Hm]. now rewrite Hm, from_elements_elements.
  Qed.
  
  Lemma elements_injective : forall m1 m2, PermutationA eq_pair (elements m1) (elements m2) -> m1 == m2.
  Proof using FMultisetsSpec. intros. setoid_rewrite <- from_elements_elements. now f_equiv. Qed.
  
  Lemma from_elements_injective : forall l1 l2, is_elements l1 -> is_elements l2 -> 
    from_elements l1 == from_elements l2 -> PermutationA eq_pair l1 l2.
  Proof using FMultisetsSpec. intros. setoid_rewrite <- elements_from_elements; trivial. now f_equiv. Qed.
  
  (* If [l] contains duplicates of [x], we need to sum all their contribution. *)
  Theorem from_elements_spec : forall x n l, (from_elements l)[x] = n <->
    List.fold_left (fun acc yp => if equiv_dec (fst yp) x then (snd yp) + acc else acc) l 0 = n.
  Proof using FMultisetsSpec.
  intros x n l. rewrite <- Nat.add_0_r at 1. generalize 0. revert n. induction l as [| [y p] l]; intros n q; simpl.
  + msetdec.
  + destruct (equiv_dec y x) as [Heq | Heq].
    - rewrite Heq, add_same, <- Nat.add_assoc, IHl. reflexivity.
    - rewrite add_other; msetdec.
  Qed.
  
  Lemma from_elements_In : forall l x, In x (from_elements l) <-> exists n, InA eq_pair (x, n) l /\ n > 0.
  Proof using FMultisetsSpec.
  intros l x. induction l as [| [y p] l].
  * simpl. split; intro Hin.
    + elim (In_empty Hin).
    + destruct Hin as [? [Hin _]]. rewrite InA_nil in Hin. elim Hin.
  * simpl. rewrite add_In, IHl; trivial. split; intros Hin.
    + destruct Hin as [[? Heq] | [n [Hin Hn]]].
      - exists p. split; try (left; split); auto; lia.
      - exists n. split; trivial. now right.
    + destruct Hin as [n [Hin Hn]]. inversion_clear Hin.
      - destruct H. left. compute in *. split; trivial. lia.
      - right. exists n. now split.
  Qed.
  
  Corollary from_elements_In_valid : forall x l, is_elements l ->
    In x (from_elements l) <-> forall n, InA eq_elt (x, n) l.
  Proof using FMultisetsSpec.
  intros x l Hl. rewrite from_elements_In. split; intro Hin.
  + destruct Hin as [n [Hin Hn]]. intro m. revert Hin. apply InA_pair_elt.
  + specialize (Hin 0). apply InA_elt_pair in Hin. destruct Hin as [n Hin].
    exists n. split; trivial. destruct Hl as [_ Hl]. rewrite Forall_forall in Hl.
    rewrite InA_alt in Hin. destruct Hin as [[y p] [[Heq Hnp] Hin]].
    compute in Hnp. subst. change p with (snd (y, p)). now apply Hl.
  Qed.
  
  Theorem from_elements_nodup_spec : forall l x n, n > 0 -> NoDupA eq_elt l ->
    (from_elements l)[x] = n <-> InA eq_pair (x, n) l.
  Proof using FMultisetsSpec.
  induction l as [| [y p] l]; intros x n Hn Hnodup.
  * simpl. rewrite InA_nil, empty_spec. lia.
  * simpl. destruct (equiv_dec x y) as [Heq | Heq].
    + assert (Hin : (from_elements l)[y] = 0).
      { setoid_replace ((from_elements l)[y] = 0) with (~In y (from_elements l)) by (unfold In; cbn; lia).
        destruct l as [| z l]; try apply In_empty. inversion_clear Hnodup.
        rewrite from_elements_In; trivial. intros [q [Hin Hq]]. apply H. revert Hin. apply InA_pair_elt. }
      rewrite Heq, add_same, Hin. simpl. split; intro Hp.
      - subst. now repeat left.
      - inversion_clear Hp.
        -- destruct H; auto.
        -- inversion_clear Hnodup. elim H0. revert H. apply InA_pair_elt.
    + rewrite add_other; trivial. destruct l as [| z l].
      - simpl. rewrite empty_spec. intuition; try lia.
        inversion_clear H. destruct H0; try contradiction. rewrite InA_nil in H0. elim H0.
      - inversion_clear Hnodup. rewrite IHl; discriminate || trivial. intuition.
        inversion_clear H1; trivial. destruct H2. contradiction.
  Qed.
  
  Corollary from_elements_valid_spec : forall l x n, n > 0 -> is_elements l ->
    (from_elements l)[x] = n <-> InA eq_pair (x, n) l.
  Proof using FMultisetsSpec.  intros ? ? ? ? [? _]. now apply from_elements_nodup_spec. Qed.
  
  Lemma from_elements_append : forall l1 l2,
   from_elements (l1 ++ l2) == union (from_elements l1) (from_elements l2).
  Proof using FMultisetsSpec.
  induction l1 as [| [x n] l]; intro l2.
  - now rewrite union_empty_l.
  - simpl from_elements. rewrite IHl. symmetry. apply union_add_comm_l.
  Qed.
  
  Lemma elements_add : forall x n m, 0 < n \/ In x m ->
    PermutationA eq_pair (elements (add x n m))
                         ((x, n + m[x]) :: removeA pair_dec (x, m[x]) (elements m)).
  Proof using FMultisetsSpec.
  intros x n m Hn.
  destruct (In_dec x m) as [Hin | Hout].
  + rewrite <- (elements_In x 0) in Hin. apply elements_elt_strengthen, PermutationA_split in Hin; refine _.
    destruct Hin as [l' Hin]. rewrite <- (from_elements_elements m), Hin at 1.
    assert (Hl' : is_elements ((x, m[x]) :: l')). { rewrite <- Hin. apply elements_is_elements. }
    assert (Hout : ~InA eq_elt (x, (m[x])) l'). { apply proj1 in Hl'. now inversion_clear Hl'. }
    rewrite from_elements_cons, add_merge. rewrite elements_add_out.
    - constructor; try reflexivity. apply is_elements_cons_inv in Hl'.
      rewrite Hin, elements_from_elements; trivial. simpl.
      destruct pair_dec as [? | Habs]; try now elim Habs.
      rewrite removeA_out; try reflexivity. intro Habs. apply Hout. revert Habs. apply InA_pair_elt.
    - apply proj2 in Hl'. inversion_clear Hl'. simpl in *. lia.
    - apply is_elements_cons_inv in Hl'. rewrite <- elements_In, elements_from_elements; eauto.
  + assert (0 < n) by tauto.
    rewrite not_In in Hout. rewrite Hout, Nat.add_0_r. rewrite <- not_In in Hout.
    rewrite elements_add_out; trivial; []. f_equiv.
    rewrite removeA_out; try reflexivity; [].
    rewrite elements_spec. simpl. lia.
  Qed.
  
  (*
  Lemma from_elements_remove : forall x n l, countA_occ eq_pair (x, n) l = 1 ->
    from_elements (removeA pair_dec (x, n) l) == remove x n (from_elements l).
  Proof.
  intros x n l Hl y. induction l as [| [z p] l]; simpl.
  + discriminate Hl.
  + destruct (pair_dec (x, n) (z, p)) as [Heq | Heq].
    - compute in Heq. destruct Heq as [Heq ?]. subst p. rewrite <- Heq. rewrite remove_add_cancel.
    - 
  Qed.
  
  Lemma from_elements_remove_all : forall x n l,
    from_elements (removeA elt_dec (x, n) l) == remove_all x (from_elements l)
  *)
  
  (** **  Results about [fold]  **)
  
  Definition fold_rect : forall {A} (f : elt -> nat -> A -> A)
                                (P : multiset elt -> A -> Type) (i : A) (m : multiset elt),
    (forall m1 m2 acc, m1 == m2 -> P m1 acc -> P m2 acc) ->
    P empty i ->
    (forall x m' acc, In x m -> ~In x m' -> P m' acc -> P (add x m[x] m') (f x m[x] acc)) ->
    P m (fold f m i).
  Proof using FMultisetsSpec.
  intros A f P i m HP H0 Hrec. rewrite fold_spec. rewrite <- fold_left_rev_right.
  assert (Hrec' : forall x acc m', InA eq_pair (x, m[x]) (rev (elements m)) -> ~In x m' ->
                                       P m' acc -> P (add x m[x] m') (f x m[x] acc)).
  { intros ? ? ? Hin ? Hacc. apply Hrec; trivial; []. now rewrite (InA_rev _), elements_spec in Hin. }
  assert (Helt : is_elements (rev (elements m))).
  { rewrite <- (PermutationA_rev _). apply (elements_is_elements _). }
  assert (Hval : forall xn, List.In xn (rev (elements m)) -> snd xn = m[fst xn]).
  { setoid_rewrite <- in_rev. intros [x n] Hin.
    eapply In_InA in Hin; try rewrite elements_spec in Hin; intuition. }
  clear Hrec. pose (l := rev (elements m)). fold l in Hrec', Helt, Hval |- *.
  eapply HP. rewrite <- from_elements_elements. rewrite (PermutationA_rev _). reflexivity.
  fold l. clearbody l. induction l as [| [x n] l]; simpl.
  + (* elements m = nil *)
    assumption.
  + (* elements m = (x, n) :: l *)
    assert (Hdup := Helt). destruct Hdup as [Hdup _]. apply is_elements_cons_inv in Helt.
    assert (n = m[x]). { apply (Hval (x, n)). now left. } subst n.
    apply Hrec'.
    - now left.
    - intro. inversion_clear Hdup. apply H1. rewrite <- elements_from_elements; trivial. now rewrite elements_In.
    - apply IHl; intuition.
  Qed.
  
  Section Fold_results.
    Variables (A : Type) (eqA : relation A).
    Context (HeqA : Equivalence eqA).
    Variable f : elt -> nat -> A -> A.
    Hypotheses (Hf : Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f) (Hf2 : transpose2 eqA f).
    
    Global Instance fold_f_compat : Proper (equiv ==> eqA ==> eqA) (fold f) := fold_compat _ _ _ Hf Hf2.
    
    Theorem fold_add : forall x n m (i : A), n > 0 -> ~In x m -> eqA (fold f (add x n m) i) (f x n (fold f m i)).
    Proof using FMultisetsSpec HeqA Hf Hf2.
    intros x n m i Hn Hin. do 2 rewrite fold_spec.
    assert (Hperm : PermutationA eq_pair (elements (add x n m)) ((elements m) ++ (x, n) :: nil)).
    { rewrite elements_add_out; trivial. apply (PermutationA_cons_append _). }
    erewrite (fold_left_symmetry_PermutationA _ _); try apply Hperm || reflexivity.
    - do 2 rewrite <- fold_left_rev_right. now rewrite rev_unit.
    - intros ? ? ? [? ?] [? ?] [Heq ?]. now apply Hf.
    - intros [? ?] [? ?] ?. simpl. apply Hf2.
    Qed.
    
    Theorem fold_add_additive : additive2 eqA f ->
      forall x n m (i : A), n > 0 -> eqA (fold f (add x n m) i) (f x n (fold f m i)).
    Proof using FMultisetsSpec HeqA Hf Hf2.
    intros Hfadd x n m i Hn. 
    destruct m[x] eqn:Hm.
    + (* If [~In x m], then we can simply use [fold_add] *)
      apply fold_add. assumption. unfold In. lia.
    + (* Otherwise, the real proof starts *)
      assert (Hperm : PermutationA eq_pair (elements (add x n m))
                     (elements (remove x (m[x]) m) ++ (x, n + m[x]) :: nil)).
      { etransitivity; try apply (PermutationA_cons_append _).
        rewrite <- elements_add_out; try lia.
          rewrite add_remove1; try lia. do 2 f_equiv. lia.
          unfold In. rewrite remove_same. lia. }
      rewrite fold_spec. erewrite (fold_left_symmetry_PermutationA _ _); try apply Hperm || reflexivity.
      - rewrite <- fold_left_rev_right. rewrite rev_unit. simpl. rewrite <- Hfadd. f_equiv.
        rewrite fold_left_rev_right, <- fold_spec. etransitivity.
          symmetry. apply fold_add. lia. unfold In. rewrite remove_same. lia.
          rewrite add_remove1; trivial. now rewrite Minus.minus_diag, add_0.
      - intros ? ? ? [? ?] [? ?] [Heq ?]. now apply Hf.
      - intros [? ?] [? ?] ?. simpl. apply Hf2.
    Qed.
    
    (* Wrong in general when m1 and m2 are not disjoint. *)
    Lemma fold_union : forall m1 m2 (i : A), (forall x, In x m1 -> In x m2 -> False) ->
      eqA (fold f (union m1 m2) i) (fold f m1 (fold f m2 i)).
    Proof using FMultisetsSpec HeqA Hf Hf2.
    intros m1 m2 i Hm. apply fold_rect with (m := m1); trivial.
    + intros * Heq. now rewrite Heq.
    + now rewrite union_empty_l.
    + intros * ? ? Hrec. rewrite union_add_comm_l, <- Hrec. apply fold_add; trivial; [].
      unfold In in *. rewrite union_spec. intro Habs. apply (Hm x); lia.
    Qed.
    
    Lemma fold_union_additive : additive2 eqA f ->
      forall m1 m2 (i : A), eqA (fold f (union m1 m2) i) (fold f m1 (fold f m2 i)).
    Proof using FMultisetsSpec HeqA Hf Hf2.
    intros Hfadd m1 m2 i. apply fold_rect with (m := m1).
    + intros * Heq. now rewrite Heq.
    + now rewrite union_empty_l.
    + intros * ? ? Hrec. rewrite union_add_comm_l, <- Hrec. now apply fold_add_additive.
    Qed.
    
  End Fold_results.

  Lemma fold_extensionality_compat (A : Type) (eqA : relation A) `(Equivalence A eqA) :
    forall f : elt -> nat -> A -> A, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
    forall g, (forall x v acc, eqA (f x v acc) (g x v acc)) ->
    forall m i, eqA (fold f m i) (fold g m i).
  Proof using FMultisetsSpec.
  intros f Hf Hf2 g Hext m i.
  assert (Hg : Proper (equiv ==> Logic.eq ==> eqA ==> eqA) g).
  { repeat intro. repeat rewrite <- Hext. apply Hf; assumption. }
  assert (Hg2 : transpose2 eqA g). { repeat intro. repeat rewrite <- Hext. apply Hf2. }
  apply fold_rect.
  + intros m1 m2 acc Hm Heq. rewrite Heq. apply (fold_compat _ _ g Hg Hg2); assumption || reflexivity.
  + rewrite fold_empty. reflexivity.
  + intros x m' acc Hin Hout Heq. rewrite Hext, Heq. rewrite fold_add; reflexivity || assumption.
  Qed.
  
  (** This is a relaxation on the equality between f and g which must hold only for [m]. *)
  Lemma fold_extensionality_compat_strong (A : Type) (eqA : relation A) `(Equivalence A eqA) :
    forall f : elt -> nat -> A -> A, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
    forall g : elt -> nat -> A -> A, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) g -> transpose2 eqA g ->
    forall m, (forall x acc, In x m -> eqA (f x m[x] acc) (g x m[x] acc)) ->
    forall i, eqA (fold f m i) (fold g m i).
  Proof using FMultisetsSpec.
  intros f Hf Hf2 g Hg Hg2 m Hext i.
  assert (Hext' : forall m', (forall y, m'[y] = m[y] \/ m'[y] = 0) ->
                  forall x acc, In x m -> ~In x m' -> eqA (f x m[x] acc) (g x m[x] acc)).
  { intros m' Hm' x acc Hin Hout. unfold In in *. now apply Hext. }
  clear Hext. revert Hext'.
  pose (P := fun m acc => (forall m', (forall y, m'[y] = m[y] \/ m'[y] = 0) ->
                           forall x acc, In x m -> ~In x m' -> eqA (f x m[x] acc) (g x m[x] acc)) ->
                          eqA acc (fold g m i)).
  change (P m (fold f m i)). apply fold_rect.
  + intros m1 m2 acc Hm Heq Hfg. rewrite Heq.
    - apply (fold_compat _ _ g Hg Hg2); assumption || reflexivity.
    - now setoid_rewrite Hm.
  + intro. rewrite fold_empty. reflexivity.
  + intros x m' acc Hin Hout Heq Hfg. rewrite fold_add; trivial; [].
    assert (Hx : m'[x] = 0) by now rewrite <- not_In.
    rewrite Heq.
    - specialize (Hfg m' ltac:(intro; msetdec) x).
      rewrite add_same, Hx in Hfg. simpl in Hfg. apply Hfg; trivial; [].
      rewrite add_In. left. split; try reflexivity. unfold In in *. lia.
    - intros m'' Hm'' x' acc' Hin' Hout'.
      assert (Hneq : x' =/= x). { intro Habs. apply Hout. now rewrite <- Habs. }
      rewrite <- (add_other x x' m[x] m' Hneq).
      assert (Hx' := Hm'' x).
      apply Hfg with m''; intros; msetdec.
  Qed.
  
  Lemma union_fold_add : forall m1 m2, fold (fun x n acc => add x n acc) m1 m2 == union m1 m2.
  Proof using FMultisetsSpec.
  intros m1 m2 x. apply fold_rect with (m := m1).
  + intros * Heq1 Heq2. now rewrite <- Heq1, Heq2.
  + now rewrite union_empty_l.
  + intros x' * ? ? Hrec. rewrite union_add_comm_l. destruct (equiv_dec x x') as [Heq | Hneq].
    - rewrite <- Heq. do 2 rewrite add_same. now rewrite Hrec.
    - now repeat rewrite add_other.
  Qed.
  
  Corollary fold_add_id : forall m, fold (fun x n acc => add x n acc) m empty == m.
  Proof using FMultisetsSpec. intro. now rewrite union_fold_add, union_empty_r. Qed.
  
  (** **  Generic induction principles on multisets  **)
  
  Definition rect : forall P, (forall m1 m2, m1 == m2 -> P m1 -> P m2) ->
    (forall m x n, ~In x m -> n > 0 -> P m -> P (add x n m)) ->
    P empty -> forall m, P m.
  Proof. intros P HP ? ? ?. apply (@fold_rect _ (fun _ _ _ => tt) (fun m _ => P m) tt); eauto. Defined.
  
  Definition ind : forall P, Proper (equiv ==> iff) P ->
    (forall m x n, ~In x m -> n > 0 -> P m -> P (add x n m)) ->
    P empty -> forall m, P m.
  Proof using FMultisetsSpec. intros. apply rect; trivial. intros ? ? Heq. now rewrite Heq. Qed.
  
  (** Direct definition by induction on [elements m], which does not use [fold]. **)
  Definition rect_bis : forall P, (forall m1 m2, m1 == m2 -> P m1 -> P m2) ->
    (forall m x n, ~In x m -> P m -> P (add x n m)) ->
    P empty -> forall m, P m.
  Proof using FMultisetsSpec.
  intros P Heq Hadd Hempty.
  (* The proof goes by induction on [elements m]
     so we first replace all occurences of [m] by [elements m] and prove the premises. *)
  pose (P' := fun l => P (fold_left (fun acc xn => add (fst xn) (snd xn) acc) l empty)).
  assert (Pequiv1 : forall m, P m -> P' (elements m)).
  { intro. unfold P'. apply Heq. rewrite <- fold_spec. symmetry. apply fold_add_id. }
  assert (Pequiv2 : forall m, P' (elements m) -> P m).
  { intro. unfold P'. apply Heq. rewrite <- fold_spec. apply fold_add_id. }
  assert (HP' : forall l1 l2, PermutationA eq_pair l1 l2 -> P' l1 -> P' l2).
  { intros l1 l2 Hl. unfold P'.
    assert (Hf : Proper (equiv ==> eq_pair ==> equiv) (fun acc xn => add (fst xn) (snd xn) acc)).
    { intros ? ? Heq1 ? ? Heq2 ?. now rewrite Heq2, Heq1. }
    apply Heq. apply (@fold_left_symmetry_PermutationA _ _ eq_pair equiv _ _ _ Hf); reflexivity || trivial.
    intros [x n] [y p] acc. simpl. apply add_comm. }
  assert (Hadd' : forall l x n, is_elements l -> n > 0 -> ~InA eq_elt (x, n) l -> P' l -> P' ((x, n) :: l)).
  { intros l x n Hl Hn Hin. apply is_elements_build in Hl. destruct Hl as [m Hm]. rewrite Hm in Hin.
    assert (Hx : ~In x m).
    { rewrite <- support_spec, support_elements. intro Habs. apply Hin. eapply InA_pair_elt. eassumption. }
    intro Hl. apply (HP' _ _ Hm), Pequiv2, Hadd with m x n, Pequiv1 in Hl; trivial. revert Hl.
    apply HP'. etransitivity. now apply elements_add_out. now apply PermutationA_cons. }
  (* The real proof starts. *)
  intro m. apply Pequiv2. generalize (elements_is_elements m).
  induction (elements m) as [| [x n] l]; intro Hl.
  + unfold P'. simpl. apply Hempty.
  + apply Hadd'.
    - eapply is_elements_cons_inv. eassumption.
    - destruct Hl as [_ Hpos]. now inversion_clear Hpos.
    - destruct Hl as [Hdup _]. now inversion_clear Hdup.
    - apply IHl. eapply is_elements_cons_inv. eassumption.
  Qed.
  
  Corollary not_empty_In : forall m, m =/= empty <-> exists x, In x m.
  Proof using FMultisetsSpec.
  intro m. split.
  + pattern m. apply ind; clear m.
    - intros m1 m2 Hm. setoid_rewrite Hm. reflexivity.
    - intros m x n Hm Hn Hrec _. exists x. apply add_In. left. split; lia || reflexivity.
    - intro Habs. now elim Habs.
  + intros [x Hin]. intro Habs. revert Hin. rewrite Habs. apply In_empty.
  Qed.
  
  Corollary empty_or_In_dec : forall m, {m == empty} + {exists x, In x m}.
  Proof using FMultisetsSpec.
  intro m. destruct (equal m empty) eqn:Heq.
  + rewrite equal_spec in Heq. now left.
  + right. rewrite <- not_empty_In. unfold complement. rewrite <- equal_spec, Heq. discriminate.
  Qed.
  
  (** **  Results about [support]  **)
  
  Lemma support_nil : forall m, support m = nil <-> m == empty.
  Proof using FMultisetsSpec.
  intro m. split; intro Heq.
  + intro x. rewrite empty_spec. destruct (m[x]) eqn:Hin. reflexivity.
    assert (Hm : In x m). { unfold In. rewrite Hin. lia. }
    rewrite <- support_spec in Hm. rewrite Heq in Hm. inversion Hm.
  + apply (@PermutationA_nil _ equiv _). rewrite Heq. now rewrite support_empty.
  Qed.
  
  Lemma support_1 : forall x m, PermutationA equiv (support m) (x :: nil)
                                <-> m == singleton x (m[x]) /\ (m[x]) > 0.
  Proof using FMultisetsSpec.
  intros x m. split; intro Hm.
  + assert (Hin : In x m). { rewrite <- support_spec, Hm. now left. }
    unfold In in Hin. split; try lia. intro y. rewrite singleton_spec.
    destruct (equiv_dec y x) as [Heq | Hneq]. now rewrite Heq.
    destruct m[y] eqn:Hy. reflexivity.
    assert (Hiny : In y m). { unfold In. rewrite Hy. lia. }
    rewrite <- support_spec, Hm in Hiny. inversion_clear Hiny. contradiction. inversion H.
  + destruct Hm as [Hm Hmult]. rewrite Hm. apply support_singleton. lia.
  Qed.
  
  Lemma support_add : forall x n m, n > 0 ->
    PermutationA equiv (support (add x n m)) (if In_dec x m then support m else x :: support m).
  Proof using FMultisetsSpec.
  intros x n m Hn. apply (NoDupA_equivlistA_PermutationA _).
  * apply support_NoDupA.
  * destruct (In_dec x m) as [Hin | Hin].
    + apply support_NoDupA.
    + constructor. now rewrite support_spec. apply support_NoDupA.
  * intro z. destruct (In_dec x m) as [Hin | Hin].
    + do 2 rewrite support_spec. unfold In in *. msetdec.
    + rewrite support_spec. unfold In in *. msetdec.
      - split; intro. now left. lia.
      - split; intro Hz.
          right. now rewrite support_spec.
          inversion Hz; subst. contradiction. now rewrite support_spec in H0.
  Qed.
  
  Lemma support_remove : forall x n m,
    PermutationA equiv (support (remove x n m))
      (if Compare_dec.le_dec (m[x]) n then removeA equiv_dec x (support m) else support m).
  Proof using FMultisetsSpec.
  intros x n m. apply (NoDupA_equivlistA_PermutationA _).
  + apply support_NoDupA. 
  + destruct (Compare_dec.le_dec (m[x]) n) as [Hin | Hin].
    - apply (removeA_NoDupA _). apply support_NoDupA.
    - apply support_NoDupA.
  + intro z. destruct (Compare_dec.le_dec (m[x]) n) as [Hle | Hlt].
    - rewrite (removeA_InA _). do 2 rewrite support_spec. unfold In in *. split; intro Hin.
        destruct (equiv_dec z x).
          exfalso. revert Hin. msetdec.
          split; msetdec.
        destruct Hin. msetdec. (* BUG?: saturate_Einequalities shou work! *) now elim H0.
    - do 2 rewrite support_spec. unfold In in *. msetdec.
  Qed.
  
  Lemma support_union : forall x m1 m2,
    InA equiv x (support (union m1 m2)) <-> InA equiv x (support m1) \/ InA equiv x (support m2).
  Proof using FMultisetsSpec. intros. repeat rewrite support_spec. apply union_In. Qed.
  
  (* The more global versions (PermutationA with union/inter/...)
     would require ListSet operations on a setoid equality. Absent from the std lib...
  Lemma support_union2 : forall m1 m2,
    PermutationA equiv (support (union m1 m2)) (ListSet.set_union (support m1) (support m2)).
  Proof.
  
  Qed. *)
  
  Lemma support_inter : forall x m1 m2,
    InA equiv x (support (inter m1 m2)) <-> InA equiv x (support m1) /\ InA equiv x (support m2).
  Proof using FMultisetsSpec. intros. repeat rewrite support_spec. apply inter_In. Qed.
  
  Lemma support_diff : forall x m1 m2, InA equiv x (support (diff m1 m2)) <-> m2[x] < m1[x].
  Proof using FMultisetsSpec. intros. rewrite support_spec, diff_In. intuition. Qed.
  
  Lemma support_lub : forall k m1 m2,
    InA equiv k (support (lub m1 m2)) <-> InA equiv k (support m1) \/ InA equiv k (support m2).
  Proof using FMultisetsSpec. intros. repeat rewrite support_spec. apply lub_In. Qed.
  
  Lemma support_map_elements : forall m, PermutationA equiv (support m) (map (@fst elt nat) (elements m)).
  Proof using FMultisetsSpec.
  intro m. apply (NoDupA_equivlistA_PermutationA _).
  + apply support_NoDupA.
  + assert (Hm := elements_NoDupA m).
    induction Hm as [| [x n] l].
    - constructor.
    - simpl. constructor; trivial.
      intro Habs. apply H. clear -Habs. induction l as [| [y p] l].
        now inversion Habs.
        inversion_clear Habs. now left. right. now apply IHl.
  + intro x. rewrite support_elements. rewrite (InA_map_iff _ _). split; intro Hin.
    - exists (x, m[x]). now split.
    - destruct Hin as [[y p] [Heq Hin]]. rewrite elements_spec in Hin |- *.
      simpl in *. intuition. rewrite <- Heq. lia.
    - clear. now intros [x n] [y p] [? ?].
  Qed.
  
  (** **  Results about [cardinal]  **)
  
  Lemma cardinal_lower_aux : forall (l : list (elt * nat)) acc, acc <= fold_left (fun acc xn => snd xn + acc) l acc.
  Proof using .
  induction l; intro acc; simpl.
  - lia.
  - transitivity (snd a + acc). lia. apply IHl.
  Qed.
  
  Lemma fold_left_cardinal : Proper (PermutationA eq_pair ==> Logic.eq ==> Logic.eq)
    (fold_left (fun (acc : nat) (xn : elt * nat) => snd xn + acc)).
  Proof using .
  apply (fold_left_symmetry_PermutationA _ _).
  - intros ? ? ? [? ?] [? ?] [? Heq]. hnf in *. simpl in *. now subst.
  - intros [? ?] [? ?] ?. lia.
  Qed.
  
  Corollary cardinal_lower : forall x m, m[x] <= cardinal m.
  Proof using FMultisetsSpec.
  intros x m. destruct (m[x]) eqn:Hm. lia.
  assert (Hin : InA eq_pair (x, S n) (elements m)). { rewrite elements_spec. split; simpl. assumption. lia. }
  rewrite cardinal_spec, fold_spec.
  apply (PermutationA_split _) in Hin. destruct Hin as [l Hperm]. assert (Heq := eq_refl 0).
  rewrite fold_left_cardinal; try eassumption. simpl. rewrite Nat.add_0_r. now apply cardinal_lower_aux.
  Qed.
  
  Corollary cardinal_In : forall x m, In x m -> 0 < cardinal m.
  Proof using FMultisetsSpec. intros. apply Nat.lt_le_trans with (m[x]). assumption. apply cardinal_lower. Qed.
  
  Lemma cardinal_0 : forall m, cardinal m = 0 <-> m == empty.
  Proof using FMultisetsSpec.
  intro m. split; intro Hm.
  + intro y. rewrite empty_spec, <- empty_spec with y. revert y. change (m == empty). rewrite <- elements_nil.
    destruct (elements m) as [| [x n] l] eqn:Helt. reflexivity.
    simpl in Hm. elim (Nat.lt_irrefl 0). apply Nat.lt_le_trans with n.
    - apply elements_pos with x m. rewrite Helt. now left.
    - assert (Hn : m[x] = n). { eapply proj1. rewrite <- (elements_spec (x, n)), Helt. now left. }
      rewrite <- Hn, <- Hm. apply cardinal_lower.
  + rewrite Hm. apply cardinal_empty.
  Qed.
  
  Instance fold_cardinal_compat : Proper (equiv ==> Logic.eq ==> Logic.eq) (fold (fun x n acc => n + acc)).
  Proof using FMultisetsSpec.
  intros m₁ m₂ Hm ? ? ?. apply (fold_compat _ _); trivial; [|].
  - now repeat intro; subst.
  - repeat intro. lia.
  Qed.
  
  Theorem cardinal_union : forall m₁ m₂, cardinal (union m₁ m₂) = cardinal m₁ + cardinal m₂.
  Proof using FMultisetsSpec.
  assert (Proper (equiv ==> eq ==> equiv ==> equiv) (fun (_ : elt) (n acc : nat) => n + acc)).
  { repeat intro. cbn in *. lia. }
  assert (transpose2 equiv (fun (_ : elt) (n0 acc : nat) => n0 + acc)).
  { repeat intro. cbn; lia. }
  intros m₁ m₂. do 2 rewrite cardinal_spec. rewrite (fold_union_additive _); trivial.
  + rewrite <- cardinal_spec. revert m₁. apply ind.
    - intros ? ? Heq. now rewrite Heq.
    - intros. destruct n.
      -- now rewrite add_0.
      -- repeat rewrite (fold_add _); trivial; lia.
    - now do 2 rewrite fold_empty.
  + repeat intro. cbn. lia.
  Qed.
  
  Corollary cardinal_add : forall x n m, cardinal (add x n m) = n + cardinal m.
  Proof using FMultisetsSpec. intros. now rewrite <- add_union_singleton_l, cardinal_union, cardinal_singleton. Qed.
  
  Theorem cardinal_remove : forall x n m, cardinal (remove x n m) = cardinal m - min n (m[x]).
  Proof using FMultisetsSpec.
  intros x n m. destruct (Compare_dec.le_dec n (m[x])) as [Hle | Hlt].
  + setoid_rewrite <- (add_0 x) at 3. erewrite <- (Minus.minus_diag n).
    rewrite <- (@add_remove1 x n n m), cardinal_add, min_l; trivial. lia.
  + assert (Hle : m[x] <= n) by lia.
    setoid_rewrite <- (add_0 x) at 3. erewrite <- Minus.minus_diag.
    rewrite <- (@add_remove2 x _ n m Hle (Nat.le_refl _)), cardinal_add, min_r; trivial. lia.
  Qed.
  
  Global Instance cardinal_sub_compat : Proper (Subset ==> le) cardinal.
  Proof using FMultisetsSpec.
  intro s. pattern s. apply ind; clear s.
  + intros ? ? Hm. now setoid_rewrite Hm.
  + intros m x n Hin Hn Hrec m' Hsub. rewrite (cardinal_add _).
    assert (n <= m'[x]). { transitivity (n + m[x]). lia. specialize (Hsub x). msetdec. }
    assert (n <= cardinal m'). { etransitivity; try eassumption. apply cardinal_lower. }
    apply add_subset_remove in Hsub. apply Hrec in Hsub. rewrite cardinal_remove in Hsub.
    etransitivity. apply Plus.plus_le_compat. reflexivity. apply Hsub. rewrite min_l; trivial. lia.
  + intros. rewrite cardinal_empty. lia.
  Qed.
  
  Lemma cardinal_inter_le_min : forall m1 m2, cardinal (inter m1 m2) <= min (cardinal m1) (cardinal m2).
  Proof using FMultisetsSpec.
  intro m1; pattern m1. apply ind; clear m1.
  * intros m1 m1' Heq. split; intros Hle m2; rewrite Heq || rewrite <- Heq; apply Hle.
  * intros m x n Hout Hn Hind m2. destruct (Compare_dec.le_lt_dec n (m2[x])) as [Hle | Hlt].
    + rewrite inter_add_l1; trivial. rewrite <- (add_remove_cancel Hle) at 2.
      do 3 rewrite cardinal_add. rewrite Min.plus_min_distr_l. apply Plus.plus_le_compat_l, Hind.
    + rewrite inter_add_l2; try lia.
      transitivity (Init.Nat.min (cardinal (add x (m2[x]) m)) (cardinal m2)).
      - rewrite <- (add_remove_cancel (reflexivity (m2[x]))) at 4.
        do 3 rewrite cardinal_add. rewrite Min.plus_min_distr_l. apply Plus.plus_le_compat_l.
        rewrite remove_cap; try lia. apply Hind.
      - do 2 rewrite cardinal_add. apply Nat.min_le_compat_r. lia.
  * intro. rewrite inter_empty_l, cardinal_empty. lia.
  Qed.
  
  Lemma cardinal_diff_upper : forall m1 m2, cardinal (diff m1 m2) <= cardinal m1.
  Proof using FMultisetsSpec. intros. apply cardinal_sub_compat, diff_subset. Qed.
  
  Lemma cardinal_diff_lower : forall m1 m2, cardinal m1 - cardinal m2 <= cardinal (diff m1 m2).
  Proof using FMultisetsSpec.
  intro m1. pattern m1. apply ind; clear m1.
  + intros m1 m1' Heq. now setoid_rewrite Heq.
  + intros m x n Hout Hn Hind m2. destruct (Compare_dec.le_lt_dec n (m2[x])) as [Hle | Hlt].
    - rewrite diff_add_l1; trivial. rewrite <- (add_remove_cancel Hle) at 1. do 2 rewrite cardinal_add.
      replace (n + cardinal m - (n + cardinal(remove x n m2))) with (cardinal m - cardinal(remove x n m2)) by lia.
      apply Hind.
    - rewrite diff_add_l2; try lia. rewrite <- (add_remove_cancel (reflexivity (m2[x]))) at 1.
      do 3 rewrite cardinal_add. rewrite <- (@remove_cap x n); try lia.
      transitivity ((n - m2[x]) + (cardinal m - cardinal(remove x n m2))); try lia.
      apply Plus.plus_le_compat_l, Hind.
  + intro. now rewrite diff_empty_l, cardinal_empty.
  Qed.
  
  Lemma cardinal_lub_upper : forall m1 m2, cardinal (lub m1 m2) <= cardinal m1 + cardinal m2.
  Proof using FMultisetsSpec. intros. rewrite <- cardinal_union. apply cardinal_sub_compat, lub_subset_union. Qed.
  
  Lemma cardinal_lub_lower : forall m1 m2, max (cardinal m1) (cardinal m2) <= cardinal (lub m1 m2).
  Proof using FMultisetsSpec.
  intro m1. pattern m1. apply ind; clear m1.
  + intros m1 m1' Heq. now setoid_rewrite Heq.
  + intros m x n Hout Hn Hind m2. rewrite lub_add_l. do 2 rewrite cardinal_add.
    transitivity (n + Init.Nat.max (cardinal m) (cardinal (remove x n m2))).
    - rewrite <- Max.plus_max_distr_l. apply Nat.max_le_compat_l. rewrite <- (cardinal_add x).
      apply cardinal_sub_compat. intro. msetdec.
    - apply Plus.plus_le_compat_l, Hind.
  + intro. now rewrite lub_empty_l, cardinal_empty.
  Qed.
  
  Lemma cardinal_fold_elements : forall m, cardinal m = List.fold_left (fun acc xn => snd xn + acc) (elements m) 0.
  Proof using FMultisetsSpec. intro. now rewrite cardinal_spec, fold_spec. Qed.
  
  Lemma cardinal_from_elements : forall l,
    cardinal (from_elements l) = List.fold_left (fun acc xn => snd xn + acc) l 0.
  Proof using FMultisetsSpec.
  intro l. rewrite <- Plus.plus_0_l at 1. generalize 0. induction l as [| [x n] l]; intro p; simpl.
  - now rewrite cardinal_empty.
  - rewrite cardinal_add, Nat.add_assoc. rewrite (Nat.add_comm  p n). apply IHl.
  Qed.
  
  Lemma cardinal_total_sub_eq : forall m1 m2, m1 [<=] m2 -> cardinal m1 = cardinal m2 -> m1 == m2.
  Proof using FMultisetsSpec.
  intro m. pattern m. apply ind; clear m.
  + intros m1 m1' Heq. now setoid_rewrite Heq.
  + intros m1 x n Hout Hn Hrec m2 Hsub Heq.
    assert (n <= m2[x]).
    { transitivity (n + m1[x]); try lia.
      specialize (Hsub x). rewrite add_same in Hsub. lia. }
    rewrite <- (@add_remove_cancel x n m2); trivial. f_equiv. apply Hrec.
    - now apply add_subset_remove.
    - rewrite cardinal_add in Heq. rewrite cardinal_remove, <- Heq, Nat.min_l; lia.
  + intros m _ Heq. symmetry. rewrite <- cardinal_0, <- Heq. apply cardinal_empty.
  Qed.
  
  (** **  Results about [size]  **)
  
  Lemma size_0 : forall m, size m = 0 <-> m == empty.
  Proof using FMultisetsSpec.
  intro m. split; intro Heq.
  - now rewrite size_spec, length_zero_iff_nil, support_nil in Heq.
  - rewrite Heq. apply size_empty.
  Qed.
  
  Lemma size_1 : forall m, size m = 1 <-> exists x, m == singleton x (m[x]) /\ m[x] > 0.
  Proof using FMultisetsSpec.
  intro m. split; intro Heq.
  - rewrite size_spec, length_1 in Heq. destruct Heq as [x Heq]. exists x. rewrite <- support_1. now rewrite Heq.
  - destruct Heq as [x [Heq Hmul]]. rewrite Heq. now apply size_singleton.
  Qed.
  
  Lemma size_In : forall m, size m > 0 <-> exists x, In x m.
  Proof using FMultisetsSpec.
  intro m. split; intro Hin.
  + rewrite size_spec in Hin. destruct (support m) as [| x l] eqn:Heq.
    - inversion Hin.
    - exists x. rewrite <- support_spec, Heq. now left.
  + destruct Hin as [x Hin]. destruct (size m) eqn:Hsize.
    - rewrite size_0 in Hsize. rewrite Hsize in Hin. elim (In_empty Hin).
    - auto with arith.
  Qed.
  
  Lemma size_add : forall x n m, n > 0 -> size (add x n m) = if In_dec x m then size m else S (size m).
  Proof using FMultisetsSpec.
  intros x n m Hn. do 2 rewrite size_spec. rewrite support_add; trivial. destruct (In_dec x m); reflexivity.
  Qed.
  
  Lemma size_remove : forall x n m,
    In x m -> size (remove x n m) = if Compare_dec.le_dec (m[x]) n then pred (size m) else size m.
  Proof using FMultisetsSpec.
  intros x n m Hin. do 2 rewrite size_spec. rewrite support_remove.
  destruct (Compare_dec.le_dec (m[x]) n) as [Hle | ?]; trivial.
  rewrite <- support_spec in Hin. apply PermutationA_split in Hin; refine _. destruct Hin as [l Hin].
  assert (Hnodup : NoDupA equiv (x :: l)). { rewrite <- Hin. apply support_NoDupA. }
  (* XXX: why does [rewrite Hin] fails here? *)
  rewrite removeA_Perm_compat; eauto; try reflexivity || apply setoid_equiv; []. rewrite Hin.
  simpl. destruct (equiv_dec x x) as [_ | Hneq]; try now elim Hneq.
  inversion_clear Hnodup. now rewrite removeA_out.
  Qed.
  
  Corollary size_remove_eq : forall x n m, n < m[x] -> size (remove x n m) = size m.
  Proof using FMultisetsSpec.
   intros x n m ?. rewrite size_remove; try (unfold In; lia). destruct (Compare_dec.le_dec (m[x]) n); lia.
  Qed.
  
  Lemma size_union_lower : forall m1 m2, max (size m1) (size m2) <= size (union m1 m2).
  Proof using FMultisetsSpec. intros. apply Max.max_case; apply size_sub_compat; apply union_subset_l || apply union_subset_r. Qed.
  
  (* TODO?: the most straigthforward way to express this would be by using set_union, hence requiring ListSetA. *)
  Lemma size_union_upper : forall m1 m2, size (union m1 m2) <= size m1 + size m2.
  Proof using FMultisetsSpec.
  intros m1 m2. pattern m1. apply ind; clear m1.
  + intros m1 m1' Heq. rewrite Heq. reflexivity.
  + intros m1 x n Hin Hn Hrec. rewrite union_add_comm_l. repeat rewrite size_add; trivial.
    destruct (In_dec x m1); try contradiction. destruct (In_dec x (union m1 m2)); lia.
  + rewrite size_empty, union_empty_l. reflexivity.
  Qed.
  
  Lemma size_inter_upper : forall m1 m2, size (inter m1 m2) <= min (size m1) (size m2).
  Proof using FMultisetsSpec. intros. apply Min.min_case; apply size_sub_compat; apply inter_subset_l || apply inter_subset_r. Qed.
  
  Lemma size_diff_upper : forall m1 m2, size (diff m1 m2) <= size m1.
  Proof using FMultisetsSpec. intros. apply size_sub_compat, diff_subset. Qed.
  
  Lemma size_lub_lower : forall m1 m2, max (size m1) (size m2) <= size (lub m1 m2).
  Proof using FMultisetsSpec. intros. apply Max.max_case; apply size_sub_compat; apply lub_subset_l || apply lub_subset_r. Qed.
  
  Lemma size_lub_upper : forall m1 m2, size (lub m1 m2) <= size m1 + size m2.
  Proof using FMultisetsSpec.
  intros. transitivity (size (union m1 m2)).
  - apply size_sub_compat. apply lub_subset_union.
  - apply size_union_upper.
  Qed.
  
  Lemma size_elements : forall m, size m = length (elements m).
  Proof using FMultisetsSpec. intro. now rewrite size_spec, support_map_elements, map_length. Qed.
  
  Lemma size_from_elements : forall l, size (from_elements l) <= length l.
  Proof using FMultisetsSpec.
  induction l as [| [x n] l].
  + rewrite from_elements_nil, size_empty. reflexivity.
  + simpl. destruct n.
    - rewrite add_0. now apply le_S.
    - rewrite size_add; try lia. destruct (In_dec x (from_elements l)); auto with arith.
  Qed.
  
  Lemma size_from_elements_valid : forall l, is_elements l -> size (from_elements l) = length l.
  Proof using FMultisetsSpec. intros. now rewrite size_elements, elements_from_elements. Qed.
  
  Lemma size_cardinal : forall m, size m <= cardinal m.
  Proof using FMultisetsSpec.
  apply ind.
  + intros ? ? Heq. now rewrite Heq.
  + intros m x n Hin Hn Hrec. rewrite size_add, cardinal_add; trivial. destruct (In_dec x m); lia.
  + rewrite size_empty, cardinal_empty. reflexivity.
  Qed.
  
  (** **  Results about [nfilter]  **)
  
  Section nFilter_results.
    Variable f : elt -> nat -> bool.
    Hypothesis Hf : compatb f.
    
    Lemma nfilter_In : forall x m, In x (nfilter f m) <-> In x m /\ f x (m[x]) = true.
    Proof using FMultisetsSpec Hf.
    intros x m. unfold In. rewrite nfilter_spec; trivial.
    destruct (f x (m[x])); intuition; discriminate.
    Qed.
    
    Corollary In_nfilter : forall x m, In x (nfilter f m) -> In x m.
    Proof using FMultisetsSpec Hf. intros x m Hin. rewrite nfilter_In in Hin; intuition. Qed.
    
    Lemma nfilter_subset : forall m, nfilter f m [<=] m.
    Proof using FMultisetsSpec Hf. intros m x. rewrite nfilter_spec; trivial. destruct (f x (m[x])); lia. Qed.
    
    Lemma nfilter_add_true : forall x n m, ~In x m -> n > 0 ->
      (nfilter f (add x n m) == add x n (nfilter f m) <-> f x n = true).
    Proof using FMultisetsSpec Hf.
    intros x n m Hin Hn. assert (Hm : m[x] = 0) by (unfold In in Hin; lia). split; intro Heq.
    + specialize (Heq x). rewrite nfilter_spec, add_same, add_same, nfilter_spec in Heq; trivial.
      rewrite Hm in Heq. simpl in Heq. destruct (f x n). reflexivity. lia.
    + intro y. msetdec. simpl. rewrite Heq. now destruct (f x 0).
    Qed.
    
    Lemma nfilter_add_false : forall x n m, ~In x m -> n > 0 ->
      (nfilter f (add x n m) == nfilter f m <-> f x n = false).
    Proof using FMultisetsSpec Hf.
    intros x n m Hin Hn. assert (Hm : m[x] = 0) by (unfold In in Hin; lia). split; intro Heq.
    + specialize (Heq x). rewrite nfilter_spec, add_same, nfilter_spec in Heq; trivial.
      rewrite Hm in Heq. simpl in Heq. destruct (f x n). destruct (f x 0); lia. reflexivity.
    + intro y. msetdec. simpl. rewrite Heq. now destruct (f x 0).
    Qed.
    
    Theorem nfilter_add : forall x n m, ~In x m -> n > 0 ->
      nfilter f (add x n m) == if f x n then add x n (nfilter f m) else nfilter f m.
    Proof using FMultisetsSpec Hf.
    intros x n m Hin Hn. destruct (f x n) eqn:Hfxn.
    - now rewrite nfilter_add_true.
    - now rewrite nfilter_add_false.
    Qed.
    
    Global Instance nfilter_sub_compat : Proper (equiv ==> le ==> Bool.le) f ->
      Proper (Subset ==> Subset) (nfilter f).
    Proof using FMultisetsSpec Hf.
    intros Hf2 m1 m2. revert m1. pattern m2. apply ind; clear m2.
    + intros ? ? Hm. now setoid_rewrite Hm.
    + intros m x n Hm Hn Hrec m' Hsub. rewrite nfilter_add; trivial. intro y. specialize (Hsub y).
      assert (m[x] = 0) by msetdec. assert (Hbool := Hf2 y y (reflexivity _) _ _ Hsub).
      destruct (f x n) eqn:Hfxn.
    - msetdec; try rewrite H in *.
          destruct (f x (m'[x])), (f x 0); lia.
          destruct (f y m'[y]); lia || now rewrite Hbool.
      - msetdec; try rewrite H1 in *.
          simpl in Hbool. rewrite Hfxn in Hbool. now destruct (f x (m'[x])), (f x 0).
          destruct (f y m[y]), (f y m'[y]); lia || inversion Hbool.
    + intros m Hm. rewrite subset_empty_r in Hm. now rewrite Hm.
    Qed.
    
    Lemma nfilter_extensionality_compat : forall g, (forall x n, f x n = g x n) ->
      forall m, nfilter f m == nfilter g m.
    Proof using FMultisetsSpec Hf.
    intros g Hext m x.
    assert (Hg : Proper (equiv ==> Logic.eq ==> Logic.eq) g). { repeat intro. do 2 rewrite <- Hext. now apply Hf. }
    repeat rewrite nfilter_spec; trivial. rewrite Hext. reflexivity.
    Qed.
    
    Lemma nfilter_extensionality_compat_strong : forall g, Proper (equiv ==> Logic.eq ==> Logic.eq) g ->
      forall m, (forall x, In x m -> f x m[x] = g x m[x]) -> nfilter f m == nfilter g m.
    Proof using FMultisetsSpec Hf.
    intros g Hg m Hext x. repeat rewrite nfilter_spec; trivial.
    destruct (Nat.eq_dec m[x] 0) as [Heq | Hneq].
    - rewrite Heq. destruct (f x 0), (g x 0); reflexivity.
    - rewrite Hext. reflexivity. unfold In. lia.
    Qed.
    
    Lemma elements_nfilter : forall m,
      PermutationA eq_pair (elements (nfilter f m)) (List.filter (fun xn => f (fst xn) (snd xn)) (elements m)).
    Proof using FMultisetsSpec Hf.
    intro m. apply NoDupA_equivlistA_PermutationA; refine _.
    * eapply NoDupA_strengthen, elements_NoDupA. apply subrelation_pair_elt.
    * apply NoDupA_filter_compat.
      + intros [x n] [y p] [? ?]; compute in *. auto.
      + eapply NoDupA_strengthen, elements_NoDupA. apply subrelation_pair_elt.
    * intros [x n]. split; intro Hin.
      + rewrite elements_spec in Hin. destruct Hin as [Hin Hpos]. simpl in *. subst.
      rewrite filter_InA; simpl in *.
        - rewrite nfilter_spec in Hpos |- *; trivial. destruct (f x (m[x])) eqn:Hfx; trivial; try lia; [].
          split; trivial. rewrite elements_spec; intuition.
        - intros [? ?] [? ?] [? ?]. compute in *. auto.
      + rewrite filter_InA in Hin.
        - rewrite elements_spec in Hin |- *. destruct Hin as [[Hin Hpos] Hfx]. simpl in *. split; trivial.
          rewrite nfilter_spec; trivial. subst. now rewrite Hfx.
        - intros [? ?] [? ?] [? ?]. compute in *. auto.
    Qed.
    
    Lemma nfilter_from_elements : forall l, is_elements l ->
      nfilter f (from_elements l) == from_elements (List.filter (fun xn => f (fst xn) (snd xn)) l).
    Proof using FMultisetsSpec Hf.
    intros l Hl. rewrite <- elements_eq. rewrite elements_nfilter; trivial.
    setoid_rewrite elements_from_elements at 2.
    * apply filter_PermutationA_compat; refine _.
      + intros [] [] []. compute in *. auto.
      + now apply elements_from_elements.
    * destruct Hl as [Hnodup Hpos]. induction l as [| [x n] l]; try (split; assumption).
      inversion_clear Hnodup. inversion_clear Hpos.
      destruct (IHl ltac:(assumption)  ltac:(assumption)) as [Hnodup Hpos].
    (* BUG?: why does _ not do the job here? (rather than ltac:(assumption)) *)
      split; simpl.
      + destruct (f x n); trivial. constructor; trivial. intro Hin. apply H.
        apply InA_elt_pair in Hin. destruct Hin as [n' Hin]. simpl in *. rewrite filter_InA in Hin.
        - destruct Hin. eapply InA_pair_elt; eassumption.
        - intros [] [] []. compute in *. auto.
      + destruct (f x n); trivial. now constructor.
    Qed.
    
    Lemma support_nfilter : forall m, inclA equiv (support (nfilter f m)) (support m).
    Proof using FMultisetsSpec Hf. intro. apply support_sub_compat, nfilter_subset. Qed.
    
    Lemma cardinal_nfilter : forall m, cardinal (nfilter f m) <= cardinal m.
    Proof using FMultisetsSpec Hf. intro. apply cardinal_sub_compat, nfilter_subset. Qed.
    
    Lemma size_nfilter : forall m, size (nfilter f m) <= size m.
    Proof using FMultisetsSpec Hf. intro. apply size_sub_compat, nfilter_subset. Qed.
  End nFilter_results.
  
  Lemma nfilter_merge : forall f g, compatb f -> compatb g ->
    forall m, nfilter f (nfilter g m) == nfilter (fun x n => f x n && g x n) m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg m x. repeat rewrite nfilter_spec; trivial.
  + destruct (g x (m[x])), (f x (m[x])); simpl; trivial; now destruct (f x 0).
  + clear x m. intros x y Hxy n m Hnm. subst. now rewrite Hxy.
  Qed.
  
  Lemma nfilter_comm : forall f g, compatb f -> compatb g ->
    forall m, nfilter f (nfilter g m) == nfilter g (nfilter f m).
  Proof using FMultisetsSpec.
  intros. repeat rewrite nfilter_merge; trivial. apply nfilter_extensionality_compat.
  + intros x y Hxy ? n ?. subst. now rewrite Hxy.
  + intros. apply andb_comm.
  Qed.
  
  Lemma fold_nfilter_fold_left A eqA `{Equivalence A eqA} :
    forall f g, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f -> compatb g ->
    forall m i, eqA (fold f (nfilter g m) i)
                    (fold_left (fun acc xn => f (fst xn) (snd xn) acc)
                               (List.filter (fun xn => g (fst xn) (snd xn)) (elements m))
                               i).
  Proof using FMultisetsSpec.
  intros. rewrite fold_spec, fold_left_symmetry_PermutationA; refine _; try reflexivity.
  + intros ? ? ? [] [] []. compute in *. auto.
  + auto.
  + now apply elements_nfilter.
  Qed.
  
  Lemma fold_nfilter A eqA `{Equivalence A eqA} :
    forall f g, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f -> compatb g ->
    forall m i, eqA (fold f (nfilter g m) i) (fold (fun x n acc => if g x n then f x n acc else acc) m i).
  Proof using FMultisetsSpec.
  intros f g Hf Hf2 Hg m.
  assert (Hf' : Proper (equiv ==> Logic.eq ==> eqA ==> eqA) (fun x n acc => if g x n then f x n acc else acc)).
  { clear -Hf Hg. intros x1 x2 Hx n1 n2 Hn m1 m2 Hm. subst.
    destruct (g x1 n2) eqn:Hgx; rewrite Hx in Hgx; rewrite Hgx; trivial. apply Hf; trivial. }
  assert (Hf2' : transpose2 eqA (fun x n acc => if g x n then f x n acc else acc)).
  { intros x1 x2 y1 y2 z. now destruct (g x1 y1), (g x2 y2); trivial. }
  pattern m. apply ind.
  * intros m1 m2 Hm. split; intros Heq i.
    + rewrite <- (fold_compat _ _ _ _ Hf2 _ _ (nfilter_compat Hg Hm) _ _ (reflexivity i)), Heq.
      apply fold_compat; trivial. reflexivity.
    + rewrite (fold_compat _ _ _ _ Hf2 _ _ (nfilter_compat Hg Hm) _ _ (reflexivity i)), Heq.
      apply fold_compat; trivial.
      - now symmetry.
      - reflexivity.
  * clear m. intros m x n Hin Hn Hrec i.
    assert (Hadd := nfilter_add Hg Hin Hn). rewrite fold_compat; try eassumption || reflexivity.
    rewrite fold_add; trivial. destruct (g x n); trivial. rewrite fold_add; trivial.
    + now apply Hf.
    + intro Hx. apply Hin. now apply In_nfilter in Hx.
  * intro i. rewrite fold_empty. rewrite fold_compat; trivial.
    + rewrite fold_empty. reflexivity.
    + now apply nfilter_empty.
    + reflexivity.
  Qed.
  
  Lemma cardinal_nfilter_is_multiplicity : forall x m,
    cardinal (nfilter (fun y _ => if equiv_dec y x then true else false) m) = m[x].
  Proof using FMultisetsSpec.
  intros x m.
  assert (Hf : Proper (equiv ==> Logic.eq ==> Logic.eq) (fun y (_ : nat) => if equiv_dec y x then true else false)).
  { intros y1 y2 Hy ? ? ?. subst. destruct (equiv_dec y1 x), (equiv_dec y2 x); auto; now rewrite Hy in *. }
  pattern m. apply ind; clear m.
  + intros m1 m2 Hm. now setoid_rewrite Hm.
  + intros m y n Hm Hn Hrec. rewrite nfilter_add; trivial. destruct (equiv_dec y x) as [Heq | Heq].
    - rewrite cardinal_add, Hrec, Heq, add_same. apply Nat.add_comm.
    - rewrite add_other; msetdec.
  + now rewrite nfilter_empty, cardinal_empty, empty_spec.
  Qed.
  
  Lemma nfilter_mono_compat : forall f g, compatb f -> compatb g -> (forall x n, Bool.le (f x n) (g x n)) ->
    forall m, nfilter f m [<=] nfilter g m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg Hfg. apply ind.
  + intros m1 m2 Hm. now rewrite Hm.
  + intros m x n Hm Hn Hrec. repeat rewrite nfilter_add; trivial. destruct (f x n) eqn:Hfx.
    - specialize (Hfg x n). rewrite Hfx in Hfg. simpl in Hfg. rewrite Hfg. now f_equiv.
    - destruct (g x n); trivial. etransitivity; try eassumption. apply add_subset.
  + repeat rewrite nfilter_empty; trivial. reflexivity.
  Qed.
  
  Lemma nfilter_disjoint_or_union : forall f g,
    Proper (equiv ==> Logic.eq ==> Logic.eq) f -> Proper (equiv ==> Logic.eq ==> Logic.eq) g ->
    forall m, (forall x, In x m -> f x m[x] && g x m[x] = false) ->
    nfilter (fun x n => f x n || g x n) m == union (nfilter f m) (nfilter g m).
  Proof using FMultisetsSpec.
  intros f g Hf Hg m.
  assert (Hforg : Proper (equiv ==> Logic.eq ==> Logic.eq) (fun x n => f x n || g x n))
(*   intros f g Hf Hg m Hdisjoint. *)
    by (intros ? ? Heq ? ? ?; subst; now rewrite Heq).
  assert (Hfandg : Proper (equiv ==> Logic.eq ==> Logic.eq) (fun x n => f x n && g x n))
    by (intros ? ? Heq ? ? ?; subst; now rewrite Heq).
  cut (m [<=] m); try reflexivity; []. pattern m at -2. apply ind.
  + intros m1 m2 Heq. split; intros Hrec Hand Hdisjoint;
    setoid_rewrite Heq in Hrec || setoid_rewrite <- Heq in Hrec; now apply Hrec.
  + intros m' x n Hin Hn Hrec Hincl Hdisjoint.
    assert (Hincl' : m' [<=] m).
    { intro y. destruct (equiv_dec y x) as [Hxy | Hxy].
      - rewrite Hxy. transitivity (m'[x] + n); try lia; [].
        rewrite <- add_same. apply Hincl.
      - now rewrite <- (add_other x y n). }
    assert (Hdisjoint' : forall x, In x m' -> f x m'[x] && g x m'[x] = false).
    { intros y Hy. assert (y =/= x) by (intro; msetdec).
      specialize (Hdisjoint y). rewrite add_other in Hdisjoint; trivial; [].
      apply Hdisjoint. rewrite add_In. tauto. }
    repeat rewrite nfilter_add; trivial.
    destruct (f x n) eqn:Hfxn, (g x n) eqn:Hgxn; cbn -[equiv].
    - assert (Hx : (add x n m')[x] = n) by msetdec.
      specialize (Hdisjoint x ltac:(msetdec)).
      rewrite Hx, Hfxn, Hgxn in Hdisjoint. discriminate.
    - rewrite union_add_comm_l. f_equiv. now apply Hrec.
    - rewrite union_add_comm_r. f_equiv. now apply Hrec.
    - now apply Hrec.
  + intros _. repeat rewrite nfilter_empty; trivial. now rewrite union_empty_l.
  Qed.
  
  (** **  Results about [filter]  **)
  
  Section Filter_results.
    Variable f : elt -> bool.
    Hypothesis Hf : Proper (equiv ==> Logic.eq) f.
    
    Theorem filter_nfilter : forall m, filter f m == nfilter (fun x _ => f x) m.
    Proof using FMultisetsSpec Hf. repeat intro. rewrite nfilter_spec, filter_spec; trivial. repeat intro. now apply Hf. Qed.
    
    Lemma filter_In : forall x m, In x (filter f m) <-> In x m /\ f x = true.
    Proof using FMultisetsSpec Hf. intros x m. unfold In. rewrite filter_spec; trivial. destruct (f x); intuition; discriminate. Qed.
    
    Corollary In_filter : forall x m, In x (filter f m) -> In x m.
    Proof using FMultisetsSpec Hf. intros x m Hin. rewrite filter_In in Hin; intuition. Qed.
    
    Lemma filter_subset : forall m, filter f m [<=] m.
    Proof using FMultisetsSpec Hf. intros m x. rewrite filter_spec; trivial. destruct (f x); lia. Qed.
    
    Lemma filter_add_true : forall x n m, n > 0 ->
      (filter f (add x n m) == add x n (filter f m) <-> f x = true).
    Proof using FMultisetsSpec Hf.
    repeat intro. split.
    * intro Heq. specialize (Heq x). rewrite filter_spec in Heq; trivial.
      destruct (f x) eqn:Hfx; trivial.
      rewrite add_same in Heq. lia.
    * intros Hfx y. rewrite filter_spec; trivial.
      destruct (equiv_dec y x) as [Hxy | Hxy].
      + rewrite Hxy, Hfx, Hxy. do 2 rewrite add_same. now rewrite filter_spec, Hfx.
      + destruct (f y) eqn:Hfy.
        - do 2 (rewrite add_other; trivial). now rewrite filter_spec, Hfy.
        - rewrite add_other; trivial. now rewrite filter_spec, Hfy.
    Qed.
    
    Lemma filter_add_false : forall x n m, n > 0 ->
      (filter f (add x n m) == filter f m <-> f x = false).
    Proof using FMultisetsSpec Hf.
    repeat intro. destruct (f x) eqn:Hfx.
    + rewrite <- (@filter_add_true x n m) in Hfx; trivial. rewrite Hfx.
      split; intro Habs; try discriminate. specialize (Habs x). rewrite add_same in Habs. lia.
    + split; intro Heq; reflexivity || clear Heq. intro y.
      do 2 (rewrite filter_spec; trivial).
      destruct (equiv_dec y x) as [Hxy | Hxy].
      - now rewrite Hxy, Hfx.
      - destruct (f y) eqn:Hfy; trivial. now apply add_other.
    Qed.
    
    Theorem filter_add : forall x n m, n > 0 ->
      filter f (add x n m) == if f x then add x n (filter f m) else filter f m.
    Proof using FMultisetsSpec Hf.
    intros x n m Hn. destruct (f x) eqn:Hfx.
    - now rewrite filter_add_true.
    - now rewrite filter_add_false.
    Qed.
    
    Global Instance filter_sub_compat : Proper (Subset ==> Subset) (filter f).
    Proof using FMultisetsSpec Hf.
    repeat intro. do 2 rewrite filter_nfilter. apply nfilter_sub_compat.
    - repeat intro. now apply Hf.
    - repeat intro. rewrite Hf; try eassumption. apply Bleb_refl.
    - assumption.
    Qed.
    
    Lemma filter_extensionality_compat : forall g, (forall x, f x = g x) -> forall m, filter f m == filter g m.
    Proof using FMultisetsSpec Hf.
    intros g Hext m x.
    assert (Hg : Proper (equiv ==> Logic.eq) g). { repeat intro. do 2 rewrite <- Hext. now apply Hf. }
    repeat rewrite filter_spec; trivial. rewrite Hext. reflexivity.
    Qed.
    
    Lemma filter_extensionality_compat_strong : forall g, Proper (equiv ==> Logic.eq) g ->
      forall m, (forall x, In x m -> f x = g x) -> filter f m == filter g m.
    Proof using FMultisetsSpec Hf.
    intros g Hg m Hext x. repeat rewrite filter_spec; trivial.
    destruct (In_dec x m) as [Hin | Hin].
    - now rewrite (Hext _ Hin).
    - rewrite not_In in Hin. rewrite Hin. destruct (f x), (g x); reflexivity.
    Qed.
    
    Lemma elements_filter : forall m,
      PermutationA eq_pair (elements (filter f m)) (List.filter (fun xn => f (fst xn)) (elements m)).
    Proof using FMultisetsSpec Hf.
    intro m. rewrite filter_nfilter, elements_nfilter.
    - reflexivity.
    - repeat intro. now apply Hf.
    Qed.
    
    Lemma filter_from_elements : forall l, is_elements l ->
      filter f (from_elements l) == from_elements (List.filter (fun xn => f (fst xn)) l).
    Proof using FMultisetsSpec Hf.
    intros l Hl. rewrite filter_nfilter, nfilter_from_elements.
    - reflexivity.
    - repeat intro. now apply Hf.
    - assumption.
    Qed.
    
    Lemma support_filter_incl : forall m, inclA equiv (support (filter f m)) (support m).
    Proof using FMultisetsSpec Hf. intro. apply support_sub_compat, filter_subset. Qed.
    
    Lemma support_filter : forall m, PermutationA equiv (support (filter f m)) (List.filter f (support m)).
    Proof using FMultisetsSpec Hf.
    intro m. apply (NoDupA_equivlistA_PermutationA _).
    - apply support_NoDupA.
    - now apply NoDupA_filter_compat, support_NoDupA.
    - intro x. rewrite support_elements, elements_filter.
      setoid_rewrite filter_InA; autoclass.
      simpl. rewrite elements_spec, support_spec, filter_spec; trivial. unfold In.
      split; intros [Hin Hfx]; rewrite Hfx in *; intuition.
    Qed.

    Lemma cardinal_filter : forall m, cardinal (filter f m) <= cardinal m.
    Proof using FMultisetsSpec Hf. intro. apply cardinal_sub_compat, filter_subset. Qed.
    
    Lemma size_filter : forall m, size (filter f m) <= size m.
    Proof using FMultisetsSpec Hf. intro. apply size_sub_compat, filter_subset. Qed.
  End Filter_results.
  
  Lemma filter_merge : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> Logic.eq) g ->
    forall m, filter f (filter g m) == filter (fun x => f x && g x) m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg m x. repeat rewrite filter_spec; trivial.
  + now destruct (f x).
  + clear x m. intros x y Hxy. now rewrite Hxy.
  Qed.
  
  Lemma filter_filtern_merge : forall f g, Proper (equiv ==> Logic.eq) f -> compatb g ->
    forall m, filter f (nfilter g m) == nfilter (fun x n => f x && g x n) m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg m x. rewrite filter_spec, nfilter_spec, nfilter_spec; trivial.
  + now destruct (f x).
  + clear x m. intros x y Hxy n m Hnm. subst. now rewrite Hxy.
  Qed.
  
  Lemma nfilter_filter_merge : forall f g, compatb f -> Proper (equiv ==> Logic.eq) g ->
    forall m, nfilter f (filter g m) == nfilter (fun x n => f x n && g x) m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg m x. rewrite nfilter_spec, nfilter_spec, filter_spec; trivial.
  + destruct (g x), (f x (m[x])); simpl; trivial; now destruct (f x 0).
  + clear x m. intros x y Hxy n m Hnm. subst. now rewrite Hxy.
  Qed.
  
  Lemma filter_comm : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> Logic.eq) g ->
    forall m, filter f (filter g m) == filter g (filter f m).
  Proof using FMultisetsSpec.
  intros. repeat rewrite filter_merge; trivial. apply filter_extensionality_compat.
  + intros x y Hxy. subst. now rewrite Hxy.
  + intros. apply andb_comm.
  Qed.
  
  Lemma nfilter_filter_comm : forall f g, compatb f -> Proper (equiv ==> Logic.eq) g ->
    forall m, nfilter f (filter g m) == filter g (nfilter f m).
  Proof using FMultisetsSpec.
  intros ** x. repeat rewrite filter_spec, nfilter_spec; trivial.
  destruct (g x), (f x (m[x])); simpl; trivial; now destruct (f x 0).
  Qed.
  
  Lemma fold_filter_fold_left A eqA `{Equivalence A eqA} : forall f g,
    Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f -> Proper (equiv ==> Logic.eq) g ->
    forall m i, eqA (fold f (filter g m) i)
                    (fold_left (fun acc xn => f (fst xn) (snd xn) acc)
                               (List.filter (fun xn => g (fst xn)) (elements m))
                               i).
  Proof using FMultisetsSpec.
  intros. rewrite fold_spec, fold_left_symmetry_PermutationA; refine _; try reflexivity.
  + intros ? ? ? [] [] []. compute in *. auto.
  + auto.
  + now apply elements_filter.
  Qed.
  
  Lemma fold_filter A eqA `{Equivalence A eqA} : forall f g,
    Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f -> Proper (equiv ==> Logic.eq) g ->
    forall m i, eqA (fold f (filter g m) i) (fold (fun x n acc => if g x then f x n acc else acc) m i).
  Proof using FMultisetsSpec.
  intros f g Hf Hf2 Hg m i. rewrite (fold_compat _ _ f Hf Hf2 _ _ (filter_nfilter Hg m) i i (reflexivity i)).
  apply fold_nfilter; trivial. repeat intro. now apply Hg.
  Qed.
  
  Lemma cardinal_filter_is_multiplicity : forall x m,
    cardinal (filter (fun y => if equiv_dec y x then true else false) m) = m[x].
  Proof using FMultisetsSpec.
  intros x m. rewrite filter_nfilter.
  - apply cardinal_nfilter_is_multiplicity.
  - intros x' y' Heq. destruct (equiv_dec x' x), (equiv_dec y' x); trivial; rewrite Heq in *; contradiction.
  Qed.
  
  Lemma filter_mono_compat : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> Logic.eq) g ->
    (forall x, Bool.le (f x) (g x)) -> forall m, filter f m [<=] filter g m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg Hfg m. repeat rewrite filter_nfilter; trivial. apply nfilter_mono_compat.
  - repeat intro. now apply Hf.
  - repeat intro. now apply Hg.
  - repeat intro. apply Hfg.
  Qed.
  
  Lemma filter_disjoint_or_union : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> Logic.eq) g ->
    forall m, (forall x, In x m -> f x && g x = false) ->
    filter (fun x => f x || g x) m == union (filter f m) (filter g m).
  Proof using FMultisetsSpec.
  intros f g Hf Hg m.
  assert (Hforg : Proper (equiv ==> Logic.eq) (fun x => f x || g x)) by (intros ? ? Heq; now rewrite Heq).
  assert (Hfandg : Proper (equiv ==> Logic.eq) (fun x => f x && g x)) by (intros ? ? Heq; now rewrite Heq).
  pattern m. apply ind; clear m.
  + intros m1 m2 Heq.
    split; intros Hrec Hand; now rewrite Heq in *; apply Hrec; setoid_rewrite Heq || setoid_rewrite <- Heq.
  + intros m' x n Hin Hn Hrec Hdisjoint.
    assert (Hdisjoint' : forall y, In y m' -> f y && g y = false).
    { intros y Hin'. apply Hdisjoint. rewrite add_In. tauto. }
    repeat rewrite filter_add; trivial.
    destruct (f x) eqn:Hfx, (g x) eqn:Hgx; simpl orb; cbn iota.
    - specialize (Hdisjoint x). rewrite Hfx, Hgx in Hdisjoint.
      cut (true = false); try discriminate; [].
      apply Hdisjoint.
      msetdec.
    - rewrite union_add_comm_l. f_equiv. now apply Hrec.
    - rewrite union_add_comm_r. f_equiv. now apply Hrec.
    - now apply Hrec.
  + intros _. repeat rewrite filter_empty; trivial. now rewrite union_empty_l.
  Qed.
  
  (** **  Results about [npartition]  **)
  
  Section nPartition_results.
    Variable f : elt -> nat -> bool.
    Hypothesis Hf : compatb f.
    
    Lemma negf_compatb : Proper (equiv ==> Logic.eq ==> Logic.eq) (fun x n => negb (f x n)).
    Proof using Hf. repeat intro. now rewrite Hf. Qed.
    
    Lemma npartition_In_fst : forall x m, In x (fst (npartition f m)) <-> In x m /\ f x (m[x]) = true.
    Proof using FMultisetsSpec Hf. intros. rewrite npartition_spec_fst; trivial. now apply nfilter_In. Qed.
    
    Lemma npartition_In_snd : forall x m, In x (snd (npartition f m)) <-> In x m /\ f x (m[x]) = false.
    Proof using FMultisetsSpec Hf.
    intros. rewrite npartition_spec_snd, <- negb_true_iff; trivial. apply nfilter_In.
    repeat intro. now rewrite Hf.
    Qed.
    
    Corollary In_npartition_fst : forall x m, In x (fst (npartition f m)) -> In x m.
    Proof using FMultisetsSpec Hf. intros x m Hin. rewrite npartition_In_fst in Hin; intuition. Qed.
    
    Corollary In_npartition_snd : forall x m, In x (snd (npartition f m)) -> In x m.
    Proof using FMultisetsSpec Hf. intros x m Hin. rewrite npartition_In_snd in Hin; intuition. Qed.
    
    Lemma npartition_subset_fst : forall m, fst (npartition f m) [<=] m.
    Proof using FMultisetsSpec Hf. intro. rewrite npartition_spec_fst; trivial. now apply nfilter_subset. Qed.
    
    Lemma npartition_subset_snd : forall m, snd (npartition f m) [<=] m.
    Proof using FMultisetsSpec Hf. intro. rewrite npartition_spec_snd; trivial. apply nfilter_subset, negf_compatb. Qed.
    
    Lemma npartition_add_true_fst : forall x n m, ~In x m -> n > 0 ->
      (fst (npartition f (add x n m)) == add x n (fst (npartition f m)) <-> f x n = true).
    Proof using FMultisetsSpec Hf. intros. repeat rewrite npartition_spec_fst; trivial. now apply nfilter_add_true. Qed.
    
    Lemma npartition_add_true_snd : forall x n m, ~In x m -> n > 0 ->
      (snd (npartition f (add x n m)) == snd (npartition f m) <-> f x n = true).
    Proof using FMultisetsSpec Hf.
    intros. repeat rewrite npartition_spec_snd; trivial. rewrite nfilter_add_false; trivial.
    apply negb_false_iff. repeat intro. f_equal. now apply Hf.
    Qed.
    
    Lemma npartition_add_false_fst : forall x n m, ~In x m -> n > 0 ->
      (fst (npartition f (add x n m)) == fst (npartition f m) <-> f x n = false).
    Proof using FMultisetsSpec Hf. intros. repeat rewrite npartition_spec_fst; trivial. now apply nfilter_add_false. Qed.
    
    Lemma npartition_add_false_snd : forall x n m, ~In x m -> n > 0 ->
      (snd (npartition f (add x n m)) == add x n (snd (npartition f m)) <-> f x n = false).
    Proof using FMultisetsSpec Hf.
    intros. repeat rewrite npartition_spec_snd; trivial. rewrite nfilter_add_true; trivial.
    apply negb_true_iff. repeat intro. f_equal. now apply Hf.
    Qed.
  
    Theorem npartition_add_fst : forall x n m, ~In x m -> n > 0 ->
      fst (npartition f (add x n m)) == if f x n then add x n (fst (npartition f m)) else fst (npartition f m).
    Proof using FMultisetsSpec Hf.
    intros x n m Hin Hn. destruct (f x n) eqn:Hfn.
    - now rewrite npartition_add_true_fst.
    - now rewrite npartition_add_false_fst.
    Qed.
    
    Theorem npartition_add_snd : forall x n m, ~In x m -> n > 0 ->
      snd (npartition f (add x n m)) == if f x n then snd (npartition f m) else add x n (snd (npartition f m)).
    Proof using FMultisetsSpec Hf.
    intros x n m Hin Hn. destruct (f x n) eqn:Hfn.
    - now rewrite npartition_add_true_snd.
    - now rewrite npartition_add_false_snd.
    Qed.
    
    Lemma npartition_swap_fst : forall m, fst (npartition (fun x n => negb (f x n)) m) == snd (npartition f m).
    Proof using FMultisetsSpec Hf.
    intros m x. rewrite npartition_spec_fst, npartition_spec_snd; trivial.
    repeat intro. rewrite Hf; try eassumption. reflexivity.
    Qed.
    
    Lemma npartition_swap_snd : forall m, snd (npartition (fun x n => negb (f x n)) m) == fst (npartition f m).
    Proof using FMultisetsSpec Hf.
    intros m x. rewrite npartition_spec_fst, npartition_spec_snd; trivial.
    - symmetry. rewrite nfilter_extensionality_compat; trivial. setoid_rewrite negb_involutive. reflexivity.
    - repeat intro. rewrite Hf; try eassumption. reflexivity.
    Qed.
    
    Lemma npartition_sub_compat_fst :
      Proper (equiv ==> le ==> Bool.le) f -> Proper (Subset ==> Subset@@1) (npartition f).
    Proof using FMultisetsSpec Hf. repeat intro. repeat rewrite npartition_spec_fst; trivial. now apply nfilter_sub_compat. Qed.
    
    Lemma npartition_sub_compat_snd :
      Proper (equiv ==> le --> Bool.le) f -> Proper (Subset ==> Subset@@2) (npartition f).
    Proof using FMultisetsSpec Hf.
    intros Hf2 ? ? ? ?. repeat rewrite npartition_spec_snd; trivial. apply nfilter_sub_compat.
    - repeat intro. f_equal. now apply Hf.
    - clear -Hf2 Hf. intros x y Hxy n p Hnp. destruct (f x n) eqn:Hfxn, (f y p) eqn:Hfyp; simpl; auto.
      assert (Himpl := Hf2 _ _ (symmetry Hxy) _ _ Hnp). rewrite Hfyp, Hfxn in Himpl. discriminate.
    - assumption.
    Qed.
    
    Lemma npartition_extensionality_compat_fst : forall g, (forall x n, f x n = g x n) ->
      forall m, fst (npartition f m) == fst (npartition g m).
    Proof using FMultisetsSpec Hf.
    intros ? Hext ? ?. setoid_rewrite npartition_spec_fst at 1; trivial.
    rewrite nfilter_extensionality_compat; trivial. symmetry. apply npartition_spec_fst.
    repeat intro. repeat rewrite <- Hext. apply Hf; assumption.
    Qed.
    
    Lemma npartition_extensionality_compat_snd : forall g, (forall x n, f x n = g x n) ->
      forall m, snd (npartition f m) == snd (npartition g m).
    Proof using FMultisetsSpec Hf.
    intros g Hext m ?. repeat rewrite npartition_spec_snd; trivial.
    + rewrite nfilter_extensionality_compat; trivial.
      - repeat intro. subst. f_equal. now apply Hf.
      - repeat intro. simpl. f_equal. apply Hext.
    + repeat intro. repeat rewrite <- Hext. apply Hf; assumption.
    Qed.
    
    Lemma elements_npartition_fst : forall m,
      PermutationA eq_pair (elements (fst (npartition f m)))
                           (List.filter (fun xn => f (fst xn) (snd xn)) (elements m)).
    Proof using FMultisetsSpec Hf. intro. rewrite npartition_spec_fst; trivial. now apply elements_nfilter. Qed.
    
    Lemma elements_npartition_snd : forall m,
      PermutationA eq_pair (elements (snd (npartition f m)))
                           (List.filter (fun xn => negb (f (fst xn) (snd xn))) (elements m)).
    Proof using FMultisetsSpec Hf. intro. rewrite npartition_spec_snd; trivial. apply elements_nfilter, negf_compatb. Qed.
    
    Lemma npartition_from_elements_fst : forall l, is_elements l ->
      fst (npartition f (from_elements l)) == from_elements (List.filter (fun xn => f (fst xn) (snd xn)) l).
    Proof using FMultisetsSpec Hf. intros. rewrite npartition_spec_fst; trivial. now apply nfilter_from_elements. Qed.
    
    Lemma npartition_from_elements_snd : forall l, is_elements l ->
      snd (npartition f (from_elements l)) == from_elements (List.filter (fun xn => negb (f (fst xn) (snd xn))) l).
    Proof using FMultisetsSpec Hf. intros. rewrite npartition_spec_snd; auto. now apply nfilter_from_elements; try apply negf_compatb. Qed.
    
    Lemma support_npartition_fst : forall m, inclA equiv (support (fst (npartition f m))) (support m).
    Proof using FMultisetsSpec Hf. intro. apply support_sub_compat, npartition_subset_fst. Qed.
    
    Lemma support_npartition_snd : forall m, inclA equiv (support (snd (npartition f m))) (support m).
    Proof using FMultisetsSpec Hf. intro. apply support_sub_compat, npartition_subset_snd. Qed.
    
    Lemma cardinal_npartition_fst : forall m, cardinal (fst (npartition f m)) <= cardinal m.
    Proof using FMultisetsSpec Hf. intro. apply cardinal_sub_compat, npartition_subset_fst. Qed.
    
    Lemma cardinal_npartition_snd : forall m, cardinal (snd (npartition f m)) <= cardinal m.
    Proof using FMultisetsSpec Hf. intro. apply cardinal_sub_compat, npartition_subset_snd. Qed.
    
    Lemma npartition_nfilter_fst : forall m, size (fst (npartition f m)) <= size m.
    Proof using FMultisetsSpec Hf. intro. apply size_sub_compat, npartition_subset_fst. Qed.
    
    Lemma npartition_nfilter_snd : forall m, size (snd (npartition f m)) <= size m.
    Proof using FMultisetsSpec Hf. intro. apply size_sub_compat, npartition_subset_snd. Qed.
    
    Lemma npartition_injective : injective equiv (equiv * equiv)%signature (npartition f).
    Proof using FMultisetsSpec Hf.
    intros m1 m2 [Heq1 Heq2] x. specialize (Heq1 x). specialize (Heq2 x).
    do 2 rewrite npartition_spec_fst, nfilter_spec in Heq1; trivial.
    do 2 rewrite npartition_spec_snd, nfilter_spec in Heq2; trivial; try now apply negf_compatb.
    destruct (f x (m1[x])), (f x (m2[x])); simpl in *; lia.
    Qed.
  End nPartition_results.
  
  Section nPartition2_results.
    Variable f g : elt -> nat -> bool.
    Hypothesis (Hf : compatb f) (Hg : compatb g).
    
    Lemma npartition_extensionality_compat_strong_fst : forall m,
      (forall x, In x m -> f x m[x] = g x m[x]) ->
      fst (npartition f m) == fst (npartition g m).
    Proof using FMultisetsSpec Hf Hg.
    intros ? Hext ?. setoid_rewrite npartition_spec_fst at 1; trivial.
    rewrite (nfilter_extensionality_compat_strong Hf Hg); trivial; [].
    symmetry. now apply npartition_spec_fst.
    Qed.
    
    Lemma npartition_extensionality_compat_strong_snd : forall m,
      (forall x, In x m -> f x m[x] = g x m[x]) ->
      snd (npartition f m) == snd (npartition g m).
    Proof using FMultisetsSpec Hf Hg.
    intros ? Hext ?. repeat rewrite npartition_spec_snd; trivial; [].
    rewrite nfilter_extensionality_compat_strong; trivial.
    - repeat intro. f_equal. now apply Hf.
    - repeat intro. f_equal. now apply Hg.
    - repeat intro. simpl. f_equal. now apply Hext.
    Qed.
    
    Lemma npartition_nfilter_merge_fst :
      forall m, fst (npartition f (nfilter g m)) == nfilter (fun x n => f x n && g x n) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite npartition_spec_fst; trivial. repeat rewrite nfilter_spec; trivial.
    + destruct (g x (m[x])), (f x (m[x])); simpl; trivial; now destruct (f x 0).
    + clear x m. intros x y Hxy n m Hnm. subst. now rewrite Hxy.
    Qed.
    
    Lemma npartition_nfilter_merge_snd :
      forall m, snd (npartition f (nfilter g m)) == nfilter (fun x n => negb (f x n) && g x n) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite npartition_spec_snd; trivial. repeat rewrite nfilter_spec; trivial.
      + destruct (g x (m[x])), (f x (m[x])); simpl; trivial; now destruct (f x 0).
    + clear x m. intros x y Hxy n m Hnm. subst. now rewrite Hxy.
    + now apply negf_compatb.
    Qed.
    
    Lemma nfilter_npartition_merge_fst :
      forall m, nfilter f (fst (npartition g m)) == nfilter (fun x n => f x n && g x n) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite npartition_spec_fst; trivial. repeat rewrite nfilter_spec; trivial.
    + destruct (g x (m[x])), (f x (m[x])); simpl; trivial; now destruct (f x 0).
    + clear x m. intros x y Hxy n m Hnm. subst. now rewrite Hxy.
    Qed.
    
    Lemma nfilter_npartition_merge_snd :
      forall m, nfilter f (snd (npartition g m)) == nfilter  (fun x n => f x n && negb (g x n)) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite npartition_spec_snd; trivial. repeat rewrite nfilter_spec; trivial.
    + destruct (f x (m[x])) eqn:Hfx, (g x (m[x]));
      simpl; trivial; now rewrite Hfx || destruct (f x 0).
    + clear x m. intros x y Hxy n m Hnm. subst. now rewrite Hxy.
    + now apply negf_compatb.
    Qed.
    
    Lemma npartition_merge_fst_fst :
      forall m, fst (npartition f (fst (npartition g m))) == nfilter (fun x n => f x n && g x n) m.
    Proof using FMultisetsSpec Hf Hg. intro. repeat rewrite npartition_spec_fst; trivial. now apply nfilter_merge. Qed.
    
    Lemma npartition_merge_fst_snd :
      forall m, snd (npartition f (fst (npartition g m))) == nfilter (fun x n => negb (f x n) && g x n) m.
    Proof using FMultisetsSpec Hf Hg.
    intro. repeat rewrite npartition_spec_fst, npartition_spec_snd; trivial.
    apply negf_compatb in Hf. now rewrite nfilter_merge.
    Qed.
    
    Lemma npartition_merge_snd_fst :
      forall m, fst (npartition f (snd (npartition g m))) == nfilter (fun x n => f x n && negb (g x n)) m.
    Proof using FMultisetsSpec Hf Hg.
    intro. repeat rewrite npartition_spec_fst, npartition_spec_snd; trivial.
    apply negf_compatb in Hg. now rewrite nfilter_merge.
    Qed.
  End nPartition2_results.
    
  Lemma npartition_merge_snd_snd : forall f g, compatb f -> compatb g ->
    forall m, snd (npartition f (snd (npartition g m))) == nfilter (fun x n => negb (f x n) && negb (g x n)) m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg m. repeat rewrite npartition_spec_snd; trivial. rewrite nfilter_npartition_merge_snd; trivial.
  - reflexivity.
  - now apply negf_compatb.
  Qed.
  
  Lemma npartition_comm_fst : forall f g, compatb f -> compatb g ->
    forall m, fst (npartition f (fst (npartition g m))) == fst (npartition g (fst (npartition f m))).
  Proof using FMultisetsSpec.
  intros. repeat rewrite npartition_merge_fst_fst; trivial. apply nfilter_extensionality_compat.
  - intros x y Hxy ? n ?. subst. now rewrite Hxy.
  - intros. apply andb_comm.
  Qed.
  
  Lemma npartition_comm_snd : forall f g, compatb f -> compatb g ->
    forall m, snd (npartition f (snd (npartition g m))) == snd (npartition g (snd (npartition f m))).
  Proof using FMultisetsSpec.
  intros. repeat rewrite npartition_merge_snd_snd; trivial. apply nfilter_extensionality_compat.
  - intros x y Hxy ? n ?. subst. now rewrite Hxy.
  - intros. apply andb_comm.
  Qed.
  
  (** **  Results about [partition]  **)
  
  Section Partition_results.
    Variable f : elt -> bool.
    Hypothesis Hf : Proper (equiv ==> Logic.eq) f.
    
    Lemma negf_proper : Proper (equiv ==> Logic.eq) (fun x => negb (f x)).
    Proof using Hf. repeat intro. now rewrite Hf. Qed.
    
    Lemma partition_In_fst : forall x m, In x (fst (partition f m)) <-> In x m /\ f x = true.
    Proof using FMultisetsSpec Hf. intros. rewrite partition_spec_fst; trivial. now apply filter_In. Qed.
    
    Lemma partition_In_snd : forall x m, In x (snd (partition f m)) <-> In x m /\ f x = false.
    Proof using FMultisetsSpec Hf.
    intros. rewrite partition_spec_snd, <- negb_true_iff; trivial. apply filter_In. repeat intro. now rewrite Hf.
    Qed.
    
    Corollary In_partition_fst : forall x m, In x (fst (partition f m)) -> In x m.
    Proof using FMultisetsSpec Hf. intros x m Hin. rewrite partition_In_fst in Hin; intuition. Qed.
    
    Corollary In_partition_snd : forall x m, In x (snd (partition f m)) -> In x m.
    Proof using FMultisetsSpec Hf. intros x m Hin. rewrite partition_In_snd in Hin; intuition. Qed.
    
    Lemma partition_subset_fst : forall m, fst (partition f m) [<=] m.
    Proof using FMultisetsSpec Hf. intro. rewrite partition_spec_fst; trivial. now apply filter_subset. Qed.
    
    Lemma partition_subset_snd : forall m, snd (partition f m) [<=] m.
    Proof using FMultisetsSpec Hf. intro. rewrite partition_spec_snd; trivial. apply filter_subset, negf_proper. Qed.
    
    Lemma partition_add_true_fst : forall x n m, ~In x m -> n > 0 ->
      (fst (partition f (add x n m)) == add x n (fst (partition f m)) <-> f x = true).
    Proof using FMultisetsSpec Hf. intros. repeat rewrite partition_spec_fst; trivial. now apply filter_add_true. Qed.
    
    Lemma partition_add_true_snd : forall x n m, ~In x m -> n > 0 ->
      (snd (partition f (add x n m)) == snd (partition f m) <-> f x = true).
    Proof using FMultisetsSpec Hf.
    intros. repeat rewrite partition_spec_snd; trivial. rewrite filter_add_false; trivial.
    apply negb_false_iff. repeat intro. f_equal. now apply Hf.
    Qed.
    
    Lemma partition_add_false_fst : forall x n m, ~In x m -> n > 0 ->
      (fst (partition f (add x n m)) == fst (partition f m) <-> f x = false).
    Proof using FMultisetsSpec Hf. intros. repeat rewrite partition_spec_fst; trivial. now apply filter_add_false. Qed.
    
    Lemma partition_add_false_snd : forall x n m, ~In x m -> n > 0 ->
      (snd (partition f (add x n m)) == add x n (snd (partition f m)) <-> f x = false).
    Proof using FMultisetsSpec Hf.
    intros. repeat rewrite partition_spec_snd; trivial. rewrite filter_add_true; trivial.
    apply negb_true_iff. repeat intro. f_equal. now apply Hf.
    Qed.
  
    Theorem partition_add_fst : forall x n m, ~In x m -> n > 0 ->
      fst (partition f (add x n m)) == if f x then add x n (fst (partition f m)) else fst (partition f m).
    Proof using FMultisetsSpec Hf.
    intros x n m Hin Hn. destruct (f x) eqn:Hfn.
    - now rewrite partition_add_true_fst.
    - now rewrite partition_add_false_fst.
    Qed.
    
    Theorem partition_add_snd : forall x n m, ~In x m -> n > 0 ->
      snd (partition f (add x n m)) == if f x then snd (partition f m) else add x n (snd (partition f m)).
    Proof using FMultisetsSpec Hf.
    intros x n m Hin Hn. destruct (f x) eqn:Hfn.
    - now rewrite partition_add_true_snd.
    - now rewrite partition_add_false_snd.
    Qed.
    
    Lemma partition_swap_fst : forall m, fst (partition (fun x => negb (f x)) m) == snd (partition f m).
    Proof using FMultisetsSpec Hf.
    intros m x. rewrite partition_spec_fst, partition_spec_snd; trivial.
    repeat intro. rewrite Hf; try eassumption. reflexivity.
    Qed.
    
    Lemma partition_swap_snd : forall m, snd (partition (fun x => negb (f x)) m) == fst (partition f m).
    Proof using FMultisetsSpec Hf.
    intros m x. rewrite partition_spec_fst, partition_spec_snd; trivial.
    - symmetry. rewrite filter_extensionality_compat; trivial. setoid_rewrite negb_involutive. reflexivity.
    - repeat intro. rewrite Hf; try eassumption. reflexivity.
    Qed.
    
    Lemma partition_sub_compat_fst :
      Proper (equiv ==> Bool.le) f -> Proper (Subset ==> Subset@@1) (partition f).
    Proof using FMultisetsSpec Hf. repeat intro. repeat rewrite partition_spec_fst; trivial. now apply filter_sub_compat. Qed.
    
    Lemma partition_sub_compat_snd :
      Proper (equiv --> Bool.le) f -> Proper (Subset ==> Subset@@2) (partition f).
    Proof using FMultisetsSpec Hf.
    repeat intro. repeat rewrite partition_spec_snd; trivial. apply filter_sub_compat.
    - repeat intro. f_equal. now apply Hf.
    - assumption.
    Qed.
    
    Lemma partition_extensionality_compat_fst : forall g, (forall x, f x = g x) ->
      forall m, fst (partition f m) == fst (partition g m).
    Proof using FMultisetsSpec Hf.
    intros ? Hext ? ?. setoid_rewrite partition_spec_fst at 1; trivial.
    rewrite filter_extensionality_compat; trivial. symmetry. apply partition_spec_fst.
    repeat intro. do 2 rewrite <- Hext. apply Hf; assumption.
    Qed.
    
    Lemma partition_extensionality_compat_snd : forall g, (forall x, f x = g x) ->
      forall m, snd (partition f m) == snd (partition g m).
    Proof using FMultisetsSpec Hf.
    intros g Hext m. intro. repeat rewrite partition_spec_snd; trivial.
    + apply filter_extensionality_compat; trivial.
      - repeat intro. f_equal. apply Hf; assumption.
      - repeat intro. f_equal. apply Hext.
    + repeat intro. do 2 rewrite <- Hext. apply Hf; assumption.
    Qed.
    
    Lemma elements_partition_fst : forall m,
      PermutationA eq_pair (elements (fst (partition f m)))
                           (List.filter (fun xn => f (fst xn)) (elements m)).
    Proof using FMultisetsSpec Hf. intro. rewrite partition_spec_fst; trivial. now apply elements_filter. Qed.
    
    Lemma elements_partition_snd : forall m,
      PermutationA eq_pair (elements (snd (partition f m)))
                           (List.filter (fun xn => negb (f (fst xn))) (elements m)).
    Proof using FMultisetsSpec Hf. intro. rewrite partition_spec_snd; trivial. apply elements_filter, negf_proper. Qed.
    
    Lemma partition_from_elements_fst : forall l, is_elements l ->
      fst (partition f (from_elements l)) == from_elements (List.filter (fun xn => f (fst xn)) l).
    Proof using FMultisetsSpec Hf. intros. rewrite partition_spec_fst; trivial. now apply filter_from_elements. Qed.
    
    Lemma partition_from_elements_snd : forall l, is_elements l ->
      snd (partition f (from_elements l)) == from_elements (List.filter (fun xn => negb (f (fst xn))) l).
    Proof using FMultisetsSpec Hf. intros. rewrite partition_spec_snd; auto. now apply filter_from_elements; try apply negf_proper. Qed.
    
    Lemma support_partition_fst : forall m, inclA equiv (support (fst (partition f m))) (support m).
    Proof using FMultisetsSpec Hf. intro. apply support_sub_compat, partition_subset_fst. Qed.
    
    Lemma support_partition_snd : forall m, inclA equiv (support (snd (partition f m))) (support m).
    Proof using FMultisetsSpec Hf. intro. apply support_sub_compat, partition_subset_snd. Qed.
    
    Lemma cardinal_partition_fst : forall m, cardinal (fst (partition f m)) <= cardinal m.
    Proof using FMultisetsSpec Hf. intro. apply cardinal_sub_compat, partition_subset_fst. Qed.
    
    Lemma cardinal_partition_snd : forall m, cardinal (snd (partition f m)) <= cardinal m.
    Proof using FMultisetsSpec Hf. intro. apply cardinal_sub_compat, partition_subset_snd. Qed.
    
    Lemma partition_nfilter_fst : forall m, size (fst (partition f m)) <= size m.
    Proof using FMultisetsSpec Hf. intro. apply size_sub_compat, partition_subset_fst. Qed.
    
    Lemma partition_nfilter_snd : forall m, size (snd (partition f m)) <= size m.
    Proof using FMultisetsSpec Hf. intro. apply size_sub_compat, partition_subset_snd. Qed.
    
    Lemma partition_injective : injective equiv (equiv * equiv)%signature (partition f).
    Proof using FMultisetsSpec Hf.
    intros m1 m2 [Heq1 Heq2] x. specialize (Heq1 x). specialize (Heq2 x).
    do 2 rewrite partition_spec_fst, filter_spec in Heq1; trivial.
    do 2 rewrite partition_spec_snd, filter_spec in Heq2; trivial; try now apply negf_proper.
    destruct (f x); simpl in *; lia.
    Qed.
  End Partition_results.
  
  Section Partition2_results.
    Variable f g : elt -> bool.
    Hypothesis (Hf : Proper (equiv ==> Logic.eq) f) (Hg : Proper (equiv ==> Logic.eq) g).
    
    Lemma partition_extensionality_compat_strong_fst : forall m,
      (forall x, In x m -> f x = g x) ->
      fst (partition f m) == fst (partition g m).
    Proof using FMultisetsSpec Hf Hg.
    intros ? Hext. repeat rewrite partition_spec_fst; trivial; [].
    now apply filter_extensionality_compat_strong.
    Qed.
    
    Lemma partition_extensionality_compat_strong_snd : forall m,
      (forall x, In x m -> f x = g x) ->
      snd (partition f m) == snd (partition g m).
    Proof using FMultisetsSpec Hf Hg.
    intros ? Hext. repeat rewrite partition_spec_snd; trivial; [].
    apply filter_extensionality_compat_strong.
    - repeat intro. f_equal. now apply Hf.
    - repeat intro. f_equal. now apply Hg.
    - repeat intro. f_equal. now apply Hext.
    Qed.
    
    Lemma partition_filter_merge_fst :
      forall m, fst (partition f (filter g m)) == filter (fun x => f x && g x) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite partition_spec_fst; trivial. repeat rewrite filter_spec; trivial.
    - now destruct (g x), (f x).
    - clear x m. intros x y Hxy. now rewrite Hxy.
    Qed.
    
    Lemma partition_filter_merge_snd :
      forall m, snd (partition f (filter g m)) == filter (fun x => negb (f x) && g x) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite partition_spec_snd; trivial. repeat rewrite filter_spec; trivial.
    - now destruct (g x), (f x).
    - clear x m. intros x y Hxy. now rewrite Hxy.
    - now apply negf_proper.
    Qed.
    
    Lemma filter_partition_merge_fst :
      forall m, filter f (fst (partition g m)) == filter (fun x => f x && g x) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite partition_spec_fst; trivial. repeat rewrite filter_spec; trivial.
    - now destruct (g x), (f x).
    - clear x m. intros x y Hxy. now rewrite Hxy.
    Qed.
    
    Lemma filter_partition_merge_snd :
      forall m, filter f (snd (partition g m)) == filter  (fun x => f x && negb (g x)) m.
    Proof using FMultisetsSpec Hf Hg.
    intros m x. rewrite partition_spec_snd; trivial. repeat rewrite filter_spec; trivial.
    - now destruct (f x), (g x).
    - clear x m. intros x y Hxy. now rewrite Hxy.
    - now apply negf_proper.
    Qed.
    
    Lemma partition_merge_fst_fst :
      forall m, fst (partition f (fst (partition g m))) == filter (fun x => f x && g x) m.
    Proof using FMultisetsSpec Hf Hg. intro. repeat rewrite partition_spec_fst; trivial. now apply filter_merge. Qed.
    
    Lemma partition_merge_fst_snd :
      forall m, snd (partition f (fst (partition g m))) == filter (fun x => negb (f x) && g x) m.
    Proof using FMultisetsSpec Hf Hg.
    intro. repeat rewrite partition_spec_fst, partition_spec_snd; trivial.
    apply negf_proper in Hf. now rewrite filter_merge.
    Qed.
    
    Lemma partition_merge_snd_fst :
      forall m, fst (partition f (snd (partition g m))) == filter (fun x => f x && negb (g x)) m.
    Proof using FMultisetsSpec Hf Hg.
    intro. repeat rewrite partition_spec_fst, partition_spec_snd; trivial.
    apply negf_proper in Hg. now rewrite filter_merge.
    Qed.
  End Partition2_results.
  
  Lemma partition_merge_snd_snd : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> Logic.eq) g ->
    forall m, snd (partition f (snd (partition g m))) == filter (fun x => negb (f x) && negb (g x)) m.
  Proof using FMultisetsSpec.
  intros f g Hf Hg m. rewrite partition_spec_snd, filter_partition_merge_snd; trivial.
  - reflexivity.
  - now apply negf_proper.
  Qed.
  
  Lemma partition_comm_fst : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> Logic.eq) g ->
    forall m, fst (partition f (fst (partition g m))) == fst (partition g (fst (partition f m))).
  Proof using FMultisetsSpec.
  intros. repeat rewrite partition_merge_fst_fst; trivial. apply filter_extensionality_compat.
  - intros x y Hxy. now rewrite Hxy.
  - intros. apply andb_comm.
  Qed.
  
  Lemma partition_comm_snd : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> Logic.eq) g ->
    forall m, snd (partition f (snd (partition g m))) == snd (partition g (snd (partition f m))).
  Proof using FMultisetsSpec.
  intros. repeat rewrite partition_merge_snd_snd; trivial. apply filter_extensionality_compat.
  - intros x y Hxy. now rewrite Hxy.
  - intros. apply andb_comm.
  Qed.
  
  (** **  Results about [choose]  **)
  
  Lemma choose_In : forall m, (exists x, In x m) <-> exists x, choose m = Some x.
  Proof using FMultisetsSpec.
  intro m. split; intros [x Hin].
  - destruct (choose m) eqn:Hm; eauto. exfalso. rewrite choose_None in Hm. rewrite Hm in Hin. apply (In_empty Hin).
  - exists x. now apply choose_Some.
  Qed.
  
  Lemma choose_not_None : forall m, choose m <> None <-> ~m == empty.
  Proof using FMultisetsSpec. intro. now rewrite choose_None. Qed.
  
  Lemma choose_sub_Some : forall m1 m2, m1 [<=] m2 -> choose m1 <> None -> choose m2 <> None.
  Proof using FMultisetsSpec.
  intros ? ? Hle Hm1 Habs. apply Hm1.
  rewrite choose_None in Habs |- *. now rewrite <- subset_empty_r, <- Habs.
  Qed.
  
  Lemma choose_add_None : forall x n m, n > 0 -> choose (add x n m) <> None.
  Proof using FMultisetsSpec. intros. rewrite choose_None, add_is_empty. lia. Qed.
  
  (*
  Lemma choose_union : forall m1 m2, choose (union m1 m2) = None <-> m1 == empty /\ m2 == empty.
  Proof. intros. rewrite choose_None. apply empty_union. Qed.
  
  Lemma choose_inter : forall m1 m2, choose (inter m1 m2) = None <->
    forall x, ~In x m1 /\ ~In x m2 \/ In x m1 /\ ~In x m2 \/ ~In x m1 /\ In x m2.
  Proof. intros. rewrite choose_None. apply empty_inter. Qed.
  
  Lemma choose_diff : forall m1 m2, choose (diff m1 m2) = None <-> m1 [<=] m2.
  Proof. intros. rewrite choose_None. apply diff_empty_subset. Qed.
  
  Lemma choose_lub : forall m1 m2, choose (lub m1 m2) = None <-> m1 == empty /\ m2 == empty.
  Proof. intros. rewrite choose_None. apply lub_is_empty. Qed.
  *)
  
  (** **  Results about [for_all] and [For_all]  **)
  
  Section for_all_results.
    Variable f : elt -> nat -> bool.
    Hypothesis Hf : compatb f.
    
    Lemma for_all_false : forall m, for_all f m = false <-> ~For_all (fun x n => f x n = true) m.
    Proof using FMultisetsSpec Hf.
    intro m. destruct (for_all f m) eqn:Hfm.
    - rewrite for_all_spec in Hfm; trivial. intuition.
    - rewrite <- for_all_spec; trivial. intuition. rewrite Hfm in *. discriminate.
    Qed.
    
    Lemma for_all_add : forall x n m, n > 0 -> ~In x m -> for_all f (add x n m) = f x n && for_all f m.
    Proof using FMultisetsSpec Hf.
    intros x n m Hn Hin. destruct (for_all f (add x n m)) eqn:Hm.
    + rewrite for_all_spec in Hm; trivial. symmetry. rewrite andb_true_iff. split.
      - specialize (Hm x). msetdec. assert (Hx : m[x] = 0) by lia. rewrite Hx in *. now apply Hm.
      - rewrite for_all_spec; trivial. intros y Hy. rewrite <- (add_other x y n).
          apply Hm. msetdec.
          intro Heq. apply Hin. now rewrite <- Heq.
    + symmetry. rewrite andb_false_iff. destruct (f x n) eqn:Hfn; intuition. right.
      rewrite for_all_false in *; trivial. intro Habs. apply Hm. intros y Hy. msetdec.
      - assert (Heq : m[x] = 0) by lia. now rewrite Heq.
      - now apply Habs.
    Qed.
    
    (** Compatibility with [\[<=\]] does not hold because new bindings can appear. *)
    Lemma for_all_sub_compat : Proper (equiv ==> le ==> Bool.le) f -> Proper (Subset ==> Bool.le) (for_all f).
    Proof. Abort.
    
    Lemma for_all_disjoint_union : forall m1 m2,
      inter m1 m2 == empty -> for_all f (union m1 m2) = for_all f m1 && for_all f m2.
    Proof using FMultisetsSpec Hf.
    intros m1 m2 Hm. rewrite empty_inter in Hm.
    destruct (for_all f m1) eqn:Hfm1; [destruct (for_all f m2) eqn:Hfm2 |];
    simpl; try rewrite for_all_spec in Hfm1, Hfm2 |- *; try rewrite for_all_false in *; trivial.
    + intros x Hin. rewrite union_In in Hin. specialize (Hm x). destruct Hin as [Hin | Hin].
      - destruct Hm as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]]; try contradiction. apply Hfm1 in Hin.
        rewrite not_In in Hin2. now rewrite union_spec, Hin2, Nat.add_0_r.
      - destruct Hm as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]]; try contradiction. apply Hfm2 in Hin.
        rewrite not_In in Hin1. now rewrite union_spec, Hin1.
    + intro Habs. apply Hfm2. intros x Hin.
      destruct (Hm x) as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]]; try contradiction.
      rewrite not_In in Hin1. setoid_rewrite <- Nat.add_0_l. rewrite <- Hin1, <- union_spec.
      apply Habs. rewrite union_In. auto.
    + intro Habs. apply Hfm1. intros x Hin.
      destruct (Hm x) as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]]; try contradiction.
      rewrite not_In in Hin2. setoid_rewrite <- Nat.add_0_r. rewrite <- Hin2, <- union_spec.
      apply Habs. rewrite union_In. auto.
    Qed.
    
    Lemma for_all_inter : forall m1 m2,
      for_all f m1 = true -> for_all f m2 = true -> for_all f (inter m1 m2) = true.
    Proof using FMultisetsSpec Hf.
    intros m1 m2 Hm1 Hm2. rewrite for_all_spec in Hm1, Hm2 |- *; trivial. intros x Hin. rewrite inter_In in Hin.
    destruct Hin. rewrite inter_spec. now apply Nat.min_case; apply Hm1 || apply Hm2.
    Qed.
    
    Lemma for_all_lub : forall m1 m2, for_all f m1 = true -> for_all f m2 = true -> for_all f (lub m1 m2) = true.
    Proof using FMultisetsSpec Hf.
    intros m1 m2 Hm1 Hm2. rewrite for_all_spec in Hm1, Hm2 |- *; trivial.
    intros x Hin. rewrite lub_In in Hin. rewrite lub_spec.
    apply Nat.max_case_strong; intro; apply Hm1 || apply Hm2; destruct Hin; unfold In in *; lia.
    Qed.
    
    Lemma for_all_choose : forall m x, for_all f m = true -> choose m = Some x -> f x (m[x]) = true.
    Proof using FMultisetsSpec Hf. intros m x Hm Hx. rewrite for_all_spec in Hm; trivial. now apply Hm, choose_Some. Qed.
  End for_all_results.
  
  Lemma For_all_elements : forall f, Proper (equiv ==> Logic.eq ==> iff) f ->
    forall m, For_all f m <-> List.Forall (fun xn => f (fst xn) (snd xn)) (elements m).
  Proof using FMultisetsSpec.
  intros f Hf m. rewrite List.Forall_forall. split; intro Hall.
  + intros [x n] Hin. simpl. apply (@In_InA _ eq_pair _) in Hin.
    assert (In x m). { rewrite <- (elements_In x 0). eapply InA_pair_elt; eassumption. }
    rewrite elements_spec in Hin. destruct Hin as [? _]. simpl in *. subst. now apply Hall.
  + intros x Hin. rewrite <- (elements_In x 0) in Hin. apply InA_elt_pair in Hin. destruct Hin as [n Hin].
    assert (Hin' : exists y, List.In (y, n) (elements m) /\ equiv y x).
    { rewrite InA_alt in Hin. destruct Hin as [[y p] [[Heqx Heqn] Hin]].
      compute in Heqx, Heqn. subst. now exists y. }
    rewrite elements_spec in Hin. destruct Hin as [Heq Hpos]. simpl in *. subst.
    destruct Hin' as [y [Hin' Heq]]. rewrite <- Heq at 1. now apply (Hall (y, m[x])).
  Qed.
  
  Corollary For_all_from_elements_valid : forall f, Proper (equiv ==> Logic.eq ==> iff) f ->
    forall l, is_elements l -> For_all f (from_elements l) <-> List.Forall (fun xn => f (fst xn) (snd xn)) l.
  Proof using FMultisetsSpec.
  intros f Hf l Hl.
  assert (Hf' : Proper (eq_pair ==> iff) (fun xn => f (fst xn) (snd xn))).
  { intros [? ?] [? ?] [Heq Hn]. compute in Heq, Hn. subst. simpl. now rewrite Heq. }
  rewrite <- (elements_from_elements Hl) at 2. now apply For_all_elements.
  Qed.
  
  Section for_all2_results.
    Variable f g : elt -> nat -> bool.
    Hypothesis (Hf : compatb f) (Hg : compatb g).
    
    Lemma for_all_andb : forall m, for_all (fun x n => f x n && g x n) m = for_all f m && for_all g m.
    Proof using FMultisetsSpec Hf Hg.
    intro m.
    assert (Hfg : compatb (fun x n => f x n && g x n)). { intros ? ? Heq ? ? ?. subst. now rewrite Heq. }
    destruct (for_all f m) eqn:Hfm; [destruct (for_all g m) eqn:Hgm |];
    simpl; try rewrite for_all_spec in Hfm, Hgm |- *; try rewrite for_all_false in *; trivial.
    - intros x Hin. now rewrite Hfm, Hgm.
    - intro Habs. apply Hgm. intros x Hin. apply Habs in Hin. now rewrite andb_true_iff in Hin.
    - intro Habs. apply Hfm. intros x Hin. apply Habs in Hin. now rewrite andb_true_iff in Hin.
    Qed.
    
    Lemma for_all_nfilter : forall m, for_all f m = true -> for_all f (nfilter g m) = true.
    Proof using FMultisetsSpec Hf Hg.
    intros m Hm. rewrite for_all_spec in Hm |- *; trivial. intros x Hin. unfold In in Hin.
    rewrite nfilter_spec in Hin |- *; trivial. now destruct (g x (m[x])); apply Hm || lia.
    Qed.
    
    Lemma for_all_nfilter_merge : forall m,
      for_all f (nfilter g m) = for_all (fun x n => if g x n then f x n else true) m.
    Proof using FMultisetsSpec Hf Hg.
    assert (Hfg : compatb (fun x n => if g x n then f x n else true)).
    { intros x y Hxy n p Hnp. subst. rewrite Hxy. destruct (g y p); trivial. now rewrite Hxy. }
    intro m. destruct (for_all f (nfilter g m)) eqn:Hfgm; symmetry.
    + rewrite for_all_spec in Hfgm |-  *; trivial. intros x Hin. destruct (g x (m[x])) eqn:Hgm; trivial.
      specialize (Hfgm x).  rewrite nfilter_spec, Hgm in Hfgm; trivial. apply Hfgm. rewrite nfilter_In; auto.
    + rewrite for_all_false in *; trivial. intros Habs. apply Hfgm. intros x Hin. rewrite nfilter_In in Hin; auto.
      destruct Hin as [Hin Hgm]. apply Habs in Hin. rewrite nfilter_spec; trivial. now rewrite Hgm in *.
    Qed.
    
    Lemma for_all_extensionality_compat : forall m,
      (forall x, In x m -> f x m[x] = g x m[x]) -> for_all f m = for_all g m.
    Proof using FMultisetsSpec Hf Hg.
    intros m Hfg. destruct (for_all f m) eqn:Hfm, (for_all g m) eqn:Hgm;
    rewrite for_all_spec in Hfm || rewrite for_all_false in Hfm;
    rewrite for_all_spec in Hgm || rewrite for_all_false in Hgm;
    try reflexivity; trivial; exfalso.
    - apply Hgm. intros x Hin. rewrite <- Hfg; trivial; []. now apply Hfm.
    - apply Hfm. intros x Hin. rewrite Hfg; trivial; []. now apply Hgm.
    Qed.
  End for_all2_results.
  
(*
  Lemma for_all_partition_fst : forall m, for_all f m = true -> for_all f (fst (partition g m)) = true.
  Proof. intros. setoid_rewrite partition_spec_fst; trivial. now apply for_all_nfilter. Qed.
  
  Lemma for_all_partition_snd : forall f g, compatb f -> compatb g ->
    forall m, for_all f m = true -> for_all f (snd (partition g m)) = true.
  Proof. intros. rewrite partition_spec_snd; trivial. apply for_all_nfilter; trivial. now apply negf_compatb. Qed.
*)
  
  (** **  Results about [exists_] and [Exists]  **)
  
  Section exists_results.
    Variable f : elt -> nat -> bool.
    Hypothesis Hf : compatb f.
    
    Lemma exists_not_empty : forall m, exists_ f m = true -> m =/= empty.
    Proof using FMultisetsSpec Hf.
    intros m Hm. rewrite exists_spec in Hm; trivial. rewrite not_empty_In. destruct Hm as [x [? ?]]. now exists x.
    Qed.
    
    Lemma exists_false : forall m, exists_ f m = false <-> ~Exists (fun x n => f x n = true) m.
    Proof using FMultisetsSpec Hf.
    intro m. destruct (exists_ f m) eqn:Hfm.
    - rewrite exists_spec in Hfm; trivial. intuition.
    - rewrite <- exists_spec; trivial. intuition. rewrite Hfm in *. discriminate.
    Qed.
    
    Lemma exists_add : forall x n m, n > 0 -> ~In x m -> exists_ f (add x n m) = f x n || exists_ f m.
    Proof using FMultisetsSpec Hf.
    intros x n m Hn Hin. destruct (exists_ f (add x n m)) eqn:Hm.
    + rewrite exists_spec in Hm; trivial. symmetry. rewrite orb_true_iff. destruct Hm as [y [Hy Hfy]]. msetdec.
      - left. assert (Hm : m[x] = 0) by lia. now rewrite Hm in Hfy.
      - right. exists y. now split.
    + symmetry. rewrite orb_false_iff. rewrite exists_false in *; trivial.
      assert (Hxm : m[x] = 0) by (unfold In in Hin; lia). split.
      - destruct (f x n) eqn:Hfxn; trivial. elim Hm. exists x. split; msetdec.
      - intros [y [Hy Hfy]]. apply Hm. exists y. unfold In in *. split; msetdec.
    Qed.
    
    Lemma exists_sub_compat : Proper (equiv ==> le ==> Bool.le) f -> Proper (Subset ==> Bool.le) (exists_ f).
    Proof using FMultisetsSpec Hf.
    intros Hf2 m1. pattern m1. apply ind; clear m1.
    * intros m1 m2 Hm. setoid_rewrite Hm. reflexivity.
    * intros m x n Hm Hn Hrec m2 Hle. destruct (exists_ f (add x n m)) eqn:Hall; try now intuition.
      simpl. rewrite exists_add in Hall; trivial. rewrite orb_true_iff in Hall. destruct Hall as [Hall | Hall].
      + specialize (Hle x). rewrite not_In in Hm. rewrite add_same, Hm in Hle.
        rewrite <- (@add_remove_cancel x), exists_add; trivial.
        - apply (Hf2 _ _ (reflexivity x)) in Hle. simpl in Hle. rewrite Hall in Hle. simpl in Hle. now rewrite Hle.
        - lia.
        - rewrite remove_In. intros [[_ Habs] | [Habs _]]; lia || now elim Habs.
      + setoid_rewrite Hall in Hrec. simpl in Hrec. apply Hrec. etransitivity; try eassumption. apply add_subset.
    * intros. rewrite exists_empty; trivial. intuition.
    Qed.
    
    Lemma exists_disjoint_union : forall m1 m2,
      inter m1 m2 == empty -> exists_ f (union m1 m2) = exists_ f m1 || exists_ f m2.
    Proof using FMultisetsSpec Hf.
    intros m1 m2 Hm. rewrite empty_inter in Hm.
    destruct (exists_ f m1) eqn:Hfm1; [| destruct (exists_ f m2) eqn:Hfm2];
    try rewrite exists_spec in Hfm1; try rewrite exists_spec in Hfm2; try rewrite exists_spec;
    simpl; try rewrite exists_false in *; trivial;
    try destruct Hfm1 as [x [Hin Hfm1]] || destruct Hfm2 as [x [Hin Hfm2]].
    + exists x. specialize (Hm x). destruct Hm as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]]; try contradiction.
      rewrite union_In. split; auto. rewrite union_spec. rewrite not_In in Hin2. now rewrite Hin2, Nat.add_0_r.
    + exists x. specialize (Hm x). destruct Hm as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]]; try contradiction.
      rewrite union_In. split; auto. rewrite union_spec. rewrite not_In in Hin1. now rewrite Hin1.
    + intro Habs. destruct Habs as [x [Hin Habs]]. rewrite union_In in Hin. specialize (Hm x).
      destruct Hin; destruct Hm as [[Hin1 Hin2] | [[Hin1 Hin2] | [Hin1 Hin2]]]; try contradiction.
      - apply Hfm1. exists x. rewrite not_In in Hin2. rewrite union_spec, Hin2, Nat.add_0_r in Habs. now split.
      - apply Hfm2. exists x. rewrite not_In in Hin1. rewrite union_spec, Hin1 in Habs. now split.
    Qed.
    
    Lemma exists_inter : forall m1 m2, exists_ f (inter m1 m2) = true -> exists_ f m1 = true \/ exists_ f m2 = true.
    Proof using FMultisetsSpec Hf.
    intros m1 m2. repeat rewrite exists_spec; trivial. intros [x [Hin Hfx]].
    rewrite inter_spec in Hfx. rewrite inter_In in Hin. destruct Hin.
    destruct (Min.min_dec (m1[x]) (m2[x])) as [Hmin | Hmin];
    rewrite Hmin in Hfx; left + right; now exists x.
    Qed.
    
    Lemma exists_lub : forall m1 m2, exists_ f (lub m1 m2) = true -> exists_ f m1 = true \/ exists_ f m2 = true.
    Proof using FMultisetsSpec Hf.
    intros m1 m2. repeat rewrite exists_spec; trivial. intros [x [Hin Hfx]]. unfold In in *.
    rewrite lub_spec in Hin, Hfx. destruct (Max.max_dec (m1[x]) (m2[x])) as [Hmax | Hmax];
    rewrite Hmax in Hin, Hfx; left + right; now exists x.
    Qed.
    
    Lemma exists_false_for_all : forall m, exists_ f m = false <-> for_all (fun x n => negb (f x n)) m = true.
    Proof using FMultisetsSpec Hf.
    intro m. rewrite exists_false, for_all_spec; try now apply negf_compatb.
    split; intro Hm.
    - intros x Hin. destruct (f x (m[x])) eqn:Habs; trivial. exfalso. apply Hm. now exists x.
    - intros [x [Hin Hx]]. apply Hm in Hin. rewrite Hx in Hin. discriminate.
    Qed.
    
    Lemma for_all_false_exists : forall m, for_all f m = false <-> exists_ (fun x n => negb (f x n)) m = true.
    Proof using FMultisetsSpec Hf.
    assert (Hnegf := negf_compatb Hf).
    assert (Hf' : Proper (equiv ==> Logic.eq ==> iff) (fun x n => f x n = true)).
    { intros ? ? Heq ? ? ?. subst. now rewrite Heq. }
    assert (Hnegf' : Proper (equiv ==> Logic.eq ==> iff) (fun x n => negb (f x n) = true)).
    { intros ? ? Heq ? ? ?. subst. now rewrite Heq. }
    intro m. rewrite for_all_false, exists_spec; trivial. split; intro Hm.
    * revert Hm. pattern m. apply ind; clear m.
      + intros m1 m2 Hm. now rewrite Hm.
      + intros m x n Hm Hn Hrec Hall. destruct (f x n) eqn:Hfxn.
        - destruct Hrec as [y [Hin Hy]].
          ++ intro Habs. apply Hall. intros y Hin. rewrite add_In in Hin. destruct (equiv_dec y x) as [Heq | Heq].
             -- rewrite not_In in Hm. now rewrite Heq, add_same, Hm.
             -- destruct Hin as [[] | Hin]; try contradiction; []. apply Habs in Hin. now rewrite add_other.
          ++ exists y. split.
             -- rewrite add_In. tauto.
             -- rewrite add_other; trivial. intro Heq. apply Hm. now rewrite <- Heq.
        - exists x. split.
          ++ rewrite add_In. left. split; lia || reflexivity.
          ++ rewrite not_In in Hm. rewrite add_same, Hm. simpl. now rewrite Hfxn.
      + intro Habs. elim Habs. intros x Hin. elim (In_empty Hin).
    * intro Habs. destruct Hm as [x [Hin Hx]]. apply Habs in Hin. rewrite Hin in Hx. discriminate.
    Qed.
    
    Lemma exists_choose : forall m x, choose m = Some x -> f x (m[x]) = true -> exists_ f m = true.
    Proof using FMultisetsSpec Hf. intros m x Hm Hx. apply choose_Some in Hm. rewrite exists_spec; trivial. now exists x. Qed.
  End exists_results.
  
  Lemma Exists_elements : forall f, Proper (equiv ==> Logic.eq ==> iff) f ->
    forall m, Exists f m <-> List.Exists (fun xn => f (fst xn) (snd xn)) (elements m).
  Proof using FMultisetsSpec.
  intros f Hf m. rewrite List.Exists_exists. split; intro Hm.
  + destruct Hm as [x [Hin Hfx]]. rewrite <- (elements_In x 0) in Hin.
    apply InA_elt_pair in Hin. destruct Hin as [n Hin].
    assert (n = m[x]). { rewrite elements_spec in Hin. intuition. }
    rewrite InA_alt in Hin. destruct Hin as [[y p] [[Heqx Heqn] Hin]].
    compute in Heqx, Heqn. subst. rewrite Heqx in *. clear Heqx x. subst.
    exists (y, m[y]). auto.
  + destruct Hm as [[x n] [Hin Hfx]]. apply (@In_InA _ eq_pair _) in Hin. rewrite elements_spec in Hin.
    destruct Hin as [Heq Hpos]. simpl in *. subst. now exists x.
  Qed.
  
  Corollary Exists_from_elements_valid : forall f, Proper (equiv ==> Logic.eq ==> iff) f ->
    forall l, is_elements l -> Exists f (from_elements l) <-> List.Exists (fun xn => f (fst xn) (snd xn)) l.
  Proof using FMultisetsSpec.
  intros f Hf l Hl.
  assert (Hf' : Proper (eq_pair ==> iff) (fun xn => f (fst xn) (snd xn))).
  { intros [? ?] [? ?] [Heq Hn]. compute in Heq, Hn. subst. simpl. now rewrite Heq. }
  rewrite <- (elements_from_elements Hl) at 2. now apply Exists_elements.
  Qed.
  
  Lemma nfilter_none : forall f, compatb f ->
    forall m, nfilter f m == empty <-> for_all (fun x n => negb (f x n)) m = true.
  Proof using FMultisetsSpec.
  intros f Hf m.
  assert (Hf2 : Proper (equiv ==> Logic.eq ==> Logic.eq) (fun x n => negb (f x n))).
  { intros x y Hxy ? n ?. subst. now rewrite Hxy. }
  assert (Hf3 : Proper (equiv ==> Logic.eq ==> Logic.eq) (fun x n => negb (negb (f x n)))).
  { intros x y Hxy ? n ?. subst. now rewrite Hxy. }
  split; intros Hall.
  + destruct (for_all (fun (x : elt) (n : nat) => negb (f x n)) m) eqn:Hforall; trivial.
    rewrite for_all_false_exists, exists_spec in Hforall; trivial.
    destruct Hforall as [x [Hin Hfx]]. rewrite negb_involutive in Hfx.
    elim (@In_empty x). rewrite <- Hall, nfilter_In; auto.
  + rewrite for_all_spec in Hall; trivial.
    destruct (empty_or_In_dec (nfilter f m)) as [? | [x Hin]]; trivial.
    rewrite nfilter_In in Hin; trivial. destruct Hin as [Hin Hfx]. apply Hall in Hin.
    rewrite Hfx in Hin. discriminate.
  Qed.
  
  Section exists2_results.
    Variable f g : elt -> nat -> bool.
    Hypothesis (Hf : compatb f) (Hg : compatb g).
    
    Lemma exists_orb : forall m, exists_ (fun x n => f x n || g x n) m = exists_ f m || exists_ g m.
    Proof using FMultisetsSpec Hf Hg.
    intro m.
    assert (Hfg : compatb (fun x n => f x n || g x n)). { intros ? ? Heq ? ? ?. subst. now rewrite Heq. }
    destruct (exists_ f m) eqn:Hfm; [| destruct (exists_ g m) eqn:Hgm];
    simpl; try rewrite exists_spec in Hfm; try rewrite exists_spec in Hgm;
    try rewrite exists_spec; try rewrite exists_false in *; trivial.
    - destruct Hfm as [x [Hin Hfm]]. exists x. now rewrite Hfm.
    - destruct Hgm as [x [Hin Hgm]]. exists x. now rewrite Hgm, orb_b_true.
    - intros [x [Hin Habs]]. rewrite orb_true_iff in Habs. destruct Habs; apply Hfm + apply Hgm; now exists x.
    Qed.
    
    Lemma exists_nfilter : forall m, exists_ f (nfilter g m) = true -> exists_ f m = true.
    Proof using FMultisetsSpec Hf Hg.
    intros m Hm. rewrite exists_spec in Hm |- *; trivial.
    destruct Hm as [x [Hin Hfm]]. rewrite nfilter_In in *; trivial.
    destruct Hin as [HIn Hgm]. rewrite nfilter_spec, Hgm in Hfm; trivial. now exists x.
    Qed.
    
    Lemma exists_nfilter_merge : forall m, exists_ f (nfilter g m) = exists_ (fun x n => f x n && g x n) m.
    Proof using FMultisetsSpec Hf Hg.
    assert (Hfg : compatb (fun x n => f x n && g x n)). { intros ? ? Heq ? ? ?. subst. now rewrite Heq. }
    intro m. destruct (exists_ f (nfilter g m)) eqn:Hfgm; symmetry.
    + rewrite exists_spec in Hfgm |- *; trivial.
      destruct Hfgm as [x [Hin Hfm]]. rewrite nfilter_spec in Hfm; trivial.
      rewrite nfilter_In in *; trivial. destruct Hin as [Hin Hgm].
      exists x. rewrite Hgm, Hfm in *. now split.
    + rewrite exists_false in *; trivial. intros [x [Hin Hm]]. rewrite andb_true_iff in Hm.
      destruct Hm as [? Hm]. apply Hfgm. exists x. rewrite nfilter_In, nfilter_spec, Hm; auto.
    Qed.
    
    Lemma exists_extensionality_compat : forall m,
      (forall x, In x m -> f x m[x] = g x m[x]) -> exists_ f m = exists_ g m.
    Proof using FMultisetsSpec Hf Hg.
    intros m Hfg. destruct (exists_ f m) eqn:Hfm, (exists_ g m) eqn:Hgm;
    rewrite exists_spec in Hfm || rewrite exists_false in Hfm;
    rewrite exists_spec in Hgm || rewrite exists_false in Hgm;
    try reflexivity; trivial; exfalso.
    - apply Hgm. destruct Hfm as [x [Hin Hfm]]. exists x. now rewrite <- Hfg.
    - apply Hfm. destruct Hgm as [x [Hin Hgm]]. exists x. now rewrite Hfg.
    Qed.
  End exists2_results.
  
(*
    Lemma exists_partition_fst : forall m, for_all f m = true -> for_all f (fst (partition g m)) = true.
    Proof. intros. setoid_rewrite partition_spec_fst; trivial. now apply for_all_nfilter. Qed.
  
  Lemma for_all_partition_snd : forall f g, compatb f -> compatb g ->
    forall m, for_all f m = true -> for_all f (snd (partition g m)) = true.
  Proof. intros. rewrite partition_spec_snd; trivial. apply for_all_nfilter; trivial. now apply negf_compatb. Qed.
*)
  
End MMultisetFacts.


(** As tactics do not survive sections, we define [msetdec] again. *)

Ltac saturate_Einequalities :=
  repeat match goal with
    (* change ~ == for =/= *)
    | H : ~?x == ?y |- _ => apply neq_is_neq in H
    (* remove duplicates *)
    | H1 : ?x =/= ?y, H2 : ?x =/= ?y |- _ => clear H2
    (* avoid reflexive inequalities *)
    | H : ?x =/= ?x |- _ => change (id (x =/= x)) in H
    (* avoid already saturated inequalities *)
    | H1 : ?x =/= ?y, H2 : ?y =/= ?x |- _ => change (id (x =/= y)) in H1; change (id (y =/= x)) in H2
    (* saturate the remaining ones *)
    | H : ?x =/= ?y |- _ => let Hneq := fresh "Hneq" in assert (Hneq := neq_sym H)
  end;
  (* remove the markers (id) *)
  repeat match goal with
    | H : id (?x =/= ?y) |- _ => change (x =/= y) in H
  end.

Ltac msetdec_step := 
  match goal with
    (* Simplifying equalities *)
    | H : ?x = ?x |- _ => clear H
    | H : ?x == ?x |- _ => clear H
    | H : ?x = ?y |- _ => subst x || rewrite H in *
    | Hneq : ?x =/= ?x |- _ => now elim Hneq
    | Heq : equiv ?x ?y |- _ => clear x Heq || rewrite Heq in *
    | Heq : @equiv (multiset _) _ ?x ?y, Hin : context[?x] |- _ => rewrite Heq in Hin
    | Heq : @equiv (multiset _) _ ?x ?y |- context[?x] => rewrite Heq
    | Heq : @equiv (multiset _) _ ?x ?y |- _ => clear x Heq
    (* Simplifying [singleton], [add] and [remove] *)
    | Hneq : ?y =/= ?x |- context[multiplicity ?y (singleton ?x ?n)] => rewrite singleton_other; trivial
    | Hneq : ?y =/= ?x |- context[multiplicity ?y (add ?x ?n ?m)] => rewrite add_other; trivial
    | Hneq : ?y =/= ?x |- context[multiplicity ?y (remove ?x ?n ?m)] => rewrite remove_other; trivial
    | Hneq : ?y =/= ?x, H : context[multiplicity ?y (singleton ?x ?n)] |- _ =>
        rewrite singleton_other in H; trivial
    | Hneq : ?y =/= ?x, H : context[multiplicity ?y (add ?x ?n ?m)] |- _ => rewrite add_other in H; trivial
    | Hneq : ?y =/= ?x, H : context[multiplicity ?y (remove ?x ?n ?m)] |- _ =>
        rewrite remove_other in H; trivial
    (* Destructing equalities *)
    | H : ?x =/= ?y |- context[?x == ?y] => destruct (equiv_dec x y) as [| _]; try contradiction
    | |- context[?x == ?y] => destruct (equiv_dec x y); trivial
    | |- context[multiplicity ?y (singleton ?x ?n)] => destruct (equiv_dec y x)
    | |- context[multiplicity ?y (add ?x ?n ?m)] => destruct (equiv_dec y x)
    | |- context[multiplicity ?y (remove ?x ?n ?m)] => destruct (equiv_dec y x)
    | H : context[multiplicity ?y (singleton ?x ?n)] |- _ => destruct (equiv_dec y x)
    | H : context[multiplicity ?y (add ?x ?n ?m)] |- _ => destruct (equiv_dec y x)
    | H : context[multiplicity ?y (remove ?x ?n ?m)] |- _ => destruct (equiv_dec y x)
    | |- context[equiv_dec ?x ?y] => destruct (equiv_dec x y)
    | Heq : context[equiv_dec ?x ?y] |- _ => destruct (equiv_dec x y)
    | _ => idtac
  end.

Ltac msetdec :=
  repeat (saturate_Einequalities; autorewrite with FMsetdec in *; unfold In in *; trivial;
          msetdec_step; easy || (try lia)).

Tactic Notation "msetdec_n" integer(n) :=
  do n (saturate_Einequalities; autorewrite with FMsetdec in *; unfold In in *; trivial;
        msetdec_step; easy || (try lia)).
