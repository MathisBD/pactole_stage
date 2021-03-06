(******************************************)
(*   Finite multiset library              *)
(*   Developped for the PACTOLE project   *)
(*   L. Rieg                              *)
(*                                        *)
(*   This file is distributed under       *)
(*   the terms of the CeCILL-C licence    *)
(*                                        *)
(******************************************)


Require Import Lia PeanoNat.
Require Import SetoidList.
Require Import RelationPairs.
Require Import SetoidDec.

Require Import Pactole.Util.MMultiset.Preliminary.
Require Import Pactole.Util.MMultiset.MMultisetInterface.
Require Import Pactole.Util.MMultiset.MMultisetFacts.


Set Implicit Arguments.
Existing Instance multiplicity_compat.
(* To have relation pairs unfolded *)
Arguments RelationPairs.RelProd {A} {B} RA RB _ _ /.
Arguments RelationPairs.RelCompFun {A} {B} R f a a' /.


Section MMultisetExtra.
  
  Context {elt : Type}.
  Context `{M : FMultisetsOn elt}.
  
  Hint Rewrite empty_spec add_same remove_same diff_spec union_spec inter_spec lub_spec singleton_same : FMsetdec.
  Hint Rewrite is_empty_spec nfilter_spec filter_spec npartition_spec_fst npartition_spec_snd : FMsetdec.
  Hint Rewrite partition_spec_fst partition_spec_snd for_all_spec exists_spec : FMsetdec.
  Hint Unfold In : FMsetdec.
  
(*   Include (MMultisetExtraOps E M). *)
  
  (** **  Function [remove_all] and its properties  **)
  
  (** Remove all copies of [x] from [m] *)
  Definition remove_all x m := remove x m[x] m.
  
  Lemma remove_all_same : forall x m, (remove_all x m)[x] = 0.
  Proof using M. intros. unfold remove_all. rewrite remove_same. lia. Qed.
  
  Lemma remove_all_other : forall x y m, y =/= x -> (remove_all x m)[y] = m[y].
  Proof using M. intros. unfold remove_all. now rewrite remove_other. Qed.
  
  Lemma remove_all_spec : forall x y m, (remove_all x m)[y] = if equiv_dec y x then 0 else m[y].
  Proof using M. intros. unfold remove_all. msetdec. Qed.
  
  Instance remove_all_compat : Proper (equiv ==> equiv ==> equiv) remove_all.
  Proof using M. repeat intro. apply remove_compat; msetdec. Qed.
  
  Instance remove_all_sub_compat : Proper (equiv ==> Subset ==> Subset) remove_all.
  Proof using M. repeat intro. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_In : forall x y m, In x (remove_all y m) <-> In x m /\ x =/= y.
  Proof using M. intros. unfold remove_all. rewrite remove_In. intuition. msetdec. Qed.
  
  Lemma remove_all_subset : forall x m, remove_all x m [<=] m.
  Proof using M. intros x m y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_singleton_same : forall x n, remove_all x (singleton x n) == empty.
  Proof using M. intros x n y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_singleton_other : forall x y n, y =/= x -> remove_all y (singleton x n) == singleton x n.
  Proof using M. intros x y n Hxy z. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_add_same : forall x n m, remove_all x (add x n m) == remove_all x m.
  Proof using M. intros x n m y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_add_other : forall x y n m, x =/= y -> remove_all x (add y n m) == add y n (remove_all x m).
  Proof using M. intros x y n m Hxy z. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_remove : forall x n m, remove_all x (remove x n m) == remove_all x m.
  Proof using M. intros x n m y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_remove_all : forall x n m, remove x n (remove_all x m) == remove_all x m.
  Proof using M. intros x n m y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_remove_other : forall x y n m,
    x =/= y -> remove_all y (remove x n m) == remove x n (remove_all y m).
  Proof using M. intros x y n m Hxy z. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_union : forall x m??? m???,
    remove_all x (union m??? m???) == union (remove_all x m???) (remove_all x m???).
  Proof using M. intros x n m y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_inter : forall x m??? m???,
    remove_all x (inter m??? m???) == inter (remove_all x m???) (remove_all x m???).
  Proof using M. intros x m??? m??? y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_diff : forall x m??? m???, remove_all x (diff m??? m???) == diff (remove_all x m???) (remove_all x m???).
  Proof using M. intros x m??? m??? y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_diff2 : forall x m??? m???, remove_all x (diff m??? m???) == diff (remove_all x m???) m???.
  Proof using M. intros x m??? m??? y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_lub : forall x m??? m???, remove_all x (lub m??? m???) == lub (remove_all x m???) (remove_all x m???).
  Proof using M. intros x m??? m??? y. unfold remove_all. msetdec. Qed.
  
  Lemma remove_all_for_all : forall f, compatb f ->
    forall x m, for_all f (remove_all x m) = for_all (fun y n => if equiv_dec y x then true else f y n) m.
  Proof using M.
  intros f Hf x m. unfold remove_all.
  destruct (for_all f (remove x m[x] m)) eqn:Hcase.
  + symmetry. rewrite for_all_spec in Hcase |- *; trivial; [|].
    - intros y Hin. specialize (Hcase y). msetdec. auto.
    - intros y y' Hy ? ? ?. subst. clear -Hf Hy.
      destruct (equiv_dec y x), (equiv_dec y' x); try apply Hf; trivial; rewrite Hy in *; contradiction.
  + symmetry. rewrite for_all_false in Hcase |- *; trivial; [|].
    - intro Hall. apply Hcase. intros y Hin. specialize (Hall y). msetdec. auto.
    - intros y y' Hy ? ? ?. subst. clear -Hf Hy.
      destruct (equiv_dec y x), (equiv_dec y' x); try apply Hf; trivial; rewrite Hy in *; contradiction.
  Qed.
  
  Lemma remove_all_exists : forall f, compatb f ->
    forall x m, exists_ f (remove_all x m) = exists_ (fun y n => if equiv_dec y x then false else f y n) m.
  Proof using M.
  intros f Hf x m. unfold remove_all.
  destruct (exists_ f (remove x m[x] m)) eqn:Hcase.
  + symmetry. rewrite exists_spec in Hcase |- *; trivial; [|].
    - destruct Hcase as [y [Hin Hy]]. exists y. msetdec.
    - intros y y' Hy ? ? ?. subst. clear -Hf Hy.
      destruct (equiv_dec y x), (equiv_dec y' x); try apply Hf; trivial; rewrite Hy in *; contradiction.
  + symmetry. rewrite exists_false in Hcase |- *; trivial; [|].
    - intros [y [Hin Hy]]. apply Hcase. exists y. msetdec.
    - intros y y' Hy ? ? ?. subst. clear -Hf Hy.
      destruct (equiv_dec y x), (equiv_dec y' x); try apply Hf; trivial; rewrite Hy in *; contradiction.
  Qed.
  
  Lemma remove_all_nfilter : forall f, compatb f ->
    forall x m, nfilter f (remove_all x m) == remove_all x (nfilter f m).
  Proof using M. repeat intro. unfold remove_all. msetdec. rewrite 2 Nat.sub_diag. now destruct_match. Qed.
  
  Lemma remove_all_filter : forall f, Proper (equiv ==> Logic.eq) f ->
    forall x m, filter f (remove_all x m) == remove_all x (filter f m).
  Proof using M.
  repeat intro. unfold remove_all. rewrite 2 filter_nfilter; trivial.
  apply remove_all_nfilter. repeat intro. auto.
  Qed.
  
  Lemma remove_all_filter_false : forall f, Proper (equiv ==> Logic.eq) f ->
    forall x m, f x = false -> filter f (remove_all x m) == filter f m.
  Proof using M.
  intros. rewrite remove_all_filter; trivial; []. apply remove_out.
  rewrite filter_In; intuition; congruence.
  Qed.
  
  Lemma remove_all_npartition_fst : forall f, compatb f ->
    forall x m, fst (npartition f (remove_all x m)) == remove_all x (fst (npartition f m)).
  Proof using M. intros. rewrite 2 npartition_spec_fst; trivial; []. now apply remove_all_nfilter. Qed.
  
  Lemma remove_all_npartition_snd : forall f, compatb f ->
    forall x m, snd (npartition f (remove_all x m)) == remove_all x (snd (npartition f m)).
  Proof using M.
  intros f Hf x m. rewrite 2 npartition_spec_snd; trivial; [].
  apply remove_all_nfilter. repeat intro. f_equal. now apply Hf.
  Qed.
  
  Lemma remove_all_partition_fst : forall f, Proper (equiv ==> Logic.eq) f ->
    forall x m, fst (partition f (remove_all x m)) == remove_all x (fst (partition f m)).
  Proof using M. intros. rewrite 2 partition_spec_fst; trivial; []. now apply remove_all_filter. Qed.
  
  Lemma remove_all_partition_snd : forall f, Proper (equiv ==> Logic.eq) f ->
    forall x m, snd (partition f (remove_all x m)) == remove_all x (snd (partition f m)).
  Proof using M.
  intros f Hf x m. rewrite 2 partition_spec_snd; trivial; [].
  apply remove_all_filter. repeat intro. f_equal. now apply Hf.
  Qed.
  
  Lemma remove_all_elements : forall x m,
    PermutationA eq_pair (elements (remove_all x m))
                         (removeA (fun x y => equiv_dec (fst x) (fst y)) (x, m[x]) (elements m)).
  Proof using M.
  assert (Hequiv : Equivalence eq_elt) by autoclass.
  intros x m.
  apply NoDupA_equivlistA_PermutationA; autoclass.
  * apply (NoDupA_strengthen subrelation_pair_elt), elements_NoDupA.
  * now apply (NoDupA_strengthen subrelation_pair_elt), removeA_NoDupA, elements_NoDupA.
  * intros [y p]. unfold remove_all. rewrite elements_remove.
    assert (Hiff : y == x /\ p = m[x] - m[x] /\ p > 0 \/ ~ y == x /\ InA eq_pair (y, p) (elements m)
                   <-> ~ y == x /\ InA eq_pair (y, p) (elements m)) by (intuition; lia).
    rewrite Hiff. clear Hiff.
    induction (elements m) as [| e l]; simpl.
    + split; intro Hin; (intuition; lia) || inv Hin.
    + destruct_match.
      - rewrite <- IHl. clear IHl.
        split; [intros [Hxy Hin] | intro Hin]; intuition.
        inv Hin; try tauto; []. elim Hxy. hnf in *. simpl in *. now transitivity (fst e).
      - split; [intros [Hxy Hin] | intro Hin].
        -- inv Hin; try (now left); []. right. intuition.
        -- inv Hin; intuition.
           lazymatch goal with H : _ =/= _, H1 : eq_pair _ e |- False =>
             apply H; rewrite <- H1; intuition end.
  Qed.
  
  Lemma remove_all_support : forall x m,
    PermutationA equiv (support (remove_all x m)) (removeA equiv_dec x (support m)).
  Proof using M. intros. unfold remove_all. rewrite support_remove. destruct_match; reflexivity || lia. Qed.
  
  Lemma remove_all_cardinal : forall x m, cardinal (remove_all x m) = cardinal m - m[x].
  Proof using M. intros. unfold remove_all. now rewrite cardinal_remove, Nat.min_id. Qed.
  
  Lemma remove_all_size_in : forall x m, In x m -> size (remove_all x m) = size m - 1.
  Proof using M. intros. unfold remove_all. rewrite size_remove; trivial; []. destruct_match; lia. Qed.
  
  Lemma remove_all_size_out : forall x m, ~In x m -> size (remove_all x m) = size m.
  Proof using M. intros. unfold remove_all. now rewrite remove_out. Qed.
  
  Lemma remove_all_as_filter : forall x m,
    remove_all x m == filter (fun y => if equiv_dec y x then false else true) m.
  Proof using M.
  intros x m y. unfold remove_all. msetdec.
  repeat intro. do 2 destruct_match; trivial; exfalso;
  match goal with H : _ =/= _ |- _ => apply H end; now etransitivity; eauto.
  Qed.
  
  (** **  Function [map] and its properties  **)
  
  Definition map f m := fold (fun x n acc => add (f x) n acc) m empty.
  
  Section map_results.
    Variable f : elt -> elt.
    Hypothesis Hf : Proper (equiv ==> equiv) f.
    
    Global Instance map_compat : Proper (equiv ==> equiv) (map f).
    Proof using Hf M.
    intros m??? m??? Hm. unfold map. apply (fold_compat _ _).
    - repeat intro. msetdec.
    - repeat intro. apply add_comm.
    - assumption.
    - reflexivity.
    Qed.
    
    Lemma map_In : forall x m, In x (map f m) <-> exists y, x == (f y) /\ In y m.
    Proof using Hf M.
    intros x m. unfold In, map. apply fold_rect.
    + intros m??? m??? acc Heq Hequiv. rewrite Hequiv. now setoid_rewrite Heq.
    + setoid_rewrite empty_spec. split; try intros [? [_ ?]]; lia.
    + intros y m' acc Hm Hin Hrec. destruct (equiv_dec x (f y)) as [Heq | Hneq]; msetdec.
      - split.
          intros. exists y. split; trivial. msetdec.
          intros [? [? ?]]. msetdec.
      - rewrite Hrec. split; intros [z [Heq ?]]; exists z; split; msetdec.
    Qed.
    
    Lemma map_empty : map f empty == empty.
    Proof using M f. unfold map. now rewrite fold_empty. Qed.
    
    Lemma map_add : forall x n m, map f (add x n m) == add (f x) n (map f m).
    Proof using Hf M.
    intros x n m y. destruct n.
    + now do 2 rewrite add_0.
    + unfold map at 1. rewrite (fold_add_additive _).
      - reflexivity.
      - repeat intro. msetdec.
      - repeat intro. apply add_comm.
      - repeat intro. apply add_merge.
      - lia.
    Qed.
    
    Lemma map_spec : forall x m,
      (map f m)[x] = cardinal (nfilter (fun y _ => if equiv_dec (f y) x then true else false) m).
    Proof using Hf M.
    intros x m. pose (g := fun y (_ : nat) => if equiv_dec (f y) x then true else false). fold g.
    assert (Hg : Proper (equiv ==> @Logic.eq nat ==> Logic.eq) g). { repeat intro. unfold g. msetdec. }
    pattern m. apply ind; clear m.
    + intros ? ? Hm. now rewrite Hm.
    + intros * Hin Hrec. rewrite map_add, nfilter_add; trivial. unfold g at 2. msetdec. rewrite cardinal_add. lia.
    + now rewrite map_empty, nfilter_empty, cardinal_empty, empty_spec.
    Qed.
    
    Global Instance map_sub_compat : Proper (Subset ==> Subset) (map f).
    Proof using Hf M.
    intro m. pattern m. apply ind; clear m.
    + intros ? ? Hm. now setoid_rewrite Hm.
    + intros m x n Hin Hn Hrec m' Hsub y.
      assert (Hx : m[x] = 0). { unfold In in Hin. lia. }
      rewrite <- (add_remove_cancel x m' (Hsub x)). do 2 rewrite (map_add _). msetdec.
      - apply Plus.plus_le_compat; trivial; [].
        repeat rewrite map_spec; trivial. apply add_subset_remove in Hsub.
        apply cardinal_sub_compat, nfilter_sub_compat; solve [lia | repeat intro; msetdec].
      - now apply Hrec, add_subset_remove.
    + intros ? _. rewrite map_empty. apply subset_empty_l.
    Qed.
    
    Lemma map_singleton : forall x n, map f (singleton x n) == singleton (f x) n.
    Proof using Hf M.
    intros x n y. destruct n.
    + repeat rewrite singleton_0. now rewrite map_empty. 
    + unfold map. rewrite fold_singleton; repeat intro; msetdec.
    Qed.
    
    Lemma map_remove1 : forall x n m, n <= m[x] -> map f (remove x n m) == remove (f x) n (map f m).
    Proof using Hf M.
    intros x n m Hle. rewrite <- (add_remove_cancel _ _ Hle) at 2. now rewrite (map_add _), remove_add_cancel.
    Qed.
    
    Lemma map_remove2 : forall x n m,
      m[x] <= n -> map f (remove x n m) == remove (f x) m[x] (map f m).
    Proof using Hf M.
    intros x n m Hle. rewrite <- (add_remove_id _ _ Hle) at 3.
    now rewrite (map_add _), remove_add_cancel.
    Qed.
    
    Lemma fold_map_union : forall m??? m???, fold (fun x n acc => add (f x) n acc) m??? m??? == union (map f m???) m???.
    Proof using Hf M.
    intros m??? m???. apply fold_rect with (m := m???).
    + repeat intro. msetdec.
    + now rewrite map_empty, union_empty_l.
    + intros * ? ? Heq. now rewrite Heq, map_add, union_add_comm_l.
    Qed.
    
    Theorem map_union : forall m??? m???, map f (union m??? m???) == union (map f m???) (map f m???).
    Proof using Hf M.
    intros m??? m???. unfold map at 1 2. rewrite (fold_union_additive _).
    + now apply fold_map_union.
    + repeat intro. msetdec.
    + repeat intro. apply add_comm.
    + repeat intro. apply add_merge.
    Qed.
    
    Theorem map_inter : forall m??? m???, map f (inter m??? m???) [<=] inter (map f m???) (map f m???).
    Proof using Hf M.
    intros m1 m2 x. destruct (map f (inter m1 m2))[x] eqn:Hfx.
    + lia.
    + assert (Hin : In x (map f (inter m1 m2))) by msetdec.
      rewrite map_In in Hin. destruct Hin as [y [Heq Hin]]. rewrite inter_In in Hin.
      destruct Hin as [Hin1 Hin2]. rewrite <- Hfx, Heq. rewrite inter_spec.
      apply Nat.min_glb; apply map_sub_compat; apply inter_subset_l + apply inter_subset_r.
    Qed.
    
    Theorem map_lub : forall m??? m???, lub (map f m???) (map f m???) [<=] map f (lub m??? m???).
    Proof using Hf M.
    intros m1 m2 x. destruct (lub (map f m1) (map f m2))[x] eqn:Hfx.
    + lia.
    + assert (Hin : In x (lub (map f m1) (map f m2))).
      { rewrite lub_spec in Hfx. rewrite lub_In. unfold In.
        destruct (Max.max_dec (map f m1)[x] (map f m2)[x]) as [Heq | Heq];
        rewrite Heq in Hfx; left + right; lia. }
      rewrite lub_In in Hin. rewrite <- Hfx.
      destruct Hin as [Hin | Hin]; rewrite map_In in Hin; destruct Hin as [y [Heq Hin]]; rewrite Heq, lub_spec;
      apply Max.max_lub; apply map_sub_compat; apply lub_subset_l + apply lub_subset_r.
    Qed.
    
    Lemma map_from_elements :
      forall l, map f (from_elements l) == from_elements (List.map (fun xn => (f (fst xn), snd xn)) l).
    Proof using Hf M.
    induction l as [| [x n] l].
    - apply map_empty.
    - simpl from_elements. rewrite map_add. f_equiv. apply IHl.
    Qed.
    
    Lemma map_support : forall m, inclA equiv (support (map f m)) (List.map f (support m)).
    Proof using Hf M.
    apply ind.
    * repeat intro. msetdec.
    * intros m x n Hin Hn Hrec. rewrite map_add; trivial. repeat rewrite support_add; try lia.
      destruct (In_dec x m); try contradiction. destruct (In_dec (f x) (map f m)).
      + intros y Hy. simpl. right. now apply Hrec.
      + intros y Hy. simpl. inversion_clear Hy.
        - left. auto.
        - right. now apply Hrec.
    * now rewrite map_empty, support_empty.
    Qed.
    
    Lemma map_cardinal : forall m, cardinal (map f m) = cardinal m.
    Proof using Hf M.
    apply ind.
    + repeat intro. msetdec.
    + intros m x n Hin Hn Hrec. rewrite (map_add _). do 2 rewrite cardinal_add. now rewrite Hrec.
    + now rewrite map_empty.
    Qed.
    
    Lemma map_size : forall m, size (map f m) <= size m.
    Proof using Hf M.
    apply ind.
    + repeat intro. msetdec.
    + intros m x n Hm Hn Hrec. rewrite map_add, size_add, size_add; trivial.
      destruct (In_dec x m) as [Hin | Hin], (In_dec (f x) (map f m)) as [Hinf | Hinf].
      - apply Hrec.
      - elim Hinf. rewrite map_In. now exists x.
      - lia.
      - lia.
    + now rewrite map_empty.
    Qed.
    
    Section map_injective_results.
      Hypothesis Hf2 : injective equiv equiv f.
      
      Lemma map_injective_spec : forall x m, (map f m)[f x] = m[x].
      Proof using Hf Hf2 M.
      intros x m. unfold map. apply fold_rect.
      + repeat intro. msetdec.
      + now do 2 rewrite empty_spec.
      + intros y m' acc Hin Hm Heq. destruct (equiv_dec x y) as [Hxy | Hxy].
        - msetdec.
        - repeat rewrite add_other; trivial. intro Habs. apply Hxy. now apply Hf2.
      Qed.
      
      Corollary map_injective_In : forall x m, In (f x) (map f m) <-> In x m.
      Proof using Hf Hf2 M.
      intros x m. rewrite map_In; trivial. split; intro Hin.
      + destruct Hin as [y [Heq Hin]]. apply Hf2 in Heq. now rewrite Heq.
      + now exists x.
      Qed.
      
      Lemma map_injective_remove : forall x n m, map f (remove x n m) == remove (f x) n (map f m).
      Proof using Hf Hf2 M.
      intros x n m. destruct (Compare_dec.le_dec n m[x]) as [Hle | Hlt].
      * now apply map_remove1.
      * intro y. msetdec.
        + repeat rewrite map_injective_spec; trivial. msetdec.
        + destruct (In_dec y (map f m)) as [Hin | Hin].
          - rewrite (map_In _) in Hin. destruct Hin as [z [Heq Hz]]. msetdec.
            repeat rewrite map_injective_spec; trivial. msetdec.
          - rewrite not_In in Hin. rewrite Hin, <- not_In, (map_In _).
            intros [z [Heq Hz]]. msetdec. rewrite map_injective_spec in Hin; trivial. lia.
      Qed.
      
      Theorem map_injective_inter : forall m??? m???, map f (inter m??? m???) == inter (map f m???) (map f m???).
      Proof using Hf Hf2 M.
      intros m??? m??? x. destruct ((inter (map f m???) (map f m???))[x]) eqn:Hn.
      + rewrite <- not_In in Hn |- *. intro Habs. apply Hn.
        rewrite (map_In _) in Habs. destruct Habs as [y [Heq Hy]]. msetdec.
        unfold gt in *. rewrite Nat.min_glb_lt_iff in *. now repeat rewrite map_injective_spec.
      + rewrite inter_spec in Hn.
        assert (Hx : In x (map f m???)).
        { msetdec. }
        rewrite map_In in *; trivial. destruct Hx as [y [Heq Hy]]. msetdec.
        do 2 (rewrite map_injective_spec in *; trivial). msetdec.
      Qed.
      
      Theorem map_injective_diff : forall m??? m???, map f (diff m??? m???) == diff (map f m???) (map f m???).
      Proof using Hf Hf2 M.
      intros m??? m??? x. destruct ((diff (map f m???) (map f m???))[x]) eqn:Hn.
      + rewrite <- not_In in Hn |- *. intro Habs. apply Hn.
        rewrite (map_In _) in Habs. destruct Habs as [y [Heq Hy]]. msetdec.
        now repeat rewrite map_injective_spec.
      + assert (Hx : In x (map f m???)) by msetdec.
        rewrite map_In in *; trivial. destruct Hx as [y [Heq _]]. msetdec.
        do 2 (rewrite map_injective_spec in *; trivial). msetdec.
      Qed.
      
      Lemma map_injective_lub_wlog : forall x m??? m???, (map f m???)[x] <= (map f m???)[x] ->
        (map f (lub m??? m???))[x] = (map f m???)[x].
      Proof using Hf Hf2 M.
      intros x m??? m??? Hle. destruct (map f m???)[x] eqn:Heq1.
      - apply Le.le_n_0_eq in Hle. symmetry in Hle. destruct (map f (lub m??? m???))[x] eqn:Heq2; trivial.
        assert (Hin : In x (map f (lub m??? m???))). { unfold In. lia. }
        rewrite map_In in Hin. destruct Hin as [y [Heq Hin]]. rewrite Heq in *. rewrite lub_In in Hin.
        rewrite map_injective_spec in *. unfold In in *. destruct Hin; lia.
      - assert (Hin : In x (map f m???)). { unfold In. lia. }
        rewrite map_In in Hin. destruct Hin as [y [Heq Hin]]. rewrite Heq, map_injective_spec in *.
        rewrite lub_spec. rewrite Nat.max_l; lia.
      Qed.
      
      Theorem map_injective_lub : forall m??? m???, map f (lub m??? m???) == lub (map f m???) (map f m???).
      Proof using Hf Hf2 M.
      intros m??? m??? x. rewrite lub_spec. apply Max.max_case_strong; intro Hle.
      - now apply map_injective_lub_wlog.
      - rewrite lub_comm. now apply map_injective_lub_wlog.
      Qed.
      
      Lemma map_injective : injective equiv equiv (map f).
      Proof using Hf Hf2 M. intros ? ? Hm x. specialize (Hm (f x)). repeat (rewrite map_injective_spec in Hm; trivial). Qed.
      
      Lemma map_injective_subset : forall m??? m???, map f m??? [<=] map f m??? <-> m??? [<=] m???.
      Proof using Hf Hf2 M.
      intros m??? m???. split; intro Hincl.
      - intro x. setoid_rewrite <- map_injective_spec. apply Hincl.
      - now apply map_sub_compat.
      Qed.
      
      Lemma map_injective_elements : forall m,
        PermutationA eq_pair (elements (map f m)) (List.map (fun xn => (f (fst xn), snd xn)) (elements m)).
      Proof using Hf Hf2 M.
      assert (Proper (eq_pair ==> eq_pair) (fun xn => (f (fst xn), snd xn))). { intros ? ? Heq. now rewrite Heq. }
      apply ind.
      + repeat intro. msetdec.
      + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite elements_add_out; trivial.
        - simpl. now constructor.
        - rewrite (map_In _). intros [y [Heq Hy]]. apply Hf2 in Heq. apply Hin. now rewrite Heq.
      + now rewrite map_empty, elements_empty.
      Qed.
      
      Lemma map_injective_support : forall m, PermutationA equiv (support (map f m)) (List.map f (support m)).
      Proof using Hf Hf2 M.
      apply ind.
      * repeat intro. msetdec.
      * intros m x n Hin Hrec. rewrite map_add; trivial. repeat rewrite support_add; try lia.
        destruct (InA_dec (eqA:=equiv) equiv_dec (f x) (support (map f m))) as [Habs | _].
        + rewrite support_spec in Habs. unfold In in *. rewrite map_injective_spec in Habs. contradiction.
        + destruct (InA_dec (eqA:=equiv) equiv_dec x (support m)) as [Habs | _].
          - rewrite support_spec in Habs. unfold In in *. contradiction.
          - simpl. destruct (In_dec x m); try contradiction. rewrite <- map_injective_In in Hin; trivial.
            destruct (In_dec (f x) (map f m)); try contradiction. now apply PermutationA_cons.
      * now rewrite map_empty, support_empty.
      Qed.
      
      Lemma map_injective_size : forall m, size (map f m) = size m.
      Proof using Hf Hf2 M.
      apply ind.
      + repeat intro. msetdec.
      + intros m x n Hin Hn Hrec. rewrite (map_add _). rewrite size_add, Hrec; trivial.
        destruct (In_dec (f x) (map f m)) as [Hinf | Hinf].
        - rewrite map_In in Hinf; trivial. destruct Hinf as [y [Heq Hiny]].
          apply Hf2 in Heq. rewrite Heq in Hin. contradiction.
        - rewrite size_add; trivial. destruct (In_dec x m); reflexivity || contradiction.
      + now rewrite map_empty.
      Qed.
      
    End map_injective_results.
  End map_results.
  
  Lemma map_extensionality_compat : forall f g, Proper (equiv ==> equiv) f ->
    (forall x, equiv (g x) (f x)) -> forall m, map g m == map f m.
  Proof using M.
  intros f g Hf Hext m x.
  assert (Hg : Proper (equiv ==> equiv) g). { intros ? ? Heq. do 2 rewrite Hext. now apply Hf. }
  repeat rewrite map_spec; trivial. f_equiv. apply nfilter_extensionality_compat.
  - intros y z Heq _ _ _. destruct (equiv_dec (g y) x), (equiv_dec (g z) x); trivial; rewrite Heq in *; contradiction.
  - intros y _. destruct (equiv_dec (f y) x), (equiv_dec (g y) x); trivial; rewrite Hext in *; contradiction.
  Qed.
  
  Lemma map_extensionality_compat_strong : forall f g, Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) g ->
    forall m, (forall x, In x m -> equiv (g x) (f x)) -> map g m == map f m.
  Proof using M.
  intros f g Hf Hg m Hext x.
  repeat rewrite map_spec; trivial. f_equiv. apply nfilter_extensionality_compat_strong.
  - intros y z Heq _ _ _. destruct (equiv_dec (g y) x), (equiv_dec (g z) x); trivial; rewrite Heq in *; contradiction.
  - intros y z Heq _ _ _. destruct (equiv_dec (f y) x), (equiv_dec (f z) x); trivial; rewrite Heq in *; contradiction.
  - intros y Hin. destruct (equiv_dec (f y) x), (equiv_dec (g y) x); rewrite Hext in *; trivial; contradiction.
  Qed.
  
  Lemma map_merge : forall f g, Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) g ->
    forall m, map f (map g m) == map (fun x => f (g x)) m.
  Proof using M.
  intros f g Hf Hg.
  apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. repeat rewrite map_add; refine _. now rewrite Hrec.
  + now repeat rewrite map_empty.
  Qed.
  
  Lemma map_id : forall m, map id m == m.
  Proof using M.
  intro m. intro x. change x with (id x) at 1.
  rewrite map_injective_spec; autoclass; []. now repeat intro.
  Qed.
  
  Theorem map_injective_fold : forall A eqA, Equivalence eqA ->
    forall f g, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
    Proper (equiv ==> equiv) g -> injective equiv equiv g ->
    forall m (i : A), eqA (fold f (map g m) i) (fold (fun x => f (g x)) m i).
  Proof using M.
  intros A eqA HeqA f g Hf Hf2 Hg Hg2 m.
  assert (Hfg2 : transpose2 eqA (fun x => f (g x))). { repeat intro. apply Hf2. }
  pattern m. apply ind.
  + intros m??? m??? Hm. split; intros Heq i; rewrite fold_compat; trivial;
    solve [rewrite Heq; now apply fold_compat; refine _ | now rewrite Hm | reflexivity].
  + intros m' x n Hin Hn Hrec i. rewrite fold_compat; try apply map_add; reflexivity || trivial.
    repeat rewrite fold_add; trivial; refine _.
    - now rewrite Hrec.
    - rewrite (map_In _). intros [y [Heq Hy]]. apply Hin. apply Hg2 in Heq. now rewrite Heq.
  + intro. rewrite fold_compat; apply map_empty || reflexivity || trivial. now do 2 rewrite fold_empty.
  Qed.
  
  Lemma map_injective_nfilter : forall f g, compatb f -> Proper (equiv ==> equiv) g -> injective equiv equiv g ->
    forall m, nfilter f (map g m) == map g (nfilter (fun x => f (g x)) m).
  Proof using M.
  intros f g Hf Hg Hg2. apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite nfilter_add; trivial.
    - destruct (f (g x) n).
        now rewrite map_add, Hrec.
        apply Hrec.
    - refine _. 
    - rewrite (map_In _). intros [y [Heq Hy]]. apply Hg2 in Heq. apply Hin. now rewrite Heq.
  + rewrite map_empty. now rewrite nfilter_empty, nfilter_empty, map_empty; autoclass.
  Qed.
  
  Lemma map_injective_npartition_fst : forall f g, compatb f -> Proper (equiv ==> equiv) g -> injective equiv equiv g ->
    forall m, fst (npartition f (map g m)) == map g (fst (npartition (fun x => f (g x)) m)).
  Proof using M. intros. repeat rewrite npartition_spec_fst; refine _. now apply map_injective_nfilter. Qed.
  
  Lemma map_injective_npartition_snd : forall f g, compatb f -> Proper (equiv ==> equiv) g -> injective equiv equiv g ->
    forall m, snd (npartition f (map g m)) == map g (snd (npartition (fun x => f (g x)) m)).
  Proof using M.
  intros. repeat rewrite npartition_spec_snd; refine _. apply map_injective_nfilter; trivial. repeat intro. msetdec.
  Qed.
  
  Lemma map_injective_for_all : forall f g, compatb f -> Proper (equiv ==> equiv) g -> injective equiv equiv g ->
    forall m, for_all f (map g m) = for_all (fun x => f (g x)) m.
  Proof using M.
  intros f g Hf Hg Hg2. apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite for_all_add; trivial.
    - now rewrite Hrec.
    - refine _.
    - now rewrite map_injective_In.
  + rewrite map_empty. repeat rewrite for_all_empty; autoclass.
  Qed.
  
  Lemma map_injective_exists : forall f g, compatb f -> Proper (equiv ==> equiv) g -> injective equiv equiv g ->
    forall m, exists_ f (map g m) = exists_ (fun x => f (g x)) m.
  Proof using M.
  intros f g Hf Hg Hg2. apply ind.
  + repeat intro. msetdec.
  + intros m x n Hin Hn Hrec. rewrite (map_add _). repeat rewrite exists_add; trivial.
    - now rewrite Hrec.
    - refine _. 
    - rewrite (map_In _). intros [y [Heq Hy]]. apply Hg2 in Heq. apply Hin. now rewrite Heq.
  + rewrite map_empty. repeat rewrite exists_empty; autoclass.
  Qed.
  
  Theorem map_filter : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> equiv) g ->
    forall m, filter f (map g m) == map g (filter (fun x => f (g x)) m).
  Proof using M.
  intros f g Hf Hg. apply ind.
  + intros m1 m2 Hm. now rewrite Hm.
  + intros m x n Hin Hn Hrec. rewrite map_add, 2 filter_add; autoclass; [].
    destruct (f (g x)).
    - rewrite map_add; trivial; []. f_equiv. apply Hrec.
    - apply Hrec.
  + rewrite map_empty, 2 filter_empty, map_empty; autoclass; reflexivity.
  Qed.
  
  Lemma map_partition_fst : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> equiv) g ->
    forall m, fst (partition f (map g m)) == map g (fst (partition (fun x => f (g x)) m)).
  Proof using M. intros. rewrite 2 partition_spec_fst; try apply map_filter; autoclass. Qed.
  
  Lemma map_partition_snd : forall f g, Proper (equiv ==> Logic.eq) f -> Proper (equiv ==> equiv) g ->
    forall m, snd (partition f (map g m)) == map g (snd (partition (fun x => f (g x)) m)).
  Proof using M. intros. rewrite 2 partition_spec_snd; try apply map_filter; autoclass. Qed.
  
  (** **  Function [max] and its properties  **)
  
  (** ***  Function [max_mult] computing the maximal multiplicity  **)
  
  (** Return the maximal multiplicity *)
  Definition max_mult m := fold (fun _ => Nat.max) m 0%nat.
  
  Instance max_mult_compat : Proper (equiv ==> Logic.eq) max_mult.
  Proof using M.
  unfold max_mult. intros m1 m2 Heq. apply fold_compat; autoclass.
  - repeat intro. now subst.
  - intros _ _ n m p. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
  Qed.
  
  Lemma max_mult_empty : max_mult empty = 0.
  Proof using M. unfold max_mult. now rewrite fold_empty. Qed.
  
  Lemma max_mult_singleton : forall x n, max_mult (singleton x n) = n.
  Proof using M.
  intros x n. destruct n.
  - rewrite singleton_0. apply max_mult_empty.
  - unfold max_mult. rewrite fold_singleton; auto with arith.
    repeat intro. now subst.
  Qed.
  
  Lemma max_mult_add : forall m x n, ~In x m ->
    max_mult (add x n m) = Nat.max n (max_mult m).
  Proof using M.
  intros m x n. destruct (Nat.eq_dec n 0).
  + subst n. now rewrite add_0, Nat.max_0_l.
  + unfold max_mult. apply fold_add; autoclass.
    - repeat intro. now subst.
    - repeat intro. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2.
    - lia.
  Qed.
  
  Theorem max_mult_spec_weak : forall m x, (m[x] <= max_mult m)%nat.
   Proof using M.
   intro m. pattern m. apply ind; clear m.
   * intros m1 m2 Hm. now setoid_rewrite Hm.
  * intros m x n Hout Hn Hrec y. rewrite max_mult_add; trivial.
    assert (Hx : m[x] = 0%nat). { rewrite not_In in Hout. assumption. }
    destruct (equiv_dec y x) as [Hxy | Hxy].
    + rewrite Hxy. rewrite add_spec, Hx. msetdec.
    + rewrite add_other; auto. transitivity (max_mult m).
      - apply Hrec.
      - apply Max.le_max_r.
  * intro x. rewrite empty_spec. lia.
  Qed.
  
  (* When [m] is empty, we need an arbitrary element as withness for [y]. *)
  Theorem max_mult_spec : forall (dummy : elt) m, (forall x, m[x] <= max_mult m) /\ (exists y, max_mult m = m[y]).
  Proof using M.
  intros dummy m. pattern m. apply ind; clear m.
  * intros m1 m2 Hm. now setoid_rewrite Hm.
  * intros m x n Hout Hn [Hall [y Hy]]. rewrite max_mult_add; trivial.
    assert (Hx : m[x] = 0%nat) by now rewrite not_In in Hout.
    split; try intro z.
    + destruct (equiv_dec z x) as [Hzx | Hzx].
      - rewrite Hzx. rewrite add_spec, Hx. msetdec.
      - rewrite add_other; trivial; [].
        transitivity (max_mult m); apply Hall || apply Max.le_max_r.
    + rewrite Hy. destruct (Compare_dec.le_dec n m[y]).
      - exists y. rewrite max_r; trivial; [].
        destruct (equiv_dec y x) as [Hyx | Hyx].
        -- rewrite Hyx in *. rewrite add_same. lia.
        -- now rewrite add_other.
      - exists x. rewrite max_l, add_same; lia.
  * split.
    + intro x. rewrite empty_spec. lia.
    + exists dummy. now rewrite empty_spec, max_mult_empty.
  Qed.
  
  Theorem max_mult_unique : forall m n, (forall x, m[x] <= n) -> (exists y, n = m[y]) -> n = max_mult m.
  Proof using M.
  intro m. unfold max_mult.
  pattern (fold (fun _ : elt => Init.Nat.max) m 0). apply fold_rect.
  * intros ? ? ? Heq. now setoid_rewrite Heq.
  * intros ? _ []. subst. apply empty_spec.
  * intros x m' acc Hin Hout Hrec n Hall [y Hy].
    subst. rewrite not_In in Hout.
    destruct (equiv_dec y x) as [Hyx | Hyx].
    + rewrite Hyx, add_same, Hout, max_l; trivial; [].
      destruct (max_mult_spec x m') as [Hall' Hex'].
      rewrite <- (Hrec _ Hall' Hex').
      destruct Hex' as [y' Hy']. rewrite Hy'.
      destruct (Nat.eq_dec (m'[y']) 0); try lia; [].
      specialize (Hall y').
      rewrite Hyx, add_same, add_other, Hout in Hall; trivial; [].
      msetdec.
    + rewrite (add_other x); trivial; [].
      rewrite <- (Hrec m'[y]), max_r; trivial.
      - specialize (Hall x). msetdec.
      - intro z. specialize (Hall z). rewrite add_spec in Hall. msetdec.
      - eauto.
  Qed.
  
  Lemma max_mult_upper_bound : forall m n, (forall x, m[x] <= n) -> max_mult m <= n.
  Proof using M.
  intro m. unfold max_mult.
  pattern (fold (fun _ : elt => Init.Nat.max) m 0). apply fold_rect.
  + intros ? ? ? Heq. now setoid_rewrite Heq.
  + intros. lia.
  + intros x m' acc Hin Hout Hrec n Hall.
    rewrite not_In in Hout. rewrite Nat.max_lub_iff. split.
    - specialize (Hall x). now rewrite add_same, Hout in Hall.
    - apply Hrec. intro y. erewrite add_subset. apply Hall.
  Qed.
  
  Lemma max_mult_0 : forall m, max_mult m = 0%nat <-> m == empty.
  Proof using M.
  intro m. split; intro Heq.
  + destruct (empty_or_In_dec m) as [? | [x Hin]]; trivial.
    elim (Nat.lt_irrefl 0). apply Nat.lt_le_trans with m[x].
    - exact Hin.
    - rewrite <- Heq. apply max_mult_spec_weak.
  + rewrite Heq. apply max_mult_empty.
  Qed.
  
  Instance max_mult_sub_compat : Proper (Subset ==> le) max_mult.
  Proof using M.
  intros m1 m2. revert m1. pattern m2. apply ind; clear m2.
  * intros ? ? Heq. now setoid_rewrite Heq.
  * intros m2 x n Hin Hn Hrec m1 Hsub.
    assert (Hle := Hsub x). rewrite add_same in Hle. unfold In in *.
    rewrite <- (add_remove_id x (n := n) m1).
    + rewrite 2 max_mult_add; trivial.
      - rewrite <- remove_subset_add in Hsub. apply Nat.max_le_compat; auto; lia.
      - rewrite remove_In. intuition.
    + replace n with (m2[x] + n) by lia. rewrite <- (add_same x n m2). apply Hsub.
  * intros m Hm. rewrite subset_empty_r in Hm. now rewrite Hm.
  Qed.
  
  Corollary max_mult_add_le : forall x n m, max_mult m <= max_mult (add x n m).
  Proof using M. intros. apply max_mult_sub_compat. apply add_subset. Qed.
  
  Corollary max_mult_remove_le : forall x n m, max_mult (remove x n m) <= max_mult m.
  Proof using M. intros. apply max_mult_sub_compat. apply remove_subset. Qed.
  
  Lemma max_mult_add_cases : forall x n m, (m[x] + n <= max_mult m <-> max_mult (add x n m) = max_mult m)
                                        /\ (max_mult m <= m[x] + n <-> max_mult (add x n m) = m[x] + n).
  Proof using M.
  intros x n m. revert x n. pattern m. apply ind; clear m.
  * intros ? ? Heq. now setoid_rewrite Heq.
  * intros m x n Hx Hn Hrec y p. rewrite (max_mult_add _ Hx) in *.
    destruct (equiv_dec y x) as [Hyx | Hyx].
    + rewrite Hyx. rewrite add_same, add_merge.
      rewrite (max_mult_add _ Hx) in *.
      assert (Hmx : m[x] = 0). { unfold In in *. lia. }
      rewrite Hmx in *. simpl. repeat split; intro Hle.
      - apply Nat.max_le in Hle. destruct Hle.
        -- assert (p = 0) by lia. subst. reflexivity.
        -- repeat rewrite max_r; trivial; lia.
      - rewrite <- Hle, Nat.add_comm. apply Nat.le_max_l.
      - apply Max.max_lub_r in Hle. rewrite max_l; lia.
      - rewrite <- Hle. apply Nat.max_le_compat; lia.
    + rewrite add_other in *; trivial; [].
      rewrite add_comm, max_mult_add; try (now rewrite add_In; intuition); [].
      destruct (Hrec y p) as [Hrec1 Hrec2], (Compare_dec.le_dec (m[y] + p) (max_mult m)) as [Hle | Hlt].
      - repeat split; intro; auto.
        -- rewrite Hrec1 in Hle. now rewrite Hle.
        -- etransitivity; eauto using Nat.le_max_r.
        -- rewrite Hrec1 in Hle. rewrite Hle.
           apply Nat.le_antisymm; trivial; []. rewrite Nat.max_le_iff. tauto.
        -- rewrite Hrec1 in Hle. rewrite Hle in *. lia.
      - rewrite (proj1 Hrec2); try lia.
  * intros x n. rewrite empty_spec, max_mult_empty, add_empty, max_mult_singleton in *. lia.
  Qed.
  
  Corollary max_mult_add1 : forall x n m, m[x] + n <= max_mult m <-> max_mult (add x n m) = max_mult m.
  Proof using M. intros. now apply max_mult_add_cases. Qed.
  
  Corollary max_mult_add2 : forall x n m, max_mult m <= m[x] + n <-> max_mult (add x n m) = m[x] + n.
  Proof using M. intros. now apply max_mult_add_cases. Qed.
  
  Corollary max_mult_remove_all_le : forall x m, max_mult (remove_all x m) <= max_mult m.
  Proof using M. intros. apply max_mult_remove_le. Qed.
  
  Lemma max_mult_remove : forall x n m, m[x] < max_mult m -> max_mult (remove x n m) = max_mult m.
  Proof using M.
  intros x n m. revert x n. pattern m. apply ind; clear m.
  * intros ? ? Heq. now setoid_rewrite Heq.
  * intros m y p Hy Hn Hrec x n.
    destruct (equiv_dec x y) as[Hxy | Hxy].
    + assert (Hmx : m[x] = 0). { unfold In in *. rewrite Hxy. lia. }
      rewrite <- Hxy in *. rewrite add_same, Hmx.
      repeat rewrite max_mult_add, Nat.max_lt_iff; trivial; []. simpl.
      destruct (Compare_dec.le_dec n p) as [Hle | Hlt].
      - rewrite remove_add1, max_mult_add; trivial; [].
        intro. rewrite 2 max_r; lia.
      - rewrite remove_add2; try lia. intro.
        rewrite Hrec, max_r; lia.
    + rewrite add_other, remove_add_comm, 2 max_mult_add, Nat.max_lt_iff; trivial.
      - intro. destruct (Compare_dec.le_dec p (max_mult m)).
        -- rewrite Hrec; lia.
        -- assert (Hle := max_mult_remove_le x n m). rewrite 2 max_l; lia.
      - rewrite remove_In. intuition.
  * intros * Habs. rewrite empty_spec, max_mult_empty in Habs. lia.
  Qed.
  
  Corollary max_mult_remove_all : forall x m, m[x] < max_mult m -> max_mult (remove_all x m) = max_mult m.
  Proof using M. intros. unfold remove_all. now apply max_mult_remove. Qed.
  
  Lemma max_mult_union : forall m??? m???,
    Nat.max (max_mult m???) (max_mult m???) <= max_mult (union m??? m???) <= max_mult m??? + max_mult m???.
  Proof using M.
  intros m??? m???. split.
  + apply Max.max_lub; f_equiv; intro; msetdec.
  + apply max_mult_upper_bound.
    intro. msetdec. apply Nat.add_le_mono; apply max_mult_spec_weak.
  Qed.
  
  Lemma max_mult_inter : forall m??? m???, max_mult (inter m??? m???) <= Nat.min (max_mult m???) (max_mult m???).
  Proof using M. intros. rewrite Nat.min_glb_iff. split; f_equiv; intro; msetdec; auto with arith. Qed.
  
  Lemma max_mult_diff : forall m??? m???, max_mult (diff m??? m???) <= max_mult m???.
  Proof using M. intros. f_equiv. intro. msetdec. Qed.
  
  Lemma max_mult_lub : forall m??? m???, max_mult (lub m??? m???) = Nat.max (max_mult m???) (max_mult m???).
  Proof using M.
  intros m??? m???. symmetry.
  destruct (empty_or_In_dec m???) as [| [x ?]].
  * msetdec. now rewrite lub_empty_l, max_mult_empty.
  * apply max_mult_unique.
    + intro. msetdec. apply Nat.max_le_compat; apply max_mult_spec_weak.
    + destruct (max_mult_spec x m???) as [Hall??? [y??? Hy???]], (max_mult_spec x m???) as [Hall??? [y??? Hy???]].
      destruct (Compare_dec.le_dec (max_mult m???) (max_mult m???)).
      - exists y???. specialize (Hall??? y???). rewrite lub_spec, 2 max_r; lia.
      - exists y???. specialize (Hall??? y???). rewrite lub_spec, 2 max_l; lia.
  Qed.
  
  (* 
  Lemma max_mult_nfilter : forall f, compatb f ->
    forall m, max_mult (nfilter f m) = fold (fun x n acc => if f x n then Nat.max n acc else acc) m 0.
  Proof.
  intros f Hf m. unfold max_mult. rewrite fold_nfilter; autoclass.
  - repeat intro. now subst.
  - repeat intro. rewrite Nat.max_comm, <- Nat.max_assoc. f_equiv. apply Nat.max_comm.
  Qed.
  
  Lemma max_mult_filter : forall f, Proper (equiv ==> Logic.eq) f ->
    forall m, max_mult (filter f m) = fold (fun x n acc => if f x then Nat.max n acc else acc) m 0.
  Proof.
  intros. rewrite filter_nfilter; trivial; []. apply max_mult_nfilter.
  intros ? ? Heq ? ? ?. now rewrite Heq.
  Qed.
   *)
  
  Lemma max_mult_map_injective_invariant : forall f, Proper (equiv ==> equiv) f -> injective equiv equiv f ->
    forall m, max_mult (map f m) = max_mult m.
  Proof using M.
  intros f Hf Hinj. apply ind.
  + intros m1 m2 Hm. now rewrite Hm.
  + intros s x n Hout Hn Hrec. rewrite map_add; try now intros ? ? Heq; rewrite Heq.
    assert (Haux : elt -> elt ->
              forall n m a : nat, Init.Nat.max m (Init.Nat.max n a) = Init.Nat.max n (Init.Nat.max m a)).
    { intros _ _ n' m' p'. do 2 rewrite Nat.max_assoc. now setoid_rewrite Nat.max_comm at 2. }
    unfold max_mult in *. repeat rewrite fold_add; trivial; refine _; try now (hnf; auto).
    intro Habs. apply Hout. apply map_In in Habs.
    - destruct Habs as [y [Heq Hin]]. apply Hinj in Heq. now rewrite Heq.
    - intros ? ? Heq. now rewrite Heq.
  + now rewrite map_empty.
  Qed.
  
  (** ***  Function [max s] returning the elements of a multiset with maximal multiplicity  **)
  
  Definition max_aux x n acc :=
      match Nat.compare n (fst acc) with
        | Lt => acc
        | Eq => (fst acc, add x n (snd acc))
        | gt => (n, singleton x n)
      end.
  Definition max m := snd (fold max_aux m (0, empty)).
  
  Instance eqb_max_mult_compat m : Proper (equiv ==> Logic.eq ==> Logic.eq) (fun _ => Nat.eqb (max_mult m)).
  Proof using . repeat intro. now subst. Qed.
  
  Instance eqb_max_compat : Proper (equiv ==> Logic.eq ==> Logic.eq ==> Logic.eq) (fun _ : elt => Init.Nat.max).
  Proof using . repeat intro. now subst. Qed.
  
  Local Hint Immediate eqb_max_mult_compat eqb_max_compat : core.
  
  (** A simple definition used for specification, proved to be equivalent to the efficient one. *)
  Definition simple_max m := nfilter (fun _ => Nat.eqb (max_mult m)) m.
  
  Instance simple_max_compat : Proper (equiv ==> equiv) simple_max.
  Proof using M.
  intros m1 m2 Heq. unfold simple_max.
  rewrite Heq. apply nfilter_extensionality_compat.
  - repeat intro. now subst.
  - intros _ n. now rewrite Heq.
  Qed.
  
  Instance max_aux_compat : Proper (equiv ==> Logic.eq ==> Logic.eq * equiv ==> Logic.eq * equiv) max_aux.
  Proof using M.
  intros m1 m2 Hm x y Hxy [] [] []. simpl in * |-. subst. unfold max_aux. cbn -[equiv].
  destruct_match; split; try reflexivity; cbn -[equiv]; trivial; now f_equiv.
  Qed.
  
  Lemma max_aux_transpose : transpose2 (Logic.eq * equiv)%signature max_aux.
  Proof using M.
  intros x y n p [k m]. unfold max_aux. cbn -[equiv].
  repeat (destruct_match; cbn -[equiv]);
  try rewrite ?Nat.compare_eq_iff, ?Nat.compare_lt_iff, ?Nat.compare_gt_iff in *;
  subst; split; cbn -[equiv]; lia || (now f_equiv) || trivial.
  - apply add_comm.
  - apply add_singleton_comm.
  Qed.
  
  Local Hint Resolve max_aux_transpose : core.
  
  Global Instance max_compat : Proper (equiv ==> equiv) max.
  Proof using M. intros m1 m2 Heq. unfold max. f_equiv. apply fold_compat; autoclass; reflexivity. Qed.
  
  Lemma max_mult_fst_max : forall m, max_mult m = fst (fold max_aux m (0, empty)).
  Proof using M.
  intro m. pattern m. apply ind; clear m.
  + intros m1 m2 Hm. rewrite Hm at 1.
    cut (fst (fold max_aux m1 (0, empty)) = fst (fold max_aux m2 (0, empty))); intuition; [].
    f_equiv. apply fold_compat; autoclass; reflexivity.
  + intros m x n Hin Hn Hrec.
    rewrite max_mult_add, Hrec; trivial; [].
    (* Anomaly with [rewrite fold_add] *)
    transitivity (fst (max_aux x n (fold max_aux m (0, empty)))).
    * unfold max_aux at 2. destruct_match; simpl.
      - rewrite Nat.compare_eq_iff in *. subst n. now rewrite Nat.max_id.
      - rewrite Nat.compare_lt_iff in *. rewrite max_r; lia.
      - rewrite Nat.compare_gt_iff in *. rewrite max_l; lia.
    * f_equiv. rewrite fold_add; autoclass; reflexivity.
  + unfold max_mult. now rewrite 2 fold_empty.
  Qed.
  
  Theorem max_simplified : forall m, max m == simple_max m.
  Proof using M.
  apply ind.
  + intros m1 m2 Hm. now rewrite Hm.
  + intros m x n Hin Hn Hrec. unfold max, simple_max.
    rewrite nfilter_add; auto; []. (* Anomaly with [rewrite fold_add] *)
    transitivity (snd (max_aux x n (fold max_aux m (0, empty)))).
    * f_equiv. rewrite fold_add; autoclass; reflexivity.
    * rewrite max_mult_add; trivial; []. unfold max_aux at 1. rewrite <- max_mult_fst_max.
      do 2 destruct_match; cbn -[equiv];
      rewrite ?Nat.compare_eq_iff, ?Nat.compare_lt_iff, ?Nat.compare_gt_iff,
              ?Nat.eqb_neq, ?Nat.eqb_eq in *; subst.
      - f_equiv. rewrite Hrec. apply nfilter_extensionality_compat;
        now autoclass; intros; rewrite Nat.max_id.
      - exfalso. rewrite Nat.max_id in *. tauto.
      - exfalso. rewrite max_r in *; lia.
      - rewrite Hrec. apply nfilter_extensionality_compat; autoclass; [].
        intros; rewrite max_r; reflexivity || lia.
      - cut (nfilter (fun _ : elt => Nat.eqb (Nat.max n (max_mult m))) m == empty);
          try (now intro Heq; rewrite Heq, add_empty); [].
        rewrite nfilter_none, for_all_spec; try (now repeat intro; subst); [].
        intros y p. rewrite Bool.negb_true_iff, Nat.eqb_neq.
        assert (Hmax := max_mult_spec_weak m y). lia.
      - exfalso. rewrite max_l in *; lia.
  + unfold max, simple_max. now rewrite fold_empty, nfilter_empty.
  Qed.
  
  Theorem max_spec : forall x m, (max m)[x] = if m[x] =? max_mult m then m[x] else 0.
  Proof using M.
  intros x m. rewrite max_simplified. unfold simple_max.
  rewrite nfilter_spec, Nat.eqb_sym; trivial; [].
  repeat intro. now subst.
  Qed.
  
  Theorem max_le : forall m x y, In y (max m) -> m[x] <= (max m)[y].
  Proof using M.
  intros m x y Hy. rewrite max_simplified in *. unfold simple_max in *.
  unfold In in Hy. rewrite nfilter_spec in Hy |- *; auto.
  destruct (max_mult m =? m[y]) eqn:Heq; try lia.
  rewrite Nat.eqb_eq in Heq. rewrite <- Heq. apply max_mult_spec_weak.
  Qed.
  
  Lemma max_subset : forall m, max m [<=] m.
  Proof using M.
  intros m x. rewrite max_simplified. unfold simple_max.
  setoid_rewrite nfilter_spec; try now repeat intro; subst.
  destruct (max_mult m =? m[x]); auto. lia.
  Qed.
  
  Theorem max_spec_non_nil : forall m x, In x m -> exists y, In y (max m).
  Proof using M.
  setoid_rewrite max_simplified.
  intro m. pattern m. apply ind; clear m.
  * intros m1 m2 Hm. now setoid_rewrite Hm.
  * intros m x n Hxnotinm Hpos HI x' Hx'.
    destruct (empty_or_In_dec m) as [Hm | [x'' Hx'']].
    + exists x. unfold simple_max. rewrite nfilter_In; auto. split.
      - rewrite add_In. left. split; reflexivity || lia.
      - rewrite Nat.eqb_eq, max_mult_add; trivial.
        rewrite Hm at 2.
        rewrite add_empty, singleton_spec.
        msetdec. rewrite max_mult_empty. apply Max.max_0_r.
    + specialize (HI x'' Hx'').
      destruct HI as [y Hy]. unfold max.
      setoid_rewrite nfilter_In; auto; [].
      rewrite max_mult_add; trivial.
      unfold simple_max in Hy. rewrite nfilter_In in Hy; auto.
      destruct Hy as [Hy Heq]. rewrite Nat.eqb_eq in Heq.
      destruct (Compare_dec.le_lt_dec n (m[y])).
      - exists y. split.
        -- msetdec.
        -- rewrite Nat.eqb_eq, Heq, add_other, Max.max_r; trivial.
           Fail now msetdec. (* BUG? *) intro Habs. msetdec.
      - exists x. split.
        -- msetdec.
        -- rewrite Nat.eqb_eq, Max.max_l; try lia. msetdec.
  * intros x Hin. elim (In_empty Hin).
  Qed.
  
  Lemma max_is_empty : forall m, max m == empty <-> m == empty.
  Proof using M.
  intro m. split; intro Heq.
  + destruct (empty_or_In_dec m) as [Hm | Hm].
    - intro. now rewrite Hm.
    - destruct Hm as [x Hx].
      destruct (max_spec_non_nil Hx) as [y Hy].
      unfold In in Hy. rewrite Heq, empty_spec in Hy. lia.
  + rewrite Heq. rewrite max_simplified. unfold simple_max.
    apply nfilter_empty; auto.
  Qed.
  
  Corollary max_empty : max empty == empty.
  Proof using M. now rewrite max_is_empty. Qed.
  
  Lemma max_singleton : forall x n, max (singleton x n) == singleton x n.
  Proof using M.
  intros x n. destruct n.
  + rewrite singleton_0. now rewrite max_empty.
  + rewrite max_simplified. unfold simple_max.
    rewrite nfilter_singleton_true; try lia.
    - rewrite max_mult_singleton. apply Nat.eqb_refl.
    - repeat intro. now subst.
  Qed.
  
  Theorem max_case : forall m x, (max m)[x] = 0 \/ (max m)[x] = m[x] /\ m[x] = max_mult m.
  Proof using M.
  intros m x. destruct (empty_or_In_dec m) as [Hm | Hm].
  + left. rewrite <- max_is_empty in Hm. rewrite (Hm x). apply empty_spec.
  + rewrite max_simplified. unfold simple_max. rewrite nfilter_spec.
    - destruct (max_mult m =? m[x]) eqn:Hcase; auto; [].
      right. split; trivial; []. now rewrite Nat.eqb_eq in *.
    - repeat intro. now subst.
  Qed.
  
  Lemma max_In_mult : forall m x, In x m -> (In x (max m) <-> (max m)[x] = m[x]).
  Proof using M. intros m x Hin. unfold In in *. destruct (max_case m x); lia. Qed.
  
  Lemma max_In_mult2 : forall m x, In x m -> (In x (max m) <-> (max m)[x] = max_mult m).
  Proof using M.
  intros m x Hin. rewrite max_In_mult; trivial; []. unfold In in *.
  destruct (max_case m x); try lia. split; intro; try lia; [].
  assert (Habs : max_mult m = 0) by congruence. rewrite max_mult_0 in Habs.
  rewrite Habs, empty_spec in Hin. lia.
  Qed.
  
  Lemma max_spec_mult : forall m x y, In x (max m) -> (In y (max m) <-> (max m)[y] = (max m)[x]).
  Proof using M.
  intros m x y Hx. split.
  + intro Hy. destruct (max_case m x) as [Hx' | Hx'], (max_case m y) as [Hy' | Hy'];
    (unfold In in *; lia) || (try congruence).
  + intro Heq. unfold In in *. now rewrite Heq.
  Qed.
  
  Lemma max_In : forall m x, In x (max m) -> m[x] = max_mult m.
  Proof using M. intros m x Hin. unfold In in *. destruct (max_case m x); lia. Qed.
  
  Theorem max_spec_lub : forall m x y,
    In x (max m) -> ~In y (max m) <-> (m[y] < m[x])%nat.
  Proof using M.
  intros m x y Hx. split; intro Hy.
  * apply le_neq_lt.
    + assert (Hx' := Hx). rewrite max_In_mult in Hx.
      - rewrite <- Hx. now apply max_le.
      - now rewrite <- max_subset.
    + intro Habs. apply Hy. rewrite max_simplified. unfold simple_max.
      rewrite nfilter_In; try now repeat intro; subst. split.
      - unfold In in *. rewrite Habs. apply Nat.lt_le_trans with (max m)[x]; trivial. apply max_subset.
      - rewrite Habs. rewrite max_simplified in*. unfold simple_max in Hx.
        rewrite nfilter_In in Hx; try now repeat intro; subst.
  * unfold In. destruct (max_case m y) as [? | [? ?]]; try lia.
    apply max_In in Hx. lia.
  Qed.
  
  Lemma max_max_mult : forall m x, ~m == empty -> In x (max m) <-> m[x] = max_mult m.
  Proof using M.
  intros m x Hm. rewrite max_simplified. split; intro Hx.
  + apply nfilter_In in Hx; auto.
    symmetry. apply Nat.eqb_eq. now destruct Hx.
  + unfold simple_max. rewrite nfilter_In; auto.
    split.
    - red. cut (m[x]<>0). lia.
      intro Habs. now rewrite Hx, max_mult_0 in Habs.
    - now rewrite Hx, <- EqNat.beq_nat_refl.
  Qed.
  
  Lemma max_max_mult_ex : forall m, ~m == empty -> exists x, max_mult m = m[x].
  Proof using M.
  intros m. pattern m. apply ind; clear m.
  * intros ? ? Heq. now setoid_rewrite Heq.
  * intros m x n Hout Hn Hrec _.
    destruct (empty_or_In_dec m) as [Hm | Hm].
    + exists x. rewrite Hm, add_empty. rewrite max_mult_singleton. msetdec.
    + assert (Hempty : m =/= empty) by now rewrite not_empty_In.
      destruct (Hrec Hempty) as [max_m Hmax_m]. rewrite max_mult_add; trivial.
      destruct (Max.max_spec n (max_mult m)) as [[Hmax1 Hmax2] | [Hmax1 Hmax2]].
      - exists max_m. msetdec.
      - exists x. msetdec.
  * intro Habs. Fail now msetdec. (* BUG? *) now elim Habs.
  Qed.
  
  Lemma max_In_mult3 : forall m x, In x m -> (In x (max m) <-> m[x] = max_mult m).
  Proof using M. intros. apply max_max_mult. intro. msetdec. Qed.
  
  Lemma max_is_singleton : forall x n m, 0 < n ->
    max m == singleton x n <-> n = m[x] /\ forall y, ~equiv y x -> m[y] < m[x].
  Proof using M.
  intros x n m Hn. split.
  + intro Hmax. split.
    - assert (Hx := Hmax x). rewrite singleton_same in Hx. rewrite <- Hx.
      rewrite <- max_In_mult; [| rewrite <- max_subset]; rewrite Hmax; apply In_singleton; intuition.
    - intros y Hy. rewrite <- max_spec_lub; msetdec.
  + intros [? Hlt]. subst.
    assert (Hmax : max_mult m = m[x]).
    { symmetry. apply max_mult_unique; eauto.
      intro y. specialize (Hlt y). destruct (equiv_dec y x); msetdec; intuition. }
    intro y. specialize (Hlt y). msetdec.
    - now rewrite <- max_In_mult, max_In_mult3.
    - destruct (max_case m y); intuition.
  Qed.
  
  Lemma max_is_id : forall m, max m == m <-> forall x, In x m -> m[x] = max_mult m.
  Proof using M.
  intro m. split.
  + intros Heq x Hin. rewrite <- Heq in Hin. now apply max_In.
  + intros Helt x. destruct (Nat.eq_dec m[x] 0) as [Hx | Hx].
    - rewrite Hx. cut ((max m)[x] <= 0); try lia. rewrite <- Hx. apply max_subset.
    - assert (In x m) by (unfold In; lia).
      rewrite <- max_In_mult, max_In_mult3; trivial; []. auto.
  Qed.
  
  Lemma max_spec_max : forall m x, ~m == empty -> (forall y, (m[y] <= m[x])) -> max_mult m = m[x].
  Proof using M.
  intros m x Hm Hmax. apply Nat.le_antisymm.
  - destruct (@max_max_mult_ex m) as [y Hy]; auto.
    rewrite Hy. apply Hmax.
  - apply max_mult_spec_weak.
  Qed.
  
  Corollary max_spec1_iff : forall m, m =/= empty -> forall x, In x (max m) <-> forall y, (m[y] <= m[x]).
  Proof using M.
  intros m Hm x. assert (Hempty := Hm).
  unfold complement in Hm. rewrite <- max_is_empty in Hm.
  change (max m =/= empty) in Hm. rewrite not_empty_In in Hm.
  destruct Hm as [z Hz].
  split; intro Hx.
  + intro y. assert (Hx' := Hx). rewrite max_In_mult in Hx.
    - rewrite <- Hx. now apply max_le.
    - now rewrite <- max_subset.
  + assert (Hmax := max_spec_max _ Hempty Hx). rewrite max_max_mult; auto.
  Qed.
  
  Lemma max_add_lt : forall x n m, m[x] + n < max_mult m -> max (add x n m) == max m.
  Proof using M.
  intros x n m Hn y.
  assert (Heq : max_mult (add x n m) = max_mult m).
  { rewrite <- max_mult_add1. lia. }
  rewrite 2 max_spec, Heq.
  destruct (equiv_dec y x) as [Hyx | Hyx].
  - rewrite Hyx in *. rewrite Hyx, add_same.
    do 2 destruct_match; rewrite ?Nat.eqb_eq, ?Nat.eqb_neq in *; lia.
  - now rewrite add_other.
  Qed.
  
  Lemma max_add_eq : forall x n m, 0 < n -> m[x] + n = max_mult m -> max (add x n m) == add x (m[x] + n) (max m).
  Proof using M.
  intros x n m ? Hn y.
  assert (Heq : max_mult (add x n m) = max_mult m).
  { rewrite <- max_mult_add1. lia. }
  rewrite max_spec, 2 add_spec, max_spec, Heq.
  destruct (equiv_dec y x) as [Hyx | Hyx].
  - rewrite Hyx, Hn, Nat.eqb_refl, Hyx. destruct_match; trivial; [].
    rewrite Nat.eqb_eq in *. lia.
  - reflexivity.
  Qed.
  
  Lemma max_add_gt : forall x n m, m[x] + n > max_mult m -> max (add x n m) == singleton x (m[x] + n).
  Proof using M.
  intros x n m Hn y.
  assert (Heq : max_mult (add x n m) = m[x] + n).
  { rewrite <- max_mult_add2. lia. }
  rewrite max_spec, add_spec, Heq.
  destruct (equiv_dec y x) as [Hyx | Hyx].
  - now rewrite Hyx, Nat.eqb_refl, singleton_same, Hyx.
  - rewrite singleton_other; trivial; [].
    destruct_match; trivial; []. rewrite Nat.eqb_eq in *.
    cut (m[y] < m[x] + n); try lia; [].
    apply Nat.le_lt_trans with (max_mult m); eauto. apply max_mult_spec_weak.
  Qed.
  
  Lemma max_remove : forall x n m, m[x] < max_mult m -> max (remove x n m) == max m.
  Proof using M.
  intros x n m. revert x n. pattern m. apply ind; clear m.
  * intros ? ? Heq. now setoid_rewrite Heq.
  * intros m y p Hy Hn Hrec x n.
    destruct (equiv_dec x y) as[Hxy | Hxy].
    + assert (Hmx : m[x] = 0). { unfold In in *. rewrite Hxy. lia. }
      rewrite <- Hxy in *. rewrite add_same, Hmx.
      repeat rewrite max_mult_add, Nat.max_lt_iff; trivial; [].
      destruct (Compare_dec.le_dec n p) as [Hle | Hlt].
      - intro. rewrite remove_add1, 2 max_add_lt; reflexivity || lia.
      - rewrite remove_add2; try lia; []. intro.
        rewrite Hrec, max_add_lt; reflexivity || lia.
    + rewrite add_other, remove_add_comm, max_mult_add, Nat.max_lt_iff; trivial; [].
      intro. rewrite not_In in Hy.
      destruct (Compare_dec.lt_eq_lt_dec p (max_mult m)) as [[Hlt | Heq] | Hlt].
      - rewrite 2 max_add_lt, Hrec; try reflexivity || lia; [].
        rewrite remove_other, max_mult_remove; lia || intuition.
      - subst p. rewrite 2 max_add_eq; try lia;
        rewrite remove_other, ?max_mult_remove, ?Hrec, ?Hy; lia || intuition.
      - rewrite 2 max_add_gt, remove_other; reflexivity || lia || (try now intuition); [].
        rewrite remove_other; generalize (max_mult_remove_le x n m); lia || intuition.
  * intros * Habs. rewrite empty_spec, max_mult_empty in Habs. lia.
  Qed.
  
  Lemma max_lub_le : forall m??? m???, max m??? [<=] max (lub m??? m???) \/ max m??? [<=] max (lub m??? m???).
  Proof using M.
  intros m??? m???. destruct (Compare_dec.le_dec (max_mult m???) (max_mult m???)) as [Hle | Hlt].
  + right. intro x. rewrite 2 max_spec, lub_spec, max_mult_lub. setoid_rewrite Nat.max_r at 2; trivial; [].
    destruct (m???[x] =? max_mult m???) eqn:Heq; auto with arith; [].
    rewrite max_r, Heq; trivial; [].
    rewrite Nat.eqb_eq in Heq. rewrite Heq. etransitivity; eauto using max_mult_spec_weak.
  + assert (Hle : max_mult m??? <= max_mult m???) by lia.
    left. intro x. rewrite 2 max_spec, lub_spec, max_mult_lub. setoid_rewrite Nat.max_l at 2; trivial; [].
    destruct (m???[x] =? max_mult m???) eqn:Heq; auto with arith; [].
    rewrite max_l, Heq; trivial; [].
    rewrite Nat.eqb_eq in Heq. rewrite Heq. etransitivity; eauto using max_mult_spec_weak.
  Qed.
  
  Lemma max_lub : forall m??? m???, max (lub m??? m???) [<=] lub (max m???) (max m???).
  Proof using M.
  intros m??? m??? x. rewrite lub_spec, 3 max_spec, lub_spec, max_mult_lub.
  destruct (Init.Nat.max m???[x] m???[x] =? Nat.max (max_mult m???) (max_mult m???)) eqn:Heq_max,
           (m???[x] =? max_mult m???) eqn:Heq1, (m???[x] =? max_mult m???) eqn:Heq2;
  auto with arith; rewrite ?Nat.eqb_eq, ?Nat.eqb_neq in *; rewrite ?Heq_max, ?Heq1, ?Heq2.
  + rewrite Nat.max_0_r.
    destruct (Compare_dec.le_dec (max_mult m???) (max_mult m???)) as [Hle | Hlt].
    - rewrite max_l; lia.
    - rewrite Heq1 in *. setoid_rewrite max_r at 2 in Heq_max; try lia.
  + rewrite Nat.max_0_l.
    destruct (Compare_dec.le_dec (max_mult m???) (max_mult m???)) as [Hle | Hlt].
    - rewrite Heq2 in *. setoid_rewrite max_l at 2 in Heq_max; try lia.
    - rewrite max_r; lia.
  + assert (Hle1 := max_mult_spec_weak m??? x). assert (Hle2 := max_mult_spec_weak m??? x).
    revert Heq_max. do 2 apply Nat.max_case_strong; intros; lia.
  Qed.
  
  Lemma fold_max : forall {A} eqA, Equivalence eqA ->
    forall f, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
    forall m (i : A), eqA (fold f (max m) i) (fold (fun x n acc => if n =? max_mult m then f x n acc else acc) m i).
  Proof using M.
  intros A eqA HeqA f Hf Hf2 m i.
  rewrite fold_compat; autoclass; try apply max_simplified; try reflexivity; [].
  unfold simple_max. rewrite fold_nfilter; autoclass; [].
  apply fold_extensionality_compat; autoclass.
  - repeat intro. subst. now destruct_match; try apply Hf.
  - intros x y n p i'. now repeat destruct_match.
  - intros. now rewrite Nat.eqb_sym.
  Qed.
  
  Lemma for_all_max : forall f, compatb f ->
    forall m, for_all f (max m) = for_all (fun x n => f x n || (n <? max_mult m))%bool m.
  Proof using M.
  intros f Hf m.
  assert (compatb (fun x n => (f x n || (n <? max_mult m))%bool)).
  { intros ? ? Heq ? ? ?. subst. now rewrite Heq. }
  destruct (for_all f (max m)) eqn:Hmax; symmetry.
  + rewrite for_all_spec in Hmax |- *; trivial; [].
    intros x Hin. destruct (m[x] <? max_mult m) eqn:Hlt; auto with bool; [].
    assert (Hx : m[x] = max_mult m).
    { rewrite Nat.ltb_nlt in *. apply Nat.le_antisymm; lia || apply max_mult_spec_weak. }
    rewrite Hx, Bool.orb_false_r.
    rewrite <- max_In_mult3 in Hx; trivial; []. specialize (Hmax x Hx).
    rewrite max_In_mult2 in Hx; trivial; []. now rewrite Hx in Hmax.
  + rewrite for_all_false in Hmax |- *; trivial; [].
    intro Hall. apply Hmax. intros x Hin. assert (Hmult := max_In _ Hin).
    rewrite max_spec, Hmult, Nat.eqb_refl, <- Hmult. rewrite (max_subset m) in Hin.
    apply Hall in Hin. now rewrite Hmult, Nat.ltb_irrefl, Bool.orb_false_r, <- Hmult in Hin.
  Qed.
  
  Lemma exists_max : forall f, compatb f ->
    forall m, exists_ f (max m) = exists_ (fun x n => f x n && (n =? max_mult m))%bool m.
  Proof using M.
  intros f Hf m.
  assert (compatb (fun x n => (f x n && (n =? max_mult m))%bool)).
  { intros ? ? Heq ? ? ?. subst. now rewrite Heq. }
  destruct (exists_ f (max m)) eqn:Hmax; symmetry.
  + rewrite exists_spec in Hmax |- *; trivial; [].
    destruct Hmax as [x [Hin Hfx]].
    assert (In x m) by now rewrite (max_subset m) in Hin.
    exists x. split; trivial; [].
    rewrite max_In_mult2 in Hin; trivial; []. rewrite Hin in Hfx.
    rewrite <- max_In_mult2 in Hin; trivial; []. apply max_In in Hin.
    now rewrite Hin, Hfx, Nat.eqb_refl.
  + rewrite exists_false in Hmax |- *; trivial; []. intros [x [Hin Hx]]. apply Hmax.
    rewrite Bool.andb_true_iff, Nat.eqb_eq in Hx. destruct Hx as [Hfx Heq].
    exists x. split; try rewrite max_In_mult3; auto; [].
    rewrite <- max_In_mult3, max_In_mult in Heq; trivial; []. now rewrite Heq.
  Qed.
  
  Lemma nfilter_max : forall f, compatb f ->
    forall m, nfilter f (max m) == nfilter (fun x n => f x n && (n =? max_mult m))%bool m.
  Proof using M.
  intros f Hf m x. rewrite 2 nfilter_spec, max_spec; trivial; [|].
  + destruct_match.
    - now destruct_match.
    - rewrite Bool.andb_false_r. now destruct_match.
  + intros ? ? Heq ? ? ?. subst. now rewrite Heq.
  Qed.
  
  Corollary filter_max : forall f, Proper (equiv ==> Logic.eq) f ->
    forall m, filter f (max m) == nfilter (fun x n => f x && (n =? max_mult m))%bool m.
  Proof using M.
  intros f Hf m x. rewrite filter_spec, nfilter_spec, max_spec; trivial; [|].
  + now destruct_match.
  + intros ? ? Heq ? ? ?. subst. now rewrite Heq.
  Qed.
  
  Lemma npartition_max_fst : forall f, compatb f ->
    forall m, fst (npartition f (max m)) == nfilter (fun x n => f x n && (n =? max_mult m))%bool m.
  Proof using M. intros. rewrite npartition_spec_fst; trivial; []. now apply nfilter_max. Qed.
  
  Lemma npartition_max_snd : forall f, compatb f ->
    forall m, snd (npartition f (max m)) == nfilter (fun x n => negb (f x n) && (n =? max_mult m))%bool m.
  Proof using M.
  intros. rewrite npartition_spec_snd; trivial; []. apply nfilter_max.
  intros ? ? Heq ? n ?. subst. now rewrite Heq.
  Qed.
  
  Corollary partition_max_fst : forall f, Proper (equiv ==> Logic.eq) f ->
    forall m, fst (partition f (max m)) == nfilter (fun x n => f x && (n =? max_mult m))%bool m.
  Proof using M. intros. rewrite partition_spec_fst; trivial; []. now apply filter_max. Qed.
  
  Lemma partition_max_snd : forall f, Proper (equiv ==> Logic.eq) f ->
    forall m, snd (partition f (max m)) == nfilter (fun x n => negb (f x) && (n =? max_mult m))%bool m.
  Proof using M. intros. rewrite partition_spec_snd; trivial; []. apply filter_max. intros ? ? Heq. now rewrite Heq. Qed.
  
  Theorem elements_max : forall m,
    PermutationA eq_pair (elements (max m)) (List.filter (fun xn => Nat.eqb (snd xn) (max_mult m)) (elements m)).
  Proof using M.
  intro m. apply NoDupA_equivlistA_PermutationA; autoclass.
  + apply (NoDupA_strengthen subrelation_pair_elt), elements_NoDupA.
  + apply NoDupA_filter_compat.
    - intros ? ? Heq. now rewrite Heq.
    - apply (NoDupA_strengthen subrelation_pair_elt), elements_NoDupA.
  + intros x. rewrite filter_InA; try (intros ? ? Heq; now rewrite Heq); [].
    rewrite 2 elements_spec, max_spec. destruct_match.
    - rewrite Nat.eqb_eq in *; intuition.
    - rewrite ?Nat.eqb_eq, ?Nat.eqb_neq in *. intuition.
  Qed.
  
  Lemma support_max : forall m, inclA equiv (support (max m)) (support m).
  Proof using M. intro. f_equiv. apply max_subset. Qed.
  
  Lemma cardinal_max : forall m, cardinal (max m) <= cardinal m.
  Proof using M. intro. f_equiv. apply max_subset. Qed.
  
  Lemma size_max : forall m, size (max m) <= size m.
  Proof using M. intro. f_equiv. apply max_subset. Qed.
  
  Lemma max_map_injective : forall f, Proper (equiv ==> equiv) f -> injective equiv equiv f ->
    forall m, (max (map f m)) == (map f (max m)).
  Proof using M.
  intros f Hf Hinj m. rewrite 2 max_simplified. unfold simple_max.
  rewrite map_injective_nfilter; auto; [].
  apply map_compat.
  - intros ? ? Heq. now rewrite Heq.
  - apply nfilter_extensionality_compat; repeat intro; subst; trivial.
    now rewrite max_mult_map_injective_invariant.
  Qed.
  
  Lemma max_remove_all : forall x m, m[x] < max_mult m -> max (remove_all x m) == max m.
  Proof using M. intros. now apply max_remove. Qed.
  
  Lemma max_mult_max : forall m, max_mult (max m) = max_mult m.
  Proof using M.
  intro m. destruct (empty_or_In_dec (max m)) as [Heq | [x Hx]].
  + rewrite max_is_empty in Heq. now rewrite Heq, max_empty.
  + symmetry. apply max_mult_unique.
    - intro y. rewrite max_subset. apply max_mult_spec_weak.
    - exists x. symmetry. rewrite <- max_In_mult2; trivial; []. now rewrite <- max_subset.
  Qed.
  
  Lemma max_idempotent : forall m, max (max m) == max m.
  Proof using M.
  intro m. rewrite max_simplified. unfold simple_max. rewrite max_mult_max.
  rewrite nfilter_max.
  + rewrite max_simplified. unfold simple_max.
    apply nfilter_extensionality_compat.
    - repeat intro. now subst.
    - intros _ n. now rewrite Nat.eqb_sym, Bool.andb_diag.
  + repeat intro. now subst.
  Qed.
  
End MMultisetExtra.
