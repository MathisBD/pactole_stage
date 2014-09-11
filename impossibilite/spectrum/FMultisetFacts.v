Require Import Omega.
Require Import PArith.
Require Import Preliminary.
Require Export FMultisetInterface.

Module Make(E : DecidableType)(M : FMultisetsOn E).
  Include M.
  
  Existing Instance multiplicity_compat.
  Existing Instance fold_compat.
  
  Instance eq_equiv : Equivalence eq.
  Proof. split.
  intros m x. reflexivity.
  intros m1 m2 H x. now symmetry.
  intros m1 m2 m3 H1 H2 x. now transitivity (multiplicity x m2).
  Qed.
  
  Instance is_empty_compat : Proper (eq ==> Logic.eq) is_empty.
  Proof.
  intros s1 s2 Heq. destruct (is_empty s2) eqn:Hs2.
    rewrite is_empty_spec in *. intro. now rewrite Heq.
    destruct (is_empty s1) eqn:Hs1.
      rewrite <- Hs2. symmetry. rewrite is_empty_spec in *. intro. now rewrite <- Heq.
      reflexivity.
  Qed.
  
  Instance add_compat : Proper (E.eq ==> Logic.eq ==> eq ==> eq) add.
  Proof.
  intros x y Hxy n m Hnm s1 s2 Hs12 z. subst m. destruct (E.eq_dec z x) as [Heq | Hneq].
    rewrite Heq. rewrite add_spec. rewrite Hxy. rewrite add_spec. now rewrite Hs12.
    repeat rewrite add_spec'; apply Hs12 || eauto.
  Qed.
  
  Instance singleton_compat : Proper (E.eq ==> Logic.eq ==> eq) singleton.
  Proof.
  intros x y Hxy n m Hnm z. subst. do 2 rewrite singleton_spec. destruct (E.eq_dec z x), (E.eq_dec z y).
    reflexivity.
    elim n. now apply E.eq_trans with x.
    elim n. apply E.eq_trans with y. assumption. now auto.
    reflexivity.
  Qed.
  
  Instance remove_compat : Proper (E.eq ==> Logic.eq ==> eq ==> eq) remove.
  Proof.
  intros x y Hxy n m Hnm s1 s2 Hs12 z. subst m. destruct (E.eq_dec z x) as [Heq | Hneq].
    rewrite Heq. rewrite remove_spec. rewrite Hxy. rewrite remove_spec. now rewrite Hs12.
    repeat rewrite remove_spec'; apply Hs12 || eauto.
  Qed.
  
  Instance union_compat : Proper (eq ==> eq ==> eq) union.
  Proof. intros m1 m1' Heq1 m2 m2' Heq2 x. now rewrite union_spec, union_spec, Heq1, Heq2. Qed.
  
  Instance inter_compat : Proper (eq ==> eq ==> eq) inter.
  Proof. intros m1 m1' Heq1 m2 m2' Heq2 x. now rewrite inter_spec, inter_spec, Heq1, Heq2. Qed.
  
  Instance diff_compat : Proper (eq ==> eq ==> eq) diff.
  Proof. intros m1 m1' Heq1 m2 m2' Heq2 x. now rewrite diff_spec, diff_spec, Heq1, Heq2. Qed.
  
  Instance subset_compat : Proper (eq ==> eq ==> iff) Subset.
  Proof. intros m1 m1' Heq1 m2 m2' Heq2. split; intros H x. now rewrite <- Heq1, <- Heq2. now rewrite Heq1, Heq2. Qed.
  
  Instance filter_compat f : compatb f -> Proper (eq ==> eq) (filter f).
  Proof. intros Hf s1 s2 Hs x. repeat rewrite filter_spec; trivial. now do 2 rewrite Hs. Qed.
  
  Instance partition_compat f : compatb f -> Proper (eq ==> eq * eq) (partition f).
  Proof.
  intros Hf s1 s2 Hs. split; intro x.
    repeat rewrite partition_spec_fst; trivial. now rewrite (filter_compat f Hf _ _ Hs).
    repeat rewrite partition_spec_snd; trivial. rewrite filter_compat; trivial.
    intros ? ? H1 ? ? H2. rewrite Hf; reflexivity|| eassumption.
  Qed.
  
  Instance elements_compat : Proper (eq ==> PermutationA eq_pair) elements.
  Proof.
  intros s1 s2 Hs. apply NoDupA_equivlistA_PermutationA.
    now apply eq_pair_equiv.
    generalize (elements_NoDupA s1). apply NoDupA_strengthen. now intros [? ?] [? ?] [? _].
    generalize (elements_NoDupA s2). apply NoDupA_strengthen. now intros [? ?] [? ?] [? _].
    intro x. do 2 rewrite elements_spec. now rewrite Hs.
  Qed.
  
  Instance support_compat : Proper (eq ==> PermutationA E.eq) support.
  Proof.
  intros s1 s2 Hs. assert (Equivalence E.eq) by auto with typeclass_instances.
  apply NoDupA_equivlistA_PermutationA. assumption.
  now apply support_NoDupA. now apply support_NoDupA.
  intro x. do 2 rewrite support_spec. unfold In. now rewrite Hs.
  Qed.
  
  Instance size_compat : Proper (eq ==> Logic.eq) size.
  Proof. intros s1 s2 Hs. do 2 rewrite size_spec. now rewrite Hs. Qed.
  
  Instance In_compat : Proper (E.eq ==> eq ==> iff) In.
  Proof. intros x y Hxy s1 s2 Hs. unfold In. now rewrite Hxy, Hs. Qed.
  
  Instance for_all_compat : forall f, compatb f -> Proper (eq ==> Logic.eq) (for_all f).
  Proof.
  intros f Hf s1 s2 Hs. destruct (for_all f s2) eqn:Hs2.
    rewrite for_all_spec in *; trivial. intros x Hin. rewrite Hs. apply Hs2. now rewrite <- Hs.
    destruct (for_all f s1) eqn:Hs1.
      rewrite <- Hs2. symmetry. rewrite for_all_spec in *; trivial.
      intros x Hin. rewrite <- Hs. apply Hs1. now rewrite Hs.
      reflexivity.
  Qed.
  
  Instance exists_compat : forall f, compatb f -> Proper (eq ==> Logic.eq) (exists_ f).
  Proof.
  intros f Hf s1 s2 Hs. destruct (exists_ f s2) eqn:Hs2.
    rewrite exists_spec in *; trivial. destruct Hs2 as [x [Hin Hfx]]. exists x. now split; rewrite Hs.
    destruct (exists_ f s1) eqn:Hs1.
      rewrite <- Hs2. symmetry. rewrite exists_spec in *; trivial.
       destruct Hs1 as [x [Hin Hfx]]. exists x. now split; rewrite <- Hs.
      reflexivity.
  Qed.
  
  Instance Empty_compat : Proper (eq ==> iff) Empty.
  Proof. intros m1 m2 Hm. do 2 rewrite <- is_empty_spec. now rewrite Hm. Qed.
  
  Instance For_all_compat : forall f, compatb f -> Proper (eq ==> iff) (For_all f).
  Proof.
  intros f Hf s1 s2 Hs. split; intros H x Hin.
    rewrite <- Hs. apply H. now rewrite Hs.
    rewrite Hs. apply H. now rewrite <- Hs.
  Qed.
  
  Instance Exists_compat : forall f, compatb f -> Proper (eq ==> iff) (Exists f).
  Proof.
  intros f Hf s1 s2 Hs. split; intros [x [Hin Hfx]].
    exists x. now split; rewrite <- Hs.
    exists x. now split; rewrite Hs.
  Qed.
  (*
  Instance cardinal_compat : Proper (eq ==> Logic.eq) cardinal.
  Proof. intros s1 s2 Hs. do 2 rewrite cardinal_spec. now rewrite Hs. Qed.
  *)

  (*
  Instance fold_proper {A} : Proper ((E.eq ==> Logic.eq ==> Logic.eq) ==> eq ==> Logic.eq ==> Logic.eq) (@fold A).
  Proof.
  intros f g Hfg s1 s2 Hs x1 x2 Hx. subst. do 2 rewrite fold_spec.
  Qed.
  *)
  
  (** ** Results about [add]. **)
  Lemma add_0 : forall x m, add x 0 m [=] m.
  Proof.
  intros x m y. destruct (E.eq_dec x y) as [Heq | Hneq].
    now rewrite <- Heq, add_spec, plus_0_r.
    now rewrite add_spec'.
  Qed.
  
  Lemma add_comm : forall x1 x2 n1 n2 m, add x1 n1 (add x2 n2 m) [=] add x2 n2 (add x1 n1 m).
  Proof.
  intros x1 x2 n1 n2 m x.
  destruct (E.eq_dec x x1) as [Heq1 | Hneq1], (E.eq_dec x x2) as [Heq2 | Hneq2].
  - rewrite Heq1 in *. rewrite add_spec. rewrite Heq2 at 1 2. do 2 rewrite add_spec.
    rewrite <- Heq2. rewrite add_spec. omega. (* BUG with typeclass resolution? *)
  - rewrite Heq1 in *. repeat rewrite add_spec || rewrite add_spec'; auto.
  - rewrite Heq2 in *. repeat rewrite add_spec || rewrite add_spec'; auto.
  - repeat rewrite add_spec'; auto.
  Qed.
  
  Lemma add_multiplicity_inf_bound : forall x n m, multiplicity x (add x n m) >= n.
  Proof. intros x n m. rewrite add_spec. omega. Qed.
  
  (** ** Results about [remove]. **)
  Lemma remove_0 : forall x m, remove x 0 m [=] m.
  Proof.
  intros x m y. destruct (E.eq_dec x y) as [Heq | Hneq].
    now rewrite <- Heq, remove_spec, <- minus_n_O.
    now rewrite remove_spec'.
  Qed.
  
  Lemma remove_comm : forall x1 x2 n1 n2 m, remove x1 n1 (remove x2 n2 m) [=] remove x2 n2 (remove x1 n1 m).
  Proof.
  intros x1 x2 n1 n2 m x.
  destruct (E.eq_dec x x1) as [Heq1 | Hneq1], (E.eq_dec x x2) as [Heq2 | Hneq2].
  - rewrite Heq1 in *. rewrite remove_spec. rewrite Heq2 at 1 2. do 2 rewrite remove_spec.
    rewrite <- Heq2. rewrite remove_spec. omega. (* BUG with typeclass resolution? *)
  - rewrite Heq1 in *. repeat rewrite remove_spec || rewrite remove_spec'; auto.
  - rewrite Heq2 in *. repeat rewrite remove_spec || rewrite remove_spec'; auto.
  - repeat rewrite remove_spec'; auto.
  Qed.
  
  (** ** Results about [union]. **)
  Lemma union_empty_l : forall m, union empty m [=] m.
  Proof. intros m x. now rewrite union_spec, empty_spec. Qed.
  
  Lemma union_empty_r : forall m, union m empty [=] m.
  Proof. intros m x. now rewrite union_spec, empty_spec, <- plus_n_O. Qed.
  
  Lemma union_comm : forall m1 m2, union m1 m2 [=] union m2 m1.
  Proof. intros m1 m2 x. do 2 rewrite union_spec. apply Plus.plus_comm. Qed.
  
  Lemma union_assoc : forall m1 m2 m3, union m1 (union m2 m3) [=] union (union m1 m2) m3.
  Proof. intros m1 m2 m3 x. repeat rewrite union_spec. apply Plus.plus_assoc. Qed.
  
  Lemma add_union_singleton : forall x n m, union (singleton x n) m [=] add x n m.
  Proof.
  intros x n m y. rewrite union_spec, singleton_spec. destruct (E.eq_dec y x) as [Heq | Hneq].
    rewrite Heq. rewrite add_spec. omega.
    rewrite add_spec'. reflexivity. auto.
  Qed.
  
  (** ** Results about [inter]. **)
  Lemma inter_empty_l : forall m, inter empty m [=] empty.
  Proof. intros m x. now rewrite inter_spec, empty_spec. Qed.
  
  Lemma inter_empty_r : forall m, inter m empty [=] empty.
  Proof. intros m x. rewrite inter_spec, empty_spec. rewrite min_r; auto with arith. Qed.
  
  Lemma inter_comm : forall m1 m2, inter m1 m2 [=] inter m2 m1.
  Proof. intros m1 m2 x. do 2 rewrite inter_spec. apply Min.min_comm. Qed.
  
  Lemma inter_assoc : forall m1 m2 m3, inter m1 (inter m2 m3) [=] inter (inter m1 m2) m3.
  Proof. intros m1 m2 m3 x. repeat rewrite inter_spec. apply Min.min_assoc. Qed.
  
  Lemma remove_diff_singleton : forall x n m, diff m (singleton x n) [=] remove x n m.
  Proof.
  intros x n m y. rewrite diff_spec, singleton_spec. destruct (E.eq_dec y x) as [Heq | Hneq].
    rewrite Heq. now rewrite remove_spec.
    rewrite remove_spec'. omega. auto.
  Qed.
  
  (** ** Results about [Subset]. **)
  Instance Subset_PreOrder : PreOrder Subset.
  Proof. split.
  intros m x. reflexivity.
  intros m1 m2 m3 Hle12 Hle23 x. now transitivity (multiplicity x m2).
  Qed.
  
  Instance Subset_PartialOrder : PartialOrder eq Subset.
  Proof.
  intros m1 m2. split; intro H.
    split; now rewrite H.
    destruct H. intro. now apply le_antisym.
  Qed.
  
  (** ** Misc lemmas **)
  Lemma singleton_0 : forall x, singleton x 0 [=] empty.
  Proof. intros x y. rewrite singleton_spec, empty_spec. now destruct (E.eq_dec y x). Qed.
  
  Lemma elements_nil : forall m, elements m = nil <-> Empty m.
  Proof.
  intro m. split; intro H.
  - unfold elements in H. intro x.
    assert (~multiplicity x m > 0).
    { intro Habs. apply (conj (eq_refl (multiplicity x m))) in Habs.
      change x with (fst (x, multiplicity x m)) in Habs at 1.
      change (multiplicity x m) with (snd (x, multiplicity x m)) in Habs at 2 3.
      rewrite <- M.elements_spec in Habs. rewrite H in Habs. now inversion Habs. }
    omega.
  - destruct (elements m) as [| [x n] l] eqn:Hm; trivial.
    assert (Habs : InA eq_pair (x, n) (elements m)). { rewrite Hm. now left. }
    rewrite elements_spec in Habs.
    exfalso. specialize (H x). simpl in Habs. rewrite H in Habs. destruct Habs. subst n. now apply (lt_irrefl 0).
  Qed.
  
  Corollary elements_empty : elements empty = nil.
  Proof. rewrite elements_nil. apply empty_spec. Qed.
  
  Corollary elements_singleton : forall x n, n > 0 -> equivlistA eq_pair (elements (singleton x n)) ((x, n) :: nil).
  Proof.
  intros x n Hn [y p]. rewrite elements_spec. simpl. split; intro H.
    destruct H as [H1 H2]. left. rewrite singleton_spec in H1. destruct (E.eq_dec y x).
      now split.
      subst p. now elim (lt_irrefl 0).
    inversion_clear H.
      compute in H0. destruct H0 as [H1 H2]. subst p. rewrite singleton_spec. destruct (E.eq_dec y x) as [| Hneq].
        now split.
        now elim Hneq.
      now inversion H0.
  Qed.
  
  Lemma fold_empty : forall A f (x : A), fold f empty x = x.
  Proof. intros. rewrite M.fold_spec. rewrite elements_empty. simpl. reflexivity. Qed.
  
  Lemma fold_singleton : forall A f (x : A) y n,
    n > 0 -> Proper (E.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq) f -> fold f (singleton y n) x = f y n x.
  Proof.
  intros A f x y n Hn Hf. rewrite fold_spec. assert (Hy := elements_singleton y n Hn).
  apply (NoDupA_equivlistA_PermutationA _) in Hy.
    apply (PermutationA_length1 _) in Hy. destruct Hy as [[z p] [Heq Hl]].
    rewrite Hl. simpl. compute in Heq. destruct Heq. now rewrite H, H0.
    generalize (elements_NoDupA (singleton y n)). apply (NoDupA_strengthen _).
    constructor. now rewrite InA_nil. constructor.
  Qed.
  
  Lemma support_empty : support empty = nil.
  Proof.
  destruct (support empty) eqn:Hl. reflexivity.
  assert (Habs : In e empty). { rewrite <- support_spec, Hl. now left. }
  unfold In in Habs. rewrite empty_spec in Habs. omega.
  Qed.
  
  Lemma support_nil : forall m, support m = nil <-> m [=] empty.
  Proof.
  intro m. split; intro H.
  + intro x. rewrite empty_spec. destruct (multiplicity x m) eqn:Hin. reflexivity.
    assert (Hm : In x m). { unfold In. rewrite Hin. omega. }
    rewrite <- support_spec in Hm. rewrite H in Hm. inversion Hm.
  + apply (@PermutationA_nil _ E.eq _). rewrite H. now rewrite support_empty.
  Qed.
  
  (** *  Extra operations  **)
  
  Definition map f m := fold (fun x n acc => add (f x) n acc) m empty.
  
  Instance map_compat : forall f, Proper (E.eq ==> E.eq) f -> Proper (eq ==> eq) (map f).
  Proof.
  intros f Hf m1 m2 Hm. unfold map. apply (fold_compat _ _).
  - clear -Hf. intros x y Hxy n m Hnm m1 m2 Hm. now rewrite Hxy, Hnm, Hm.
  - intros. now rewrite (add_comm (f x) (f y) n m a).
  - assumption.
  - reflexivity.
  Qed.
  
  Lemma map_spec : forall f, Proper (E.eq ==> E.eq) f -> injective E.eq E.eq f ->
    forall x m, multiplicity (f x) (map f m) = multiplicity x m.
  Proof.
  Admitted.
  
  Lemma map_empty : forall f, map f empty [=] empty.
  Proof. intro f. unfold map. now rewrite fold_empty. Qed.
  
  Lemma map_add : forall f x n m, map f (add x n m) [=] add (f x) n (map f m).
  Proof.
  Admitted.
  
  Lemma map_support : forall f m, PermutationA E.eq (support (map f m)) (List.map f (support m)).
  Proof.
  Admitted.
  
End Make.
