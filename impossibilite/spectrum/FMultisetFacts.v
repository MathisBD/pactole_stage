Require Import Omega.
Require Import PArith.
Require Import Preliminary.
Require Export FMultisetInterface.

Module Make(E : DecidableType)(M : FMultisetsOn E).
  Include M.
  
  Lemma subrelation_pair_key : subrelation eq_pair eq_key.
  Proof. now intros [x n] [y p] [H _]. Qed.

  (** *  Instances for rewriting  **)
  
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
  
  Instance cardinal_compat : Proper (eq ==> Logic.eq) cardinal.
  Proof.
  intros s1 s2 Hs. do 2 rewrite cardinal_spec. rewrite (fold_left_symmetry_PermutationA _ _).
    reflexivity.
    intros x ? ? [? ?] [? ?] [? Heq]. hnf in *. simpl in *. now subst.
    intros [? ?] [? ?] ?. omega.
    now rewrite Hs.
    reflexivity.
  Qed.
  

  (** ** Other results **)
  
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
  
  Lemma add_empty : forall x n, add x n empty [=] singleton x n.
  Proof.
  intros x n y. rewrite singleton_spec. destruct (E.eq_dec y x) as [Heq | Hneq].
  - rewrite Heq. now rewrite add_spec, empty_spec.
  - rewrite add_spec', empty_spec; auto.
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
  (*
  Lemma union_empty : forall m1 m2, union m1 m2 [=] empty <-> m1 [=] empty /\ m2 [=] empty.
  Proof.
  intros m1 m2. split; intro H.
    
  Qed.
  *)
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
  
  (*
  Lemma elements_key_strengthen : forall xn m,
    InA eq_key xn (elements m) -> InA eq_pair (fst xn, multiplicity (fst xn) m) (elements m).
  Proof.
  intros [x n] m Hin. generalize (eq_refl (elements m)). pattern (elements m) at 1 3.
  induction Hin as [[y p] l | y l]; simpl.
    intro Heq. assert (Hin : InA eq_pair (y, p) (elements m)). { rewrite <- Heq. now left. }
    rewrite elements_spec in Hin. destruct Hin as [Hin _]. hnf in H.
    left. split; hnf; simpl in *. apply H. now rewrite H.
    simpl in IHHin. now right.
  rewrite elements_spec. split; simpl. reflexivity.
  induction Hin.
  rewrite <- support_elements, support_spec. simpl.
  Admitted.
  *)
  
  (** **  Results about [elements]  **)

  Lemma elements_pos : forall xn m, InA eq_pair xn (elements m) -> snd xn > 0.
  Proof. intros [x n] m Hin. now rewrite elements_spec in Hin. Qed.
  
  Theorem elements_eq_equiv : forall m₁ m₂, equivlistA eq_pair (elements m₁) (elements m₂) <-> m₁ [=] m₂.
  Proof.
  intros m₁ m₂. split; intro H.
  + assert (Hdup₁ := NoDupA_strengthen subrelation_pair_key (elements_NoDupA m₁)).
    assert (Hdup₂ := NoDupA_strengthen subrelation_pair_key (elements_NoDupA m₂)).
    apply (NoDupA_equivlistA_PermutationA _) in H; trivial. clear Hdup₁ Hdup₂.
    intro x. destruct (multiplicity x m₂) eqn:Hm₂.
    - assert (Hin : forall n, ~InA eq_pair (x, n) (elements m₂)).
      { intros n Habs. rewrite elements_spec in Habs. destruct Habs as [Heq Habs]. simpl in *. omega. }
      destruct (multiplicity x m₁) eqn:Hm₁. reflexivity.
      specialize (Hin (S n)). rewrite <- H in Hin. rewrite elements_spec in Hin.
      elim Hin. split; simpl. assumption. omega.
    - assert (Hin : InA eq_pair (x, S n) (elements m₂)).
      { rewrite elements_spec. split; simpl. assumption. omega. }
      rewrite <- H in Hin. rewrite elements_spec in Hin. now destruct Hin.
  + intros [x n]. now rewrite H.
  Qed.
  
  Corollary elements_eq : forall m₁ m₂, PermutationA eq_pair (elements m₁) (elements m₂) <-> m₁ [=] m₂.
  Proof.
  intros m₁ m₂. rewrite <- elements_eq_equiv. split; intro H.
    now apply (PermutationA_equivlistA _).
    apply (NoDupA_equivlistA_PermutationA _).
      apply (NoDupA_strengthen _ (elements_NoDupA _)).
      apply (NoDupA_strengthen _ (elements_NoDupA _)).
      assumption.
    Qed.
    
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
  
  Corollary elements_singleton : forall x n, n > 0 -> PermutationA eq_pair (elements (singleton x n)) ((x, n) :: nil).
  Proof.
  intros x n Hn. apply (NoDupA_equivlistA_PermutationA _).
  + apply NoDupA_strengthen with eq_key. refine _. apply elements_NoDupA.
  + repeat constructor. intro Habs. inversion Habs.
  + intros [y p]. rewrite elements_spec. simpl. split; intro H.
    - destruct H as [H1 H2]. left. rewrite singleton_spec in H1. destruct (E.eq_dec y x).
        now split.
        subst p. now elim (lt_irrefl 0).
    - inversion_clear H.
        compute in H0. destruct H0 as [H1 H2]. subst p. rewrite singleton_spec. destruct (E.eq_dec y x) as [| Hneq].
          now split.
          now elim Hneq.
        now inversion H0.
  Qed.
  
  Lemma elements_union : forall m₁ m₂ xn, InA eq_pair xn (elements (union m₁ m₂))
    <-> (In (fst xn) m₁ \/ In (fst xn) m₂) /\ snd xn = multiplicity (fst xn) m₁ + multiplicity (fst xn) m₂.
  Proof.
  intros m₁ m₂ xn. rewrite elements_spec, union_spec. unfold In.
  split; intros [Heq Hpos]; split; now symmetry || omega.
  Qed.

  Lemma elements_inter : forall xn m₁ m₂, InA eq_pair xn (elements (inter m₁ m₂))
    <-> (In (fst xn) m₁ /\ In (fst xn) m₂) /\ snd xn = min (multiplicity (fst xn) m₁) (multiplicity (fst xn) m₂).
  Proof.
  intros xn m₁ m₂. rewrite elements_spec, inter_spec. unfold In.
  split; intros [Heq Hpos]; split; try (now symmetry).
    rewrite <- Heq in *. unfold gt in *. now rewrite NPeano.Nat.min_glb_lt_iff in *.
    rewrite Hpos. unfold gt in *. now rewrite NPeano.Nat.min_glb_lt_iff in *.
  Qed.
  
  Lemma elements_add : forall y p m xn, InA eq_pair xn (elements (add y p m))
    <-> E.eq (fst xn) y /\ snd xn = p + multiplicity y m /\ snd xn > 0
        \/ ~E.eq (fst xn) y /\ InA eq_pair xn (elements m).
  Proof.
  intros y p m [x n]. rewrite elements_spec. simpl. split; intro H.
  + destruct H as [H1 H2]. destruct (E.eq_dec x y) as [Heq | Hneq].
      left. repeat split; try assumption. subst n. rewrite <- Heq. rewrite add_spec. apply plus_comm.
      right. split. assumption. rewrite elements_spec. rewrite add_spec' in H1. simpl. now split. auto.
  + destruct H as [[H1 [H2 H3]] | [H1 H2]].
      rewrite H1, add_spec. split; omega.
      rewrite elements_spec in H2. destruct H2. simpl in *. rewrite add_spec'. now split. auto.
  Qed.
  
  (** ** Misc lemmas **)
  
  Lemma fold_empty : forall A f (x : A), fold f empty x = x.
  Proof. intros. rewrite M.fold_spec. rewrite elements_empty. simpl. reflexivity. Qed.
  
  Lemma fold_singleton : forall A f (x : A) y n,
    n > 0 -> Proper (E.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq) f -> fold f (singleton y n) x = f y n x.
  Proof.
  intros A f x y n Hn Hf. rewrite fold_spec. assert (Hy := elements_singleton y n Hn).
  apply (PermutationA_length1 _) in Hy. destruct Hy as [[z p] [Heq Hl]].
  rewrite Hl. simpl. compute in Heq. destruct Heq. now rewrite H, H0.
  Qed.
  (*
  Lemma union_fold_add : forall m₁ m₂, union m₁ m₂ [=] fold (fun x n acc => add x n acc) m₁ m₂.
  Proof.
  SearchAbout eq. intros m₁ m₂. rewrite <- elements_eq_equiv. intros [x n].
  rewrite elements_union, fold_spec, elements_spec. simpl.
  Qed.
  *)
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
  
  Lemma support_singleton : forall x n, n <> 0 -> PermutationA E.eq (support (singleton x n)) (x :: nil).
  Proof.
  intros x n Hn. rewrite <- union_empty_r, add_union_singleton.
  apply (NoDupA_equivlistA_PermutationA _).
    now apply support_NoDupA.
    repeat constructor. intro Habs. now inversion Habs.
    intro y. rewrite support_spec. unfold In. split; intro Hin.
      left. destruct (E.eq_dec x y). easy. rewrite add_spec', empty_spec in Hin. omega. assumption.
      inversion_clear Hin. rewrite H, add_spec. omega. inversion H.
  Qed.
  
  Lemma support_1 : forall x m, PermutationA E.eq (support m) (x :: nil)
                                <-> m [=] singleton x (multiplicity x m) /\ (multiplicity x m) <> 0.
  Proof.
  intros x m. split; intro Hm.
  + assert (Hin : In x m). { rewrite <- support_spec, Hm. now left. }
    unfold In in Hin. split; try omega. intro y. rewrite singleton_spec.
    destruct (E.eq_dec y x) as [Heq | Hneq]. now rewrite Heq.
    destruct (multiplicity y m) eqn:Hy. reflexivity.
    assert (Hiny : In y m). { unfold In. rewrite Hy. omega. }
    rewrite <- support_spec, Hm in Hiny. inversion_clear Hiny. contradiction. inversion H.
  + destruct Hm as [Hm Hmult]. rewrite Hm. now apply support_singleton.
  Qed.
  
  Lemma support_add : forall x n m, n > 0 ->
    PermutationA E.eq (support (add x n m)) (if InA_dec E.eq_dec x (support m) then support m else x :: support m).
  Proof.
  intros x n m Hn. apply (NoDupA_equivlistA_PermutationA _).
  + apply support_NoDupA. 
  + destruct (InA_dec E.eq_dec x (support m)) as [Hin | Hin].
    - apply support_NoDupA.
    - constructor. assumption. apply support_NoDupA.
  + intro z. destruct (InA_dec E.eq_dec x (support m)) as [Hin | Hin]; rewrite support_spec in Hin.
    - do 2 rewrite support_spec. unfold In in *. destruct (E.eq_dec x z) as [Heq | Hneq].
        rewrite <- Heq, M.add_spec. omega.
        now rewrite M.add_spec'.
    - rewrite support_spec. unfold In in *. destruct (E.eq_dec x z) as [Heq | Hneq].
        rewrite <- Heq, M.add_spec. split; intro H. now left. omega.
        rewrite M.add_spec'; trivial. split; intro H.
          right. now rewrite support_spec.
          inversion H; subst. now elim Hneq. now rewrite support_spec in H1.
  Qed.
  
  Lemma cardinal_lower_aux : forall (l : list (E.t * nat)) acc, acc <= fold_left (fun acc xn => snd xn + acc) l acc.
  Proof.
  induction l; intro acc; simpl.
    omega.
    transitivity (snd a + acc). omega. apply IHl.
  Qed.
  
  Lemma fold_left_cardinal : Proper (PermutationA eq_pair ==> Logic.eq ==> Logic.eq)
    (fold_left (fun (acc : nat) (xn : elt * nat) => snd xn + acc)).
  Proof.
  apply (fold_left_symmetry_PermutationA _ _).
    intros ? ? ? [? ?] [? ?] [? Heq]. hnf in *. simpl in *. now subst.
    intros [? ?] [? ?] ?. omega.
  Qed.
  
  Corollary cardinal_lower : forall x m, multiplicity x m <= cardinal m.
  Proof.
  intros x m. destruct (multiplicity x m) eqn:Hm. omega.
  assert (Hin : InA eq_pair (x, S n) (elements m)). { rewrite elements_spec. split; simpl. assumption. omega. }
  rewrite cardinal_spec.
  apply (PermutationA_split _) in Hin. destruct Hin as [l Hperm]. assert (H0 := eq_refl 0).
  rewrite fold_left_cardinal; try eassumption. simpl. rewrite plus_0_r. now apply cardinal_lower_aux.
  Qed.
  
  Lemma cardinal_empty : cardinal empty = 0.
  Proof. now rewrite cardinal_spec, elements_empty. Qed.
  
  Lemma cardinal_0 : forall m, cardinal m = 0 <-> m [=] empty.
  Proof.
  intro m. split; intro Hm.
  + intro y. rewrite empty_spec. revert y. change (Empty m). rewrite <- elements_nil.
    destruct (elements m) as [| [x n] l] eqn:Helt. reflexivity.
    simpl in Hm. elim (lt_irrefl 0). apply lt_le_trans with n.
      change n with (snd (x, n)). apply elements_pos with m. rewrite Helt. now left.
      assert (Hn : multiplicity x m = n). { eapply proj1. rewrite <- (elements_spec (x, n)), Helt. now left. }
      rewrite <- Hn, <- Hm. apply cardinal_lower.
  + rewrite Hm. apply cardinal_empty.
  Qed.
  
  Lemma singleton_0 : forall x, singleton x 0 [=] empty.
  Proof. intros x y. rewrite singleton_spec, empty_spec. now destruct (E.eq_dec y x). Qed.
  
  Lemma cardinal_singleton : forall x n, cardinal (singleton x n) = n.
  Proof.
  intros. destruct n.
  + rewrite singleton_0. apply cardinal_empty.
  + rewrite cardinal_spec.
    rewrite fold_left_cardinal; try eapply elements_singleton.
      simpl. now rewrite plus_0_r.
      omega.
      omega.
  Qed.
  
  Theorem cardinal_union : forall m₁ m₂, cardinal (union m₁ m₂) = cardinal m₁ + cardinal m₂.
  Proof.
  intros m₁ m₂. repeat rewrite cardinal_spec.
  assert (Helt := elements_union m₁ m₂).
  Admitted.
  
  Corollary cardinal_add : forall x n m, cardinal (add x n m) = n + cardinal m.
  Proof. intros. now rewrite <- add_union_singleton, cardinal_union, cardinal_singleton. Qed.
  
  Lemma support_map_elements : forall m, PermutationA E.eq (support m) (map (@fst E.t nat) (elements m)).
  Proof.
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
    - exists (x, multiplicity x m). now split.
    - destruct Hin as [[y p] [Heq Hin]]. rewrite elements_spec in *. simpl in *.
      split. reflexivity. destruct Hin. subst. now rewrite <- Heq.
    - clear. intros [x n] [y p] [? ?]. apply H.
  Qed.
  
  Lemma elements_length : forall m, length (elements m) = size m.
  Proof. intro. now rewrite size_spec, support_map_elements, map_length. Qed.
  
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
  (*
  Lemma map_In : forall x f m, In x (map f m) -> exists y, x = f y.
  Proof.
  intros x f m Hin. rewrite <- support_spec in Hin.
  unfold map in Hin. rewrite fold_spec in Hin. revert Hin. generalize empty as acc.
  induction (elements m); simpl in *; intros acc Hin.
  - rewrite support_empty in Hin. inversion Hin.
  - 
  Qed.
  *)
  Lemma map_union : forall f m₁ m₂, map f (union m₁ m₂) [=] union (map f m₁) (map f m₂).
  Proof.
  intros f m₁ m₂ x.
  Admitted.
  
  Lemma map_add : forall f x n m, map f (add x n m) [=] add (f x) n (map f m).
  Proof.
  intros f x n m.
  Admitted.
  
  Lemma map_support : forall f m, PermutationA E.eq (support (map f m)) (List.map f (support m)).
  Proof.
  Admitted.
  
End Make.
