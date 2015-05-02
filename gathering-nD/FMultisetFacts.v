Require Import Omega.
Require Import PArith.
Require Import SetoidList.
Require Import Preliminary.
Require Export FMultisetInterface.


Set Implicit Arguments.


Module Make(E : DecidableType)(M : FMultisetsOn E).
  Include M.
  
  Hint Extern 1 (~E.eq ?x ?y) => let Heq := fresh "Heq" in
    congruence || intro Heq; symmetry in Heq; revert Heq; assumption.
  
  Lemma subrelation_pair_key : subrelation eq_pair eq_key.
  Proof. now intros [x n] [y p] [H _]. Qed.

  Lemma InA_pair_key : forall x n p l, InA eq_pair (x, n) l -> InA eq_key (x, p) l.
  Proof.
  intros x n p l Hin. induction l as [| [y q] l].
  + rewrite InA_nil in Hin. elim Hin.
  + inversion_clear Hin.
    - destruct H as [ H _]. now left.
    - right. now apply IHl.
  Qed.
  
  Lemma InA_key_pair : forall xn l, InA eq_key xn l -> exists n, InA eq_pair (fst xn, n) l.
  Proof.
  intros [x n] l Hin. induction l as [| [y p] l].
  + rewrite InA_nil in Hin. elim Hin.
  + inversion_clear Hin.
    - compute in H. exists p. left. now rewrite H.
    - apply IHl in H. destruct H as [k Hin]. exists k. now right.
  Qed.
  
  (** *  Instances for rewriting  **)
  
  Existing Instance multiplicity_compat.
  Existing Instance fold_compat.
  
  Instance eq_equiv : Equivalence eq.
  Proof. split.
  intros m x. reflexivity.
  intros m1 m2 H x. now symmetry.
  intros m1 m2 m3 H1 H2 x. now transitivity (multiplicity x m2).
  Qed.
  
  Theorem eq_dec : forall m1 m2 : t, {eq m1 m2} + {~eq m1 m2}.
  Proof.
  intros m1 m2. destruct (M.equal m1 m2) eqn:Heq.
  - left. now rewrite <- M.equal_spec.
  - right. rewrite <- M.equal_spec, Heq. discriminate.
  Qed.
  
  Instance InA_key_compat : Proper (eq_key ==> PermutationA eq_pair ==> iff) (InA eq_key).
  Proof.
  intros [x n] [y p] Hxy l1. compute in Hxy. setoid_rewrite Hxy. clear Hxy x.
  induction l1 as [| [z q] l]; intros l2 Hperm.
  + apply (PermutationA_nil _) in Hperm. subst. split; intro Hin; rewrite InA_nil in Hin; elim Hin.
  + assert (Hl : InA eq_pair (z, q) ((z, q) :: l)) by now left.
    rewrite Hperm in Hl. apply InA_split in Hl.
    destruct Hl as [l1' [[w r] [l2' [Heq ?]]]]. subst l2. rewrite <- Heq in Hperm.
    assert (Hl : PermutationA eq_pair (l1' ++ l2') l).
    { eapply (PermutationA_cons_inv _). etransitivity. apply (PermutationA_middle _). symmetry. apply Hperm. }
    symmetry in Hl. apply IHl in Hl. split; intro H.
    - rewrite (InA_app_iff _). inversion_clear H.
        right. left. destruct Heq as [Heq _]. now rewrite <- Heq.
        rewrite Hl in H0. rewrite (InA_app_iff _) in H0. destruct H0.
          now left.
          now do 2 right.
    - rewrite (InA_app_iff _) in H. destruct H.
        right. rewrite Hl. rewrite (InA_app_iff _). now left.
        inversion_clear H. left. destruct Heq as [Heq _]. now rewrite Heq.
        right. rewrite Hl. rewrite (InA_app_iff _). now right.
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
    repeat rewrite add_spec'; apply Hs12 || intro; apply Hneq; rewrite Hxy in *; symmetry; assumption.
  Qed.
  
  Instance singleton_compat : Proper (E.eq ==> Logic.eq ==> eq) singleton.
  Proof.
  intros x y Hxy n m Hnm z. subst. do 2 rewrite singleton_spec. destruct (E.eq_dec z x), (E.eq_dec z y).
    reflexivity.
    elim n. now transitivity x.
    elim n. transitivity y. assumption. now auto.
    reflexivity.
  Qed.
  
  Instance remove_compat : Proper (E.eq ==> Logic.eq ==> eq ==> eq) remove.
  Proof.
  intros x y Hxy n m Hnm s1 s2 Hs12 z. subst m. destruct (E.eq_dec z x) as [Heq | Hneq].
    rewrite Heq. rewrite remove_spec. rewrite Hxy. rewrite remove_spec. now rewrite Hs12.
    repeat rewrite remove_spec'; apply Hs12 || auto. intro; apply Hneq; rewrite Hxy in *; symmetry; assumption.
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
    repeat rewrite partition_spec_fst; trivial. now rewrite (filter_compat Hf Hs).
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
  intros s1 s2 Hs. do 2 rewrite cardinal_spec, fold_spec. rewrite (fold_left_symmetry_PermutationA _ _).
    reflexivity.
    intros x ? ? [? ?] [? ?] [? Heq]. hnf in *. simpl in *. now subst.
    intros [? ?] [? ?] ?. omega.
    now rewrite Hs.
    reflexivity.
  Qed.
  
  
  (** *  Other results  **)
  
  (** **  Results about [singleton]  **)
  
  Lemma singleton_0 : forall x, singleton x 0 [=] empty.
  Proof. intros x y. rewrite singleton_spec, empty_spec. now destruct (E.eq_dec y x). Qed.
  
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
  
  (** **  Results about [add]  **)

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
  
  Lemma add_disjoint : forall x n m, add x n m [=] add x (n + multiplicity x m) (remove x (multiplicity x m) m).
  Proof.
  intros x n m y. destruct (E.eq_dec x y) as [Hxy | Hxy].
  - rewrite Hxy, add_spec, add_spec, remove_spec. omega.
  - now rewrite add_spec', add_spec', remove_spec'.
  Qed.
  
  Lemma add_combine : forall x n p m, add x n (add x p m) [=] add x (n + p) m.
  Proof.
  intros x n p m y. destruct (E.eq_dec x y) as [Hxy | Hxy].
  - rewrite Hxy. repeat rewrite add_spec. omega.
  - now repeat rewrite add_spec'.
  Qed.
  
  (** ** Results about [remove] **)

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
  
  Lemma remove_add_comm : forall x1 x2 n1 n2 m, ~E.eq x1 x2 ->
    remove x1 n1 (add x2 n2 m) [=] add x2 n2 (remove x1 n1 m).
  Proof.
  intros x1 x2 n1 n2 m Hneq x.
  destruct (E.eq_dec x x1) as [Heq1 | Hneq1], (E.eq_dec x x2) as [Heq2 | Hneq2]; try rewrite Heq1 in *.
  - contradiction.
  - rewrite remove_spec, add_spec', add_spec', remove_spec; auto.
  - rewrite Heq2 in *. rewrite remove_spec', add_spec, add_spec, remove_spec'; auto.
  - rewrite remove_spec', add_spec', add_spec', remove_spec'; auto.
  Qed.
  
  Lemma remove_add1 : forall x n p m, n <= p -> remove x n (add x p m) [=] add x (p - n) m.
  Proof.
  intros x n p m Hle y. destruct (E.eq_dec x y) as [Heq | Hneq].
    rewrite <- Heq, remove_spec, add_spec, add_spec. omega.
    now rewrite remove_spec', add_spec', add_spec'.
  Qed.
  
  Lemma remove_add2 : forall x n p m, p <= n -> remove x n (add x p m) [=] remove x (n - p) m.
  Proof.
  intros x n p m Hle y. destruct (E.eq_dec x y) as [Heq | Hneq].
    rewrite <- Heq, remove_spec, add_spec, remove_spec. omega.
    now rewrite remove_spec', add_spec', remove_spec'.
  Qed.
  
  Lemma add_remove1 : forall x n p m, p <= multiplicity x m -> p <= n -> add x n (remove x p m) [=] add x (n - p) m.
  Proof.
  intros x n p m Hle1 Hle2 y. destruct (E.eq_dec x y) as [Heq | Hneq].
    rewrite <- Heq, add_spec, remove_spec, add_spec. omega.
    now rewrite add_spec', remove_spec', add_spec'.
  Qed.
  
  Lemma add_remove2 : forall x n p m, multiplicity x m <= p -> multiplicity x m <= n ->
    add x n (remove x p m) [=] add x (n - multiplicity x m) m.
  Proof.
  intros x n p m Hle1 Hle2 y. destruct (E.eq_dec x y) as [Heq | Hneq].
    rewrite <- Heq, add_spec, remove_spec, add_spec. omega.
    now rewrite add_spec', remove_spec', add_spec'.
  Qed.

  Lemma add_remove3 : forall x n p m, n <= multiplicity x m <= p -> 
    add x n (remove x p m) [=] remove x (multiplicity x m - n) m.
  Proof.
  intros x n p m Hle y. destruct (E.eq_dec x y) as [Heq | Hneq].
    rewrite <- Heq, remove_spec, add_spec, remove_spec. omega.
    now rewrite remove_spec', add_spec', remove_spec'.
  Qed.
  
  Lemma add_remove4 : forall x n p m, n <= p <= multiplicity x m -> 
    add x n (remove x p m) [=] remove x (p - n) m.
  Proof.
  intros x n p m Hle y. destruct (E.eq_dec x y) as [Heq | Hneq].
    rewrite <- Heq, remove_spec, add_spec, remove_spec. omega.
    now rewrite remove_spec', add_spec', remove_spec'.
  Qed.
  
  Lemma add_remove_id : forall n x m, multiplicity x m <= n -> add x (multiplicity x m) (remove x n m) [=] m.
  Proof. intros. rewrite add_remove2; trivial. now rewrite minus_diag, add_0. Qed.
  
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
  
  Lemma union_add_comm_l : forall x n m1 m2, union (add x n m1) m2 [=] add x n (union m1 m2).
  Proof.
  intros x n m1 m2 y. destruct (E.eq_dec x y) as [Hxy | Hxy].
  + rewrite Hxy. do 2 rewrite add_spec, union_spec. omega.
  + now repeat rewrite add_spec', union_spec.
  Qed.
  
  Lemma union_add_comm_r : forall x n m1 m2, union m1 (add x n m2) [=] add x n (union m1 m2).
  Proof. intros. setoid_rewrite union_comm. apply union_add_comm_l. Qed.
  
  Lemma union_empty : forall m1 m2, union m1 m2 [=] empty <-> m1 [=] empty /\ m2 [=] empty.
  Proof.
  intros m1 m2. split; intro H.
  + split; intro x.
    - specialize (H x). rewrite union_spec, empty_spec in H. rewrite empty_spec. omega.
    - specialize (H x). rewrite union_spec, empty_spec in H. rewrite empty_spec. omega.
  + intro x. destruct H as [H1 H2]. rewrite union_spec, H1, H2. now rewrite empty_spec.
  Qed.
  
  (** **  Results about [inter]  **)
  
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
  
  (** **  Results about [Subset]  **)
  
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
    rewrite <- Heq in *. unfold gt in *. now rewrite Nat.min_glb_lt_iff in *.
    rewrite Hpos. unfold gt in *. now rewrite Nat.min_glb_lt_iff in *.
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
  
  Lemma elements_add_out : forall x n m, n > 0 -> ~In x m ->
    PermutationA eq_pair (elements (add x n m)) ((x, n) :: elements m).
  Proof.
  intros x n m Hn Hin. apply (NoDupA_equivlistA_PermutationA _).
  + apply (NoDupA_strengthen _ (elements_NoDupA _)).
  + constructor.
      rewrite elements_spec. simpl. intros [H1 H2]. apply Hin. unfold In. omega.
      apply (NoDupA_strengthen _ (elements_NoDupA _)).
  + intros [y p]. rewrite elements_add. split; intro H.
    - destruct H as [[H1 [H2 Hpos]] | [H1 H2]]; simpl in *.
        unfold In in Hin. left. split. assumption. compute. omega.
        now right.
    - simpl. inversion_clear H.
        destruct H0 as [H1 H2]. compute in H1, H2. left. subst. unfold In in Hin. repeat split; trivial. omega.
        right. split; trivial. intro Habs. apply Hin. rewrite <- Habs. rewrite <- support_spec, support_elements.
        assert (H1 := H0). rewrite elements_spec in H1. destruct H1 as [H1 _]. simpl in H1. now subst.
  Qed.
  
  Theorem elements_In : forall x n m, InA eq_key (x, n) (elements m) <-> In x m.
  Proof.
  intros x n m. split; intro H.
  + apply InA_key_pair in H. destruct H as [p Hp]. simpl in Hp. rewrite elements_spec in Hp.
    destruct Hp as [Heq Hpos]. unfold In. simpl in *. now subst.
  + rewrite <- support_spec, support_elements in H. revert H. apply InA_pair_key.
  Qed.
  
  (** [is_elements] tests wether a given list can be the elements of a multiset **)
  Definition is_elements l := NoDupA eq_key l /\ Forall (fun xn => snd xn > 0) l.
  
  Lemma is_elements_nil : is_elements nil.
  Proof. split; constructor. Qed.

  Lemma is_elements_cons : forall xn l, is_elements l -> ~InA eq_key xn l -> snd xn > 0 -> is_elements (xn :: l).
  Proof.
  unfold is_elements. setoid_rewrite Forall_forall. intros xn l [Hdup Hpos] Hx Hn. split.
  - now constructor.
  - intros [y p] Hin. inversion_clear Hin.
      inversion H. now subst.
      now apply Hpos.
  Qed.
  
  Lemma is_elements_cons_inv : forall x n l, is_elements ((x, n) :: l) -> is_elements l.
  Proof. intros x n l [Hdup Hpos]. inversion_clear Hpos. inversion_clear Hdup. now split. Qed.
  
  Lemma elements_is_elements : forall m, is_elements (elements m).
  Proof.
  intro m. split.
  - now apply elements_NoDupA.
  - rewrite Forall_forall. intros x Hx. apply (@elements_pos x m). now apply (In_InA _).
  Qed.
  
  Instance is_elements_compat : Proper (PermutationA eq_pair ==> iff) is_elements.
  Proof.
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
  Proof.
  induction l as [| [x n] l].
  + split; intro H.
    - exists empty. now rewrite elements_empty.
    - apply is_elements_nil.
  + split; intro H.
    - destruct H as [Hdup Hpos].
      assert (Hel : is_elements l). { split. now inversion_clear Hdup. now inversion_clear Hpos. }
      rewrite IHl in Hel. destruct Hel as [m Hm]. exists (add x n m). symmetry. rewrite Hm. apply elements_add_out.
        now inversion_clear Hpos.
        inversion_clear Hdup. rewrite <- support_spec, support_elements. intro Habs. apply H.
        rewrite <- Hm in Habs. eapply InA_pair_key. apply Habs.
    - destruct H as [m Hperm]. rewrite Hperm. apply elements_is_elements.
  Qed.
  
  Theorem is_elements_build : forall l, is_elements l -> {m |PermutationA eq_pair l (elements m)}.
  Proof.
  induction l as [| [x n] l]; intro H.
  + exists empty. now rewrite elements_empty.
  + destruct H as [Hdup Hpos].
    assert (Hel : is_elements l). { split. now inversion_clear Hdup. now inversion_clear Hpos. }
    apply IHl in Hel. destruct Hel as [m Hm]. exists (add x n m). symmetry. rewrite Hm. apply elements_add_out.
        now inversion_clear Hpos.
        inversion_clear Hdup. rewrite <- support_spec, support_elements. intro Habs. apply H.
        rewrite <- Hm in Habs. eapply InA_pair_key. apply Habs.
  Defined.
  
  (** [from_elements] builds back a multiset from its elements **)
  Fixpoint from_elements l :=
    match l with
      | nil => empty
      | (x, n) :: l => add x n (from_elements l)
    end.
  
  Instance from_elements_compat : Proper (PermutationA eq_pair ==> eq) from_elements.
  Proof.
  intros l1 l2 perm. induction perm as [| [x n] [y p] ? ? [Hxy Hnp] | [x n] [y p] |]; simpl.
  + reflexivity.
  + intro z. compute in Hxy, Hnp. now rewrite Hxy, Hnp, IHperm.
  + apply add_comm.
  + now transitivity (from_elements l₂).
  Qed.
  
  Lemma from_elements_out : forall x n l, ~InA eq_key (x, n) l -> multiplicity x (from_elements l) = 0.
  Proof.
  intros x n l Hin. induction l as [| [y p] l]; simpl.
  + apply empty_spec.
  + rewrite add_spec'.
      apply IHl. intro Habs. apply Hin. now right.
      intro Habs. apply Hin. now left.
  Qed.
  
  Lemma from_elements_in : forall x n l,
    NoDupA eq_key l -> InA eq_pair (x, n) l -> multiplicity x (from_elements l) = n.
  Proof.
  intros x n l Hl Hin. induction l as [| [y p] l].
  + rewrite InA_nil in Hin. elim Hin.
  + simpl. inversion_clear Hin.
    - destruct H as [Hx Hn]. compute in Hx, Hn. rewrite Hx, add_spec, (@from_elements_out y p). easy. now inversion Hl.
    - inversion_clear Hl. rewrite add_spec'. now apply IHl.
      intro Habs. apply H0. apply InA_pair_key with n. now rewrite Habs.
  Qed.
  
  Lemma from_elements_elements : forall m, from_elements (elements m) [=] m.
  Proof.
  intros m x. destruct (multiplicity x m) eqn:Hn.
  - apply from_elements_out with 0. intro Habs. apply InA_key_pair in Habs.
    destruct Habs as [n Habs]. rewrite elements_spec in Habs. simpl in Habs. omega.
  - apply from_elements_in. apply elements_NoDupA. rewrite elements_spec. simpl. omega.
  Qed.
  
  Lemma elements_from_elements : forall l, is_elements l -> PermutationA eq_pair (elements (from_elements l)) l.
  Proof.
  intros l Hl. rewrite is_elements_spec in Hl. destruct Hl as [m Hm]. now rewrite Hm, from_elements_elements.
  Qed.
  
  (** **  Results about [fold]  **)
  
  Lemma fold_empty : forall A f (x : A), fold f empty x = x.
  Proof. intros. rewrite M.fold_spec. rewrite elements_empty. simpl. reflexivity. Qed.
  
  Lemma fold_singleton : forall A f (x : A) y n,
    n > 0 -> Proper (E.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq) f -> fold f (singleton y n) x = f y n x.
  Proof.
  intros A f x y n Hn Hf. rewrite fold_spec. assert (Hy := elements_singleton y Hn).
  apply (PermutationA_length1 _) in Hy. destruct Hy as [[z p] [Heq Hl]].
  rewrite Hl. simpl. compute in Heq. destruct Heq. now rewrite H, H0.
  Qed.
  
  Section Fold_results.
    Variables (A : Type) (eqA : relation A).
    Context (HeqA : Equivalence eqA).
    Variable f : elt -> nat -> A -> A.
    Hypotheses (Hf : Proper (E.eq ==> Logic.eq ==> eqA ==> eqA) f)
               (Hf2 : forall x y n m a, eqA (f y m (f x n a)) (f x n (f y m a))).
    
    Instance fold_f_compat : Proper (eq ==> eqA ==> eqA) (fold f) := fold_compat _ _ _ Hf Hf2.
    
    Theorem fold_add : forall x n m (i : A), n > 0 -> ~In x m -> eqA (fold f (add x n m) i) (f x n (fold f m i)).
    Proof.
    intros x n m i Hn Hin. do 2 rewrite fold_spec.
    assert (Hperm : PermutationA eq_pair (elements (add x n m)) ((elements m) ++ (x, n) :: nil)).
    { rewrite elements_add_out; trivial. apply (PermutationA_cons_append _). }
    erewrite (fold_left_symmetry_PermutationA _ _); try apply Hperm || reflexivity.
    - do 2 rewrite <- fold_left_rev_right. now rewrite rev_unit.
    - intros ? ? ? [? ?] [? ?] [Heq ?]. now apply Hf.
    - intros [? ?] [? ?] ?. simpl. apply Hf2.
    Qed.
    
    Theorem fold_add_additive : (forall x n p acc, eqA (f x n (f x p acc)) (f x (n + p) acc)) ->
      forall x n m (i : A), n > 0 -> eqA (fold f (add x n m) i) (f x n (fold f m i)).
    Proof.
    intros Hfadd x n m i Hn. 
    destruct (multiplicity x m) eqn:Hm.
    + (* If [In x m], then we can simply use [fold_add] *)
      apply fold_add. assumption. unfold In. omega.
    + assert (Hperm : PermutationA eq_pair (elements (add x n m))
                     (elements (remove x (multiplicity x m) m) ++ (x, n + multiplicity x m) :: nil)).
      { etransitivity; try apply (PermutationA_cons_append _).
        rewrite <- elements_add_out; try omega.
          rewrite add_remove1; try omega. do 2 f_equiv. omega.
          unfold In. rewrite remove_spec. omega. }
      rewrite fold_spec. erewrite (fold_left_symmetry_PermutationA _ _); try apply Hperm || reflexivity.
      - rewrite <- fold_left_rev_right. rewrite rev_unit. simpl. rewrite <- Hfadd. f_equiv.
        rewrite fold_left_rev_right, <- fold_spec. etransitivity.
          symmetry. apply fold_add. omega. unfold In. rewrite remove_spec. omega.
          rewrite add_remove1; trivial. now rewrite minus_diag, add_0.
      - intros ? ? ? [? ?] [? ?] [Heq ?]. now apply Hf.
      - intros [? ?] [? ?] ?. simpl. apply Hf2.
    Qed.
    
    Existing Instance PermutationA_NoDupA_compat.
    
    Definition fold_rect : forall (P : t -> A -> Type) (i : A) (m : t),
    (forall m1 m2 acc, m1 [=] m2 -> P m1 acc -> P m2 acc) -> P empty i ->
    (forall x n m' acc, In x m -> n > 0 -> ~In x m' -> P m' acc -> P (add x n m') (f x n acc)) -> P m (fold f m i).
    Proof.
    intros P i m HP H0 Hrec. rewrite fold_spec. rewrite <- fold_left_rev_right.
    assert (Hrec' : forall x n acc m', InA eq_pair (x, n) (rev (elements m)) -> ~In x m' ->
                                         P m' acc -> P (add x n m') (f x n acc)).
    { intros ? ? ? ? ? Hin. rewrite (InA_rev _), elements_spec in H. simpl in H.
      destruct H. apply Hrec; trivial. unfold In. omega. }
    assert (Helt : is_elements (rev (elements m))). { rewrite <- (PermutationA_rev _). apply (elements_is_elements _). }
    clear Hrec. pose (l := rev (elements m)). fold l in Hrec', Helt.
    eapply HP. rewrite <- from_elements_elements. rewrite (PermutationA_rev _). reflexivity.
    fold l. clearbody l. induction l as [| [x n] l]; simpl.
    + (* elements m = nil *)
      assumption.
    + (* elements m = (x, n) :: l *)
      assert (Hdup := Helt). destruct Hdup as [Hdup _]. apply is_elements_cons_inv in Helt.
      apply Hrec'.
      - now left.
      - intro Habs. inversion_clear Hdup. apply H. rewrite <- elements_from_elements; trivial. now rewrite elements_In.
      - apply IHl.
          intros. apply Hrec'; trivial. now right.
          assumption.
    Qed.
    
    Lemma fold_rect_weak : forall (P : t -> A -> Type) (i : A) (m : t),
    (forall m1 m2 acc, m1 [=] m2 -> P m1 acc -> P m2 acc) -> P empty i ->
    (forall x n m' acc, n > 0 -> ~In x m' -> P m' acc -> P (add x n m') (f x n acc)) -> P m (fold f m i).
    Proof. intros * ? ? Hrec. apply fold_rect; trivial. intros. now apply Hrec. Qed.
    
    Lemma fold_rect_nodep : forall (P : A -> Type) (f : elt -> nat -> A -> A) (i : A) (m : t),
      P i -> (forall x n acc, In x m -> P acc -> P (f x n acc)) -> P (fold f m i).
    Proof.
    intros P ff i m H0 Hrec. rewrite fold_spec.
    assert (Hrec' : forall x n k acc, InA eq_key (x, k) (rev (elements m)) -> P acc -> P (ff x n acc)).
    { intros ? ? ? ? Hin. apply Hrec. rewrite <- elements_In, <- (InA_rev _). eassumption. }
    rewrite <- fold_left_rev_right. induction (rev (elements m)) as [| [x n] l]; simpl.
    + assumption.
    + eapply Hrec'. now left. apply IHl. intros. apply Hrec' with k; trivial. now right.
    Qed.
    
    (* Wrong in general when m1 and m2 are not disjoint. *)
    Lemma fold_union : forall m1 m2 (i : A), (forall x, In x m1 -> In x m2 -> False) ->
      eqA (fold f (union m1 m2) i) (fold f m1 (fold f m2 i)).
    Proof.
    intros m1 m2 i Hm. apply fold_rect with (m := m1); trivial.
    + intros * Heq. now rewrite Heq.
    + now rewrite union_empty_l.
    + intros. rewrite union_add_comm_l, <- H2. apply fold_add. assumption.
      unfold In in *. rewrite union_spec. intro Habs. apply (Hm x). assumption. omega.
    Qed.
    
    Lemma fold_union_additive : (forall x n p acc, eqA (f x n (f x p acc)) (f x (n + p) acc)) ->
      forall m1 m2 (i : A), eqA (fold f (union m1 m2) i) (fold f m1 (fold f m2 i)).
    Proof.
    intros Hfadd m1 m2 i. apply fold_rect with (m := m1).
    + intros * Heq. now rewrite Heq.
    + now rewrite union_empty_l.
    + intros. rewrite union_add_comm_l, <- H2. now apply fold_add_additive.
    Qed.
  End Fold_results.
  
  Lemma union_fold_add : forall m1 m2, fold (fun x n acc => add x n acc) m1 m2 [=] union m1 m2.
  Proof.
  intros m1 m2 x. apply fold_rect with (m := m1).
  + intros * Heq1 Heq2. now rewrite <- Heq1, Heq2.
  + now rewrite union_empty_l.
  + intros. rewrite union_add_comm_l. destruct (E.eq_dec x0 x) as [Heq | Hneq].
    - rewrite Heq. do 2 rewrite add_spec. now rewrite H2.
    - now repeat rewrite add_spec'.
  Qed.
  
  Corollary fold_add_id : forall m, fold (fun x n acc => add x n acc) m empty [=] m.
  Proof. intro. now rewrite union_fold_add, union_empty_r. Qed.
  
  (** **  Generic induction principles on multisets  **)
  
  Definition rect : forall P, (forall m1 m2, m1 [=] m2 -> P m1 -> P m2) ->
    (forall m x n, ~In x m -> n > 0 -> P m -> P (add x n m)) ->
    P empty -> forall m, P m.
  Proof. intros P HP ? ? ?. apply (@fold_rect _ (fun _ _ _ => tt) (fun m _ => P m) tt); eauto. Defined.
  
  Definition ind : forall P, Proper (eq ==> iff) P ->
    (forall m x n, ~In x m -> n > 0 -> P m -> P (add x n m)) ->
    P empty -> forall m, P m.
  Proof. intros. apply rect; trivial. intros ? ? Heq. now rewrite Heq. Qed.
  (*  
  Definition rect : forall P, (forall m1 m2, m1 [=] m2 -> P m1 -> P m2) ->
    (forall m x n, ~In x m -> P m -> P (add x n m)) ->
    P empty -> forall m, P m.
  Proof.
  intros P Heq Hadd H0.
  (* The proof goes by induction on [elements m] so we first replace all [m] by [elements m] and prove the premises. *)
  pose (P' := fun l => P (fold_left (fun acc xn => add (fst xn) (snd xn) acc) l empty)).
  assert (Pequiv1 : forall m, P m -> P' (elements m)).
  { intro. unfold P'. apply Heq. rewrite <- fold_spec. symmetry. apply fold_add_id. }
  assert (Pequiv2 : forall m, P' (elements m) -> P m).
  { intro. unfold P'. apply Heq. rewrite <- fold_spec. apply fold_add_id. }
  assert (HP' : forall l1 l2, PermutationA eq_pair l1 l2 -> P' l1 -> P' l2).
  { intros l1 l2 Hl. unfold P'.
    assert (Hf : Proper (eq ==> eq_pair ==> eq) (fun acc xn => add (fst xn) (snd xn) acc)).
    { repeat intro. now rewrite H1, H. }
    apply Heq. apply (@fold_left_symmetry_PermutationA _ _ eq_pair eq _ _ _ Hf); reflexivity || trivial.
    intros [x n] [y p] acc. simpl. apply add_comm. }
  assert (Hadd' : forall l x n, is_elements l -> n > 0 -> ~InA eq_key (x, n) l -> P' l -> P' ((x, n) :: l)).
  { intros l x n Hl Hn Hin. apply is_elements_build in Hl. destruct Hl as [m Hm]. rewrite Hm in Hin.
    assert (Hx : ~In x m).
    { rewrite <- support_spec, support_elements. intro Habs. apply Hin. eapply InA_pair_key. eassumption. }
    intro Hl. apply (HP' _ _ Hm), Pequiv2, Hadd with m x n, Pequiv1 in Hl; trivial. revert Hl.
    apply HP'. etransitivity. now apply elements_add_out. now apply PermutationA_cons. }
  (* The real proof starts. *)
  intro m. apply Pequiv2. generalize (elements_is_elements m).
  induction (elements m) as [| [x n] l]; intro Hl.
  + unfold P'. simpl. apply H0.
  + apply Hadd'.
    - eapply is_elements_cons_inv. eassumption.
    - destruct Hl as [_ Hpos]. now inversion_clear Hpos.
    - destruct Hl as [Hdup _]. now inversion_clear Hdup.
    - apply IHl. eapply is_elements_cons_inv. eassumption.
  Qed.
  *)
  
  (** **  Results about [support]  **)
  
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
                                <-> m [=] singleton x (multiplicity x m) /\ (multiplicity x m) > 0.
  Proof.
  intros x m. split; intro Hm.
  + assert (Hin : In x m). { rewrite <- support_spec, Hm. now left. }
    unfold In in Hin. split; try omega. intro y. rewrite singleton_spec.
    destruct (E.eq_dec y x) as [Heq | Hneq]. now rewrite Heq.
    destruct (multiplicity y m) eqn:Hy. reflexivity.
    assert (Hiny : In y m). { unfold In. rewrite Hy. omega. }
    rewrite <- support_spec, Hm in Hiny. inversion_clear Hiny. contradiction. inversion H.
  + destruct Hm as [Hm Hmult]. rewrite Hm. apply support_singleton. omega.
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
  
  (** **  Results about [cardinal]  **)
  
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
  rewrite cardinal_spec, fold_spec.
  apply (PermutationA_split _) in Hin. destruct Hin as [l Hperm]. assert (H0 := eq_refl 0).
  rewrite fold_left_cardinal; try eassumption. simpl. rewrite plus_0_r. now apply cardinal_lower_aux.
  Qed.
  
  Lemma cardinal_empty : cardinal empty = 0.
  Proof. now rewrite cardinal_spec, fold_spec, elements_empty. Qed.
  
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
  
  Lemma cardinal_singleton : forall x n, cardinal (singleton x n) = n.
  Proof.
  intros. destruct n.
  + rewrite singleton_0. apply cardinal_empty.
  + rewrite cardinal_spec, fold_spec.
    rewrite fold_left_cardinal; try eapply elements_singleton.
      simpl. now rewrite plus_0_r.
      omega.
      omega.
  Qed.
  
  Instance fold_cardinal_compat : Proper (eq ==> Logic.eq ==> Logic.eq) (fold (fun x n acc => n + acc)).
  Proof.
  intros m₁ m₂ Hm ? ? ?. apply (fold_compat _ _); trivial.
  - now repeat intro; subst.
  - intros. omega.
  Qed.
  
  Theorem cardinal_union : forall m₁ m₂, cardinal (union m₁ m₂) = cardinal m₁ + cardinal m₂.
  Proof.
  intros m₁ m₂. do 2 rewrite cardinal_spec. rewrite (fold_union_additive _).
  + rewrite <- cardinal_spec. revert m₁. apply ind.
    - intros ? ? Heq. now rewrite Heq.
    - intros. destruct n.
        now rewrite add_0.
        repeat rewrite (fold_add _); trivial; intros; omega || now repeat intro; subst.
    - now do 2 rewrite fold_empty.
  + now repeat intro; subst.
  + intros. omega.
  + intros. omega.
  Qed.
  
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
  
  Lemma Empty_spec : forall m, Empty m <-> m [=] empty.
  Proof.
  intro m. split; intros H x.
  - rewrite empty_spec. apply H.
  - rewrite H. apply empty_spec.
  Qed.
  
  Lemma fold_extensionality_compat (A : Type) (eqA : relation A) `(Equivalence A eqA) :
    forall f : elt -> nat -> A -> A, Proper (E.eq ==> Logic.eq ==> eqA ==> eqA) f ->
      (forall x y x' y' z, eqA (f x x' (f y y' z)) (f y y' (f x x' z))) ->
    forall g, (forall x v acc, eqA (f x v acc) (g x v acc)) ->
    forall m i, eqA (fold f m i) (fold g m i).
  Proof.
  intros f Hf Hf2 g Hext m i.
  assert (Hg : Proper (E.eq ==> Logic.eq ==> eqA ==> eqA) g).
  { repeat intro. repeat rewrite <- Hext. apply Hf; assumption. }
  assert (Hg2 : forall x y x' y' z, eqA (g y y' (g x x' z)) (g x x' (g y y' z))).
  { repeat intro. repeat rewrite <- Hext. apply Hf2. }
  apply fold_rect.
  + intros m1 m2 acc Hm Heq. rewrite Heq. apply (fold_compat _ _ g Hg Hg2); assumption || reflexivity.
  + rewrite fold_empty. reflexivity.
  + intros x n m' acc Hin Hn Hout Heq. rewrite Hext, Heq. rewrite fold_add; reflexivity || assumption.
  Qed.
  
  Lemma filter_extensionality_compat : forall f, compatb f ->
    forall g m, (forall x n, g x n = f x n) -> filter f m [=] filter g m.
  Proof.
  intros f Hf g m Hext x.
  assert (Hg : Proper (E.eq ==> Logic.eq ==> Logic.eq) g). { repeat intro. repeat rewrite Hext. now apply Hf. }
  repeat rewrite filter_spec; trivial. rewrite Hext. reflexivity.
  Qed.
  
  (** *  Extra operations  **)
  
  (** **  Function [map] and its properties  **)
  
  Definition map f m := fold (fun x n acc => add (f x) n acc) m empty.
  
  Global Instance map_compat : forall f, Proper (E.eq ==> E.eq) f -> Proper (eq ==> eq) (map f).
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
  intros f Hf Hinj x m. unfold map. apply fold_rect.
  + intros * Heq. now rewrite Heq.
  + now do 2 rewrite empty_spec.
  + intros y n m' Hin Hn Hpos Hm Heq. destruct (E.eq_dec y x) as [Hxy | Hxy].
    - rewrite Hxy. do 2 rewrite add_spec. now rewrite Heq.
    - repeat rewrite add_spec'; trivial. intro Habs. apply Hxy. now apply Hinj.
  Qed.
  
  Lemma map_empty : forall f, map f empty [=] empty.
  Proof. intro f. unfold map. now rewrite fold_empty. Qed.
  
  Lemma map_In : forall x f m, In x (map f m) -> exists y, E.eq x (f y) /\ In y m.
  Proof.
  intros x f m. unfold In, map. apply fold_rect_nodep.
  + rewrite empty_spec. omega.
  + intros y p acc Hm Hrec Hin. destruct (E.eq_dec (f y) x).
    - now exists y.
    - apply Hrec. now rewrite add_spec' in Hin.
  Qed.
  
  Lemma map_add : forall f, Proper (E.eq ==> E.eq) f ->
    forall x n m, map f (add x n m) [=] add (f x) n (map f m).
  Proof.
  intros f Hf x n m y. destruct n.
  + now do 2 rewrite add_0.
  + unfold map at 1. rewrite (fold_add_additive _).
    - reflexivity.
    - intros ? ? Heq1 * ? * Heq2 ? ? Heq3. now rewrite Heq1, Heq2, Heq3.
    - intros. apply add_comm.
    - intros. apply add_combine.
    - omega.
  Qed.
  
  Lemma fold_map_union : forall f, Proper (E.eq ==> E.eq) f ->
    forall m₁ m₂, fold (fun x n acc => add (f x) n acc) m₁ m₂ [=] union (map f m₁) m₂.
  Proof.
  intros f Hf m₁ m₂. apply fold_rect with (m := m₁).
  + intros * Heq. now rewrite Heq.
  + now rewrite map_empty, union_empty_l.
  + intros. now rewrite H2, map_add, union_add_comm_l.
  Qed.
  
  Lemma map_union : forall f, Proper (E.eq ==> E.eq) f ->
    forall m₁ m₂, map f (union m₁ m₂) [=] union (map f m₁) (map f m₂).
  Proof.
  intros f Hf m₁ m₂. unfold map at 1 2. rewrite (fold_union_additive _).
  + now apply fold_map_union.
  + intros ? ? Heq1 * ? * Heq2 ? ? Heq3. now rewrite Heq1, Heq2, Heq3.
  + intros. apply add_comm.
  + intros. apply add_combine.
  Qed.
  
  Lemma map_support : forall f, Proper (E.eq ==> E.eq) f -> injective E.eq E.eq f ->
    forall m, PermutationA E.eq (support (map f m)) (List.map f (support m)).
  Proof.
  intros f Hf Hfinj. apply ind.
  + intros m1 m2 Heq. now rewrite Heq.
  + intros m x n Hin Hrec. destruct n.
    - now rewrite add_0.
    - rewrite map_add; trivial. repeat rewrite support_add; try omega.
      destruct (InA_dec (eqA:=E.eq) E.eq_dec (f x) (support (map f m))) as [Habs | _].
        rewrite support_spec in Habs. unfold In in *. rewrite (map_spec Hf Hfinj) in Habs. contradiction.
        destruct (InA_dec (eqA:=E.eq) E.eq_dec x (support m)) as [Habs | _].
          rewrite support_spec in Habs. unfold In in *. contradiction.
          simpl. now apply PermutationA_cons.
  + now rewrite map_empty, support_empty.
  Qed.
  
  Lemma map_injective_filter : forall f g, compatb f -> Proper (E.eq ==> E.eq) g -> injective E.eq E.eq g ->
    forall m, filter f (map g m) [=] map g (filter (fun x => f (g x)) m).
  Proof. Admitted. (* proved in the bigger library *)
  
  Lemma map_extensionality_compat : forall f g, Proper (E.eq ==> E.eq) f ->
    (forall x, g x = f x) -> forall m, map g m [=] map f m.
  Proof. Admitted. (* proved in the bigger library *)
  
  Lemma cardinal_total_sub_eq : forall m1 m2, m1 [<=] m2 -> cardinal m1 = cardinal m2 -> m1 [=] m2.
  Proof. Admitted. (* proved in the bigger library *)
  
  Lemma support_filter : forall f, compatb f -> forall m, inclA E.eq (support (filter f m)) (support m).
  Proof. Admitted. (* proved in the bigger library *)
  
  Lemma filter_empty : forall f, compatb f -> filter f empty [=] empty.
  Proof. repeat intro. rewrite filter_spec, empty_spec; trivial. now destruct (f x 0). Qed.
  
  Lemma filter_none : forall f, compatb f ->
    forall m, filter f m [=] empty <-> for_all (fun x n => negb (f x n)) m = true.
  Proof. Admitted. (* proved in the bigger library *)
  
  Lemma empty_or_In_dec : forall m : t, {m [=] empty} + {(exists x : elt, In x m)}.
  Proof. Admitted. (* proved in the bigger library *)
  
  Lemma filter_In : forall f, compatb f ->
    forall x m, In x (filter f m) <-> In x m /\ f x (multiplicity x m) = true.
  Proof.
  intros f Hf x m. unfold In. rewrite filter_spec; trivial.
  destruct (f x (multiplicity x m)); intuition; discriminate.
  Qed.
  
End Make.
