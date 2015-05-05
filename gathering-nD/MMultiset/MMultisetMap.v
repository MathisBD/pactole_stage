Require Import Arith_base.
Require Import Omega.
Require Import PArith.
Require Import Equalities.
Require Import FMapInterface.
Require Import RelationPairs.
Require Import FMultisets.Preliminary.
Require Import FMultisets.FMultisetInterface.


Module FMultisets (FMap : WSfun) (E : DecidableType) : FMultisetsOn E.

Module M := FMap(E).

Definition eq_pair := RelProd E.eq (@Logic.eq nat).
Definition eq_key := RelCompFun E.eq (@fst E.t nat).

Instance Eeq_equiv : Equivalence E.eq.
Proof. split.
  exact E.eq_refl.
  exact E.eq_sym.
  exact E.eq_trans.
Qed.

Instance Meq_equiv A : Equivalence (@M.eq_key_elt A).
Proof. split.
  intro. reflexivity.
  intros ? ?. now symmetry.
  intros ? y ? ? ?. now transitivity y.
Qed.

Instance Meq_key_equiv A : Equivalence (@M.eq_key A).
Proof. split.
  intro. reflexivity.
  intros ? ?. now symmetry.
  intros ? y ? ? ?. now transitivity y.
Qed.

Instance eq_pair_equiv : Equivalence eq_pair.
Proof. split. easy. easy. intros ? y ? ? ?. now transitivity y. Qed.

Lemma Meq_dec : forall x y : E.t * positive, {M.eq_key_elt x y} + {~M.eq_key_elt x y}.
Proof.
intros [t1 n1] [t2 n2].
destruct (E.eq_dec t1 t2). destruct (Pos.eq_dec n1 n2).
  left. now split.
  right. intros []. contradiction.
  right. intros []. contradiction.
Defined.

Lemma eq_key_elt_eq_key_weak_In B : forall x y n m l, 
  E.eq x y -> InA (@M.eq_key_elt B) (x, n) l -> InA (@M.eq_key B) (y, m) l.
Proof.
intros x y n m l Heq Hin. induction l.
+ now inversion Hin.
+ inversion_clear Hin.
  - left. destruct a. compute in *. destruct H. now transitivity x; auto.
  - right. now apply IHl.
Qed.

Lemma NoDup_pair_In : forall A x y n m l, NoDupA (@M.eq_key A) l ->
  InA (@M.eq_key_elt _) (x, n) l -> InA (@M.eq_key_elt _) (y, m) l -> E.eq x y -> n = m.
Proof.
intros A x y n m l Hl Hinx Hiny Heq. induction Hl as [| [z p] l]. inversion_clear Hiny.
inversion_clear Hinx; inversion_clear Hiny.
- compute in H0, H1. destruct H0 as [H0 ?], H1 as [H1 ?]. now subst p m.
- compute in H0. destruct H0 as [H0 ?]. subst p. elim H.
  apply eq_key_elt_eq_key_weak_In with y m. transitivity x; auto. assumption.
- compute in H1. destruct H1 as [H1 ?]. subst p. elim H.
  apply eq_key_elt_eq_key_weak_In with x n. now transitivity y; auto. assumption.
- now apply IHHl.
Qed.

Lemma Melements_InA : forall A x n s, InA (@M.eq_key_elt A) (x, n) (M.elements s) <-> M.MapsTo x n s.
Proof. intros. split; intro H. now apply M.elements_2. now apply M.elements_1. Qed.

Definition elt := E.t.
Definition t := M.t positive.

Definition empty : t := M.empty positive.
Definition is_empty (s : t) := M.is_empty s.
Definition multiplicity x (s : t) := match M.find x s with Some n => Pos.to_nat n | None => 0 end.
Definition add (x : elt) (n : nat) (s : t) : t := 
  if eq_nat_dec n 0 then s else M.add x (Pos.of_nat (multiplicity x s + n)) s.
Definition singleton x n := add x n empty.
Definition remove (x : elt) (n : nat) (s : t) : t :=
  if eq_nat_dec n 0 then s else
  if le_lt_dec (multiplicity x s) n then M.remove x s else M.add x (Pos.of_nat (multiplicity x s - n)) s.
Definition union (s s' : t) := M.fold (fun x n acc => add x (Pos.to_nat n) acc) s s'.
Definition inter (s s' : t) :=
  M.fold (fun x n acc => add x ((fun x n => min (multiplicity x s) (Pos.to_nat n)) x n) acc) s' empty.
Definition diff (s s' : t) := M.fold (fun x n acc => add x (Pos.to_nat n - multiplicity x s') acc) s empty.
Definition lub (s s' : t) := M.fold (fun x n acc => add x (Pos.to_nat n - multiplicity x s') acc) s s'.
Definition equal (s s' : t) := M.equal Pos.eqb s s'.
Definition subset s s' := is_empty (diff s s').
(* Definition fold {A} f (s : t) := @M.fold _ A (fun x _ => f x) (projS1 s). *)
Definition fold {A} f (s : t) := @M.fold positive A (fun x y => f x (Pos.to_nat y)) s.
Definition for_all f (s : t) := M.fold (fun x n b => b && f x (Pos.to_nat n)) s true.
Definition exists_ f (s : t) := M.fold (fun x n b => b || f x (Pos.to_nat n)) s false.
Definition filter f (s : t) :=
  M.fold (fun x n acc => if f x (Pos.to_nat n) : bool then add x (Pos.to_nat n) acc else acc) s empty.
Definition partition f (s : t) :=
  M.fold (fun x n acc => if f x (Pos.to_nat n) : bool then (add x (Pos.to_nat n) (fst acc), snd acc)
                                                      else (fst acc, add x (Pos.to_nat n) (snd acc))) s (empty,empty).
Definition cardinal (s : t) := M.fold (fun _ n acc => Pos.to_nat n + acc) s 0.
Definition size (s : t) := M.fold (fun _ _ n => S n) s 0.
Definition elements (s : t) := List.map (fun xy => (fst xy, Pos.to_nat (snd xy))) (M.elements s).
Definition support (s : t) := M.fold (fun x _ l => cons x l) s nil.
Definition choose (s : t) := M.fold (fun x _ _ => Some x) s None.

Definition In := fun x s => multiplicity x s > 0.
Definition eq s s' := forall x, multiplicity x s = multiplicity x s'.
Definition Subset s s' := forall x, multiplicity x s <= multiplicity x s'.
Definition For_all (P : elt -> nat -> Prop) s := forall x, In x s -> P x (multiplicity x s).
Definition Exists (P : elt -> nat -> Prop) s := exists x, In x s /\ P x (multiplicity x s).

Global Notation "s  [=]  t" := (eq s t) (at level 70, no associativity).
Global Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

Instance multiplicity_compat : Proper (E.eq ==> eq ==> Logic.eq) multiplicity.
Proof.
intros x y Hxy s s' ?. transitivity (multiplicity x s').
* apply H.
* unfold multiplicity. simpl. destruct (M.find x s') eqn:Hin.
  + apply M.find_2 in Hin. apply (M.MapsTo_1 Hxy) in Hin.
    apply M.find_1 in Hin. now rewrite Hin.
  + destruct (M.find y s') eqn:Hy.
    - apply M.find_2 in Hy. apply (M.MapsTo_1 (symmetry Hxy)) in Hy.
      apply M.find_1 in Hy. rewrite Hy in Hin. discriminate Hin.
    - reflexivity.
Qed.

Global Instance eq_equiv : Equivalence eq.
Proof. split; try easy. intros x y z Hxy Hyz a. now rewrite Hxy, Hyz. Qed.
(** [eq] is obviously an equivalence, for subtyping only. *)

Instance In_compat : Proper (E.eq ==> eq ==> iff) In.
Proof. intros x y Hxy s s' ?. unfold In. now rewrite H, Hxy. Qed.

Theorem In_dec : forall x s, {In x s} + {~In x s}.
Proof. unfold In. intros. apply gt_dec. Qed.

Lemma In_MIn : forall x s, In x s <-> M.In x s.
Proof.
intros x s. split; intro H.
- exists (Pos.of_nat (multiplicity x s)). apply M.find_2. unfold In, multiplicity in *.
  destruct (M.find x s). now rewrite Pos2Nat.id. now inversion H.
- destruct H as [n Hn]. apply M.find_1 in Hn. unfold In, multiplicity. rewrite Hn. now apply Pos2Nat.is_pos.
Qed.

Lemma Mequal_Mequivb_equiv : forall s s' : M.t positive, M.Equal s s' <-> M.Equivb Pos.eqb s s'.
Proof.
intros s s'. split.
+ intro Heq. split.
  - intro x. split; intros [e Hin]; exists e; apply M.find_1 in Hin; apply M.find_2.
    now rewrite <- Heq. now rewrite Heq.
  - intros x e e' He He'. apply M.find_1 in He. apply M.find_1 in He'.
    rewrite Heq in He. rewrite He in He'. inversion_clear He'. unfold Cmp. now apply Pos.eqb_refl.
+ intros [Heq1 Heq2] x.
  destruct (M.find x s) as [e |] eqn:Hfind, (M.find x s') as [e' |] eqn:Hfind'.
  - f_equal. apply Pos.eqb_eq. apply (Heq2 x); now apply M.find_2.
  - assert (Habs : M.In x s'). { rewrite <- Heq1. exists e. now apply M.find_2. }
    destruct Habs as [e' Habs]. apply M.find_1 in Habs. rewrite Hfind' in Habs. discriminate Habs.
  - assert (Habs : M.In x s). { rewrite Heq1. exists e'. now apply M.find_2. }
    destruct Habs as [e Habs]. apply M.find_1 in Habs. rewrite Hfind in Habs. discriminate Habs.
  - reflexivity.
Qed.

Lemma multiplicity_find_in : forall x s, In x s -> M.find x s = Some (Pos.of_nat (multiplicity x s)).
Proof.
intros x s Hin. unfold In, multiplicity in *. destruct (M.find x s) eqn:Hfind.
- now rewrite Pos2Nat.id.
- now inversion Hin.
Qed.

Lemma multiplicity_out : forall x s, multiplicity x s = 0 <-> M.find x s = None.
Proof.
unfold multiplicity. intros x s. split; intro Hs.
+ destruct (M.find x s).
  - elim (lt_irrefl 0). rewrite <- Hs at 2. now apply Pos2Nat.is_pos.
  - reflexivity.
+ now rewrite Hs.
Qed.

Lemma equal_spec : forall s s', equal s s' = true <-> s[=]s'.
Proof.
intros s s'. unfold equal. simpl. destruct (M.equal Pos.eqb s s') eqn:Heq.
+ split; intro H; trivial || clear H. apply M.equal_2 in Heq.
  rewrite <- Mequal_Mequivb_equiv in Heq. unfold eq, multiplicity. intro. now rewrite Heq.
+ split; intro Habs; try discriminate Habs. exfalso.
  assert (Hneq : ~M.Equivb Pos.eqb s s').
  { intro Habs'. apply M.equal_1 in Habs'. rewrite Heq in Habs'. discriminate Habs'. }
  rewrite <- Mequal_Mequivb_equiv in Hneq. apply Hneq. intro x.
  unfold eq, multiplicity in Habs. specialize (Habs x). simpl in Habs.
  destruct (M.find x s) eqn:Hin1, (M.find x s') eqn:Hin2.
  - f_equal. now apply Pos2Nat.inj.
  - elim (lt_irrefl 0). rewrite <- Habs at 2. now apply Pos2Nat.is_pos.
  - elim (lt_irrefl 0). rewrite Habs at 2. now apply Pos2Nat.is_pos.
  - reflexivity.
Qed.

Corollary eq_dec : forall s s' : t, {s [=] s'} + {~s [=] s'}.
Proof.
intros s s'. destruct (equal s s') eqn:Heq.
- left. now rewrite <- equal_spec.
- right. rewrite <- equal_spec. rewrite Heq. discriminate.
Qed.

Lemma empty_spec : forall x, multiplicity x empty = 0.
Proof.
intro x. unfold multiplicity, empty.
destruct (M.find x (M.empty positive)) eqn:Hin.
- elim (@M.empty_1 positive x p). now apply M.find_2.
- reflexivity.
Qed.

Lemma is_empty_spec : forall s, is_empty s = true <-> s [=] empty.
Proof.
intros s. unfold is_empty. split; intro H.
+ apply M.is_empty_2 in H. intros x. unfold M.Empty in H. rewrite empty_spec.
  unfold multiplicity. destruct (M.find x s) eqn:Hin.
  - elim (H x p). now apply M.find_2.
  - reflexivity.
+ apply M.is_empty_1. intros x n Habs. apply M.find_1 in Habs. specialize (H x). rewrite empty_spec in H.
  unfold multiplicity in H. rewrite Habs in H. elim (lt_irrefl 0). rewrite <- H at 2. apply Pos2Nat.is_pos.
Qed.

Corollary is_empty_multiplicity : forall x s, is_empty s = true -> multiplicity x s = 0.
Proof.
intros x s Hs. unfold multiplicity. destruct (M.find x s) eqn:Hin.
+ rewrite is_empty_spec in Hs. specialize (Hs x). unfold multiplicity in Hs. rewrite Hin in Hs.
  rewrite Hs. destruct (M.find x empty) eqn:Habs.
  - apply M.find_2 in Habs. now elim (M.empty_1 Habs).
  - reflexivity.
+ reflexivity.
Qed.

Lemma add_same : forall x n s, multiplicity x (add x n s) = multiplicity x s + n.
Proof.
intros x n s. unfold add. destruct (eq_nat_dec n 0). omega.
unfold multiplicity at 1. simpl.
rewrite (M.find_1 (M.add_1 s (Pos.of_nat (multiplicity x s + n)) (reflexivity x))).
rewrite Nat2Pos.id. reflexivity. omega.
Qed.

Lemma add_other : forall x y n s, ~E.eq y x -> multiplicity y (add x n s) = multiplicity y s.
Proof.
intros x y n s Hyx. unfold add. destruct (eq_nat_dec n 0). reflexivity. unfold multiplicity at 1 3. simpl.
assert (Hxy : ~E.eq x y) by auto. destruct (M.find y s) eqn:Heq.
+ apply (@M.add_2 positive s x y (Pos.of_nat (multiplicity y s)) (Pos.of_nat (multiplicity x s + n))) in Hxy.
  - apply M.find_1 in Hxy. rewrite Hxy. unfold multiplicity. now rewrite Heq, Pos2Nat.id.
  - apply M.find_2. unfold multiplicity. now rewrite Heq, Pos2Nat.id.
+ destruct (M.find y (M.add x (Pos.of_nat (multiplicity x s + n)) s)) eqn:Heq2.
  - apply M.find_2 in Heq2. apply (M.add_3 Hxy) in Heq2. apply M.find_1 in Heq2.
    rewrite Heq2 in Heq. discriminate Heq.
  - reflexivity.
Qed.

Lemma remove_same : forall x n s, multiplicity x (remove x n s) = multiplicity x s - n.
Proof.
intros x n s. unfold remove. destruct (eq_nat_dec n 0). omega.
destruct (le_lt_dec (multiplicity x s) n) as [Hle | Hlt]; unfold multiplicity at 1; simpl.
+ destruct (M.find x (M.remove x s)) eqn:Hin.
  - apply M.find_2 in Hin. exfalso. apply (@M.remove_1 _ s x x (reflexivity x)). now exists p.
  - omega.
+ assert (Heq : M.find x (M.add x (Pos.of_nat (multiplicity x s - n)) s) = Some (Pos.of_nat (multiplicity x s - n))).
  { apply M.find_1. apply M.add_1. reflexivity. }
  rewrite Heq, Nat2Pos.id. reflexivity. omega.
Qed.

Lemma remove_other : forall x y n s, ~E.eq y x -> multiplicity y (remove x n s) = multiplicity y s.
Proof.
intros x y n s Hyx. unfold remove. destruct (eq_nat_dec n 0). reflexivity.
assert (Hxy : ~E.eq x y) by auto.
destruct (le_lt_dec (multiplicity x s) n) as [Hle | Hlt]; unfold multiplicity at 1; simpl.
* destruct (M.find y (M.remove x s)) eqn:Hin.
  + apply M.find_2, (@M.remove_3 _ s), M.find_1 in Hin. unfold multiplicity. now rewrite Hin.
  + unfold multiplicity. destruct (M.find y s) eqn:Habs.
    - apply M.find_2, (M.remove_2 Hxy), M.find_1 in Habs. rewrite Hin in Habs. discriminate Habs.
    - reflexivity.
* unfold multiplicity at 2. destruct (M.find y s) eqn:Hin.
  + apply M.find_2, (M.add_2 (Pos.of_nat (multiplicity x s - n)) Hxy), M.find_1 in Hin. now rewrite Hin.
  + destruct (M.find y (M.add x (Pos.of_nat (multiplicity x s - n)) s)) eqn:Habs.
    - apply M.find_2, (@M.add_3 _ s), M.find_1 in Habs. rewrite Hin in Habs. discriminate Habs. assumption.
    - reflexivity.
Qed.

Lemma singleton_same : forall x n, multiplicity x (singleton x n) = n.
Proof.
intros x n. unfold singleton, add. destruct (eq_nat_dec n 0).
+ subst n. apply empty_spec.
+ rewrite empty_spec. simpl. unfold multiplicity.
  rewrite (M.find_1 (M.add_1 _ _ (reflexivity _))). now apply Nat2Pos.id.
Qed.

Lemma singleton_other : forall x y n, ~E.eq y x -> multiplicity y (singleton x n) = 0.
Proof.
intros x y n Heq. unfold singleton, add. destruct (eq_nat_dec n 0).
+ subst n. apply empty_spec.
+ rewrite empty_spec. simpl. unfold multiplicity.
  destruct (M.find y (M.add x (Pos.of_nat n) empty)) eqn:Hin; trivial.
  apply M.find_2, M.add_3 in Hin. exfalso. apply (M.empty_1 Hin). now auto.
Qed.

Lemma fold_add_out_list : forall f x n l s, ~InA (@M.eq_key positive) (x, n) l -> NoDupA (@M.eq_key _) l ->
  multiplicity x (fold_left (fun acc xn => add (fst xn) (f (fst xn) (snd xn)) acc) l s) = multiplicity x s.
Proof.
intros f x n l s Hin Hdup. revert s. induction l as [| [y m] l]; intro s; simpl.
- reflexivity.
- rewrite IHl. apply add_other. intro Habs. apply Hin. left. compute. auto. auto. now inversion_clear Hdup.
Qed.

Lemma fold_add_out : forall f x (s s' : t), ~M.In x s -> 
  multiplicity x (M.fold (fun x n acc => add x (f x n) acc) s s') = multiplicity x s'.
Proof.
intros f x s s' Hin. rewrite M.fold_1.
assert (Hs : forall n, ~(InA (@M.eq_key_elt _) (x, n) (M.elements s))).
{ intros n Habs. apply Hin. exists n. now apply M.elements_2. }
revert s'. induction (M.elements s) as [| [y m] l]; intro s'; simpl.
+ reflexivity.
+ assert ( Hxy : ~E.eq x y). { intro Habs. apply (Hs m). left. now split. }
  rewrite IHl.
  - apply add_other. now auto.
  - intros n Habs. apply (Hs n). now right.
Qed.

Notation compatb := (Proper (E.eq ==> Logic.eq ==> Logic.eq)) (only parsing).

Lemma fold_add : forall f x (s s' : t), compatb f -> M.In x s -> 
  multiplicity x (M.fold (fun x n acc => add x (f x (Pos.to_nat n)) acc) s s')
  = f x (multiplicity x s) + multiplicity x s'.
Proof.
intros f x s s' Hf [n Hin]. rewrite M.fold_1.
assert (Hs : InA (@M.eq_key_elt positive) (x, n) (M.elements s)) by now apply M.elements_1.
assert (Hdup := M.elements_3w s).
revert s'. induction (M.elements s) as [| [y m] l]; intro s'; simpl; [now inversion Hs |].
destruct (Meq_dec (x, n) (y, m)) as [[H1 H2] | Hneq]; simpl in *; try subst m.
* transitivity (multiplicity x (add y (f y (Pos.to_nat n)) s')).
  + rewrite (fold_add_out_list (fun x y => f x (Pos.to_nat y)) x n).
    - reflexivity.
    - inversion_clear Hdup. clear -H H1. intro Habs. apply H. revert Habs. apply InA_eqA; trivial. refine _.
    - now inversion_clear Hdup.
  + rewrite H1, add_same, plus_comm. f_equal. unfold multiplicity.
    apply (M.MapsTo_1 H1) in Hin. apply M.find_1 in Hin. now rewrite Hin.
* rewrite IHl.
  + f_equal. apply add_other. intro Habs. apply Hneq. compute. split. now auto.
    apply (NoDup_pair_In _ x y n m ((y, m) :: l)); trivial. left. compute. now auto.
  + inversion_clear Hs. contradiction. assumption.
  + now inversion_clear Hdup.
Qed.

Lemma union_spec : forall x s s', multiplicity x (union s s') = multiplicity x s + multiplicity x s'.
Proof.
intros x s s'. unfold union. destruct (M.find x s) eqn:Hin.
- apply (fold_add (fun x n => n)). now intros until 2. exists p. now apply M.find_2.
- unfold multiplicity at 2. rewrite Hin. simpl. apply fold_add_out.
  intros [n Habs]. apply M.find_1 in Habs. rewrite Hin in Habs. discriminate Habs.
Qed.

Lemma inter_spec : forall x s s', multiplicity x (inter s s') = min (multiplicity x s) (multiplicity x s').
Proof.
intros x s s'. unfold inter. destruct (M.find x s') eqn:Hin.
+ rewrite (fold_add (fun x n => min (multiplicity x s) n) x s' empty).
  - rewrite (empty_spec x). now rewrite plus_0_r.
  - intros ? ? Heq ? ? ?. simpl. subst. now rewrite Heq.
  - exists p. now apply M.find_2.
+ rewrite fold_add_out.
  - unfold multiplicity at 3. rewrite Hin. rewrite Min.min_0_r. now apply empty_spec.
  - intros [n Habs]. apply M.find_1 in Habs. rewrite Hin in Habs. discriminate Habs.
Qed.

Lemma diff_spec : forall x s s', multiplicity x (diff s s') = multiplicity x s - multiplicity x s'.
Proof.
intros x s s'. unfold diff. destruct (M.find x s) eqn:Hin.
+ rewrite (fold_add (fun x n => n - multiplicity x s') x s empty).
  - rewrite empty_spec. now rewrite plus_0_r.
  - intros ? ? Heq ? ? ?. subst. now rewrite Heq.
  - exists p. now apply M.find_2.
+ rewrite fold_add_out.
  - unfold multiplicity at 2. rewrite Hin. simpl. now apply empty_spec.
  - intros [n Habs]. apply M.find_1 in Habs. rewrite Hin in Habs. discriminate Habs.
Qed.

Lemma lub_spec : forall x s s', multiplicity x (lub s s') = max (multiplicity x s) (multiplicity x s').
Proof.
Proof.
intros x s s'. unfold lub.
replace (max (multiplicity x s) (multiplicity x s'))
  with (multiplicity x s - multiplicity x s'  + multiplicity x s') by (apply Max.max_case_strong; omega).
destruct (M.find x s) eqn:Hin.
+ apply (fold_add (fun x n => n - multiplicity x s')).
  - intros ? ? Heq ? ? ?. subst. now rewrite Heq.
  - exists p. now apply M.find_2.
+ rewrite fold_add_out.
  - unfold multiplicity at 2. rewrite Hin. simpl. reflexivity.
  - intros [n Habs]. apply M.find_1 in Habs. rewrite Hin in Habs. discriminate Habs.
Qed.

Lemma subset_spec : forall s s', subset s s' = true <-> s [<=] s'.
Proof.
intros s s'. split; intro Hle.
- intro x. apply (is_empty_multiplicity x) in Hle. rewrite diff_spec in Hle. omega.
- unfold subset. rewrite is_empty_spec. intro x. unfold In. rewrite diff_spec.
  specialize (Hle x). rewrite empty_spec. omega.
Qed.
(*
Lemma fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A) s,
    fold f s i = fold_left (flip f) (elements s) i.
*)
Lemma fold_spec : forall (A : Type) s (i : A) (f : elt -> nat -> A -> A),
    fold f s i = fold_left (fun acc xn => f (fst xn) (snd xn) acc) (elements s) i.
Proof. intros A i f s. unfold fold, elements. now rewrite M.fold_1, fold_left_map. Qed.

Lemma cardinal_spec : forall s, cardinal s = fold (fun x n acc => n + acc) s 0.
Proof. intro. unfold cardinal. rewrite fold_spec. unfold elements. now rewrite fold_left_map, M.fold_1. Qed.

Lemma size_spec : forall s, size s = length (support s).
Proof. intro. unfold size, support. now rewrite M.fold_1, fold_left_length, M.fold_1, fold_left_cons_length. Qed.


Lemma Melements_multiplicity : forall s x n,
  InA (@M.eq_key_elt _) (x, n) (M.elements s)
  <-> multiplicity x s = Pos.to_nat n /\ Pos.to_nat n > 0.
Proof.
intros s x n. simpl.
split; intro H.
+ apply M.elements_2 in H. apply M.find_1 in H. unfold multiplicity. 
  rewrite H. split. reflexivity. apply Pos2Nat.is_pos.
+ destruct H as [H1 H2]. unfold multiplicity in H1. destruct (M.find x s) eqn:Hin.
  - apply M.elements_1. apply M.find_2. rewrite Hin. f_equal. now apply Pos2Nat.inj.
  - rewrite  <-H1 in H2. inversion H2.
Qed.

Corollary elements_spec : forall x n s,
  InA eq_pair (x, n) (elements s) <-> multiplicity x s = n /\ n > 0.
Proof.
intros x n s. unfold elements. rewrite InA_map_iff.
split; intro H.
+ destruct H as [[y m] [[Heq1 Heq2] Hin]]. rewrite Melements_multiplicity in Hin.
  hnf in Heq1, Heq2. simpl in *. subst n. now rewrite <- Heq1.
+ exists (x, Pos.of_nat n). destruct H as [H1 H2]. simpl in *. split.
  - split; hnf; simpl. reflexivity. apply Nat2Pos.id. omega.
  - rewrite Melements_multiplicity. simpl. rewrite H1. rewrite Nat2Pos.id. now split. omega.
+ apply Meq_equiv.
+ apply Meq_equiv.
+ clear. intros [] [] []. intros. split; simpl in *. assumption. now subst.
Qed.

Lemma elements_NoDupA : forall s, NoDupA (@M.eq_key _) (elements s).
Proof.
intro s. unfold elements. rewrite NoDupA_inj_map; 
apply M.elements_3w || apply Meq_key_equiv || (intros [] [] ?; assumption).
Qed.

Lemma support_elements_aux : forall x l1 l2, NoDupA (@M.eq_key _) (l1 ++ l2) -> 
  ((InA E.eq x (fold_left (fun acc xn => fst xn :: acc) l1 (map (@fst _ _) l2)) <->
  exists n, InA eq_pair (x, n) (map (fun xn => (fst xn, Pos.to_nat (snd xn))) (l1 ++ l2)))).
Proof.
intros x l1. induction l1; simpl; intros l2 Hdup.
* split; intro H.
  + induction l2.
    - now inversion H.
    - destruct a as [y m]. inversion_clear H.
        exists (Pos.to_nat m). left. now split.
        apply IHl2 in H0. destruct H0 as [n Hn]. exists n. simpl. now right. now inversion_clear Hdup.
  + destruct H as [n Hn]. induction l2; simpl.
    - now inversion Hn.
    - destruct a as [y m]. inversion_clear Hdup. inversion_clear Hn.
        left. now destruct H1.
        right. now apply IHl2.
* destruct a as [y m]. simpl. split; intro H.
  + destruct (E.eq_dec x y). exists (Pos.to_nat m). left. now split.
    change (y :: map (fst (B:=positive)) l2) with (map (fst (B:=positive)) ((y,m) :: l2)) in H.
    rewrite IHl1 in H.
    - destruct H as [p Hp]. exists p. rewrite map_app in *. rewrite InA_app_iff in Hp.
        simpl in Hp. destruct Hp.
          right. rewrite InA_app_iff. now left.
          inversion_clear H.
             now left.
             right. rewrite InA_app_iff. now right.
    - rewrite NoDupA_swap_iff. assumption. refine _.
  + change (y :: map (fst (B:=positive)) l2) with (map (fst (B:=positive)) ((y,m) :: l2)).
    rewrite IHl1. destruct H as [n Hn]. exists n. rewrite map_app, InA_app_iff. inversion_clear Hn.
    - right. now left.
    - rewrite map_app, InA_app_iff in H. destruct H. now left. now do 2 right.
    - rewrite NoDupA_swap_iff. assumption. now apply Meq_key_equiv.
Qed.

Lemma support_elements : forall x s, InA E.eq x (support s) <-> InA eq_pair (x, multiplicity x s) (elements s).
Proof.
intros x s. unfold support, elements. rewrite M.fold_1.
change nil with (map (@fst E.t nat) nil).
rewrite (support_elements_aux x (M.elements s) nil); rewrite app_nil_r; [split; intro H |].
+ destruct H as [n Hn].
  assert (n = multiplicity x s).
  { rewrite (InA_map_iff (Meq_equiv _) eq_pair_equiv) in Hn.
    - destruct Hn as [[y m] [[Heqx Heqn] Hin]]. rewrite Melements_multiplicity in Hin. 
      hnf in *. simpl in *. subst. symmetry. destruct Hin. rewrite <- Heqx. assumption.
    - intros [? ?] [? ?] Heq; simpl in *. hnf in Heq. destruct Heq; split; hnf; simpl in *; subst; auto. }
  now subst n.
+ now exists (multiplicity x s).
+ apply M.elements_3w.
Qed.

Corollary support_spec : forall x s, InA E.eq x (support s) <-> In x s.
Proof. intros x s. rewrite support_elements. rewrite elements_spec. intuition. Qed.

Lemma support_NoDupA_aux : forall A B (l1 : list (A*B)) l2,
  fold_left (fun acc p => fst p :: acc) l1 l2 = rev (map (@fst _ _) l1) ++ l2.
Proof.
intros A B l1. induction l1; intro l2; simpl.
  reflexivity.
  rewrite IHl1. now rewrite <- app_assoc.
Qed.

Lemma support_NoDupA : forall s, NoDupA E.eq (support s).
Proof.
intro s. unfold support. rewrite M.fold_1. rewrite support_NoDupA_aux. rewrite app_nil_r.
apply NoDupA_rev. now auto with typeclass_instances.
rewrite NoDupA_inj_map; (now apply M.elements_3w) || (now auto with typeclass_instances) || (now intros ? ? ?).
Qed.


Lemma fold_filter_out_list : forall f x n l s, ~InA (@M.eq_key positive) (x, n) l -> NoDupA (@M.eq_key _) l ->
  multiplicity x (fold_left (fun acc xn => if f (fst xn) (snd xn) : bool
                                           then add (fst xn) (Pos.to_nat (snd xn)) acc else acc) l s)
  = multiplicity x s.
Proof.
intros f x n l s Hin Hdup. revert s. induction l as [| [y m] l]; intro s; simpl.
  reflexivity.
  rewrite IHl.
    destruct (f y m). apply add_other. intro Habs. apply Hin. left. compute. auto. auto.
    intro Habs. apply Hin. now right.
    now inversion_clear Hdup.
Qed.

Lemma filter_spec_In : forall f s s' x, compatb f -> In x s ->
  multiplicity x
    (M.fold
       (fun (x0 : M.key) (n : positive) (acc : t) =>
        if f x0 (Pos.to_nat n) : bool then add x0 (Pos.to_nat n) acc else acc) s s')
  = if f x (multiplicity x s) then multiplicity x s + multiplicity x s' else multiplicity x s'.
Proof.
intros f s s' x Hf Hin. rewrite M.fold_1. revert s'. unfold In in Hin.
assert (Hs : InA (@M.eq_key_elt _) (x, multiplicity x s) (elements s)). { rewrite elements_spec. simpl. now split. }
assert (Hdup : NoDupA (@M.eq_key _) (elements s)) by apply elements_NoDupA.
unfold elements in Hs, Hdup.
induction (M.elements s); simpl; intro s'; simpl in Hs.
* exfalso. rewrite <- InA_nil. apply Hs.
* destruct a as [y m].
  destruct (Meq_dec (x, Pos.of_nat (multiplicity x s)) (y, m)) as [Heq | Hneq].
  + destruct Heq as [H1 H2]. simpl in H1, H2 |- *. rewrite H1 in *. subst m.
    rewrite (fold_filter_out_list (fun x y => f x (Pos.to_nat y)) _ (Pos.of_nat (multiplicity y s))).
    - rewrite Nat2Pos.id; try omega.
      destruct (f y (multiplicity y s)) eqn:Htest.
        rewrite add_same, H1. now apply plus_comm.
        now rewrite H1.
    - inversion_clear Hdup. intro Habs. apply H. rewrite InA_map_iff.
        exists (y, Pos.of_nat (multiplicity y s)). split. reflexivity. eassumption.
        apply Meq_key_equiv.
        apply Meq_key_equiv.
        clear. intros [] [] Hxy. now compute in *.
    - inversion_clear Hdup. rewrite NoDupA_inj_map in H0.
        eassumption.
        now apply Meq_key_equiv.
        now apply Meq_key_equiv.
        now intros [] [].
        now intros [] [].
  + inversion_clear Hs.
    - elim Hneq. destruct H. split. assumption. simpl in *. now rewrite H0, Pos2Nat.id.
    - inversion_clear Hdup. assert (Hxy : ~E.eq x y).
      { intro Habs. apply H0. now apply (eq_key_elt_eq_key_weak_In _ x y (multiplicity x s)). }
      rewrite IHl; try assumption. simpl.
      destruct (f x (multiplicity x s)), (f y (Pos.to_nat m));
      reflexivity || rewrite add_other; reflexivity || now auto.
Qed.

Lemma filter_spec_out : forall f s s' x, ~In x s ->
  multiplicity x
    (M.fold
       (fun (x0 : M.key) (n : positive) (acc : t) =>
        if f x0 (Pos.to_nat n) : bool then add x0 (Pos.to_nat n) acc else acc) s s')
  = multiplicity x s'.
Proof.
intros f s s' x Hin. rewrite M.fold_1.
assert (Hs : forall n, ~(InA (@M.eq_key_elt _) (x, n) (M.elements s))).
{ intros n Habs. apply Hin. apply M.elements_2 in Habs. apply M.find_1 in Habs.
  unfold In, multiplicity. rewrite Habs. apply Pos2Nat.is_pos. }
revert s'. induction (M.elements s) as [| [y m] l]; intro s'; simpl.
  reflexivity.
  assert ( Hxy : ~E.eq x y). { intro Habs. apply (Hs m). left. now split. }
  rewrite IHl. destruct (f y (Pos.to_nat m)). apply add_other. now auto. reflexivity.
  intros n Habs. apply (Hs n). now right.
Qed.

Corollary filter_spec : forall f x s, compatb f ->
    multiplicity x (filter f s) = if f x (multiplicity x s) then multiplicity x s else 0.
Proof.
intros f x s Hf. unfold filter.
destruct (multiplicity x s) eqn:Hin.
  rewrite filter_spec_out.
    now destruct (f x 0); apply empty_spec.
    unfold In. omega.
  rewrite filter_spec_In.
    now rewrite empty_spec, Hin, plus_0_r.
    assumption.
    unfold In. rewrite Hin. omega.
Qed.


Lemma choose_spec_aux : forall x s o, ~M.In x s ->
  fold_left (fun (_ : option M.key) (p : M.key * positive) => Some (fst p)) (M.elements s) o = Some x ->
  o = Some x.
Proof.
intros x s o Hs.
assert (Hs' : forall n, ~InA (@M.eq_key_elt _) (x, n) (M.elements s)).
{ intros n Habs. apply Hs. exists n. now apply M.elements_2. } clear Hs.
revert o. induction (M.elements s); simpl; intros o Hin.
  assumption.
  apply IHl in Hin.
    elim (Hs' (snd a)). left. split; simpl. now inversion Hin. reflexivity.
    intros n Habs. apply (Hs' n). now right.
Qed.

Lemma choose_Some : forall x s, choose s = Some x -> In x s.
Proof.
intros x s Hin. destruct (In_dec x s). assumption. unfold choose in Hin.
rewrite M.fold_1 in Hin. apply choose_spec_aux in Hin. now inversion Hin. now rewrite <- In_MIn.
Qed.

Lemma choose_None : forall s, choose s = None <-> s [=] empty.
Proof.
intros s. split; intro Hs.
+ intro x. unfold choose in Hs. rewrite M.fold_1 in Hs. rewrite empty_spec, multiplicity_out.
  destruct (M.find x s) eqn:Habs.
  - apply M.find_2 in Habs. apply M.elements_1 in Habs. destruct (M.elements s).
      now inversion Habs.
      clear -Hs. simpl in Hs. revert p0 Hs. induction l. discriminate. intros. simpl in Hs. now apply (IHl _ Hs).
  - reflexivity.
+ destruct (choose s) eqn:H.
  - apply choose_Some in H. rewrite Hs in H. unfold In in H. rewrite empty_spec in H. omega.
  - reflexivity.
Qed.

Lemma fold_and_true_base_step : forall A f (l : list A) b, 
  fold_left (fun a x => a && f x) l b = true -> b = true.
Proof.
intros A f l. induction l; simpl; intros b Hl.
  assumption.
  apply IHl in Hl. destruct b. reflexivity. simpl in Hl. discriminate Hl.
Qed.

Lemma fold_and_true_inductive_step : forall A f (l : list A) a b, 
  fold_left (fun a x => a && f x) (a :: l) b = true -> f a = true.
Proof.
simpl. intros A f l a b Hl. apply fold_and_true_base_step in Hl.
destruct (f a). reflexivity. destruct b; simpl in Hl; discriminate Hl.
Qed.

Lemma for_all_spec_aux : forall (f : M.key -> nat -> bool) s b, compatb f ->
  (M.fold (fun x n b => b && (f x (Pos.to_nat n))) s b = true
   <-> b = true /\ For_all (fun x n => f x n = true) s).
Proof.
intros f s b Hf. rewrite M.fold_1. unfold For_all. split; intro H.
+ split. now apply fold_and_true_base_step in H.
  intros x Hin. rewrite In_MIn in Hin. destruct Hin as [n Hin]. apply M.elements_1 in Hin.
  assert (Hn : multiplicity x s = Pos.to_nat n) by now rewrite Melements_multiplicity in Hin.
  revert b H x n Hn Hin. induction (M.elements s); intros b H x n Hn Hin; inversion_clear Hin.
  - simpl in H. apply fold_and_true_base_step in H. rewrite andb_true_iff in H.
    destruct H as [_ H ], a, H0 as [H1 H2]. simpl in *. rewrite Hn, H1. now subst p.
  - simpl in H. apply (IHl _ H _ _ Hn H0).
+ destruct H as [Hb H]. subst b.
  assert (forall xn, InA (@M.eq_key_elt _) xn (M.elements s) -> f (fst xn) (Pos.to_nat (snd xn)) = true).
  { intros [x n] Hx. simpl. rewrite Melements_multiplicity in Hx. destruct Hx as [Hm Hp].
    setoid_rewrite <- Pos2Nat.id. rewrite <- Hm. rewrite Nat2Pos.id. apply H. unfold In. now rewrite Hm. omega. }
  clear H. revert H0. induction (M.elements s); simpl; intro Hin; trivial.
  rewrite Hin. apply IHl. intros x Hx. apply Hin. now right. now left.
Qed.

Corollary for_all_spec : forall f s, compatb f ->
  (for_all f s = true <-> For_all (fun x n => f x n = true) s).
Proof. intros. unfold for_all. rewrite for_all_spec_aux; intuition. Qed.

Lemma exists_spec_aux : forall (f : M.key -> nat -> bool) s b, compatb f ->
  (M.fold (fun x n b => b || (f x (Pos.to_nat n))) s b = true
   <-> b = true \/ Exists (fun x n => f x n = true) s).
Proof.
intros f s b Hf.
assert (Hequiv : Exists (fun x n => f x n = true) s <->
        exists x, exists n, InA (@M.eq_key_elt _) (x, n) (M.elements s) /\ f x (Pos.to_nat n) = true).
{ split; intros [x Hx].
  destruct Hx as [Hin Hfx]. exists x. exists (Pos.of_nat (multiplicity x s)). split.
    rewrite Melements_multiplicity. unfold In in Hin. simpl. rewrite Nat2Pos.id. now split. omega.
    rewrite Nat2Pos.id. assumption. unfold In in Hin. omega.
  destruct Hx as [n [Hin Hfx]]. exists x. rewrite Melements_multiplicity in Hin. destruct Hin as [Hn Hp]. split.
    simpl in *. unfold In. now rewrite Hn.
    simpl in *. now rewrite Hn. }
rewrite Hequiv. clear Hequiv. rewrite M.fold_1. unfold For_all. split; intro H.
+ revert b H. induction (M.elements s); intros b H.
  - simpl in H. now left.
  - simpl in H. apply IHl in H. rewrite orb_true_iff in H. destruct H as [[H | H] | H]; (now left) || right.
      destruct a as [x n]. exists x. exists n. split. now left. assumption.
      destruct H as [x [n [Hin Hfx]]]. exists x. exists n. split. now right. assumption.  
+ revert b H. induction (M.elements s); simpl; intros b H.
  - destruct H. assumption.
    destruct H as [? [? [Habs _]]]. now inversion Habs.
  - apply IHl. rewrite orb_true_iff. destruct H as [H | H].
      now do 2 left.
      destruct H as [x [n [Hin Hfx]]]. inversion_clear Hin.
        left. right. destruct H as [H1 H2]. simpl in H1, H2. now rewrite <- H1, <- H2.
        right. exists x. exists n. now split.
Qed.

Corollary exists_spec : forall f s, compatb f ->
  (exists_ f s = true <-> Exists (fun x n => f x n = true) s).
Proof. intros. unfold exists_. rewrite exists_spec_aux; intuition discriminate. Qed.


Definition partition_fun f := fun x n acc =>
         if f x (Pos.to_nat n) : bool
         then (add x (Pos.to_nat n) (fst acc), snd acc)
         else (fst acc, add x (Pos.to_nat n) (snd acc)).

Lemma fold_partition_fst_out_list : forall f x n l s12,
  ~InA (@M.eq_key positive) (x, n) l -> NoDupA (@M.eq_key _) l ->
  multiplicity x
  (fst
     (fold_left (fun acc xn => if f (fst xn) (Pos.to_nat (snd xn)) : bool
         then (add (fst xn) (Pos.to_nat (snd xn)) (fst acc), snd acc)
         else (fst acc, add (fst xn) (Pos.to_nat (snd xn)) (snd acc))) l s12))
  = multiplicity x (fst s12).
Proof.
intros f x n l s12 Hin Hdup. revert s12. induction l as [| [y m] l]; intros s12; simpl.
  reflexivity.
  rewrite IHl.
    destruct (f y (Pos.to_nat m)); simpl.
      apply add_other. intro Habs. apply Hin. left. compute. auto. auto.
    intro Habs. apply Hin. now right.
    now inversion_clear Hdup.
Qed.

Lemma partition_spec_fst_In : forall f (s : t) (s12 : t * t) x, compatb f -> In x s ->
  multiplicity x (fst (M.fold (fun x n acc =>
         if f x (Pos.to_nat n) : bool
         then (add x (Pos.to_nat n) (fst acc), snd acc)
         else (fst acc, add x (Pos.to_nat n) (snd acc))) s s12)) =
  (if f x (multiplicity x s) then multiplicity x s + multiplicity x (fst s12) else multiplicity x (fst s12)).
Proof.
intros f s s' x Hf Hin. rewrite M.fold_1. revert s'. unfold In in Hin.
assert (Hs : InA (@M.eq_key_elt _) (x, multiplicity x s) (elements s)). { rewrite elements_spec. simpl. now split. }
assert (Hdup : NoDupA (@M.eq_key _) (elements s)) by apply elements_NoDupA.
unfold elements in Hs, Hdup.
induction (M.elements s); simpl; intros [s1 s2]; simpl in Hs.
* exfalso. rewrite <- InA_nil. apply Hs.
* destruct a as [y m].
  destruct (Meq_dec (x, Pos.of_nat (multiplicity x s)) (y, m)) as [Heq | Hneq].
  + destruct Heq as [H1 H2]. simpl in H1, H2 |- *. rewrite H1 in *. subst m.
    rewrite (fold_partition_fst_out_list f _ (Pos.of_nat (multiplicity y s))).
    - unfold partition_fun. rewrite Nat2Pos.id; try omega.
      destruct (f y (multiplicity y s)) eqn:Htest; simpl.
        rewrite add_same, H1. now apply plus_comm.
        now rewrite H1.
    - inversion_clear Hdup. intro Habs. apply H. rewrite InA_map_iff.
        exists (y, Pos.of_nat (multiplicity y s)). split. reflexivity. eassumption.
        apply Meq_key_equiv.
        apply Meq_key_equiv.
        clear. intros [] [] Hxy. now compute in *.
    - inversion_clear Hdup. rewrite NoDupA_inj_map in H0.
        eassumption.
        now apply Meq_key_equiv.
        now apply Meq_key_equiv.
        now intros [] [].
        now intros [] [].
  + inversion_clear Hs.
    - elim Hneq. destruct H. split. assumption. simpl in *. now rewrite H0, Pos2Nat.id.
    - inversion_clear Hdup. assert (Hxy : ~E.eq x y).
      { intro Habs. apply H0. now apply (eq_key_elt_eq_key_weak_In _ x y (multiplicity x s)). }
      rewrite IHl; try assumption. simpl. unfold partition_fun.
      destruct (f x (multiplicity x s)), (f y (Pos.to_nat m));
      reflexivity || simpl; rewrite add_other; reflexivity || now auto.
Qed.

Lemma partition_spec_fst_out : forall f s s12 x, ~In x s ->
  multiplicity x (fst (M.fold (fun x n acc =>
         if f x (Pos.to_nat n) : bool
         then (add x (Pos.to_nat n) (fst acc), snd acc)
         else (fst acc, add x (Pos.to_nat n) (snd acc))) s s12)) = multiplicity x (fst s12).
Proof.
intros f s s' x Hin. rewrite M.fold_1.
assert (Hs : forall n, ~(InA (@M.eq_key_elt _) (x, n) (M.elements s))).
{ intros n Habs. apply Hin. apply M.elements_2 in Habs. apply M.find_1 in Habs.
  unfold In, multiplicity. rewrite Habs. apply Pos2Nat.is_pos. }
revert s'. induction (M.elements s) as [| [y m] l]; intro s'; simpl.
  reflexivity.
  assert ( Hxy : ~E.eq x y). { intro Habs. apply (Hs m). left. now split. }
  rewrite IHl. unfold partition_fun. destruct (f y (Pos.to_nat m)). apply add_other. now auto. reflexivity.
  intros n Habs. apply (Hs n). now right.
Qed.

Corollary partition_spec_fst : forall f s, compatb f -> fst (partition f s) [=] filter f s.
Proof.
intros f s Hf x. unfold partition. rewrite filter_spec; trivial.
destruct (multiplicity x s) eqn:Hin.
  fold partition_fun. rewrite partition_spec_fst_out.
    now destruct (f x 0); apply empty_spec.
    unfold In. omega.
  rewrite partition_spec_fst_In.
    now rewrite empty_spec, Hin, plus_0_r.
    assumption.
    unfold In. rewrite Hin. omega.
Qed.

Lemma fold_partition_snd_out_list : forall f x n l s12,
  ~InA (@M.eq_key positive) (x, n) l -> NoDupA (@M.eq_key _) l ->
  multiplicity x
  (snd
     (fold_left
        (fun acc xn =>
         if f (fst xn) (Pos.to_nat (snd xn)) : bool
         then (add (fst xn) (Pos.to_nat (snd xn)) (fst acc), snd acc)
         else (fst acc, add (fst xn) (Pos.to_nat (snd xn)) (snd acc))) l s12))
  = multiplicity x (snd s12).
Proof.
intros f x n l s12 Hin Hdup. revert s12. induction l as [| [y m] l]; intros s12; simpl.
  reflexivity.
  rewrite IHl.
    destruct (f y (Pos.to_nat m)). reflexivity. simpl. apply add_other. intro Habs. apply Hin. left. compute. auto.
    intro Habs. apply Hin. now right.
    now inversion_clear Hdup.
Qed.

Lemma partition_spec_snd_In : forall f (s : t) (s12 : t * t) x, compatb f -> In x s ->
  multiplicity x
  (snd
     (M.fold
        (fun y n acc =>
         if f y (Pos.to_nat n) : bool
         then (add y (Pos.to_nat n) (fst acc), snd acc)
         else (fst acc, add y (Pos.to_nat n) (snd acc))) s s12)) =
  (if f x (multiplicity x s) then multiplicity x (snd s12) else multiplicity x s + multiplicity x (snd s12)).
Proof.
intros f s s' x Hf Hin. rewrite M.fold_1. revert s'. unfold In in Hin.
assert (Hs : InA (@M.eq_key_elt _) (x, multiplicity x s) (elements s)). { rewrite elements_spec. simpl. now split. }
assert (Hdup : NoDupA (@M.eq_key _) (elements s)) by apply elements_NoDupA.
unfold elements in Hs, Hdup.
induction (M.elements s); simpl; intros [s1 s2]; simpl in Hs.
* exfalso. rewrite <- InA_nil. apply Hs.
* destruct a as [y m].
  destruct (Meq_dec (x, Pos.of_nat (multiplicity x s)) (y, m)) as [Heq | Hneq].
  + destruct Heq as [H1 H2]. simpl in H1, H2 |- *. rewrite H1 in *. subst m.
    rewrite (fold_partition_snd_out_list f _ (Pos.of_nat (multiplicity y s))).
    - rewrite Nat2Pos.id; try omega.
      destruct (f y (multiplicity y s)) eqn:Htest; simpl.
        now rewrite H1.
        rewrite add_same, H1. now apply plus_comm.
    - inversion_clear Hdup. intro Habs. apply H. rewrite InA_map_iff.
        exists (y, Pos.of_nat (multiplicity y s)). split. reflexivity. eassumption.
        apply Meq_key_equiv.
        apply Meq_key_equiv.
        clear. intros [] [] Hxy. now compute in *.
    - inversion_clear Hdup. rewrite NoDupA_inj_map in H0.
        eassumption.
        now apply Meq_key_equiv.
        now apply Meq_key_equiv.
        now intros [] [].
        now intros [] [].
  + inversion_clear Hs.
    - elim Hneq. destruct H. split. assumption. simpl in *. now rewrite H0, Pos2Nat.id.
    - inversion_clear Hdup. assert (Hxy : ~E.eq x y).
      { intro Habs. apply H0. now apply (eq_key_elt_eq_key_weak_In _ x y (multiplicity x s)). }
      rewrite IHl; try assumption. simpl.
      destruct (f x (multiplicity x s)), (f y (Pos.to_nat m));
      reflexivity || simpl; rewrite add_other; reflexivity || now auto.
Qed.

Lemma partition_spec_snd_out : forall f s s12 x, ~In x s ->
  multiplicity x
  (snd
     (M.fold
        (fun y n acc =>
         if f y (Pos.to_nat n) : bool
         then (add y (Pos.to_nat n) (fst acc), snd acc)
         else (fst acc, add y (Pos.to_nat n) (snd acc))) s s12)) =
  multiplicity x (snd s12).
Proof.
intros f s s' x Hin. rewrite M.fold_1.
assert (Hs : forall n, ~(InA (@M.eq_key_elt _) (x, n) (M.elements s))).
{ intros n Habs. apply Hin. apply M.elements_2 in Habs. apply M.find_1 in Habs.
  unfold In, multiplicity. rewrite Habs. apply Pos2Nat.is_pos. }
revert s'. induction (M.elements s) as [| [y m] l]; intro s'; simpl.
  reflexivity.
  assert ( Hxy : ~E.eq x y). { intro Habs. apply (Hs m). left. now split. }
  rewrite IHl. destruct (f y (Pos.to_nat m)); simpl. reflexivity. apply add_other. now auto.
  intros n Habs. apply (Hs n). now right.
Qed.

Corollary partition_spec_snd : forall f s, compatb f -> snd (partition f s) [=] filter (fun x n => negb (f x n)) s.
Proof.
intros f s Hf x. unfold partition. rewrite filter_spec.
destruct (multiplicity x s) eqn:Hin.
  rewrite partition_spec_snd_out.
    now destruct (f x 0); apply empty_spec.
    unfold In. omega.
  rewrite partition_spec_snd_In.
    rewrite empty_spec, Hin, plus_0_r. now destruct (f x (S n)).
    assumption.
    unfold In. rewrite Hin. omega.
    intros ? ? Heq ? ? ?. subst. now rewrite Heq.
Qed.

Instance fold_compat A (eqA : A -> A -> Prop) `{Equivalence A eqA} : forall f,
  Proper (E.eq ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
  Proper (eq ==> eqA ==> eqA) (fold f).
Proof.
intros f Hf Hfcomm s1 s2 Hs x y Hxy. unfold fold. do 2 rewrite M.fold_1.
rewrite fold_left_symmetry_PermutationA.
+ reflexivity.
+ now apply Meq_equiv.
+ assumption.
+ repeat intro. now apply Hf; rewrite H1 || rewrite H0.
+ intros. apply Hfcomm.
+ apply NoDupA_equivlistA_PermutationA.
  - now apply Meq_equiv.
  - eapply NoDupA_strengthen; try apply M.elements_3w. now intros [? ?] [? ?] [? ?].
  - eapply NoDupA_strengthen; try apply M.elements_3w. now intros [? ?] [? ?] [? ?].
  - clear -Hs. intros [x n]. do 2 rewrite Melements_multiplicity. now rewrite Hs.
+ assumption.
Qed.

End FMultisets.
