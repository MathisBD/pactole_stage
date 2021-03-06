(******************************************)
(*   Finite multiset library              *)
(*   Developped for the PACTOLE project   *)
(*   L. Rieg                              *)
(*                                        *)
(*   This file is distributed under       *)
(*   the terms of the CeCILL-C licence    *)
(*                                        *)
(******************************************)


(* Require Import MMapInterface. *)
Require Import Arith_base.
Require Import Lia.
Require Import PArith.
Require Import Bool.
Require Import RelationPairs.
Require Import SetoidList.
Require Import Pactole.Util.FMaps.FMapInterface.
Require Import Pactole.Util.FMaps.FMapFacts.
Require Import Pactole.Util.MMultiset.Preliminary.
Require Import Pactole.Util.MMultiset.MMultisetInterface.
Require Import SetoidDec.


Section WMapImplementation.
Context (elt : Type).
Context (elt_Setoid : Setoid elt).
Context (elt_EqDec : @EqDec elt elt_Setoid).
Context (MapImpl : @FMap elt elt_Setoid elt_EqDec).
Context (MapSpec : FMapSpecs MapImpl).

Definition m_multiplicity :=
  fun x m => match find x m with Some n => Pos.to_nat n | None => 0 end.
Definition m_add := fun x n m =>
    if eq_nat_dec n 0 then m else FMapInterface.add x (Pos.of_nat (m_multiplicity x m + n)) m.
Definition m_fold := fun {A} (f : elt -> nat -> A -> A) m =>
  FMapInterface.fold (fun x y => f x (Pos.to_nat y)) m.

Global Instance FMOps_WMap : FMOps elt elt_EqDec := {|
  multiset := Map[elt, positive];
  empty := FMapInterface.empty positive;
  is_empty := FMapInterface.is_empty;
  multiplicity := m_multiplicity;
  add := m_add;
  singleton x n :=
    if eq_nat_dec n 0 then FMapInterface.empty _ else FMapInterface.add x (Pos.of_nat n) (FMapInterface.empty _);
  remove x n m := if eq_nat_dec n 0 then m else
    if le_lt_dec (m_multiplicity x m) n then FMapInterface.remove x m
    else FMapInterface.add x (Pos.of_nat (m_multiplicity x m - n)) m;
  union := fun m m' => m_fold m_add m m';
  inter := fun m m' => m_fold (fun x n acc => m_add x (min (m_multiplicity x m) n) acc) m' (FMapInterface.empty _);
  diff := fun m m' => m_fold (fun x n acc => m_add x (n - m_multiplicity x m') acc) m (FMapInterface.empty _);
  lub := fun m m' => m_fold (fun x n acc => m_add x (n - (m_multiplicity x m')) acc) m m';
  equal := fun m m' => FMapInterface.equal Pos.eqb m m';
  subset := fun m m' => FMapInterface.is_empty
              (m_fold (fun x n acc => m_add x (n - m_multiplicity x m') acc) m (FMapInterface.empty _));
  fold := @m_fold;
  for_all := fun f m => m_fold (fun x n b => b && f x n) m true;
  exists_ := fun f m => m_fold (fun x n b => b || f x n) m false;
  nfilter := fun f m => m_fold (fun x n acc => if f x n then m_add x n acc else acc) m (FMapInterface.empty _);
  filter := fun f m => m_fold (fun x n acc => if f x then m_add x n acc else acc) m (FMapInterface.empty _);
  npartition := fun (f : elt -> nat -> bool) m => m_fold
                  (fun x n acc => if f x n then (m_add x n (fst acc), snd acc) else (fst acc, m_add x n (snd acc)))
                  m (FMapInterface.empty _, FMapInterface.empty _);
  partition := fun (f : elt -> bool) m => m_fold
                 (fun x n acc => if f x then (m_add x n (fst acc), snd acc) else (fst acc, m_add x n (snd acc)))
                  m (FMapInterface.empty _, FMapInterface.empty _);
  elements := fun m => List.map (fun xy => (fst xy, Pos.to_nat (snd xy))) (FMapInterface.elements m);
  support := fun m => FMapInterface.fold (fun x _ l => cons x l) m nil;
  cardinal := fun m => FMapInterface.fold (fun _ n acc => Pos.to_nat n + acc) m 0;
  size := fun m => FMapInterface.fold (fun _ _ n => S n) m 0;
  choose := fun m =>  FMapInterface.fold (fun x _ _ => Some x) m None |}.
Local Arguments multiplicity : simpl nomatch.

(** **  Compatibility properties  **)

Instance pre_multiplicity_compat : Proper (equiv ==> Equal ==> Logic.eq) multiplicity.
Proof using MapSpec.
intros x y Hxy m m' Hm. simpl. unfold m_multiplicity. rewrite Hm.
assert (Heq : find x m' = find y m') by now apply find_m.
now rewrite Heq.
Qed.

Instance m_add_compat : Proper (equiv ==> Logic.eq ==> Equal ==> Equal) m_add.
Proof using MapSpec.
intros x y Hxy ? n ? m m' Hm z. subst. unfold m_add.
destruct (Nat.eq_dec n 0).
- apply Hm.
- cbn. apply add_m; trivial. do 2 f_equal. rewrite Hxy. unfold m_multiplicity. now rewrite Hm.
Qed.

Global Instance eq_pair_equiv : Equivalence eq_pair.
Proof using . split. easy. easy. intros ? y ? ? ?. now transitivity y. Qed.

Global Instance eq_pair_Setoid : Setoid (elt * positive)%type := _.

Global Instance eq_pair_EqDec : @EqDec (elt * positive)%type _.
Proof.
intros [x n] [y p]. destruct (equiv_dec x y).
+ destruct (Pos.eq_dec n p).
  - left. now split; cbn.
  - right. intro Heq. now destruct Heq.
+ right. intro Heq. now destruct Heq.
Defined.

Global Instance eq_elt_equiv : Equivalence eq_elt.
Proof using . split. easy. easy. intros ? y ? ? ?. now transitivity y. Qed.

Global Instance eq_elt_Setoid : Setoid (elt * nat)%type := {| equiv := eq_elt; setoid_equiv := _ |}.

Global Instance eq_elt_EqDec : @EqDec (elt * nat)%type _.
Proof.
intros [x n] [y p]. destruct (equiv_dec x y); now left + right; cbn.
Defined.

Global Instance eq_pair_elt_subrelation : subrelation eq_pair eq_elt.
Proof using . intros x y [H _]. apply H. Qed.

Global Instance eq_key_eq_key_elt_subrelation : subrelation (@eq_key_elt elt _ _ _ positive) eq_key.
Proof using . intros x y [H _]. apply H. Qed.

Global Instance multiset_Setoid : Setoid (multiset elt).
refine {| equiv := fun m m' => forall x, m[x] = m'[x] |}.
Proof. split; repeat intro; solve [ eauto | etransitivity; eauto ]. Defined.

Global Instance multiplicity_compat : Proper (equiv ==> equiv ==> Logic.eq) MMultisetInterface.multiplicity.
Proof using MapSpec.
intros x y Hxy m m' Hm. rewrite Hm. simpl. unfold m_multiplicity.
assert (Heq : find x m' = find y m') by now apply find_m.
now rewrite Heq.
Qed.

(** ***  Preliminary results  **)

Lemma eq_pair_elt_weak_In : forall x y n m l,
  x == y -> InA eq_pair (x, n) l -> InA eq_elt (y, m) l.
Proof using .
intros x y n m l Heq Hin. induction l.
+ now inversion Hin.
+ inversion_clear Hin.
  - left. destruct a. compute in *. destruct H. now transitivity x; auto.
  - right. now apply IHl.
Qed.

Lemma NoDup_pair_In : forall x y n m l, NoDupA eq_elt l ->
  InA eq_pair (x, n) l -> InA eq_pair (y, m) l -> x == y -> n = m.
Proof using .
intros x y n m l Hl Hinx Hiny Heq. induction Hl as [| [z p] l]. inversion_clear Hiny.
inversion_clear Hinx; inversion_clear Hiny.
- compute in H0, H1. destruct H0 as [H0 ?], H1 as [H1 ?]. now subst p m.
- compute in H0. destruct H0 as [H0 ?]. subst p. elim H.
  apply eq_pair_elt_weak_In with y m. now transitivity x. assumption.
- compute in H1. destruct H1 as [H1 ?]. subst p. elim H.
  apply eq_pair_elt_weak_In with x n. now transitivity y; auto. assumption.
- now apply IHHl.
Qed.

Notation "s  [c=]  t" := (Subset s t) (at level 70, no associativity).

Lemma m_add_same : forall x n s, (m_add x n s)[x] = n + s[x].
Proof using MapSpec.
intros x n s. unfold m_add. simpl. destruct (Nat.eq_dec n 0). lia.
unfold m_multiplicity at 1. rewrite add_eq_o, Nat2Pos.id; lia || reflexivity.
Qed.

Lemma m_add_other : forall x y n s, x =/= y -> (m_add y n s)[x] = s[x].
Proof using MapSpec.
intros x y n s Hyx. unfold add. simpl. unfold m_add, m_multiplicity.
destruct (Nat.eq_dec n 0); trivial; []. rewrite add_neq_o; reflexivity || now symmetry.
Qed.

Lemma fold_add_out_list : forall (f : elt -> nat -> nat) x n l s,
  ~InA eq_key (x, n) l -> NoDupA eq_key l ->
  (fold_left (fun acc xn => m_add (fst xn) (f (fst xn) (Pos.to_nat (snd xn))) acc) l s)[x] = s[x].
Proof using MapSpec.
intros f x n l s Hin Hdup. revert s. induction l as [| [y m] l]; intro s; simpl.
+ reflexivity.
+ rewrite IHl.
  - rewrite m_add_other; trivial. intro. apply Hin. now left.
  - auto.
  - now inversion_clear Hdup.
Qed.

Lemma fold_add_out : forall (f : elt -> nat -> nat) x s s', ~FMapInterface.In x s ->
  (m_fold (fun y n acc => m_add y (f y n) acc) s s')[x] = s'[x].
Proof using MapSpec.
intros f x s s' Hin. unfold m_fold. rewrite FMapInterface.fold_1.
assert (Hs : forall n, ~(InA eq_key_elt (x, n) (FMapInterface.elements s))).
{ intros n Habs. apply Hin. exists n. now apply elements_2. }
revert s'. induction (FMapInterface.elements s) as [| [y m] l]; intro s'; simpl.
+ reflexivity.
+ assert ( Hxy : x =/= y). { intro Habs. apply (Hs m). left. now split. }
  rewrite IHl.
  - now rewrite m_add_other.
  - intros n Habs. apply (Hs n). now right.
Qed.

Notation compatb := (Proper (@equiv elt _ ==> Logic.eq ==> Logic.eq)) (only parsing).

Lemma fold_add : forall (f : elt -> nat -> nat) x n m m', compatb f -> find x m = Some n ->
  (m_fold (fun x n acc => m_add x (f x n) acc) m m')[x] = f x (Pos.to_nat n) + m'[x].
Proof using MapSpec.
intros f x n m m' Hf Hin. unfold m_fold. rewrite fold_1.
assert (Hm : InA eq_key_elt (x, Pos.of_nat (multiplicity x m)) (FMapInterface.elements m)).
{ apply elements_1. rewrite find_mapsto_iff. unfold multiplicity. simpl. unfold m_multiplicity.
  destruct (find x m); discriminate || now rewrite Pos2Nat.id. }
assert (Hdup := elements_3 m).
revert m'. induction (FMapInterface.elements m) as [| [y p] l]; intro m'; simpl; [now inversion Hm |].
destruct (equiv_dec x y) as [Hxy | Hxy].
+ assert (Heq : eq_key (x, Pos.of_nat m[x]) (y, p)) by auto.
  assert (p = n).
  { inversion_clear Hm.
    - destruct H as [_ H]. revert H. simpl. unfold m_multiplicity. now rewrite Hin, Pos2Nat.id.
    - exfalso. inversion_clear Hdup. now rewrite eq_key_elt_eq_key_subrelation, Heq in H. }
  subst p. inversion_clear Hdup. change m_multiplicity with multiplicity in *.
  rewrite (fold_add_out_list _  _ n); trivial; [|].
  - rewrite Hxy. apply m_add_same.
  - assert (Heq' : eq_key (x, n) (y, n)) by auto. now rewrite Heq'.
+ rewrite IHl.
  - f_equal. now apply m_add_other.
  - inversion_clear Hm; trivial. now destruct H as [? _].
  - now inversion_clear Hdup.
Qed.

Lemma In_MIn : forall x s, FMapInterface.In x s <-> s[x] > 0.
Proof using MapSpec.
intros x s. split; intro H.
- destruct H as [n Hn]. rewrite find_mapsto_iff in Hn. simpl.
  unfold m_multiplicity. rewrite Hn. now apply Pos2Nat.is_pos.
- exists (Pos.of_nat (m_multiplicity x s)). rewrite find_mapsto_iff. simpl in *. unfold multiplicity in *.
  unfold m_multiplicity in *. destruct (find x s). now rewrite Pos2Nat.id. now inversion H.
Qed.

Lemma Mequal_Mequivb_equiv : forall s s', Equal s s' <-> Equivb Pos.eqb s s'.
Proof using MapSpec.
intros s s'. split.
+ intro Heq. split.
  - intro x. split; intros [e Hin]; exists e.
      now rewrite find_mapsto_iff, <- Heq, <- find_mapsto_iff.
      now rewrite find_mapsto_iff, Heq, <- find_mapsto_iff.
  - intros x e e' He He'. rewrite find_mapsto_iff in He, He'.
    rewrite Heq in He. rewrite He in He'. inversion_clear He'. unfold Cmp. now apply Pos.eqb_refl.
+ intros [Heq1 Heq2] x.
  destruct (find x s) as [e |] eqn:Hfind, (find x s') as [e' |] eqn:Hfind'.
  - f_equal. apply Pos.eqb_eq. apply (Heq2 x); now rewrite find_mapsto_iff.
  - assert (Habs : FMapInterface.In x s'). { rewrite <- Heq1. exists e. now rewrite find_mapsto_iff. }
    destruct Habs as [e' Habs]. rewrite find_mapsto_iff, Hfind' in Habs. discriminate Habs.
  - assert (Habs : FMapInterface.In x s). { rewrite Heq1. exists e'. now rewrite find_mapsto_iff. }
    destruct Habs as [e Habs]. rewrite find_mapsto_iff, Hfind in Habs. discriminate Habs.
  - reflexivity.
Qed.

Lemma multiplicity_out : forall x m, m[x] = 0 <-> find x m = None.
Proof using .
simpl. unfold m_multiplicity. intros x m. split; intro Hm.
+ destruct (find x m) eqn:Hfind.
  - elim (lt_irrefl 0). rewrite <- Hm at 2. now apply Pos2Nat.is_pos.
  - reflexivity.
+ now rewrite Hm.
Qed.

(** **  Specifications of operations  **)

(** Specification of [multiplicity] *)
Global Instance multiplicity_spec : MultiplicitySpec elt _.
Proof using MapSpec.
split.
intros x y Hxy m m' Hm. rewrite Hm. simpl. unfold m_multiplicity.
assert (Heq : find x m' = find y m') by now apply find_m.
now rewrite Heq.
Qed.

(** Specification of [empty] *)
Global Instance empty_full_spec : EmptySpec elt _.
Proof using MapSpec.
split. intro x. simpl. unfold m_multiplicity, empty.
destruct (find x (FMapInterface.empty positive)) eqn:Hin.
- rewrite (empty_o positive x) in Hin. discriminate Hin.
- reflexivity.
Qed.

(** Specification of [singleton] *)
Global Instance singleton_spec : SingletonSpec elt _.
Proof using MapSpec. split.
+ intros x n. unfold singleton, add. simpl. destruct (Nat.eq_dec n 0).
  - subst n. unfold m_multiplicity. now rewrite empty_o.
  - unfold m_multiplicity. rewrite add_eq_o, Nat2Pos.id; trivial; reflexivity.
+ intros x y n Heq. unfold singleton, add. simpl. destruct (Nat.eq_dec n 0).
  - subst n. unfold m_multiplicity. now rewrite empty_o.
  - unfold m_multiplicity. rewrite add_neq_o, empty_o; reflexivity || now symmetry.
Qed.

(** Specification of [add] *)
Global Instance add_spec : AddSpec elt _.
Proof using MapSpec. split.
+ intros x n s. unfold add. simpl. unfold m_add. destruct (Nat.eq_dec n 0). lia.
  unfold m_multiplicity at 1. rewrite add_eq_o, Nat2Pos.id; reflexivity || lia.
+ intros x y n s Hyx. unfold add. simpl. unfold m_add. destruct (Nat.eq_dec n 0); trivial; [].
  unfold m_multiplicity at 1 3. rewrite add_neq_o; reflexivity || now symmetry.
Qed.

(** Specification of [remove] *)
Global Instance remove_spec : RemoveSpec elt _.
Proof using MapSpec. split.
+ intros x n s. unfold remove. simpl. destruct (Nat.eq_dec n 0). lia.
  destruct (le_lt_dec (m_multiplicity x s) n) as [Hle | Hlt]; unfold m_multiplicity at 1; simpl.
  - rewrite remove_eq_o; reflexivity || lia.
  - rewrite add_eq_o, Nat2Pos.id; reflexivity || lia.
+ intros x y n s Hyx. unfold remove. simpl. destruct (Nat.eq_dec n 0); trivial.
  destruct (le_lt_dec (m_multiplicity x s) n) as [Hle | Hlt]; unfold m_multiplicity at 1; simpl.
  - rewrite remove_neq_o; reflexivity || now symmetry.
  - rewrite add_neq_o; reflexivity || now symmetry.
Qed.

(** Specifications of [union], [inter], [diff], and [lub] *)
Global Instance binary_spec :  BinarySpec elt _.
Proof using MapSpec. split.
* intros x s s'. unfold union. simpl. destruct (find x s) eqn:Hin.
  - unfold m_multiplicity at 2. rewrite Hin. erewrite fold_add; eauto. now repeat intro.
  - unfold m_multiplicity at 2. rewrite Hin. erewrite fold_add_out; eauto.
    intros [n Habs]. now rewrite find_mapsto_iff, Hin in Habs.
* intros x s s'. unfold inter. simpl. destruct (find x s') eqn:Hin.
  + setoid_rewrite (fold_add (fun x n => min (m_multiplicity x s) n) x p s' (FMapInterface.empty _)); trivial; [|].
    - unfold multiplicity. simpl. unfold m_multiplicity. now rewrite empty_o, Hin, plus_0_r.
    - intros ? ? Heq ? ? ?. subst. now rewrite Heq.
  + rewrite fold_add_out.
    - unfold multiplicity. simpl. unfold m_multiplicity. now rewrite Hin, Min.min_0_r, empty_o.
    - intros [n Habs]. now rewrite find_mapsto_iff, Hin in Habs.
* intros x s s'. unfold diff. simpl. destruct (find x s) eqn:Hin.
  + setoid_rewrite (fold_add (fun x n => n - multiplicity x s') x p s (FMapInterface.empty _)); trivial.
    - unfold multiplicity. simpl. unfold m_multiplicity. now rewrite empty_o, Hin, plus_0_r.
    - intros ? ? Heq ? ? ?. subst. now rewrite Heq.
  + rewrite fold_add_out.
    - unfold multiplicity. simpl. unfold m_multiplicity. now rewrite Hin, empty_o.
    - intros [n Habs]. now rewrite find_mapsto_iff, Hin in Habs.
* intros x s s'. unfold lub. simpl.
  replace (max (m_multiplicity x s) (m_multiplicity x s'))
    with (m_multiplicity x s - m_multiplicity x s' + m_multiplicity x s') by (apply Max.max_case_strong; lia).
  destruct (find x s) eqn:Hin.
  + erewrite (fold_add); eauto.
    -unfold multiplicity. simpl. unfold m_multiplicity. now rewrite Hin.
    - intros ? ? Heq ? ? ?. subst. now rewrite Heq.
  + rewrite fold_add_out.
    - unfold multiplicity. simpl. unfold m_multiplicity. now rewrite Hin.
    - intros [n Habs]. now rewrite find_mapsto_iff, Hin in Habs.
Qed.

(** Specification of [fold] *)
Global Instance fold_full_spec : FoldSpec elt _.
Proof using MapSpec. split.
* intros A i f s. unfold fold, elements. simpl. unfold m_fold.
  now rewrite FMapInterface.fold_1, fold_left_map.
* intros A eqA HeqA f Hf Hfcomm s1 s2 Hs x y Hxy.
  unfold fold. simpl. unfold m_fold. do 2 rewrite FMapInterface.fold_1.
  rewrite fold_left_symmetry_PermutationA.
  + reflexivity.
  + apply eq_key_elt_Equivalence.
  + assumption.
  + intros ? ? Heq ? ? [? Heq']. now apply Hf; try rewrite Heq || rewrite Heq'.
  + intros. apply Hfcomm.
  + apply NoDupA_equivlistA_PermutationA.
    - autoclass.
    - eapply NoDupA_strengthen; apply eq_key_eq_key_elt_subrelation || apply elements_3.
    - eapply NoDupA_strengthen; apply eq_key_eq_key_elt_subrelation || apply elements_3.
    - clear -Hs MapSpec. intros [x n].
      setoid_rewrite <- @elements_mapsto_iff; trivial; []. setoid_rewrite @find_mapsto_iff; trivial; [].
      specialize (Hs x). cbn in Hs. unfold m_multiplicity in Hs.
      destruct (find x s1), (find x s2);
      solve [ apply Pos2Nat.inj in Hs; subst; reflexivity
            | elim (lt_irrefl 0); rewrite Hs at 2 || rewrite <- Hs at 2; apply Pos2Nat.is_pos
            | split; intro; discriminate ].
  + assumption.
Qed.

(** Specifications of [equal], [subset], and [is_empty] *)
Global Instance test_spec : TestSpec elt _.
Proof using MapSpec.
assert (His_empty_spec : forall s, is_empty s = true <-> s == empty).
{ intros s. unfold is_empty. simpl. split; intro H.
  + rewrite <- is_empty_iff in H. intros x. unfold m_multiplicity. rewrite empty_o.
    destruct (find x s) eqn:Hin; trivial. rewrite <- find_mapsto_iff in Hin. now apply H in Hin.
  + rewrite <- is_empty_iff. intros x n Habs.
    rewrite find_mapsto_iff in Habs. specialize (H x).
    unfold m_multiplicity in H. rewrite Habs, empty_o in H.
    apply (lt_irrefl 0). rewrite <- H at 2. apply Pos2Nat.is_pos. }
split; trivial.
* intros s s'. unfold equal. simpl.
  destruct (FMapInterface.equal Pos.eqb s s') eqn:Heq.
  + split; intro H; trivial || clear H. rewrite <- equal_iff, <- Mequal_Mequivb_equiv in Heq.
    unfold m_multiplicity. intro. now rewrite Heq.
  + split; intro Habs; try discriminate Habs. exfalso.
    assert (Hneq : ~FMapInterface.Equivb Pos.eqb s s').
    { intro Habs'. rewrite equal_iff, Heq in Habs'. discriminate Habs'. }
    rewrite <- Mequal_Mequivb_equiv in Hneq. apply Hneq. intro x.
    unfold m_multiplicity in Habs. specialize (Habs x). simpl in Habs.
    destruct (find x s) eqn:Hin1, (find x s') eqn:Hin2.
    - f_equal. now apply Pos2Nat.inj.
    - elim (lt_irrefl 0). rewrite <- Habs at 2. now apply Pos2Nat.is_pos.
    - elim (lt_irrefl 0). rewrite Habs at 2. now apply Pos2Nat.is_pos.
    - reflexivity.
* intros s s'. unfold subset. simpl.
  cbn in His_empty_spec. rewrite His_empty_spec. clear His_empty_spec.
  unfold m_multiplicity at 3. setoid_rewrite empty_o.
  split; intro Hle.
  + intro x. destruct (find x s) eqn:Hin.
    - cut (s[x] - s'[x] = 0). lia. rewrite <- diff_spec. simpl.
      erewrite fold_add; eauto; [|].
      ++ unfold multiplicity. simpl. unfold m_multiplicity at 2. rewrite empty_o, plus_0_r.
         specialize (Hle x). erewrite fold_add in Hle; eauto.
         -- unfold multiplicity in Hle. simpl in Hle. unfold m_multiplicity at 2 in Hle.
            now rewrite empty_o, plus_0_r in Hle.
         -- intros ? ? Heq ? ? ?. subst. now rewrite Heq.
      ++ intros ? ? Heq ? ? ?. subst. now rewrite Heq.
    - simpl. unfold m_multiplicity at 1. rewrite Hin. lia.
  + intro x. destruct (find x s) eqn:Hin.
    - erewrite fold_add; eauto.
      -- unfold multiplicity. simpl. unfold m_multiplicity at 2. rewrite empty_o, plus_0_r.
         specialize (Hle x). simpl in Hle. unfold m_multiplicity at 1 in Hle. rewrite Hin in Hle. lia.
      -- intros ? ? Heq ? ? ?. subst. now rewrite Heq.
    - erewrite fold_add_out; eauto.
      -- unfold multiplicity. simpl. unfold m_multiplicity. now rewrite empty_o.
      -- intros [n Habs]. now rewrite find_mapsto_iff, Hin in Habs.
Qed.

Corollary eq_dec : forall s s', {s == s'} + {s =/= s'}.
Proof using MapSpec.
intros s s'. destruct (equal s s') eqn:Heq.
- left. now rewrite <- equal_spec.
- right. intro H. revert H. rewrite <- equal_spec. rewrite Heq. discriminate.
Qed.

(** Specification of [elements] *)
Global Instance elements_full_spec : ElementsSpec elt _.
Proof using MapSpec. split.
* intros [x n] s. unfold elements. simpl. rewrite InA_map_iff; [split; intro H |..].
  + destruct H as [[y m] [[Heq1 Heq2] Hin]]. hnf in Heq1, Heq2. cbn in Heq1, Heq2. subst.
    rewrite <- elements_mapsto_iff, find_mapsto_iff in Hin.
    unfold m_multiplicity. rewrite <- Heq1, Hin. split; trivial. apply Pos2Nat.is_pos.
  + exists (x, Pos.of_nat n). destruct H as [H1 H2]. simpl in *. split.
    - split; hnf; simpl. reflexivity. apply Nat2Pos.id. lia.
    - rewrite <- elements_mapsto_iff, find_mapsto_iff. subst. unfold m_multiplicity in *.
      destruct (find x s). now rewrite Pos2Nat.id. lia.
  + autoclass.
  + autoclass.
  + clear. intros [] [] []. intros. split; simpl in *. assumption. now subst.
* intro s. unfold elements. simpl. rewrite NoDupA_inj_map;
  apply elements_3 || autoclass || (intros [] [] ?; assumption).
Qed.

(** Specification of [support] *)
Local Lemma support_elements_aux : forall x l1 l2, NoDupA eq_key (l1 ++ l2) -> 
  ((InA equiv x (fold_left (fun acc xn => fst xn :: acc) l1 (List.map (@fst _ positive) l2)) <->
  exists n, InA eq_key_elt (x, n) (List.map (fun xn => (fst xn, snd xn)) (l1 ++ l2)))).
Proof using .
intros x l1. induction l1; simpl; intros l2 Hdup.
* split; intro H.
  + induction l2.
    - now inversion H.
    - destruct a as [y m]. inversion_clear H.
        exists m. left. now split.
        apply IHl2 in H0. destruct H0 as [n Hn]. exists n. simpl. now right. now inversion_clear Hdup.
  + destruct H as [n Hn]. induction l2; simpl.
    - now inversion Hn.
    - destruct a as [y m]. inversion_clear Hdup. inversion_clear Hn.
        left. now destruct H1.
        right. now apply IHl2.
* destruct a as [y m]. simpl. split; intro H.
  + destruct (equiv_dec x y). exists m. left. now split.
    change (y :: List.map (fst (B:=positive)) l2) with (List.map (fst (B:=positive)) ((y,m) :: l2)) in H.
    rewrite IHl1 in H.
    - destruct H as [p Hp]. exists p. rewrite map_app in *. rewrite InA_app_iff in Hp.
        simpl in Hp. destruct Hp.
          right. rewrite InA_app_iff. now left.
          inversion_clear H.
             now left.
             right. rewrite InA_app_iff. now right.
    - rewrite NoDupA_swap_iff. assumption. refine _.
  + change (y :: List.map (fst (B:=positive)) l2) with (List.map (fst (B:=positive)) ((y,m) :: l2)).
    rewrite IHl1. destruct H as [n Hn]. exists n. rewrite map_app, InA_app_iff. inversion_clear Hn.
    - right. now left.
    - rewrite map_app, InA_app_iff in H. destruct H. now left. now do 2 right.
    - rewrite NoDupA_swap_iff. assumption. autoclass.
Qed.

Lemma support_elements : forall x s, InA equiv x (support s) <-> InA eq_pair (x, multiplicity x s) (elements s).
Proof using MapSpec.
intros x s. unfold support, elements. simpl. rewrite fold_1.
change nil with (List.map (@fst elt positive) nil).
rewrite (support_elements_aux x (FMapInterface.elements s) nil); rewrite app_nil_r; [split; intro H |].
+ destruct H as [n Hn].
  rewrite (@InA_map_iff _ _ eq_key_elt) in Hn; try rewrite (@InA_map_iff _ _ eq_key_elt); autoclass;
  try (now intros [? ?] [? ?] Heq; simpl in *; hnf in Heq; destruct Heq; split; hnf; simpl in *; subst; auto); [].
  destruct Hn as [[y m] [[Heqx Heqn] Hin]]. exists (y, m). repeat split; eauto; try now hnf in *; cbn in *.
  subst. rewrite <- elements_mapsto_iff, find_mapsto_iff in Hin. 
  hnf in *. simpl in *. subst. unfold m_multiplicity.
  rewrite find_m in Hin; eauto; try now intro; reflexivity. now rewrite Hin.
+ exists (Pos.of_nat (multiplicity x s)).
  rewrite (@InA_map_iff _ _ eq_key_elt) in H; try rewrite (@InA_map_iff _ _ eq_key_elt); autoclass;
  try (now intros [? ?] [? ?] Heq; simpl in *; hnf in Heq; destruct Heq; split; hnf; simpl in *; subst; auto); [].
  destruct H as [[y m] [[Heqx Heqn] Hin]]. exists (y, m). repeat split; eauto; try now hnf in *; cbn in *.
  subst. rewrite <- elements_mapsto_iff, find_mapsto_iff in Hin. 
  hnf in *. simpl in *. subst. unfold m_multiplicity.
  rewrite find_m in Hin; eauto; try now intro; reflexivity. now rewrite Hin, Pos2Nat.id.
+ apply elements_3.
Qed.

Local Lemma support_NoDupA_aux : forall A B (l1 : list (A*B)) l2,
  fold_left (fun acc p => fst p :: acc) l1 l2 = rev (List.map (@fst _ _) l1) ++ l2.
Proof using .
intros A B l1. induction l1; intro l2; simpl.
- reflexivity.
- rewrite IHl1. now rewrite <- app_assoc.
Qed.

Global Instance support_spec : SupportSpec elt _.
Proof using MapSpec. split.
* intros x s. rewrite support_elements. rewrite elements_spec. intuition.
* intro s. unfold support. simpl. rewrite fold_1, support_NoDupA_aux, app_nil_r.
  apply NoDupA_rev; autoclass; [].
  rewrite NoDupA_inj_map; (now apply elements_3) || autoclass || (now intros ? ? ?).
Qed.

(** Specification of [choose] *)
Local Lemma choose_spec_aux : forall x s o, ~FMapInterface.In x s ->
  fold_left (fun (_ : option elt) (p : elt * positive) => Some (fst p)) (FMapInterface.elements s) o = Some x ->
  o = Some x.
Proof using MapSpec.
intros x s o Hs.
assert (Hs' : forall n, ~InA eq_key_elt (x, n) (FMapInterface.elements s)).
{ intros n Habs. apply Hs. exists n. now apply elements_2. } clear Hs.
revert o. induction (FMapInterface.elements s); simpl; intros o Hin.
+ assumption.
+ apply IHl in Hin.
  - elim (Hs' (snd a)). left. split; simpl. now inversion Hin. reflexivity.
  - intros n Habs. apply (Hs' n). now right.
Qed.

Global Instance choose_spec : ChooseSpec elt _.
Proof using MapSpec.
assert (Hchoose_Some : forall (x : elt) (s : multiset elt), choose s = Some x -> In x s).
{ intros x s Hin. destruct (In_dec s x).
  + unfold In. now rewrite <- In_MIn.
  + unfold choose in Hin. simpl in Hin. rewrite fold_1 in Hin.
    apply choose_spec_aux in Hin; trivial; discriminate. }
split; trivial.
* intros s. split; intro Hs.
  + intro x. unfold choose in Hs. simpl in Hs. rewrite fold_1 in Hs. rewrite empty_spec. rewrite multiplicity_out.
    destruct (find x s) eqn:Habs; trivial; [].
    rewrite <- find_mapsto_iff in Habs. apply elements_1 in Habs. destruct (FMapInterface.elements s).
    - now inversion Habs.
    - clear -Hs. simpl in Hs. revert p0 Hs. induction l. discriminate. intros. simpl in Hs. now apply (IHl _ Hs).
  + destruct (choose s) eqn:H; trivial; [].
    apply Hchoose_Some in H. rewrite Hs in H. unfold In in H. rewrite empty_spec in H. lia.
Qed.

(** Specification of [filter] *)
Local Lemma fold_nfilter_out_list : forall f x n l s, ~InA eq_key (x, n) l -> NoDupA eq_key l ->
  multiplicity x (fold_left (fun acc xn => if f (fst xn) (snd xn) : bool
                                           then add (fst xn) (Pos.to_nat (snd xn)) acc else acc) l s)
  = multiplicity x s.
Proof using MapSpec.
intros f x n l s Hin Hdup. revert s. induction l as [| [y m] l]; intro s; simpl.
+ reflexivity.
+ rewrite IHl.
  - destruct (f y m); auto. apply m_add_other. intro Habs. apply Hin. now left.
  - intro Habs. apply Hin. now right.
  - now inversion_clear Hdup.
Qed.

Local Lemma nfilter_spec_In : forall f s s' x, compatb f -> In x s ->
  multiplicity x
    (m_fold (fun y n acc => if f y n : bool then add y n acc else acc) s s')
  = if f x (multiplicity x s) then multiplicity x s + multiplicity x s' else multiplicity x s'.
Proof using MapSpec.
intros f s s' x Hf Hin. unfold m_fold. rewrite fold_1. revert s'. unfold In in Hin.
assert (Hs : InA eq_pair (x, multiplicity x s) (elements s)). { rewrite elements_spec. simpl. now split. }
assert (Hdup : NoDupA eq_elt (elements s)) by apply elements_NoDupA.
unfold elements in Hs, Hdup. simpl in Hs, Hdup.
induction (FMapInterface.elements s); simpl; intro s'; simpl in Hs.
* exfalso. rewrite <- InA_nil. apply Hs.
* destruct a as [y m].
  destruct (equiv_dec (x, Pos.of_nat (multiplicity x s)) (y, m)) as [Heq | Hneq].
  + destruct Heq as [H1 H2]. simpl in H1, H2 |- *. rewrite H1 in *. subst m.
    rewrite (fold_nfilter_out_list (fun x y => f x (Pos.to_nat y)) _ (Pos.of_nat (multiplicity y s))).
    - cbn in Hin. rewrite Nat2Pos.id; try lia; [].
      destruct (f y (m_multiplicity y s)) eqn:Htest; now rewrite ?m_add_same, H1.
    - inversion_clear Hdup. intro Habs. apply H. rewrite InA_map_iff; autoclass.
      -- exists (y, Pos.of_nat (m_multiplicity y s)). split; reflexivity || eassumption.
      -- clear. intros [] [] Hxy. now compute in *.
    - inversion_clear Hdup. rewrite NoDupA_inj_map in H0; solve [ eassumption | autoclass | now intros [] [] ].
  + inversion_clear Hs.
    - elim Hneq. destruct H as [H1 H2]. split; trivial; [].
      simpl in *. hnf in H2. cbn in H2. now rewrite H2, Pos2Nat.id.
    - inversion_clear Hdup.
      assert (Hxy : x =/= y) by (intro; eauto using eq_pair_elt_weak_In).
      rewrite IHl; try assumption. simpl.
      destruct (f x (multiplicity x s)), (f y (Pos.to_nat m));
      reflexivity || rewrite m_add_other; reflexivity || now auto.
Qed.

Local Lemma nfilter_spec_out : forall f s s' x, ~In x s ->
  multiplicity x (m_fold (fun y n acc => if f y n : bool then m_add y n acc else acc) s s')
  = multiplicity x s'.
Proof using MapSpec.
intros f s s' x Hin. unfold m_fold. rewrite fold_1.
assert (Hs : forall n, ~(InA eq_key_elt (x, n) (FMapInterface.elements s))).
{ intros n Habs. apply Hin. apply elements_2, find_mapsto_iff in Habs.
  unfold In. simpl. unfold m_multiplicity. rewrite Habs. apply Pos2Nat.is_pos. }
revert s'. induction (FMapInterface.elements s) as [| [y m] l]; intro s'; trivial; [].
assert ( Hxy : x =/= y). { intro Habs. apply (Hs m). left. now split. }
simpl. rewrite IHl.
- destruct (f y (Pos.to_nat m)); trivial; []. apply m_add_other. auto.
- intros n Habs. apply (Hs n). now right.
Qed.

Global Instance filter_spec : FilterSpec elt _.
Proof using MapSpec.
assert (Hnfilter : forall (f : elt -> nat -> bool) (x : elt) (s : multiset elt),
        Proper (equiv ==> eq ==> eq) f ->
        (nfilter f s)[x] = (if f x s[x] then s[x] else 0)).
* intros f x s Hf. unfold nfilter. simpl.
  destruct (m_multiplicity x s) eqn:Hin.
  + rewrite nfilter_spec_out.
    - unfold multiplicity. simpl. unfold m_multiplicity. rewrite empty_o. now destruct (f x 0).
    - unfold In. simpl. lia.
  + rewrite nfilter_spec_In.
    - unfold multiplicity. simpl. unfold m_multiplicity at 3 4. now rewrite empty_o, Hin, plus_0_r.
    - assumption.
    - unfold In. simpl. lia.
* split; trivial.
  intros f x s Hf. change (filter f s) with (nfilter (fun x _ => f x) s).
  apply Hnfilter. repeat intro. now apply Hf.
Qed.


(* Theorem filter_nfilter : forall f s, filter f s [=] nfilter (fun x _ => f x) s.
Proof. now unfold filter. Qed. *)

(** Specifications of [cardinal] and [size] *)
Global Instance size_spec : SizeSpec elt _.
Proof using MapSpec. split.
* intro. unfold cardinal. simpl. unfold m_fold. reflexivity.
* intro. unfold size, support. simpl. now rewrite fold_1, fold_left_length, fold_1, fold_left_cons_length.
Qed.

(** Specifications of [for_all] and [exists_] *)
Lemma fold_and_true_base_step : forall A f (l : list A) b, 
  fold_left (fun a x => a && f x) l b = true -> b = true.
Proof using .
intros A f l. induction l; simpl; intros b Hl.
- assumption.
- apply IHl in Hl. destruct b. reflexivity. simpl in Hl. discriminate Hl.
Qed.

Lemma fold_and_true_inductive_step : forall A f (l : list A) a b, 
  fold_left (fun a x => a && f x) (a :: l) b = true -> f a = true.
Proof using .
simpl. intros A f l a b Hl. apply fold_and_true_base_step in Hl.
destruct (f a). reflexivity. destruct b; simpl in Hl; discriminate Hl.
Qed.

Lemma Melements_multiplicity : forall s x n,
  InA eq_key_elt (x, n) (FMapInterface.elements s)
  <-> multiplicity x s = Pos.to_nat n /\ Pos.to_nat n > 0.
Proof using MapSpec.
intros s x n. split; intro H.
+ apply elements_2, find_mapsto_iff in H. unfold multiplicity. simpl. unfold m_multiplicity.
  rewrite H. split; trivial; []. apply Pos2Nat.is_pos.
+ destruct H as [H1 H2]. unfold multiplicity in H1. simpl in H1. unfold m_multiplicity in H1.
  destruct (find x s) eqn:Hin.
  - apply elements_1, find_mapsto_iff. rewrite Hin. f_equal. now apply Pos2Nat.inj.
  - rewrite  <- H1 in H2. inversion H2.
Qed.

Lemma for_all_spec_aux : forall (f : elt -> nat -> bool) s b, compatb f ->
  (m_fold (fun x n b => b && (f x n)) s b = true
   <-> b = true /\ For_all (fun x n => f x n = true) s).
Proof using MapSpec.
intros f s b Hf. unfold m_fold. rewrite fold_1. unfold For_all. split; intro H.
+ split. now apply fold_and_true_base_step in H.
  intros x Hin. unfold In in Hin. rewrite <- In_MIn in Hin. destruct Hin as [n Hin]. apply elements_1 in Hin.
  assert (Hn : multiplicity x s = Pos.to_nat n) by now rewrite Melements_multiplicity in Hin.
  revert b H x n Hn Hin. induction (FMapInterface.elements s); intros b H x n Hn Hin; inversion_clear Hin.
  - simpl in H. apply fold_and_true_base_step in H. rewrite andb_true_iff in H.
    destruct H as [_ H ], a, H0 as [H1 H2]. simpl in *. rewrite Hn, H1. now subst p.
  - simpl in H. apply (IHl _ H _ _ Hn H0).
+ destruct H as [Hb H]. subst b.
  assert (forall xn, InA eq_key_elt xn (FMapInterface.elements s) -> f (fst xn) (Pos.to_nat (snd xn)) = true).
  { intros [x n] Hx. simpl. rewrite Melements_multiplicity in Hx. destruct Hx as [Hm Hp].
    setoid_rewrite <- Pos2Nat.id. rewrite <- Hm, Nat2Pos.id. apply H. unfold In. simpl. now setoid_rewrite Hm. lia. }
  clear H. revert H0. induction (FMapInterface.elements s); simpl; intro Hin; trivial.
  rewrite Hin. apply IHl. intros x Hx. apply Hin. now right. now left.
Qed.

Lemma exists_spec_aux : forall (f : elt -> nat -> bool) s b, compatb f ->
  (m_fold (fun x n b => b || (f x n)) s b = true
  <-> b = true \/ Exists (fun x n => f x n = true) s).
Proof using MapSpec.
intros f s b Hf.
assert (Hequiv : Exists (fun x n => f x n = true) s <->
        exists x, exists n, InA eq_key_elt (x, n) (FMapInterface.elements s) /\ f x (Pos.to_nat n) = true).
{ split; intros [x Hx].
  + destruct Hx as [Hin Hfx]. exists x. exists (Pos.of_nat (m_multiplicity x s)). split.
    - rewrite Melements_multiplicity. unfold In in Hin. simpl in *. rewrite Nat2Pos.id. now split. lia.
    - rewrite Nat2Pos.id. assumption. unfold In in Hin. simpl in Hin. lia.
  + destruct Hx as [n [Hin Hfx]]. exists x. rewrite Melements_multiplicity in Hin. destruct Hin as [Hn Hp]. split.
    - simpl in *. unfold In. simpl. now rewrite Hn.
    - simpl in *. now rewrite Hn. }
rewrite Hequiv. clear Hequiv. unfold m_fold. rewrite fold_1. unfold For_all. split; intro H.
* revert b H. induction (FMapInterface.elements s); intros b H.
  + simpl in H. now left.
  + simpl in H. apply IHl in H. rewrite orb_true_iff in H. destruct H as [[H | H] | H]; (now left) || right.
    - destruct a as [x n]. exists x. exists n. split. now left. assumption.
    - destruct H as [x [n [Hin Hfx]]]. exists x. exists n. split. now right. assumption.
* revert b H. induction (FMapInterface.elements s); simpl; intros b H.
  + destruct H. assumption.
    destruct H as [? [? [Habs _]]]. now inversion Habs.
  + apply IHl. rewrite orb_true_iff. destruct H as [H | H].
    - now do 2 left.
    - destruct H as [x [n [Hin Hfx]]]. inversion_clear Hin.
      -- left. right. destruct H as [H1 H2]. simpl in H1, H2. now rewrite <- H1, <- H2.
      -- right. exists x. exists n. now split.
Qed.

Global Instance quantifiers_spec : QuantifierSpec elt _.
Proof using MapSpec. split.
* intros. unfold for_all. simpl. rewrite for_all_spec_aux; intuition.
* intros. unfold exists_. simpl. rewrite exists_spec_aux; intuition discriminate.
Qed.

(** Specification of [npartition] *)
Definition npartition_fun f := fun x n acc =>
         if f x (Pos.to_nat n) : bool
         then (add x (Pos.to_nat n) (fst acc), snd acc)
         else (fst acc, add x (Pos.to_nat n) (snd acc)).

Lemma fold_npartition_fst_out_list : forall f x n l s12,
  ~InA eq_key (x, n) l -> NoDupA eq_key l ->
  multiplicity x
  (fst
     (fold_left (fun acc xn => if f (fst xn) (Pos.to_nat (snd xn)) : bool
         then (add (fst xn) (Pos.to_nat (snd xn)) (fst acc), snd acc)
         else (fst acc, add (fst xn) (Pos.to_nat (snd xn)) (snd acc))) l s12))
  = multiplicity x (fst s12).
Proof using MapSpec.
intros f x n l s12 Hin Hdup. revert s12. induction l as [| [y m] l]; intros s12; trivial.
simpl. rewrite IHl.
- destruct (f y (Pos.to_nat m)); trivial; [].
  apply m_add_other. intro Habs. apply Hin. now left.
- intro Habs. apply Hin. now right.
- now inversion_clear Hdup.
Qed.

Lemma npartition_spec_fst_In : forall f s s12 x, compatb f -> In x s ->
  multiplicity x (fst (m_fold (fun x n acc =>
         if f x n : bool
         then (m_add x n (fst acc), snd acc)
         else (fst acc, m_add x n (snd acc))) s s12)) =
  (if f x (multiplicity x s) then multiplicity x s + multiplicity x (fst s12) else multiplicity x (fst s12)).
Proof using MapSpec.
intros f s s' x Hf Hin. unfold m_fold. rewrite fold_1. revert s'. unfold In in Hin. simpl in Hin.
assert (Hs : InA eq_pair (x, multiplicity x s) (elements s)). { rewrite elements_spec. simpl. now split. }
assert (Hdup : NoDupA eq_elt (elements s)) by apply elements_NoDupA.
unfold elements in Hs, Hdup. simpl in Hs, Hdup.
induction (FMapInterface.elements s); simpl; intros [s1 s2]; simpl in Hs.
* exfalso. rewrite <- InA_nil. apply Hs.
* destruct a as [y m]. simpl.
  destruct (equiv_dec (x, Pos.of_nat (multiplicity x s)) (y, m)) as [Heq | Hneq].
  + destruct Heq as [H1 H2]. simpl in H1, H2 |- *. rewrite H1 in *. subst m.
    rewrite (fold_npartition_fst_out_list f _ (Pos.of_nat (multiplicity y s))).
    - rewrite Nat2Pos.id; try lia; [].
      destruct (f y (m_multiplicity y s)) eqn:Htest; simpl; now rewrite ?m_add_same, H1.
    - inversion_clear Hdup. intro Habs. apply H. rewrite InA_map_iff.
      -- exists (y, Pos.of_nat (multiplicity y s)). split; eauto; reflexivity.
      -- autoclass.
      -- autoclass.
      -- clear. intros [] [] Hxy. now compute in *.
    - inversion_clear Hdup. rewrite NoDupA_inj_map in H0;
       solve [ eassumption | autoclass | now intros [] [] ].
  + inversion_clear Hs.
    - elim Hneq. destruct H as [H1 H2]. split. assumption. hnf in *. simpl in *. now rewrite H2, Pos2Nat.id.
    - inversion_clear Hdup.
      assert (Hxy : x =/= y) by (intro; eauto using eq_pair_elt_weak_In).
      rewrite IHl; try assumption. simpl. unfold npartition_fun.
      destruct (f x (multiplicity x s)), (f y (Pos.to_nat m));
      reflexivity || simpl; rewrite m_add_other; reflexivity || now auto.
Qed.

Lemma npartition_spec_fst_out : forall f s s12 x, ~In x s ->
  multiplicity x (fst (m_fold (fun x n acc =>
      if f x n : bool then (m_add x n (fst acc), snd acc) else (fst acc, m_add x n (snd acc))) s s12))
  = multiplicity x (fst s12).
Proof using MapSpec.
intros f s s' x Hin. unfold m_fold. rewrite fold_1.
assert (Hs : forall n, ~(InA eq_key_elt (x, n) (FMapInterface.elements s))).
{ intros n Habs. apply Hin. apply elements_2, find_mapsto_iff in Habs.
  unfold In. simpl. unfold m_multiplicity. rewrite Habs. apply Pos2Nat.is_pos. }
revert s'. induction (FMapInterface.elements s) as [| [y m] l]; intro s'; simpl; trivial; [].
assert ( Hxy : x =/= y). { intro Habs. apply (Hs m). left. now split. }
rewrite IHl.
+ unfold npartition_fun. destruct (f y (Pos.to_nat m)).
  - apply m_add_other. now auto.
  - reflexivity.
+ intros n Habs. apply (Hs n). now right.
Qed.

Lemma fold_npartition_snd_out_list : forall f x n l s12,
  ~InA eq_key (x, n) l -> NoDupA eq_key l ->
  multiplicity x
  (snd
     (fold_left
        (fun acc xn =>
         if f (fst xn) (Pos.to_nat (snd xn)) : bool
         then (add (fst xn) (Pos.to_nat (snd xn)) (fst acc), snd acc)
         else (fst acc, add (fst xn) (Pos.to_nat (snd xn)) (snd acc))) l s12))
  = multiplicity x (snd s12).
Proof using MapSpec.
intros f x n l s12 Hin Hdup. revert s12.
induction l as [| [y m] l]; intros s12; simpl.
+ reflexivity.
+ rewrite IHl.
  - destruct (f y (Pos.to_nat m)). reflexivity. simpl. apply m_add_other. intro Habs. apply Hin. now left.
  - intro Habs. apply Hin. now right.
  - now inversion_clear Hdup.
Qed.

Lemma npartition_spec_snd_In : forall f s s12 x, compatb f -> In x s ->
  multiplicity x
  (snd
     (m_fold
        (fun y n acc =>
         if f y n : bool then (m_add y n (fst acc), snd acc) else (fst acc, m_add y n (snd acc))) s s12))
  = if f x (multiplicity x s) then multiplicity x (snd s12) else multiplicity x s + multiplicity x (snd s12).
Proof using MapSpec.
intros f s s' x Hf Hin. unfold m_fold. rewrite fold_1. revert s'. unfold In in Hin. simpl in Hin.
assert (Hs : InA eq_pair (x, multiplicity x s) (elements s)). { rewrite elements_spec. simpl. now split. }
assert (Hdup : NoDupA eq_elt (elements s)) by apply elements_NoDupA.
unfold elements in Hs, Hdup. simpl in Hs, Hdup.
induction (FMapInterface.elements s); simpl; intros [s1 s2]; simpl in Hs.
* exfalso. rewrite <- InA_nil. apply Hs.
* destruct a as [y m].
  destruct (equiv_dec (x, Pos.of_nat (multiplicity x s)) (y, m)) as [Heq | Hneq].
  + destruct Heq as [H1 H2]. simpl in H1, H2 |- *. rewrite H1 in *. subst m.
    rewrite (fold_npartition_snd_out_list f _ (Pos.of_nat (multiplicity y s))).
    - rewrite Nat2Pos.id; try lia; [].
      destruct (f y (m_multiplicity y s)) eqn:Htest; simpl; now rewrite ?m_add_same, H1.
    - inversion_clear Hdup. intro Habs. apply H. rewrite InA_map_iff.
      -- exists (y, Pos.of_nat (multiplicity y s)). split; reflexivity || eassumption.
      -- autoclass.
      -- autoclass.
      -- clear. intros [] [] Hxy. now compute in *.
    - inversion_clear Hdup. rewrite NoDupA_inj_map in H0;
      solve [eassumption | autoclass | now intros [] [] ].
  + inversion_clear Hs.
    - elim Hneq. destruct H as [H1 H2]. split. assumption. hnf in *. simpl in *. now rewrite H2, Pos2Nat.id.
    - inversion_clear Hdup.
      assert (Hxy : x =/= y) by (intro; eauto using eq_pair_elt_weak_In).
      rewrite IHl; try assumption. simpl.
      destruct (f x (multiplicity x s)), (f y (Pos.to_nat m));
      reflexivity || simpl; rewrite m_add_other; reflexivity || now auto.
Qed.

Lemma npartition_spec_snd_out : forall f s s12 x, ~In x s ->
  multiplicity x
  (snd
     (m_fold
        (fun y n acc =>
         if f y n : bool then (m_add y n (fst acc), snd acc) else (fst acc, m_add y n (snd acc))) s s12))
  = multiplicity x (snd s12).
Proof using MapSpec.
intros f s s' x Hin. unfold m_fold. rewrite fold_1.
assert (Hs : forall n, ~(InA eq_key_elt (x, n) (FMapInterface.elements s))).
{ intros n Habs. apply Hin. apply elements_2, find_mapsto_iff in Habs.
  unfold In. simpl. unfold m_multiplicity. rewrite Habs. apply Pos2Nat.is_pos. }
revert s'. induction (FMapInterface.elements s) as [| [y m] l]; intro s'; trivial.
assert (Hxy : x =/= y). { intro Habs. apply (Hs m). left. now split. }
simpl. rewrite IHl.
- destruct (f y (Pos.to_nat m)); trivial; [].
  apply m_add_other. now auto.
- intros n Habs. apply (Hs n). now right.
Qed.

Global Instance npartition_spec : NpartitionSpec elt _.
Proof using MapSpec. split.
* intros f s Hf x. unfold npartition. rewrite nfilter_spec; trivial. simpl.
  destruct (m_multiplicity x s) eqn:Hin.
  + rewrite npartition_spec_fst_out.
    - simpl. unfold multiplicity. simpl. unfold m_multiplicity. rewrite empty_o. now destruct (f x 0).
    - unfold In. simpl. lia.
  + setoid_rewrite npartition_spec_fst_In.
    - simpl. unfold m_multiplicity at 3 4. now rewrite empty_o, Hin, plus_0_r.
    - assumption.
    - unfold In. simpl. lia.
* intros f s Hf x. rewrite nfilter_spec.
  + unfold npartition. simpl.
    destruct (m_multiplicity x s) eqn:Hin.
    - rewrite npartition_spec_snd_out.
      -- simpl. unfold m_multiplicity. rewrite empty_o. now destruct (f x 0).
      -- unfold In. simpl. lia.
    - rewrite npartition_spec_snd_In.
      -- simpl. unfold m_multiplicity at 2 4. rewrite empty_o, Hin, plus_0_r. now destruct (f x (S n)).
      -- assumption.
      -- unfold In. simpl. lia.
  + intros ? ? Heq ? ? ?. subst. now rewrite Heq.
Qed.

(** Specification of [partition] *)
Theorem partition_npartition_fst : forall f s, fst (partition f s) == fst (npartition (fun x _ => f x) s).
Proof using . now unfold partition. Qed.

Theorem partition_npartition_snd : forall f s, snd (partition f s) == snd (npartition (fun x _ => f x) s).
Proof using . now unfold partition. Qed.

Global Instance partition_spec : PartitionSpec elt _.
Proof using MapSpec. split.
* intros f s Hf. rewrite partition_npartition_fst, npartition_spec_fst.
  - reflexivity.
  - repeat intro. now apply Hf.
* intros f s Hf. rewrite partition_npartition_snd, npartition_spec_snd.
  - reflexivity.
  - repeat intro. now apply Hf.
Qed.

(** The full set of specifications. *)
Global Instance MakeFMultisetsFacts : FMultisetsOn elt _.
Proof using MapSpec. split; autoclass. Qed.

End WMapImplementation.
