(* Partly taken from Containers library and the StdLib FMapWeakList.v *)

Require Import RelationPairs.
Require Import List SetoidList.
Require Import Bool.
Require Import SetoidDec.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.FMaps.FMapInterface.


Set Implicit Arguments.
Open Scope signature_scope.

(** *  Operations  **)

Section ListOperations.
Variable key : Type.
Context `{EqDec key}.
Variable elt : Type.

(** **  Operations on raw lists  **)

Notation t := (fun T => list (key * T)).
Notation eq_pair := (fun xn yp => fst xn == fst yp /\ snd xn = snd yp).

Fixpoint list_mem (k : key) (s : t elt) {struct s} : bool :=
  match s with
   | nil => false
   | (k',_) :: l => if equiv_dec k k' then true else list_mem k l
  end.

Fixpoint list_add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => (k,x) :: nil
   | (k',y) :: l => if equiv_dec k k' then (k, x) :: l else (k', y) :: list_add k x l
  end.

Fixpoint list_find (k:key) (s: t elt) {struct s} : option elt :=
  match s with
   | nil => None
   | (k',x)::s' => if equiv_dec k k' then Some x else list_find k s'
  end.

(* In the then branch, we can optimize away the recursive call
   if we preserve the invariant that l does not contains duplicates. *)
Fixpoint list_remove (k : key) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => nil
   | (k',x) :: l => if equiv_dec k k' then list_remove k l else (k',x) :: list_remove k l
  end.

Fixpoint list_fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc : A) {struct m} : A :=
  match m with
   | nil => acc
   | (k,e)::m' => list_fold f m' (f k e acc)
  end.

Definition list_check (cmp : elt -> elt -> bool)(k:key)(e:elt)(m': t elt) :=
  match list_find k m' with
   | None => false
   | Some e' => cmp e e'
  end.

Definition list_submap (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  list_fold (fun k e b => andb (list_check cmp k e m') b) m true.

Definition list_equal (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  andb (list_submap cmp m m') (list_submap (fun e' e => cmp e e') m' m).

Fixpoint list_map {elt'} (f:elt -> elt') (m:t elt) : t elt' :=
  match m with
   | nil => nil
   | (k,e)::m' => (k,f e) :: list_map f m'
  end.

Fixpoint list_mapi {elt'} (f: key -> elt -> elt') (m:t elt) : t elt' :=
  match m with
   | nil => nil
   | (k,e)::m' => (k,f k e) :: list_mapi f m'
  end.

(** **  Preservation of the [NoDupA] property  **)

Notation tt elt := (sig (@NoDupA (key * elt) (equiv@@1))).

Lemma list_add_3 : forall (m : t elt) x y e e',
  x =/= y -> InA (equiv@@1) (y, e) (list_add x e' m) -> InA (equiv@@1) (y, e) m.
Proof using .
intros m x y e e' Hxy Hy. simpl. induction m as [| [z p] l].
+ inversion_clear Hy; try inversion H0. now elim Hxy.
+ simpl in *. destruct (equiv_dec x z).
  - right. inversion_clear Hy; trivial. now elim Hxy.
  - inversion_clear Hy; now left + (right; apply IHl).
Qed.

Lemma t_add_lemma : forall k x (s : t elt),
  NoDupA (equiv@@1) s -> NoDupA (equiv@@1) (list_add x k s).
Proof using .
intros k x s Hs. induction s as [| [y p] l].
+ constructor; trivial. intro Habs. inversion Habs.
+ simpl. destruct (equiv_dec x y) as [Hxy | Hxy]; constructor; inversion_clear Hs.
  - assert (Heq : equiv@@1 (x, k) (y, p)) by assumption. now rewrite Heq.
  - assumption.
  - intro Habs. apply H0. eauto using list_add_3.
  - auto.
Qed.

Definition t_add (k : key) (x : elt) (s : tt elt) : tt elt :=
  exist _ (list_add k x (proj1_sig s)) (t_add_lemma _ _ (proj2_sig s)).


Lemma list_remove_3 : forall (m : t elt) x y e,
  InA (equiv@@1) (y, e) (list_remove x m) -> InA (equiv@@1) (y, e) m.
Proof using .
intros m x y e Hy. simpl. induction m as [| [z p] l].
- inversion_clear Hy.
- simpl in *. destruct (equiv_dec x z); auto.
  inversion_clear Hy; now left + (right; apply IHl).
Qed.

Lemma t_remove_lemma : forall k (s : t elt),
  NoDupA (equiv@@1) s -> NoDupA (equiv@@1) (list_remove k s).
Proof using .
intros x s Hs. induction s as [| [y p] l].
+ now constructor.
+ simpl. destruct (equiv_dec x y) as [Hxy | Hxy].
  - inversion_clear Hs. auto.
  - constructor; inversion_clear Hs.
    -- intro Habs. apply H0. eauto using list_remove_3.
    -- auto.
Qed.

Definition t_remove (k : key) (s : tt elt) : tt elt :=
  exist _ (list_remove k (proj1_sig s)) (t_remove_lemma _ (proj2_sig s)).


Lemma t_map_lemma : forall {elt'} (f : elt -> elt') (s : t elt),
  NoDupA (equiv@@1) s -> NoDupA (equiv@@1) (list_map f s).
Proof using .
intros elt' f s Hs. induction s as [| [y p] l].
+ now constructor.
+ simpl. inversion_clear Hs. constructor.
  - intro. apply H0. clear -H2. induction l as [| [] ?]; inversion_clear H2.
    -- hnf in H. cbn in *. now left.
    -- right. auto.
  - auto.
Qed.

Definition t_map {elt'} (f : elt -> elt') (s : tt elt) : tt elt' :=
  exist _ (list_map f (proj1_sig s)) (t_map_lemma _ (proj2_sig s)).


Lemma t_mapi_lemma : forall {elt'} (f : key -> elt -> elt') (s : t elt),
  NoDupA (equiv@@1) s -> NoDupA (equiv@@1) (list_mapi f s).
Proof using .
intros elt' f s Hs. induction s as [| [y p] l].
+ now constructor.
+ simpl. inversion_clear Hs. constructor.
  - intro. apply H0. clear -H2. induction l as [| [] ?]; inversion_clear H2.
    -- hnf in H. cbn in *. now left.
    -- right. auto.
  - auto.
Qed.

Definition t_mapi {elt'} (f : key -> elt -> elt') (s : tt elt) : tt elt' :=
  exist _ (list_mapi f (proj1_sig s)) (t_mapi_lemma _ (proj2_sig s)).

End ListOperations.

(** The full set of operations. *)
Instance MapList key `{EqDec key} : FMap := {|
  dict := fun elt => sig (@NoDupA (key * elt) (equiv@@1));
  MapsTo := fun elt k e m => InA equiv (k, e) (proj1_sig m);
  empty := fun elt => (exist _ nil (NoDupA_nil (equiv@@1)));
  is_empty := fun elt m => match proj1_sig m with nil => true | cons _ _ => false end;
  mem := fun elt k m => list_mem k (proj1_sig m);
  add := fun elt => @t_add _ _ _ elt;
  find := fun elt x m => @list_find _ _ _ elt x (proj1_sig m);
  remove := fun elt => @t_remove _ _ _ elt;
  equal := fun elt cmp m m' => @list_equal _ _ _ elt cmp (proj1_sig m) (proj1_sig m');
  map := fun elt => @t_map _ _ elt;
  mapi := fun elt => @t_mapi _ _ elt;
  fold := fun elt A f m => @list_fold _ elt A f (proj1_sig m);
  cardinal := fun elt m => @length _ (proj1_sig m);
  elements := fun elt m => (proj1_sig m) |}.

Local Transparent dict MapsTo empty is_empty mem add find
                  remove equal map mapi fold cardinal elements.
Local Notation t := (sig (@NoDupA (_ * _) (equiv@@1))).
Local Notation eq_pair := (fun xn yp => fst xn == fst yp /\ snd xn = snd yp).

(** **  Proofs of the specifications  **)

Instance MapListFacts_MapsTo key `{EqDec key} : FMapSpecs_MapsTo MapList.
Proof using .
split. intros elt [m Hm] x y e Hxy Hx. simpl in *.
induction m; inversion_clear Hx.
- left. simpl in *. now rewrite <- Hxy.
- right. inversion_clear Hm. now apply IHm.
Qed.

Instance MapListFacts_mem key `{EqDec key} : FMapSpecs_mem MapList.
Proof using . split.
* intros elt [m Hm] x [e Hin]. simpl in *. induction m as [| [y n] l]; inversion_clear Hin.
  + simpl. destruct (equiv_dec x y) as [Hxy | Hxy]; trivial. elim Hxy. now destruct H0.
  + simpl. destruct (equiv_dec x y) as [Hxy | Hxy]; trivial. inversion_clear Hm. auto.
* intros elt [m Hm] x Hmem. unfold In. simpl in *. induction m as [| [y n] l]; simpl in Hmem.
  + discriminate.
  + destruct (equiv_dec x y) as [Hxy | Hxy].
    - exists n. left. now split.
    - inversion_clear Hm. apply IHl in Hmem; trivial; [].
      destruct Hmem as [e ?]. exists e. now right.
Qed.

Instance MapListFacts_empty key `{EqDec key} : FMapSpecs_empty MapList.
Proof using . split. intros elt x e Hin. inversion Hin. Qed.

Instance MapListFacts_is_empty key `{EqDec key} : FMapSpecs_is_empty MapList.
Proof using . split.
* intros elt [m Hm] Hm'. destruct m as [| [x n] l]; trivial.
  elim Hm' with x n. now left.
* intros elt [m Hm] Hm'. destruct m as [| [x n] l]; try discriminate.
  intros x n Hin. inversion Hin.
Qed.

Instance MapListFacts_add key `{EqDec key} : FMapSpecs_add MapList.
Proof using . split.
* intros elt [m Hm] x y e Hxy. simpl in *. induction m as [| [z p] l]; simpl.
  + now left.
  + inversion_clear Hm. destruct (equiv_dec x z); now left + right; auto.
* intros elt [m Hm] x y e e' Hxy Hy. simpl in *. induction m as [| [z p] l].
  + inversion Hy.
  + simpl. destruct (equiv_dec x z).
    - right. inversion_clear Hy; trivial.
      elim Hxy. destruct H0. now transitivity z.
    - inversion_clear Hm. inversion_clear Hy; now left + (right; apply IHl).
* intros elt [m Hm] x y e e' Hxy Hy. simpl in *. induction m as [| [z p] l].
  + inversion_clear Hy; inversion H0. now elim Hxy.
  + simpl in *. destruct (equiv_dec x z).
    - right. inversion_clear Hy; trivial. now elim Hxy.
    - inversion_clear Hm. inversion_clear Hy; now left + (right; apply IHl).
Qed.

Instance MapListFacts_remove key `{EqDec key} : FMapSpecs_remove MapList.
Proof using . split.
* intros elt [m Hm] x y Hxy. simpl. unfold t_remove, In. simpl. induction m as [| [z p] l].
  + simpl. intros [? Habs]. inversion Habs.
  + simpl. inversion_clear Hm. destruct (equiv_dec x z) as [Hxz | Hxz]; auto; [].
    intros [n Habs]. inversion_clear Habs.
    - elim Hxz. destruct H2. now transitivity y.
    - apply IHl; eauto.
* intros elt [m Hm] x y e Hxy Hy. simpl in *. induction m as [| [z p] l].
  + inversion Hy.
  + inversion_clear Hm. simpl. destruct (equiv_dec x z).
    - inversion_clear Hy; simpl in *; auto; [].
      elim Hxy. destruct H2. now transitivity z.
    - inversion_clear Hy; now left + (right; apply IHl).
* intros elt [m Hm] x y e Hy. simpl in *. induction m as [| [z p] l].
  + inversion_clear Hy.
  + inversion_clear Hm. simpl in *. destruct (equiv_dec x z); auto.
    inversion_clear Hy; now left + (right; apply IHl).
Qed.

Instance MapListFacts_find key `{EqDec key} : FMapSpecs_find MapList.
Proof using . split.
* intros elt [m Hm] x e Hin. simpl in *. induction m as [| [y p] l].
  + inversion Hin.
  + inversion_clear Hm. simpl. destruct (equiv_dec x y).
    - inversion_clear Hin; try (now f_equal); [].
      assert (Heq : equiv@@1 (x, e) (y, p)) by assumption.
      elim H0. eapply InA_eqA; eauto with typeclass_instances; [].
      revert H2. apply InA_impl_compat; trivial; [].
      now repeat intro.
    - inversion_clear Hin; now auto.
* intros elt [m Hm] x e Hin. simpl in *. induction m as [| [y p] l].
  + inversion Hin.
  + inversion_clear Hm. simpl in Hin. destruct (equiv_dec x y).
    - inversion_clear Hin; now auto.
    - right. auto.
Qed.

Instance MapListFacts_elements key `{EqDec key} : FMapSpecs_elements MapList.
Proof using . split.
* tauto.
* tauto.
* intros elt [m Hm]. simpl. assumption.
Qed.

Instance MapListFacts_cardinal key `{EqDec key} : FMapSpecs_cardinal MapList.
Proof using . split. tauto. Qed.

Instance MapListFacts_fold key `{EqDec key} : FMapSpecs_fold MapList.
Proof using . split.
intros elt [m Hm] A i f. simpl. revert i. induction m as [| [y p] l]; simpl.
- reflexivity.
- intro i. inversion_clear Hm. now rewrite IHl.
Qed.

Definition Submap key `{EqDec key} {elt : Type} cmp (m m' : Map [key, elt]) :=
  (forall k, In k m -> In k m') /\
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

Local Lemma submap_1 key elt `{EqDec key} : forall m m' cmp,
  Submap cmp m m' -> list_submap (elt:=elt) cmp (proj1_sig m) (proj1_sig m') = true.
Proof using .
unfold Submap, list_submap.
intros [m Hm].
induction m as [| [k e] m].
* simpl; auto.
* simpl; intros m' cmp [H1 H2].
  inversion_clear Hm.
  assert (Hin : In k m') by now apply H1; exists e; simpl; left.
  destruct Hin as (e', Hin).
  unfold list_check at 2. apply find_1 in Hin. simpl in Hin. rewrite Hin.
  rewrite (H2 k); simpl.
  + apply (IHm H3).
    split; intuition.
    - apply H1. destruct H4 as [e'' H4]; exists e''; simpl in *; auto.
    - apply H2 with k0; auto.
  + now left.
  + change (MapsTo k e' m'). now apply find_2.
Qed.

Local Lemma submap_2 key elt `{EqDec key} : forall m m' cmp,
  list_submap (elt:=elt) cmp (proj1_sig m) (proj1_sig m') = true -> Submap cmp m m'.
Proof using .
unfold Submap, list_submap.
intros [m Hm]. induction m as [| [k e] m].
* simpl in *; auto.
  split; intros * Hin.
  + destruct Hin. inversion H1.
  + inversion Hin.
* simpl; intros * Hsub.
  inversion_clear Hm.
  rewrite andb_b_true in Hsub.
  assert (Hcheck : list_check cmp k e (proj1_sig m') = true).
  { clear H1 H0 IHm.
    set (b := list_check cmp k e (proj1_sig m')) in *.
    revert Hsub. generalize b; clear b.
    induction m as [| [y p] m]; simpl; auto; intros; simpl in *.
    assert (Hnodup : NoDupA (equiv @@1) ((k, e) :: m)).
    { inversion_clear Hm. inversion_clear H1. constructor; auto. }
    destruct (andb_prop _ _ (IHm Hnodup _ Hsub)); auto. }
  rewrite Hcheck in Hsub.
  destruct (IHm H1 m' cmp Hsub) as [H2 H3]; auto.
  unfold list_check in Hcheck.
  case_eq (list_find k (proj1_sig m')); [intros e' H4 | intros H4];
    rewrite H4 in Hcheck; try discriminate.
  split; intros.
  + destruct H5 as [e0 H6]; inversion_clear H6.
    - destruct H5 as [H5 H6]; simpl in H5, H6.
      exists e'.
      apply MapsTo_1 with k; try easy.
      apply find_2; auto.
    - apply H2. exists e0; auto.
  + inversion_clear H5.
    - compute in H7; destruct H7; subst.
      change (MapsTo k0 e'0 m') in H6. apply (MapsTo_1 H5), find_1 in H6.
      simpl in H6. congruence.
    - apply H3 with k0; auto.
Qed.


Instance MapListFacts_equal key `{EqDec key} : FMapSpecs_equal MapList.
Proof using . split.
* unfold Equivb, equal.
  intuition.
  apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
* unfold Equivb, equal.
  intros elt m m' cmp Heq.
  destruct (andb_prop _ _ Heq); clear Heq.
  generalize (submap_2 m m' cmp H0).
  generalize (submap_2 m' m _ H1).
  firstorder.
Qed.

Instance MapListFacts_map key `{EqDec key} : FMapSpecs_map MapList.
Proof using . split.
* intros elt elt' [m Hm] x e f Hin. simpl in *. induction m as [| [y p] m].
  + inversion Hin.
  + inversion_clear Hm. simpl. destruct (equiv_dec x y).
    - left. simpl. split; trivial. inversion_clear Hin.
      -- simpl in *. destruct H2. now subst.
      -- assert (Heq : equiv@@1 (x, e) (y, p)) by assumption.
         elim H0. eapply InA_eqA; eauto with typeclass_instances; [].
         revert H2. apply InA_impl_compat; trivial; [].
         now repeat intro.
    - inversion_clear Hin; try easy; [].
      right. auto.
* unfold In. intros elt elt' [m Hm] x f [e Hin]. simpl in *. induction m as [| [y p] m].
  + inversion Hin.
  + inversion_clear Hm. simpl. destruct (equiv_dec x y).
    - exists p. now left.
    - inversion_clear Hin; try easy; [].
      destruct IHm as [e' ?]; trivial; [].
      exists e'. now right.
Qed.

Instance MapListFacts_mapi key `{EqDec key} : FMapSpecs_mapi MapList.
Proof using . split.
* intros elt elt' [m Hm] x e f Hin. simpl in *. induction m as [| [y p] m].
  + inversion Hin.
  + inversion_clear Hm. simpl. destruct (equiv_dec x y).
    - exists y. split; try (now symmetry); []. left.
      simpl. split; trivial. inversion_clear Hin.
      -- simpl in *. destruct H2. now subst.
      -- assert (Heq : equiv@@1 (x, e) (y, p)) by assumption.
         elim H0. eapply InA_eqA; eauto with typeclass_instances; [].
         revert H2. apply InA_impl_compat; trivial; [].
         now repeat intro.
    - inversion_clear Hin; try easy; [].
      destruct IHm as [y' Hy']; trivial; []. exists y'.
      split; try (now symmetry); []. now right.
* unfold In. intros elt elt' [m Hm] x f [e Hin]. simpl in *. induction m as [| [y p] m].
  + inversion Hin.
  + inversion_clear Hm. destruct (equiv_dec x y).
    - exists p. now left.
    - inversion_clear Hin; try easy; [].
      destruct IHm as [e' ?]; trivial; [].
      exists e'. now right.
Qed.

(** The full set of specifications. *)
Instance MapListFacts key `{EqDec key} : FMapSpecs MapList.
Proof using . split; auto with typeclass_instances. Qed.
