(* Partly taken from Containers library and the StdLib FSetWeakList.v *)

Require Import List SetoidPermutation SetoidList.
Require Import Bool.
Require Import SetoidDec.
Require Pactole.Util.Coqlib.
Require Import Pactole.Util.FSets.FSetInterface.



Set Implicit Arguments.
Open Scope signature_scope.

(** *  Operations  **)

Definition set_ (A : Type) `{EqDec A} := list A.

Section ListOperations.
  Variable elt : Type.
  Context `{EqDec elt}.
  Notation t := (@set_ elt _ _).

  (** **  Operations on raw lists  **)
  
(*  Definition empty : set := nil. *)
  Definition list_is_empty (s : t) : bool := if s then true else false.
  
  Fixpoint list_mem (x : elt) (s : t) {struct s} : bool :=
    match s with
    | nil => false
    | y :: l => if x == y then true else list_mem x l
    end.
  
  Definition list_add (x : elt) (s : t) : t :=
    if list_mem x s then s else x :: s.
  
  Definition list_singleton (x : elt) : t := x :: nil.
  
  Fixpoint list_remove (x : elt) (s : t) {struct s} : t :=
    match s with
    | nil => nil
    | y :: l => if x == y then l else y :: list_remove x l
    end.
  
  Definition list_fold {B : Type} (f : elt -> B -> B) : t -> B -> B :=
    fold_left (flip f).
  
  Definition list_union (s : t) : t -> t := list_fold list_add s.
  
  Definition list_inter (s s': t) : t :=
    list_fold (fun x s => if list_mem x s' then list_add x s else s) s nil.
  
  Definition list_diff (s s' : t) : t := list_fold list_remove s' s.
  
  Definition list_subset (s s' : t) : bool := list_is_empty (list_diff s s').
  
  Definition list_equal (s s' : t) : bool := andb (list_subset s s') (list_subset s' s).
  
  Fixpoint list_filter (f : elt -> bool) (s : t) : t :=
    match s with
    | nil => nil
    | x :: l => if f x then x :: list_filter f l else list_filter f l
    end.
  
  Fixpoint list_for_all (f : elt -> bool) (s : t) : bool :=
    match s with
    | nil => true
    | x :: l => if f x then list_for_all f l else false
    end.
  
  Fixpoint list_exists_ (f : elt -> bool) (s : t) : bool :=
    match s with
    | nil => false
    | x :: l => if f x then true else list_exists_ f l
    end.
  
  Fixpoint list_partition (f : elt -> bool) (s : t) : t * t :=
    match s with
    | nil => (nil, nil)
    | x :: l =>
      let (s1, s2) := list_partition f l in
      if f x then (x :: s1, s2) else (s1, x :: s2)
    end.
  
  Definition list_choose (s : t) : option elt :=
    match s with
    | nil => None
    | x::_ => Some x
    end.
  
  (** **  Preservation of the [NoDupA] property  **)
  
  Lemma t_add_lemma : forall x (s : t),
    NoDupA equiv s -> NoDupA equiv (list_add x s).
  Proof.
  intros x s Hs. induction s as [| y l].
  + constructor; trivial; []. intro Habs. inversion Habs.
  + specialize (IHl ltac:(now inversion_clear Hs)).
    unfold list_add in *. simpl in *.
    destruct (x == y) as [| Hxy]; [| destruct (list_mem x l)]; try apply Hs; [].
    constructor; trivial; [].
    inversion_clear Hs. inversion_clear IHl.
    intro Habs. inversion_clear Habs; contradiction.
  Qed.
  
  Notation set elt := (sig (@NoDupA elt equiv)).
  
  Definition t_add (x : elt) (s : set elt) : set elt :=
    exist _ (list_add x (proj1_sig s)) (t_add_lemma _ (proj2_sig s)).
  
  
  Lemma list_remove_aux : forall (m : t) x y,
    InA equiv y (list_remove x m) -> InA equiv y m.
  Proof.
  intros m x y Hy. simpl. induction m as [| z l].
  - inversion_clear Hy.
  - simpl in *. destruct (x == z); auto.
    inversion_clear Hy; now left + (right; apply IHl).
  Qed.
  
  Lemma t_remove_lemma : forall k (s : t),
    NoDupA equiv s -> NoDupA equiv (list_remove k s).
  Proof.
  intros x s Hs. induction s as [| y l].
  + now constructor.
  + simpl. destruct (x == y) as [Hxy | Hxy].
    - inversion_clear Hs. auto.
    - constructor; inversion_clear Hs.
      -- intro Habs. apply H0. eauto using list_remove_aux.
      -- auto.
  Qed.
  
  Definition t_remove (x : elt) (s : set elt) : set elt :=
    exist _ (list_remove x (proj1_sig s)) (t_remove_lemma _ (proj2_sig s)).
  
  
  Lemma t_union_lemma : forall s1 s2,
    NoDupA equiv s1 -> NoDupA equiv s2 -> NoDupA equiv (list_union s1 s2).
  Proof.
  intros s1 s2 Hs1. unfold list_union, list_fold, flip.
  revert s2. induction s1; simpl; intros s2 Hs2.
  + assumption.
  + inversion_clear Hs1. apply IHs1; auto using t_add_lemma.
  Qed.
  
  Definition t_union (s1 s2 : set elt) : set elt :=
    exist _ (list_union (proj1_sig s1) (proj1_sig s2)) (t_union_lemma (proj2_sig s1) (proj2_sig s2)).
  
  
  Lemma t_inter_lemma : forall s1 s2,
    NoDupA equiv s1 -> NoDupA equiv (list_inter s1 s2).
  Proof.
  intros s1 s2 Hs1. unfold list_inter, list_fold, flip.
  generalize (NoDupA_nil equiv). generalize (@nil elt) as acc.
  induction s1 as [| e1 s1]; simpl; intros acc Hacc.
  + assumption.
  + inversion_clear Hs1. apply IHs1; trivial; [].
    destruct (list_mem e1 s2); auto using t_add_lemma.
  Qed.
  
  Definition t_inter (s1 s2 : set elt) : set elt :=
    exist _ (list_inter (proj1_sig s1) (proj1_sig s2)) (t_inter_lemma (proj1_sig s2) (proj2_sig s1)).
  
  
  Lemma t_diff_lemma : forall s1 s2,
    NoDupA equiv s1 -> NoDupA equiv (list_diff s1 s2).
  Proof.
  intros s1 s2. unfold list_diff, list_fold, flip.
  revert s1. induction s2 as [| e2 s2]; simpl; intros s1 Hs1.
  + assumption.
  + now apply IHs2, t_remove_lemma.
  Qed.
  
  Definition t_diff (s1 s2 : set elt) : set elt :=
    exist _ (list_diff (proj1_sig s1) (proj1_sig s2)) (t_diff_lemma (proj1_sig s2) (proj2_sig s1)).
  
  
  Lemma list_filter_incl : forall f s, inclA equiv (list_filter f s) s.
  Proof.
  intros f s. induction s as [| e s]; simpl.
  + reflexivity.
  + destruct (f e).
    - intros x Hin. inversion_clear Hin; (now left) || now right; apply IHs.
    - etransitivity; eauto; []. intros x Hin. now right.
  Qed.
  
  Lemma t_filter_lemma : forall (f : elt -> bool) (s : @set_ elt _ _),
    NoDupA equiv s -> NoDupA equiv (list_filter f s).
  Proof.
  intros f s Hs. induction Hs as [| e s He Hs IHs]; simpl.
  + constructor.
  + destruct (f e); trivial; [].
    constructor; trivial; [].
    intro Habs. apply He. eapply list_filter_incl, Habs.
  Qed.
  
  Definition t_filter f (s : set elt) : set elt :=
    exist _ (list_filter f (proj1_sig s)) (t_filter_lemma f (proj2_sig s)).
  
  
  Lemma list_partition_fst_incl : forall f s, inclA equiv (fst (list_partition f s)) s.
  Proof.
  intros f s. induction s as [| e s]; simpl.
  + reflexivity.
  + destruct (list_partition f s) as [s1 s2], (f e); simpl.
    - intros x Hin. inversion_clear Hin; (now left) || now right; apply IHs.
    - etransitivity; eauto; []. intros x Hin. now right.
  Qed.
  
  Lemma t_partition_lemma_fst : forall (f : elt -> bool) (s : @set_ elt _ _),
    NoDupA equiv s -> NoDupA equiv (fst (list_partition f s)).
  Proof.
  intros f s Hs. induction Hs as [| e s He Hs IHs]; simpl.
  + constructor.
  + destruct (list_partition f s) as [s1 s2] eqn:Hfs, (f e); simpl in *.
    - constructor; trivial; [].
      intro Hin. apply He. eapply list_partition_fst_incl. now rewrite Hfs.
    - assumption.
  Qed.
  
  Lemma list_partition_snd_incl : forall f s, inclA equiv (snd (list_partition f s)) s.
  Proof.
  intros f s. induction s as [| e s]; simpl.
  + reflexivity.
  + destruct (list_partition f s) as [s1 s2], (f e); simpl.
    - etransitivity; eauto; []. intros x Hin. now right.
    - intros x Hin. inversion_clear Hin; (now left) || now right; apply IHs.
  Qed.
  
  Lemma t_partition_lemma_snd : forall (f : elt -> bool) (s : @set_ elt _ _),
    NoDupA equiv s -> NoDupA equiv (snd (list_partition f s)).
  Proof.
  intros f s Hs. induction Hs as [| e s He Hs IHs]; simpl.
  + constructor.
  + destruct (list_partition f s) as [s1 s2] eqn:Hfs, (f e); simpl in *.
    - assumption.
    - constructor; trivial; [].
      intro Hin. apply He. eapply list_partition_snd_incl. now rewrite Hfs.
  Qed.
  
  Definition t_partition f (s : set elt) : set elt * set elt :=
    (exist _ (fst (list_partition f (proj1_sig s))) (t_partition_lemma_fst f (proj2_sig s)),
     exist _ (snd (list_partition f (proj1_sig s))) (t_partition_lemma_snd f (proj2_sig s))).
  
End ListOperations.

(*  Notation In := (@InA elt equiv).
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : set) := exists x, In x s /\ P x. *)


(*
Lemma list_add_3 : forall (m : t elt) x y e e',
  x =/= y -> InA (equiv@@1) (y, e) (list_add x e' m) -> InA (equiv@@1) (y, e) m.
Proof.
intros m x y e e' Hxy Hy. simpl. induction m as [| [z p] l].
+ inversion_clear Hy; try inversion H0. now elim Hxy.
+ simpl in *. destruct (equiv_dec x z).
  - right. inversion_clear Hy; trivial. now elim Hxy.
  - inversion_clear Hy; now left + (right; apply IHl).
Qed.*)

(** **  Map between sets (not currently incorporated to the signature)  **)
Section SetMap.
  
  Variable elt : Type.
  Context `{EqDec elt}.
  Notation set elt := (sig (@NoDupA elt equiv)).
  
  Definition list_map {elt' : Type} `{EqDec elt'}
                      (f : elt -> elt') (s : @set_ elt _ _) : @set_ elt' _ _ :=
    list_fold (fun x acc => list_add (f x) acc) s nil.
  
  Lemma t_map_lemma {elt'} `{EqDec elt'} : forall (f : elt -> elt') (s : @set_ elt _ _),
    NoDupA equiv s -> NoDupA equiv (list_map f s).
  Proof.
  intros f s Hs. unfold list_map, list_fold, list_add, flip.
  generalize (@NoDupA_nil elt' equiv).
  generalize (@nil elt') as acc.
  induction Hs as [| y l Hy Hs IHs]; simpl; intros acc Hacc.
  * assumption.
  * apply IHs.
    destruct (list_mem (f y) acc) eqn:Htest.
    + assumption.
    + constructor; trivial; [].
      intro Hin. induction acc.
      - inversion Hin.
      - simpl in *. destruct (f y == a) as [Heq | Heq]; try discriminate; [].
        inversion_clear Hacc. inversion_clear Hin; auto.
  Qed.
  
  Definition t_map {elt'} `{EqDec elt'} (f : elt -> elt') (s : set elt) : set elt' :=
    exist _ (list_map f (proj1_sig s)) (t_map_lemma f (proj2_sig s)).
  
End SetMap.

(*
Arguments empty {_%type_scope} {_} {_}.
Arguments In  {_%type_scope} {_} {_} {_} _ _%list_scope.
Arguments is_empty {_%type_scope} {_} {_} _%list_scope.
Arguments mem {_%type_scope} {_} {_}  _ _%set_scope.
Arguments add {_%type_scope} {_} {_} _%set_scope.
Arguments remove {_%type_scope} {_} {_} _ _%set_scope.
Arguments union {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments inter {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments diff {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments equal {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments subset {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments fold {elt%type_scope} {_%type_scope} {_} _ _%set_scope _.
Arguments map {elt%type_scope} {_%type_scope} {_} {_} {_} _ _%set_scope.
Arguments for_all {_%type_scope} {_} _ _%set_scope.
Arguments exists_ {_%type_scope} {_} _ _%set_scope.
Arguments filter {_%type_scope} {_} _ _%set_scope.
Arguments partition {_%type_scope} {_} _ _%set_scope.
Arguments cardinal {_%type_scope} {_} _%set_scope.
Arguments elements {_%type_scope} {_} _%set_scope.
Arguments choose {_%type_scope} {_} _%set_scope.
*)
(** The full set of operations. *)
Instance SetList elt `{EqDec elt} : FSet := {|
  set := sig (@NoDupA elt equiv);
  In := fun x s => InA equiv x (proj1_sig s);
  empty := exist _ nil (NoDupA_nil equiv);
  is_empty := fun s => match proj1_sig s with nil => true | cons _ _ => false end;
  mem := fun x s => list_mem x (proj1_sig s);
  add := @t_add _ _ _;
  singleton := fun x => t_add x (exist _ nil (NoDupA_nil equiv));
  remove := @t_remove _ _ _;
  union := @t_union _ _ _;
  inter := @t_inter _ _ _;
  diff := @t_diff _ _ _;
  equal := fun s s' => @list_equal _ _ _ (proj1_sig s) (proj1_sig s');
  subset := fun s s' => @list_subset _ _ _ (proj1_sig s) (proj1_sig s');
(*   map := t_map _ _; *)
  fold := fun A f s => @list_fold _ _ _ A f (proj1_sig s);
  for_all := fun f s => List.forallb f (proj1_sig s);
  exists_ := fun f s => List.existsb f (proj1_sig s);
  filter := @t_filter _ _ _;
  partition := @t_partition _ _ _;
  cardinal := fun s => @length _ (proj1_sig s);
  elements := fun s => (proj1_sig s);
  choose := fun s => list_choose (proj1_sig s) |}.

(* Typeclasses Opaque set. *)



(** **  Proofs of the specifications  **)
(*
Instance MapListFacts_MapsTo key `{EqDec key} : FMapSpecs_MapsTo (MapList _).
Proof.
split. intros elt [m Hm] x y e Hxy Hx. simpl in *.
induction m; inversion_clear Hx.
- left. simpl in *. now rewrite <- Hxy.
- right. inversion_clear Hm. now apply IHm.
Qed.

Instance MapListFacts_mem key `{EqDec key} : FMapSpecs_mem (MapList _).
Proof. split.
* intros elt [m Hm] x [e Hin]. simpl in *. induction m as [| [y n] l]; inversion_clear Hin.
  + simpl. destruct (equiv_dec x y) as [Hxy | Hxy]; trivial. elim Hxy. now destruct H0.
  + simpl. destruct (equiv_dec x y) as [Hxy | Hxy]; trivial. inversion_clear Hm. auto.
* intros elt [m Hm] x Hmem. unfold In. simpl in *. induction m as [| [y n] l]; simpl in Hmem.
  + discriminate.
  + destruct (equiv_dec x y) as [Hxy | Hxy].
    - exists n. left. now split.
    - inversion_clear Hm. apply IHl in Hmem; trivial; []. destruct Hmem as [e ?]. exists e. now right.
Qed.

Instance MapListFacts_empty key `{EqDec key} : FMapSpecs_empty (MapList _).
Proof. split. intros elt x e Hin. inversion Hin. Qed.

Instance MapListFacts_is_empty key `{EqDec key} : FMapSpecs_is_empty (MapList _).
Proof. split.
* intros elt [m Hm] Hm'. destruct m as [| [x n] l]; trivial.
  elim Hm' with x n. now left.
* intros elt [m Hm] Hm'. destruct m as [| [x n] l]; try discriminate.
  intros x n Hin. inversion Hin.
Qed.
*)

Local Transparent
  In empty is_empty mem add singleton remove
  union inter diff equal subset fold
  for_all exists_ filter partition cardinal elements choose.

Instance SetListFacts_In elt `{EqDec elt} : FSetSpecs_In (SetList _).
Proof. split. simpl. intros s x y Heq. now rewrite Heq. Qed.

Local Lemma mem_aux elt `{EqDec elt} : forall x l, list_mem x l = true <-> InA equiv x l.
Proof.
intros x l. induction l as [| e l]; simpl.
* rewrite InA_nil. intuition.
* destruct (x == e).
  + intuition.
  + rewrite IHl. split; intro Hin.
    - now right.
    - inversion_clear Hin; assumption || contradiction.
Qed.

Instance SetListFacts_mem elt `{EqDec elt} : FSetSpecs_mem (SetList _).
Proof. split.
* intros [s Hs] x Hin. simpl in *. now rewrite mem_aux.
* intros [s Hs] x Hin. simpl in *. now rewrite mem_aux in Hin.
Qed.

Instance SetLIst_Facts_empty elt `{EqDec elt} : FSetSpecs_empty (SetList _).
Proof. split. intros x Hin; simpl in *. now rewrite InA_nil in Hin. Qed.

Instance SetListFacts_is_empty elt `{EqDec elt} : FSetSpecs_is_empty (SetList _).
Proof. split.
* intros [[| e s] Hs] Hempty; simpl in *.
  + reflexivity.
  + specialize (Hempty e ltac:(now left)). tauto.
* intros [[| e s] Hs] Hempty; simpl in *.
  + intros x Hin. rewrite <- InA_nil. apply Hin.
  + discriminate.
Qed.

Local Lemma add_aux elt `{EqDec elt} : forall x e l,
  InA equiv x (list_add e l) <-> x == e \/ InA equiv x l.
Proof.
intros x e l. unfold list_add.
destruct (list_mem e l) eqn:Hmem.
+ split; intro Hin.
  - now right.
  - destruct Hin as [Hin | Hin]; trivial; [].
    rewrite mem_aux in Hmem. now rewrite Hin.
+ split; intro Hin.
  - inversion_clear Hin; tauto.
  - destruct Hin; now left + right.
Qed.

Instance SetListFacts_add elt `{EqDec elt} : FSetSpecs_add (SetList _).
Proof. split.
* intros [s Hs] x y Heq. simpl. rewrite add_aux. now left.
* intros [s Hs] x y Hin. simpl in *. rewrite add_aux. now right.
* intros s x e Hneq Hin. simpl in *. rewrite add_aux in Hin.
  destruct Hin; intuition.
Qed.

Local Lemma remove_aux elt `{EqDec elt} : forall x e l, NoDupA equiv l ->
  InA equiv x (list_remove e l) <-> InA equiv x l /\ x =/= e.
Proof.
intros x e l Hnodup. induction l as [| e' l]; simpl.
* rewrite InA_nil. tauto.
* destruct (e == e') as [Heq | Hneq]; repeat rewrite InA_cons.
  + split; intro Hin.
    - split; try (now right); [].
      intro Habs. inversion_clear Hnodup.
      rewrite Habs, Heq in *. contradiction.
    - rewrite Heq in Hin. intuition.
  + inversion_clear Hnodup. rewrite IHl; trivial; [].
    split; intro Hin.
    - destruct Hin as [Hin | [Hin ?]]; split; try tauto; [].
      rewrite Hin. intro. now apply Hneq.
    - destruct Hin as [[] ?]; now left + right.
Qed.

Instance SetListFacts_remove elt `{EqDec elt} : FSetSpecs_remove (SetList _).
Proof. split.
* intros [s Hs] x y Heq. simpl. symmetry in Heq. now rewrite remove_aux.
* intros [s Hs] x y Hxy Hin. simpl in *. now rewrite remove_aux.
* intros [s Hs] x y Hin. simpl in *. now rewrite remove_aux in Hin.
Qed.

Instance SetListFacts_singleton elt `{EqDec elt} : FSetSpecs_singleton (SetList _).
Proof. split.
* intros x y Hin. simpl in *. unfold list_add in Hin.
  destruct (list_mem x nil); now inversion_clear Hin.
* intros x y Heq. simpl. rewrite <- Heq.
  unfold list_add. simpl. now left.
Qed.

Local Lemma union_aux elt `{EqDec elt} : forall s1 s2 x,
  InA equiv x s2 -> InA equiv x (fold_left (fun s y => list_add y s) s1 s2).
Proof.
intros s1. induction s1 as [| e1 s1]; simpl; intros s2 x Hin.
+ assumption.
+ apply IHs1; eauto using t_add_lemma; [].
  unfold list_add. now destruct (list_mem e1 s2); try right.
Qed.

Instance SetListFacts_union elt `{EqDec elt} : FSetSpecs_union (SetList _).
Proof. split.
* intros [s1 Hs1] [s2 Hs2]. simpl.
  unfold list_union, list_fold, flip.
  revert s2 Hs2. induction s1 as [| e1 s1]; simpl; intros s2 Hs2 x Hin.
  + now right.
  + inversion_clear Hs1.
    apply IHs1 in Hin; auto using t_add_lemma; [].
    destruct Hin as [Hin | Hin].
    - now left; right.
    - unfold list_add in Hin. destruct (list_mem e1 s2); try (now right); [].
      inversion_clear Hin; (now do 2 left) || now right.
* intros [s1 Hs1] [s2 Hs2] x Hin. simpl in *.
  unfold list_union, list_fold, flip.
  revert s2 Hs2. induction s1 as [| e1 s1]; simpl; intros s2 Hs2.
  + now rewrite InA_nil in Hin.
  + inversion_clear Hs1.
    inversion_clear Hin.
    - match goal with H : _ == _ |- _ => rewrite H end. apply union_aux.
      unfold list_add. destruct (list_mem e1 s2) eqn:Hmem; try (now left); [].
      change (e1 ∈ (exist _ s2 Hs2))%set. now apply mem_2.
    - apply IHs1; auto using t_add_lemma.
* intros [s1 Hs1] [s2 Hs2]. simpl in *.
  unfold list_union, list_fold, flip.
  apply union_aux.
Qed.

Lemma inter_aux elt `{EqDec elt} : forall (f : elt -> bool), Proper (equiv ==> equiv) f ->
  forall l1 l x,
  InA equiv x (fold_left (fun s y => if f y then list_add y s else s) l1 l)
  <-> InA equiv x l1 /\ f x = true \/ InA equiv x l.
Proof.
intros f Hf l1. induction l1 as [| e1 l1]; simpl; intros l x.
* rewrite InA_nil. tauto.
* rewrite IHl1.
  split; intros [[Hin Hfx] | Hin].
  + left. split; trivial; []. now right.
  + destruct (f e1) eqn:Hfe; try tauto; [].
    rewrite add_aux in Hin. destruct Hin as [Hin | ?]; try tauto; [].
    rewrite Hin. left. now split; try left.
  + inversion_clear Hin.
    - Preliminary.revert_one equiv. intro Heq. rewrite Heq in *.
      rewrite Hfx. right. rewrite add_aux. now left.
    - tauto.
  + right. destruct (f e1); trivial; []. rewrite add_aux. now right.
Qed.

Local Lemma mem_compat elt `{EqDec elt} :
  forall l, Proper (equiv ==> equiv) (fun y => list_mem y l).
Proof.
intros l x y Heq. induction l as [| e l]; simpl; trivial; [].
destruct (x == e), (y == e).
- reflexivity.
- rewrite Heq in *. contradiction.
- rewrite Heq in *. contradiction.
- apply IHl.
Qed.

Instance SetListFacts_inter elt `{EqDec elt} : FSetSpecs_inter (SetList _).
Proof. split.
* intros [s1 Hs1] [s2 Hs2] x. simpl.
  unfold list_inter, list_fold, flip. rewrite inter_aux.
  + rewrite InA_nil. tauto.
  + apply mem_compat.
* intros [s1 Hs1] [s2 Hs2] x. simpl.
  unfold list_inter, list_fold, flip. rewrite inter_aux.
  + rewrite InA_nil, mem_aux. tauto.
  + apply mem_compat.
* intros [s1 Hs1] [s2 Hs2] x. simpl.
  unfold list_inter, list_fold, flip. rewrite inter_aux.
  + rewrite InA_nil, mem_aux. tauto.
  + apply mem_compat.
Qed.

Lemma diff_aux elt `{EqDec elt} : forall l1 l2 x, NoDupA equiv l1 ->
  InA equiv x (fold_left (fun s y => list_remove y s) l2 l1)
  <-> InA equiv x l1 /\ ~InA equiv x l2.
Proof.
intros l1 l2 x. revert l1. induction l2 as [| e2 l2]; simpl; intros l1 Hnodup.
* rewrite InA_nil. tauto.
* rewrite IHl2.
  + rewrite remove_aux, InA_cons; trivial; []. intuition.
  + now apply t_remove_lemma.
Qed.

Instance SetListFacts_diff elt `{EqDec elt} : FSetSpecs_diff (SetList _).
Proof.
split;
intros [s1 Hs1] [s2 Hs2] x; simpl;
unfold list_diff, list_fold, flip; now rewrite diff_aux.
Qed.

Instance SetListFacts_subset elt `{EqDec elt} : FSetSpecs_subset (SetList _).
Proof. split.
* intros s1 s2 Hle. simpl. unfold list_subset.
  change (is_empty (diff s1 s2) = true).
  apply is_empty_1. intros x Hin.
  assert (Hin1 := diff_1 Hin). assert (Hin2 := diff_2 Hin).
  apply Hin2. apply Hle. apply Hin1.
* intros s1 s2 Hle. simpl in Hle. unfold list_subset in Hle.
  change (is_empty (diff s1 s2) = true) in Hle.
  apply is_empty_2 in Hle. intros x Hin. specialize (Hle x).
  destruct (mem x s2) eqn:Hmem.
  + now apply mem_2.
  + elim Hle. apply diff_3; trivial; [].
    intro Habs. apply mem_1 in Habs. congruence.
Qed.

Instance SetListFacts_equal elt `{EqDec elt} : FSetSpecs_equal (SetList _).
Proof. split.
* intros s1 s2 Heq. simpl.
  change (subset s1 s2 && subset s2 s1 = true).
  rewrite andb_true_iff. split.
  + apply subset_1. intros x Hin. rewrite <- (Heq x). apply Hin.
  + apply subset_1. intros x Hin. rewrite (Heq x). apply Hin.
* intros s1 s2 Heq x. simpl in Heq.
  change (subset s1 s2 && subset s2 s1 = true) in Heq.
  rewrite andb_true_iff in Heq. destruct Heq as [Hle1 Hle2].
  split; now apply subset_2.
Qed.

Instance SetListFacts_cardinal elt `{EqDec elt} : FSetSpecs_cardinal (SetList _).
Proof. split. reflexivity. Qed.

Instance SetListFacts_fold elt `{EqDec elt} : FSetSpecs_fold (SetList _).
Proof. split. reflexivity. Qed.

Instance SetListFacts_filter elt `{EqDec elt} : FSetSpecs_filter (SetList _).
Proof. split.
* intros [s Hs] x f Hf Hin.
  induction s as [| e s]; simpl in *.
  + assumption.
  + inversion_clear Hs.
    destruct (f e).
    - inversion_clear Hin; now constructor; auto.
    - right. auto.
* intros [s Hs] x f Hf Hin.
  induction s as [| e s]; simpl in *.
  + rewrite InA_nil in *. tauto.
  + inversion_clear Hs.
    destruct (f e) eqn:Hfe.
    - inversion_clear Hin; auto; [].
      Preliminary.revert_one equiv. intro Heq. now rewrite Heq.
    - auto.
* intros [s Hs] x f Hf Hin Hfx.
  induction s as [| e s]; simpl in *.
  + assumption.
  + inversion_clear Hs.
    destruct (f e) eqn:Hfe.
    - inversion_clear Hin; auto.
    - inversion_clear Hin; auto; [].
      cut (true = false); try discriminate; [].
      rewrite <- Hfe, <- Hfx. now apply Hf.
Qed.

Instance SetListFacts_for_all elt `{EqDec elt} : FSetSpecs_for_all (SetList _).
Proof. split.
* intros [s Hs] f Hf Hall. unfold For_all in Hall. simpl in *.
  rewrite forallb_forall. intros x Hin. apply Hall. apply In_InA; Preliminary.autoclass.
* intros [s Hs] f Hf Hall x Hin. simpl in *.
  rewrite forallb_forall in Hall.
  rewrite InA_alt in Hin. destruct Hin as [y [Heq Hin]].
  rewrite Heq. auto.
Qed.

Instance SetListFacts_exists elt `{EqDec elt} : FSetSpecs_exists (SetList _).
Proof. split.
* intros [s Hs] f Hf [x [Hin Hfx]]. simpl in *. rewrite existsb_exists.
  rewrite InA_alt in Hin. destruct Hin as [y [Heq Hin]].
  rewrite Heq in Hfx. eauto.
* intros [s Hs] f Hf Hex. simpl in *. rewrite existsb_exists in Hex.
  destruct Hex as [x [Hin Hfx]]. exists x. simpl. split; trivial; []. apply In_InA; Preliminary.autoclass.
Qed.

Instance SetListFacts_partition elt `{EqDec elt} : FSetSpecs_partition (SetList _).
Proof. split.
* intros [s Hs] f Hf x. simpl. induction s as [| e s]; simpl.
  + reflexivity.
  + destruct (list_partition f s) as [s1 s2]; simpl in *.
    destruct (f e) eqn:Hfe; simpl.
    - inversion_clear Hs. specialize (IHs ltac:(assumption)).
      split; intro Hin; inversion_clear Hin; auto;
      (progress rewrite IHs in * || rewrite <- IHs in *); auto.
    - apply IHs. now inversion_clear Hs.
* intros [s Hs] f Hf x. simpl. induction s as [| e s]; simpl.
  + reflexivity.
  + destruct (list_partition f s) as [s1 s2]; simpl in *.
    destruct (f e) eqn:Hfe; simpl.
    - apply IHs. now inversion_clear Hs.
    - inversion_clear Hs. specialize (IHs ltac:(assumption)).
      split; intro Hin; inversion_clear Hin; auto;
      (progress rewrite IHs in * || rewrite <- IHs in *); auto.
Qed.

Instance SetListFacts_elements elt `{EqDec elt} : FSetSpecs_elements (SetList _).
Proof. split.
* simpl. auto.
* simpl. auto.
* intros [s Hs]. simpl. assumption.
Qed.

Instance SetListFacts_choose elt `{EqDec elt} : FSetSpecs_choose (SetList _).
Proof. split.
* intros [[| e s] Hs] x Hin; simpl in *.
  + discriminate.
  + inversion_clear Hin. now left.
* intros [[| e s] Hs] x Hin; simpl in *.
  + rewrite InA_nil. tauto.
  + discriminate.
Qed.


(** The full set of specifications. *)
Instance SetListFacts elt `{EqDec elt} : FSetSpecs (SetList _).
Proof. split; auto with typeclass_instances. Qed.
