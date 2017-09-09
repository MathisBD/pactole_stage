(******************************************)
(*   Finite multiset library              *)
(*   Developped for the PACTOLE project   *)
(*   L. Rieg                              *)
(*                                        *)
(*   This file is distributed under       *)
(*   the terms of the CeCILL-C licence    *)
(*                                        *)
(******************************************)


Require Import RelationPairs.
Require Import MSetInterface.
Require Import SetoidDec.
Require Import SetoidPermutation.
Require Import Pactole.Util.MMultiset.Preliminary.

(* based on MSets *)

(** **  Operations on multisets  **)

Class FMOps elt `(EqDec elt) := {

  multiset : Type;
  (** The types of elements and multisets. *)

  empty : multiset;
  (** The empty multiset. *)

  is_empty : multiset -> bool;
  (** Test whether a multiset is empty or not. *)

  multiplicity : elt -> multiset -> nat;
  (** [multiplicity x s] gives the number of occurences of [x] inside [s]. *)

  add : elt -> nat -> multiset -> multiset;
  (** [add x n s] returns a multiset containing all elements of s, plus [n] copies of [x]. *)
  (* If [n] is [0], should we return /exactly/ the original multiset? *)

  singleton : elt -> nat -> multiset;
  (** [singleton x n] returns the multiset containing only [n] copies of [x].
      It is [empty] if [n] is [0]. *)

  remove : elt -> nat -> multiset -> multiset;
  (** [remove x n s] returns a multiset containing all elements of s, minus [n] copies of [x].
      If the multiplicity of [x] in [s] is less than [n], we remove all the copies of [x] from [s]. *)

  union : multiset -> multiset -> multiset;
  (** Multiset union. *)

  inter : multiset -> multiset -> multiset;
  (** Multiset intersection. *)

  diff : multiset -> multiset -> multiset;
  (** Multiset difference. *)

  lub : multiset -> multiset -> multiset;
  (** Multiset lowest upper bound: the multiplicity of any [x] in [sup s1 s2] is the maximum of the multiplicities
  of [x] in [s1] and [s2]. *)

  equal : multiset -> multiset -> bool;
  (** [equal s1 s2] tests whether the multisets [s1] and [s2] are equal,
      that is, contain equal elements with equal multiplicities. *)

  subset : multiset -> multiset -> bool;
  (** [subset s1 s2] tests whether the multiset [s1] is a subset of the multiset [s2]. *)

  fold : forall {A : Type}, (elt -> nat -> A -> A) -> multiset -> A -> A;
  (** [fold f s a] computes [(f xN nN ... (f x2 n2 (f x1 n1 a))...)], where [x1 ... xN]
      are the distinct elements of [s] with respective positive multiplicities [n1 ... nN].
      The order in which the elements of [s] are presented to [f] is unspecified. *)

  for_all : (elt -> nat -> bool) -> multiset -> bool;
  (** [for_all p s] checks if all elements of the multiset (with their multiplicities) satisfy the predicate [p]. *)

  exists_ : (elt -> nat -> bool) -> multiset -> bool;
  (** [exists_ p s] checks if at least one element of the multiset (with its multiplicity)
      satisfies the predicate [p]. *)

  nfilter : (elt -> nat -> bool) -> multiset -> multiset;
  (** [nfilter p s] returns the multiset of all elements with multiplicity in [s] that satisfy the predicate [p]. *)

  filter : (elt -> bool) -> multiset -> multiset;
  (** [filter p s] returns the multiset of all elements in [s] that satisfy the predicate [p],
      keeping their multiplicity. *)

  npartition : (elt -> nat -> bool) -> multiset -> multiset * multiset;
  (** [partition p s] returns a pair of multisets [(s1, s2)],
      where [s1] is the multiset of all the elements of [s] with multiplicity that satisfy the predicate [p],
      and [s2] is the multiset of all the elements of [s] with multiplicity that do not satisfy [p]. *)

  partition : (elt -> bool) -> multiset -> multiset * multiset;
  (** [partition p s] returns a pair of multisets [(s1, s2)],
      where [s1] is the multiset of all the elements of [s] that satisfy the predicate [p],
      and [s2] is the multiset of all the elements of [s] that do not satisfy [p]. *)

  elements : multiset -> list (elt * nat);
  (** Return the list of all elements with multiplicity of the given multiset, in any order. *)

  support : multiset -> list elt;
  (** Return the list of all different elements without multiplicity of the given multiset, in any order. *)

  cardinal : multiset -> nat;
  (** Return the number of elements of a multiset, with multiplicity. *)

  size : multiset -> nat;
  (** Return the size of the support of a multiset,
      that is, the number of different elements (without multiplicity). *)

  choose : multiset -> option elt
  (** Return one element of the given multiset, or [None] if the multiset is empty.
      Which element is chosen is unspecified: equal multisets could return different elements. *)
}.
Arguments multiset elt {_} {_} {_}.
Arguments multiplicity {elt} {_} {_} {_} x m : simpl never.
Arguments fold {elt} {_} {_} {_} {A} f m i : simpl never.

Global Instance MMultiset_Setoid elt `{FMOps elt} : Setoid (multiset elt) := {
  equiv := fun s s' => forall x, multiplicity x s = multiplicity x s' }.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Notation compatb := (Proper (equiv ==> Logic.eq ==> @Logic.eq bool)) (only parsing).
Global Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").

Definition eq_pair {elt : Type} `{FMOps elt} := RelProd (@equiv elt _) (@Logic.eq nat).
Definition eq_elt {elt : Type} `{FMOps elt} := RelCompFun equiv (@fst elt nat).

(** ** Logical predicates *)
Definition In {elt : Type} `{FMOps elt} := fun x s => multiplicity x s > 0.
Definition Subset {elt : Type} `{FMOps elt} s s' := forall x, multiplicity x s <= multiplicity x s'.
Definition For_all {elt : Type} `{FMOps elt} (P : elt -> nat -> Prop) s :=
  forall x, In x s -> P x (multiplicity x s).
Definition Exists {elt : Type} `{FMOps elt} (P : elt -> nat -> Prop) s :=
  exists x, In x s /\ P x (multiplicity x s).

(** **  Specifications of multisets  **)

(** Specification of [multiplicity]. **)
Class MultiplicitySpec elt `(FMOps elt) := {
  multiplicity_compat : Proper (equiv ==> equiv ==> Logic.eq) multiplicity}.
Global Existing Instance multiplicity_compat.

(** Specification of [empty]. **)
Class EmptySpec elt `(FMOps elt) := {
  empty_spec : forall x, empty[x] = 0}.

(** Specification of [singleton]. **)
Class SingletonSpec elt `(FMOps elt) := {
  singleton_same : forall x n, (singleton x n)[x] = n;
  singleton_other : forall x y n, y =/= x -> (singleton x n)[y] = 0}.

(** Specification of [add]. **)
Class AddSpec elt `(FMOps elt) := {
  add_same : forall x n s, (add x n s)[x] = s[x] + n;
  add_other : forall x y n s, y =/= x -> (add x n s)[y] = s[y]}.

(** Specification of [remove]. **)
Class RemoveSpec elt `(FMOps elt) := {
  remove_same : forall x n s, (remove x n s)[x] = s[x] - n;
  remove_other : forall x y n s, y =/= x -> (remove x n s)[y] = s[y]}.

(** Specification of binary operations: [union], [inter], [diff] ans [lub]. **)
Class BinarySpec elt `(FMOps elt) := {
  union_spec : forall x s s', (union s s')[x] = s[x] + s'[x];
  inter_spec : forall x s s', (inter s s')[x] = min s[x] s'[x];
  diff_spec : forall x s s', (diff s s')[x] = s[x] - s'[x];
  lub_spec : forall x s s', (lub s s')[x] = max s[x] s'[x]}.

(** Specification of [fold]. **)
Class FoldSpec elt `(FMOps elt) := {
  fold_spec : forall (A : Type) s (i : A) (f : elt -> nat -> A -> A),
    fold f s i = fold_left (fun acc xn => f (fst xn) (snd xn) acc) (elements s) i;
  fold_compat A (eqA : A -> A -> Prop) `{Equivalence A eqA} :
    forall f, Proper (equiv ==> Logic.eq ==> eqA ==> eqA) f -> transpose2 eqA f ->
    Proper (equiv ==> eqA ==> eqA) (fold f)}.
Global Existing Instance fold_compat.

(** Specification of [equal], [subset] and [is_empty]. **)
Class TestSpec elt `(FMOps elt) := {
  equal_spec : forall s s', equal s s' = true <-> s == s';
  subset_spec : forall s s', subset s s' = true <-> Subset s s';
  is_empty_spec : forall s, is_empty s = true <-> s == empty}.

(** Specification of [elements]. **)
Class ElementsSpec elt `(FMOps elt) := {
  elements_spec : forall x n s, InA eq_pair (x, n) (elements s) <-> s[x] = n /\ n > 0;
  elements_NoDupA : forall s, NoDupA eq_elt (elements s)}.

(** Specification of [support]. **)
Class SupportSpec elt `(FMOps elt) := {
  support_spec : forall x s, InA equiv x (support s) <-> In x s;
  support_NoDupA : forall s, NoDupA equiv (support s)}.

(** Specification of [choose]. **)
Class ChooseSpec elt `(FMOps elt) := {
  choose_Some : forall x s, choose s = Some x -> In x s;
  choose_None : forall s, choose s = None <-> s == empty}.

(** Specification of filtering functions. **)
Class FilterSpec elt `(FMOps elt) := {
  nfilter_spec : forall f x s, compatb f -> (nfilter f s)[x] = if f x s[x] then s[x] else 0;
  filter_spec : forall f x s, Proper (equiv ==> Logic.eq) f -> (filter f s)[x] = if f x then s[x] else 0}.

(** Specification of [partition]. **)
Class PartitionSpec elt `(FMOps elt) := {
  partition_spec_fst : forall f s, Proper (equiv ==> Logic.eq) f -> fst (partition f s) == filter f s;
  partition_spec_snd : forall f s, Proper (equiv ==> Logic.eq) f ->
    snd (partition f s) == filter (fun x => negb (f x)) s}.

(** Specification of [npartition]. **)
Class NpartitionSpec elt `(FMOps elt) := {
  npartition_spec_fst : forall f s, compatb f -> fst (npartition f s) == nfilter f s;
  npartition_spec_snd : forall f s, compatb f ->
    snd (npartition f s) == nfilter (fun x n => negb (f x n)) s}.

(** Specification of quantifiers. **)
Class QuantifierSpec elt `(FMOps elt) := {
  for_all_spec : forall f s, compatb f -> (for_all f s = true <-> For_all (fun x n => f x n = true) s);
  exists_spec : forall f s, compatb f -> (exists_ f s = true <-> Exists (fun x n => f x n = true) s)}.

(** Specification of size measures. **)
Class SizeSpec elt `(FMOps elt) := {
  cardinal_spec : forall s, cardinal s = fold (fun x n acc => n + acc) s 0;
  size_spec : forall s, size s = length (support s)}.

(** ***  Full specification  **)

Global Class FMultisetsOn elt `(Ops : FMOps elt) := {
  FullMultiplicitySpec :> MultiplicitySpec elt Ops;
  FullEmptySpec :> EmptySpec elt Ops;
  FullSingletonSpec :> SingletonSpec elt Ops;
  FullAddSpec :> AddSpec elt Ops;
  FullRemoveSpec :> RemoveSpec elt Ops;
  FullBinarySpec :> BinarySpec elt Ops;
  FullFoldSpec :> FoldSpec elt Ops;
  FullTestSpec: > TestSpec elt Ops;
  FullElementsSpec :> ElementsSpec elt Ops;
  FullSupportSpec :> SupportSpec elt Ops;
  FullChooseSpec :> ChooseSpec elt Ops;
  FullPartitionSpec :> PartitionSpec elt Ops;
  FullNpartitionSpec :> NpartitionSpec elt Ops;
  FullQuantifierSpec :> QuantifierSpec elt Ops;
  FullSizeSpec :> SizeSpec elt Ops;
  FullFilterSpec :> FilterSpec elt Ops}.


(* Global Notation "s  [=]  t" := (eq s t) (at level 70, no associativity, only parsing). *)
(* Global Notation "m1  ≡  m2" := (eq m1 m2) (at level 70). *)
Global Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity, only parsing).
Global Notation "m1  ⊆  m2" := (Subset m1 m2) (at level 70).


Class FMultisetOrd elt lt `(FMultisetsOn elt) `(@StrictOrder elt lt) := {

  (** Orders on elements *)
  lt_elt (xn yp : elt * nat) := lt (fst xn) (fst yp);

  elements_Sorted : forall s, Sorted lt_elt (elements s);

(* Multiset ordering is left as future works

  Include HasLt <+ IsEq <+ IsStrOrder.

  Definition cmp := Nat.eqb.

  Parameter compare : t -> t -> comparison.

  Parameter compare_spec : forall m1 m2, CompSpec eq lt m1 m2 (compare m1 m2).
*)
}.
