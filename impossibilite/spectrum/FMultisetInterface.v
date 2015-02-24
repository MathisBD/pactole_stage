Require Export RelationPairs.
Require Import MSetInterface.
Require Export Equalities.
Require Export SetoidPermutation.
Require Import Preliminary.

(* based on MSets *)

Module Type FMOps (E : DecidableType).
  
  Definition elt := E.t.
  Parameter t : Type.
  
   Parameter empty : t.
   (** The empty multiset. *)

  Parameter is_empty : t -> bool.
  (** Test whether a multiset is empty or not. *)

  Parameter multiplicity : elt -> t -> nat.
  (** [multiplicity x s] gives the number of occurences of [x] inside [s]. *)

  Parameter add : elt -> nat -> t -> t.
  (** [add x n s] returns a multiset containing all elements of s, plus [n] copies of [x]. *)
  (* If [n] is [0], should we return the original multiset? *)

  Parameter singleton : elt -> nat -> t.
  (** [singleton x n] returns the multiset containing only [n] copies of [x]. *)

  Parameter remove : elt -> nat -> t -> t.
  (** [remove x n s] returns a multiset containing all elements of s, minus [n] copies of [x].
      If the multiplicity of [x] in [s] is less than [n], we remove all the copies of [x] from [s]. *)

  Parameter union : t -> t -> t.
  (** Multiset union. *)

  Parameter inter : t -> t -> t.
  (** Multiset intersection. *)

  Parameter diff : t -> t -> t.
  (** Multiset difference. *)

  Parameter equal : t -> t -> bool.
  (** [equal s1 s2] tests whether the multisets [s1] and [s2] are equal,
      that is, contain equal elements with equal multiplicities. *)

  Parameter subset : t -> t -> bool.
  (** [subset s1 s2] tests whether the multiset [s1] is a subset of the multiset [s2]. *)
(*
  Parameter fold : forall {A : Type}, (elt -> A -> A) -> t -> A -> A.
  (** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)], where [x1 ... xN] are the elements of [s]
      with multiplicities. The order in which elements of [s] are presented to [f] is unspecified. *)
*)
  Parameter fold : forall {A : Type}, (elt -> nat -> A -> A) -> t -> A -> A.
  (** [fold f s a] computes [(f xN nN ... (f x2 n2 (f x1 n1 a))...)], where [x1 ... xN]
      are the distinct elements of [s] with respective positive multiplicities [n1 ... nN].
      The order in which the elements of [s] are presented to [f] is unspecified. *)

  Parameter for_all : (elt -> nat -> bool) -> t -> bool.
  (** [for_all p s] checks if all elements of the multiset (with their multiplicities) satisfy the predicate [p]. *)

  Parameter exists_ : (elt -> nat -> bool) -> t -> bool.
  (** [exists p s] checks if at least one element of the multiset (with its multiplicity) satisfies the predicate p. *)

  Parameter filter : (elt -> nat -> bool) -> t -> t.
  (** [filter p s] returns the multiset of all elements in [s] that satisfy predicate [p]. *)

  Parameter partition : (elt -> nat -> bool) -> t -> t * t.
  (** [partition p s] returns a pair of multisets [(s1, s2)], where [s1] is the multiset of all the elements of [s]
      that satisfy the predicate [p], and [s2] is the multiset of all the elements of [s] that do not satisfy [p]. *)

  Parameter cardinal : t -> nat.
  (** Return the number of elements of a multiset, with multiplicity. *)

  Parameter size : t -> nat.
  (** Return the size of the support of the multipset,
      that is, the number of different elements without multiplicity. *)

  Parameter elements : t -> list (elt * nat).
  (** Return the list of all elements with multiplicity of the given multiset, in any order. *)

  Parameter support : t -> list elt.
  (** Return the list of all different elements without multiplicity of the given multiset, in any order. *)

  Parameter choose : t -> option elt.
  (** Return one element of the given multiset, or [None] if the multiset is empty.
      Which element is chosen is unspecified. Equal multisets could return different elements. *)
End FMOps.


Module Type FMultisetsOn (E : DecidableType).
  (** First, we ask for all the functions *)
  Include FMOps E.

  Instance Eeq_equiv : Equivalence E.eq := E.eq_equiv.
  
  (** ** Logical predicates *)

  Definition In := fun x s => multiplicity x s > 0.

  Definition eq s s' := forall x, multiplicity x s = multiplicity x s'.
  Definition Subset s s' := forall x, multiplicity x s <= multiplicity x s'.
  Definition Empty s := forall x : elt, multiplicity x s = 0.
  Definition For_all (P : elt -> nat -> Prop) s := forall x, In x s -> P x (multiplicity x s).
  Definition Exists (P : elt -> nat -> Prop) s := exists x, In x s /\ P x (multiplicity x s).

  Global Notation "s  [=]  t" := (eq s t) (at level 70, no associativity).
  Global Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).
  
  (** ** Specifications of set operators *)

  Notation compatb := (Proper (E.eq ==> Logic.eq ==> Logic.eq)) (only parsing).
  Declare Instance multiplicity_compat : Proper (E.eq ==> eq ==> Logic.eq) multiplicity.
  Declare Instance fold_compat A (eqA : A -> A -> Prop) `{Equivalence A eqA} :
  forall f, Proper (E.eq ==> Logic.eq ==> eqA ==> eqA) f ->
  (forall x y n m a, eqA (f y m (f x n a)) (f x n (f y m a))) ->
  Proper (eq ==> eqA ==> eqA) (fold f).

  Parameter mutiplicity_spec : forall x s, multiplicity x s > 0 <-> In x s.
  Parameter equal_spec : forall s s', equal s s' = true <-> s [=] s'.
  Parameter subset_spec : forall s s', subset s s' = true <-> s [<=] s'.
  Parameter empty_spec : Empty empty.
  Parameter is_empty_spec : forall s, is_empty s = true <-> Empty s.
  Parameter add_spec : forall x n s, multiplicity x (add x n s) = multiplicity x s + n.
  Parameter add_spec' : forall x y n s, ~E.eq x y -> multiplicity y (add x n s) = multiplicity y s.
  Parameter remove_spec : forall x n s, multiplicity x (remove x n s) = multiplicity x s - n.
  Parameter remove_spec' : forall x y n s, ~E.eq x y -> multiplicity y (remove x n s) = multiplicity y s.
  Parameter singleton_spec : forall x y n, multiplicity y (singleton x n) = if E.eq_dec y x then n else 0.
  Parameter union_spec : forall x s s', multiplicity x (union s s') = multiplicity x s + multiplicity x s'.
  Parameter inter_spec : forall x s s', multiplicity x (inter s s') = min (multiplicity x s) (multiplicity x s').
  Parameter diff_spec : forall x s s', multiplicity x (diff s s') = multiplicity x s - multiplicity x s'.
  Parameter fold_spec : forall (A : Type) s (i : A) (f : elt -> nat -> A -> A),
    fold f s i = fold_left (fun acc xn => f (fst xn) (snd xn) acc) (elements s) i.
(*  Parameter fold_spec : forall (A : Type) s (i : A) (f : elt -> nat -> A -> A),
    fold f s i = fold_left (fun acc x => f x (multiplicity x s) acc) (support s) i.*)
  Parameter cardinal_spec : forall s, cardinal s = fold (fun x n acc => n + acc) s 0.
  Parameter size_spec : forall s, size s = length (support s).
  Parameter filter_spec : forall f x s, compatb f ->
    multiplicity x (filter f s) = if f x (multiplicity x s) then multiplicity x s else 0.
  Parameter for_all_spec : forall f s, compatb f ->
    (for_all f s = true <-> For_all (fun x n => f x n = true) s).
  Parameter exists_spec : forall f s, compatb f ->
    (exists_ f s = true <-> Exists (fun x n => f x n = true) s).
  Parameter partition_spec_fst : forall f s, compatb f ->
    fst (partition f s) [=] filter f s.
  Parameter partition_spec_snd : forall f s, compatb f ->
    snd (partition f s) [=] filter (fun x n => negb (f x n)) s.

  Definition eq_pair := RelProd E.eq (@Logic.eq nat).
  Definition eq_key := RelCompFun E.eq (@fst E.t nat).
  
  Instance eq_pair_equiv : Equivalence eq_pair.
  Proof. split.
  intros [x n]. now split; hnf.
  intros [x n] [y m] [H1 H2]; split; hnf in *; now auto.
  intros ? ? ? [? ?] [? ?]. split. hnf in *. now transitivity (fst y). now transitivity (snd y).
  Qed.
  
  Parameter elements_spec : forall xn s,
    InA eq_pair xn (elements s) <-> multiplicity (fst xn) s = snd xn /\ snd xn > 0.
    (*InA eq_pair (x, n) (elements s) <-> multiplicity x s = n /\ multiplicity x s > 0.*)
  Parameter elements_NoDupA : forall s, NoDupA eq_key (elements s).
  Parameter support_spec : forall x s, InA E.eq x (support s) <-> In x s.
  Parameter support_NoDupA : forall s, NoDupA E.eq (support s).
  Parameter support_elements : forall x s, InA E.eq x (support s) <-> InA eq_pair (x, multiplicity x s) (elements s).

  Parameter choose_spec1 : forall x s, choose s = Some x -> In x s.
  Parameter choose_spec2 : forall s, choose s = None -> Empty s.

End FMultisetsOn.
