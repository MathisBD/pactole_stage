
(* Adpated from Stephan Lescuyer's Containers library to avoid ordering of elts. *)
Require Import SetoidList.
Require Import SetoidDec.
(* Require Import Morphisms. *)

Generalizable All Variables.

(** This file defines the interface of typeclass-based
   finite sets. *)
(** * Pointwise-equality

   We define pointwise equality for any structure with a membership
   predicate [In : elt -> container -> Prop], and prove it is an
   equivalence relation. This is required for the sets' interface.
   *)
Section Equal.
  Variable container : Type.
  Variable elt : Type.
  Variable In : elt -> container -> Prop.
  Definition Equal_pw (s s' : container) : Prop :=
    forall a : elt, In a s <-> In a s'.
  Program Definition Equal_pw_Equivalence : Equivalence Equal_pw :=
    Build_Equivalence _ _ _ _.
  Next Obligation.
    constructor; auto.
  Qed.
  Next Obligation.
    constructor; firstorder.
  Qed.
  Next Obligation.
    constructor; firstorder eauto.
  Qed.
End Equal.
Hint Unfold Equal_pw.


(** * [FSet] : the interface of sets

   We define the class [FSet] of structures that implement finite
   sets. An instance of [FSet] for an ordered type [A] contains the
   type [set A] of sets of elements of type [A]. It also contains all
   the operations that these sets support : insertion, membership,
   etc. The specifications of these operations are in a different
   class (see below).

   The operations provided are the same as in the standard [FSets]
   library.

   The last member of the class states that for any ordered type [A],
   [set A] is itself an ordered type for pointwise equality. This makes
   building sets of sets possible.
   *)
Class FSet `{EqDec elt} := {
  (** The container type *)
  set : Type;

  (** The specification of all set operations is done
     with respect to the sole membership predicate. *)
  In : elt -> set -> Prop;

  (** Set Operations  *)
  empty : set;
  is_empty : set -> bool;
  mem : elt -> set -> bool;

  add : elt -> set -> set;
  singleton : elt -> set;
  remove : elt -> set -> set;
  union : set -> set -> set;
  inter : set -> set -> set;
  diff : set -> set -> set;

  equal : set -> set -> bool;
  subset : set -> set -> bool;

  fold : forall {B : Type}, (elt -> B -> B) -> set -> B -> B;
  for_all : (elt -> bool) -> set -> bool;
  exists_ : (elt -> bool) -> set -> bool;
  filter : (elt -> bool) -> set -> set;
  partition : (elt -> bool) -> set -> set * set;

  cardinal : set -> nat;
  elements : set -> list elt;
  choose :  set -> option elt;
  (* min_elt :  set -> option elt; *)
  (* max_elt :  set -> option elt; *)

  (** Sets should be ordered types as well, in order to be able
     to use sets in containers.
     See wget http://www.lix.polytechnique.fr/coq/pylons/contribs/files/Containers/v8.4/Containers.tar.gz file OrderedType.v
   *)
  (*  FSet_OrderedType :>
    SpecificOrderedType _ (Equal_pw set elt In) *)
}.

Arguments set elt%type_scope {_} {_} {FSet}.

(** Set notations (see below) are interpreted in scope [set_scope],
   delimited with elt [scope]. We bind it to the type [set] and to
   other operations defined in the interface. *)
Delimit Scope set_scope with set.
Bind Scope set_scope with set.
Global Arguments In  {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments is_empty {_%type_scope} {_} {_} {_} _%set_scope.
Global Arguments mem {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments add {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments remove {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments union {_%type_scope} {_} {_} {_} _%set_scope _%set_scope.
Global Arguments inter {_%type_scope} {_} {_} {_} _%set_scope _%set_scope.
Global Arguments diff {_%type_scope} {_} {_} {_} _%set_scope _%set_scope.
Global Arguments equal {_%type_scope} {_} {_} {_} _%set_scope _%set_scope.
Global Arguments subset {_%type_scope} {_} {_} {_} _%set_scope _%set_scope.
Global Arguments fold {_%type_scope} {_} {_} {_} {_} _ _%set_scope _.
Global Arguments for_all {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments exists_ {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments filter {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments partition {_%type_scope} {_} {_} {_} _ _%set_scope.
Global Arguments cardinal {_%type_scope} {_} {_} {_} _%set_scope.
Global Arguments elements {_%type_scope} {_} {_} {_} _%set_scope.
Global Arguments choose {_%type_scope} {_} {_} {_} _%set_scope.
(* Global Arguments min_elt {_%type_scope} {_} {_} {_} _%set_scope. *)
(* Global Arguments max_elt {_%type_scope} {_} {_} {_} _%set_scope. *)

(** All projections should be made opaque for tactics using [delta]-conversion,
   otherwise the underlying instances may appear during proofs, which then
   causes several problems (notations not being used, unification failures...).
   This doesnt stop computation with [compute] or [vm_compute] though, which is
   exactly what we want.
*)
Global Opaque
  set In empty is_empty mem add singleton remove
  union inter diff equal subset fold
  for_all exists_ filter partition cardinal elements choose
  (*FSet_OrderedType*).


(** There follow definitions of predicates about sets expressable
   in terms of [In], and which are not provided by the [FSet] class. *)
Global Instance Set_Setoid elt `{FSet elt} : Setoid (set elt) := {
  equiv := fun s s' => forall x, In x s <-> In x s' }.
Proof. split.
+ repeat intro. reflexivity.
+ repeat intro. now symmetry.
+ repeat intro. etransitivity; eauto.
Defined.

Definition Subset `{FSet elt} s s' :=
  forall a : elt, In a s -> In a s'.
Definition Empty `{FSet elt} s :=
  forall a : elt, ~ In a s.
Definition For_all `{FSet elt} (P : elt -> Prop) s :=
  forall x, In x s -> P x.
Definition Exists `{FSet elt} (P : elt -> Prop) s :=
  exists x, In x s /\ P x.

(** We also define a couple of notations for set-related operations.
   These notations can be used to avoid ambiguity when dealing
   simultaneously with operations on lists and sets that have
   similar names ([mem], [In], ...). *)
Global Notation "s [=] t" := (s == t) (at level 70, no associativity) : set_scope.
Global Notation "s [<=] t" := (Subset s t) (at level 70, no associativity) : set_scope.
Global Notation "v '\In' S" := (In v S) (at level 70, no associativity, only parsing) : set_scope.
Global Notation "v '∈' S" := (In v S) (at level 70, no associativity) : set_scope.
Global Notation "'{}'" := (empty) (at level 0, no associativity) : set_scope.
Global Notation "'{' v '}'" := (singleton v) : set_scope.
Global Notation "'{' v ';' S '}'" := (add v S) (v at level 99) : set_scope.
Global Notation "'{' S '~' v '}'" := (remove v S) (S at level 99) : set_scope.
Global Notation "v '\in' S" := (mem v S)(at level 70, no associativity) : set_scope.
Global Notation "S '∪' T" := (union S T) (at level 60, right associativity) : set_scope.
Global Notation "S '\' T" := (diff S T) (at level 60, no associativity) : set_scope.

Set Implicit Arguments.
Unset Strict Implicit.


(** * [FSetSpecs] : finite sets' specification

   We provide the specifications of set operations in a separate class
   [FSetSpecs] parameterized by an [FSet] instance. The specifications
   are the same as in the standard [FSets.FSetInterface.S] module type,
   with the exception that compatibility hypotheses for functions used
   in [filter], [exists_], etc are replaced by morphism hypotheses,
   which can be handled by the typeclass mechanism.
   *)
Class FSetSpecs_In `(FSet A) := {
  In_1 : forall s (x y : A), x == y -> In x s -> In y s
}.
Class FSetSpecs_mem `(FSet A) := {
  mem_1 : forall s x, In x s -> mem x s = true;
  mem_2 : forall s x, mem x s = true -> In x s
}.
Class FSetSpecs_equal `(FSet A) := {
  equal_1 : forall s s', s == s' -> equal s s' = true;
  equal_2 : forall s s', equal s s' = true -> s == s'
}.
Class FSetSpecs_subset `(FSet A) := {
  subset_1 : forall s s', Subset s s' -> subset s s' = true;
  subset_2 : forall s s', subset s s' = true -> Subset s s'
}.
Class FSetSpecs_empty `(FSet A) := {
  empty_1 : Empty empty
}.
Class FSetSpecs_is_empty `(FSet A) := {
  is_empty_1 : forall s, Empty s -> is_empty s = true;
  is_empty_2 : forall s, is_empty s = true -> Empty s
}.
Class FSetSpecs_add `(FSet A) := {
  add_1 : forall s (x y : A), x == y -> In y (add x s);
  add_2 : forall s x y, In y s -> In y (add x s);
  add_3 : forall s (x y : A), x =/= y -> In y (add x s) -> In y s
}.
Class FSetSpecs_remove `(FSet A) := {
  remove_1 : forall s (x y : A), x == y -> ~ In y (remove x s);
  remove_2 : forall s (x y : A),
    x =/= y -> In y s -> In y (remove x s);
  remove_3 : forall s x y, In y (remove x s) -> In y s
}.
Class FSetSpecs_singleton `(FSet A) := {
  singleton_1 : forall (x y : A), In y (singleton x) -> x == y;
  singleton_2 : forall (x y : A), x == y -> In y (singleton x)
}.
Class FSetSpecs_union `(FSet A) := {
  union_1 : forall s s' x,
    In x (union s s') -> In x s \/ In x s';
  union_2 : forall s s' x, In x s -> In x (union s s');
  union_3 : forall s s' x, In x s' -> In x (union s s')
}.
Class FSetSpecs_inter `(FSet A) := {
  inter_1 : forall s s' x, In x (inter s s') -> In x s;
  inter_2 : forall s s' x, In x (inter s s') -> In x s';
  inter_3 : forall s s' x,
    In x s -> In x s' -> In x (inter s s')
}.
Class FSetSpecs_diff `(FSet A) := {
  diff_1 : forall s s' x, In x (diff s s') -> In x s;
  diff_2 : forall s s' x, In x (diff s s') -> ~ In x s';
  diff_3 : forall s s' x,
    In x s -> ~ In x s' -> In x (diff s s')
}.
Class FSetSpecs_fold `(FSet A) := {
  fold_spec : forall s (B : Type) (i : B) (f : A -> B -> B),
      fold f s i = fold_left (fun a e => f e a) (elements s) i
}.
Class FSetSpecs_cardinal `(FSet A) := {
  cardinal_spec : forall s, cardinal s = length (elements s)
}.
Class FSetSpecs_filter `(FSet A) := {
  filter_1 : forall s x f, Proper (equiv ==> @eq bool) f ->
    In x (filter f s) -> In x s;
  filter_2 : forall s x f, Proper (equiv ==> @eq bool) f ->
    In x (filter f s) -> f x = true;
  filter_3 : forall s x f, Proper (equiv ==> @eq bool) f ->
    In x s -> f x = true -> In x (filter f s)
}.
Class FSetSpecs_for_all `(FSet A) := {
  for_all_1 : forall s f, Proper (equiv ==> @eq bool) f ->
    For_all (fun x => f x = true) s -> for_all f s = true;
  for_all_2 : forall s f, Proper (equiv ==> @eq bool) f ->
    for_all f s = true -> For_all (fun x => f x = true) s
}.
Class FSetSpecs_exists `(FSet A) := {
  exists_1 : forall s f, Proper (equiv ==> @eq bool) f ->
    Exists (fun x => f x = true) s -> exists_ f s = true;
  exists_2 : forall s f, Proper (equiv ==> @eq bool) f ->
    exists_ f s = true -> Exists (fun x => f x = true) s
}.
Class FSetSpecs_partition `(FSet A) := {
  partition_1 : forall s f, Proper (equiv ==> @eq bool) f ->
    fst (partition f s) == filter f s;
  partition_2 : forall s f, Proper (equiv ==> @eq bool) f ->
    snd (partition f s) == filter (fun x => negb (f x)) s
}.
Class FSetSpecs_elements `(FSet A) := {
  elements_1 : forall s x, In x s -> InA equiv x (elements s);
  elements_2 : forall s x, InA equiv x (elements s) -> In x s;
  (* elements_3 : forall s, sort _lt (elements s); *)
  elements_NoDupA : forall s, NoDupA equiv (elements s)
}.
Class FSetSpecs_choose `(FSet A) := {
  choose_1 : forall s x, choose s = Some x -> In x s;
  choose_2 : forall s, choose s = None -> Empty s;
(*  choose_3 : forall s s' x y, /!\ This one is wrong without ordering
    choose s = Some x -> choose s' = Some y -> s == s' -> x == y *)
}.
(*Class FSetSpecs_min_elt `(FSet A) := {
  min_elt_1 : forall s x, min_elt s = Some x -> In x s;
  min_elt_2 : forall s x y,
    min_elt s = Some x -> In y s -> ~ y <<< x;
  min_elt_3 : forall s, min_elt s = None -> Empty s
}.
Class FSetSpecs_max_elt `(FSet A) := {
  max_elt_1 : forall s x, max_elt s = Some x -> In x s;
  max_elt_2 : forall s x y,
    max_elt s = Some x -> In y s -> ~ x <<< y;
  max_elt_3 : forall s, max_elt s = None -> Empty s
}.*)

Class FSetSpecs `(F : FSet A) := {
  FFSetSpecs_In :> FSetSpecs_In F;
  FFSetSpecs_mem :> FSetSpecs_mem F;
  FFSetSpecs_equal :> FSetSpecs_equal F;
  FFSetSpecs_subset :> FSetSpecs_subset F;
  FFSetSpecs_empty :> FSetSpecs_empty F;
  FFSetSpecs_is_empty :> FSetSpecs_is_empty F;
  FFSetSpecs_add :> FSetSpecs_add F;
  FFSetSpecs_remove :> FSetSpecs_remove F;
  FFSetSpecs_singleton :> FSetSpecs_singleton F;
  FFSetSpecs_union :> FSetSpecs_union F;
  FFSetSpecs_inter :> FSetSpecs_inter F;
  FFSetSpecs_diff :> FSetSpecs_diff F;
  FFSetSpecs_fold :> FSetSpecs_fold F;
  FFSetSpecs_cardinal :> FSetSpecs_cardinal F;
  FFSetSpecs_filter :> FSetSpecs_filter F;
  FFSetSpecs_for_all :> FSetSpecs_for_all F;
  FFSetSpecs_exists :> FSetSpecs_exists F;
  FFSetSpecs_partition :> FSetSpecs_partition F;
  FFSetSpecs_elements :> FSetSpecs_elements F;
  FFSetSpecs_choose :> FSetSpecs_choose F;
  (* FFSetSpecs_min_elt :> FSetSpecs_min_elt F; *)
  (* FFSetSpecs_max_elt :> FSetSpecs_max_elt F *)
}.
(* About FSetSpecs. *)

(* Because of a bug (or limitation, depending on your leniency)
   of interaction between hints and implicit typeclasses parameters
   we define aliases to add as hints. *)
Definition zmem_1 `{H : @FSetSpecs A St HA F} :=
  @mem_1 _ _ _ _ (@FFSetSpecs_mem _ _ _ _ H).
Definition zequal_1 `{H : @FSetSpecs A St HA F} :=
  @equal_1 _ _ _ _ (@FFSetSpecs_equal _ _ _ _ H).
Definition zsubset_1 `{H : @FSetSpecs A St HA F} :=
  @subset_1 _ _ _ _ (@FFSetSpecs_subset _ _ _ _ H).
Definition zempty_1 `{H : @FSetSpecs A St HA F} :=
  @empty_1 _ _ _ _ (@FFSetSpecs_empty _ _ _ _ H).
Definition zis_empty_1 `{H : @FSetSpecs A St HA F} :=
  @is_empty_1 _ _ _ _ (@FFSetSpecs_is_empty _ _ _ _ H).
Definition zchoose_1 `{H : @FSetSpecs A St HA F} :=
  @choose_1 _ _ _ _ (@FFSetSpecs_choose _ _ _ _ H).
Definition zchoose_2 `{H : @FSetSpecs A St HA F} :=
  @choose_2 _ _ _ _ (@FFSetSpecs_choose _ _ _ _ H).
Definition zadd_1 `{H : @FSetSpecs A St HA F} :=
  @add_1 _ _ _ _ (@FFSetSpecs_add _ _ _ _ H).
Definition zadd_2 `{H : @FSetSpecs A St HA F} :=
  @add_2 _ _ _ _ (@FFSetSpecs_add _ _ _ _ H).
Definition zremove_1 `{H : @FSetSpecs A St HA F} :=
  @remove_1 _ _ _ _ (@FFSetSpecs_remove _ _ _ _ H).
Definition zremove_2 `{H : @FSetSpecs A St HA F} :=
  @remove_2 _ _ _ _ (@FFSetSpecs_remove _ _ _ _ H).
Definition zsingleton_2 `{H : @FSetSpecs A St HA F} :=
  @singleton_2 _ _ _ _ (@FFSetSpecs_singleton _ _ _ _ H).
Definition zunion_1 `{H : @FSetSpecs A St HA F} :=
  @union_1 _ _ _ _ (@FFSetSpecs_union _ _ _ _ H).
Definition zunion_2 `{H : @FSetSpecs A St HA F} :=
  @union_2 _ _ _ _ (@FFSetSpecs_union _ _ _ _ H).
Definition zunion_3 `{H : @FSetSpecs A St HA F} :=
  @union_3 _ _ _ _ (@FFSetSpecs_union _ _ _ _ H).
Definition zinter_3 `{H : @FSetSpecs A St HA F} :=
  @inter_3 _ _ _ _ (@FFSetSpecs_inter _ _ _ _ H).
Definition zdiff_3 `{H : @FSetSpecs A St HA F} :=
  @diff_3 _ _ _ _ (@FFSetSpecs_diff _ _ _ _ H).
Definition zfold_1 `{H : @FSetSpecs A St HA F} :=
  @fold_spec _ _ _ _ (@FFSetSpecs_fold _ _ _ _ H).
Definition zfilter_3 `{H : @FSetSpecs A St HA F} :=
  @filter_3 _ _ _ _ (@FFSetSpecs_filter _ _ _ _ H).
Definition zfor_all_1 `{H : @FSetSpecs A St HA F} :=
  @for_all_1 _ _ _ _ (@FFSetSpecs_for_all _ _ _ _ H).
Definition zexists_1 `{H : @FSetSpecs A St HA F} :=
  @exists_1 _ _ _ _ (@FFSetSpecs_exists _ _ _ _ H).
Definition zpartition_1 `{H : @FSetSpecs A St HA F} :=
  @partition_1 _ _ _ _ (@FFSetSpecs_partition _ _ _ _ H).
Definition zpartition_2 `{H : @FSetSpecs A St HA F} :=
  @partition_2 _ _ _ _ (@FFSetSpecs_partition _ _ _ _ H).
Definition zelements_1 `{H : @FSetSpecs A St HA F} :=
  @elements_1 _ _ _ _ (@FFSetSpecs_elements _ _ _ _ H).
Definition zelements_3w `{H : @FSetSpecs A St HA F} :=
  @elements_NoDupA _ _ _ _ (@FFSetSpecs_elements _ _ _ _ H).
(* Definition zelements_3 `{H : @FSetSpecs A St HA F} := *)
  (* @elements_3 _ _ _ _ (@FFSetSpecs_elements _ _ _ _ H). *)

Definition zIn_1 `{H : @FSetSpecs A St HA F} :=
  @In_1 _ _ _ _ (@FFSetSpecs_In _ _ _ _ H).
Definition zmem_2 `{H : @FSetSpecs A St HA F} :=
  @mem_2 _ _ _ _ (@FFSetSpecs_mem _ _ _ _ H).
Definition zequal_2 `{H : @FSetSpecs A St HA F} :=
  @equal_2 _ _ _ _ (@FFSetSpecs_equal _ _ _ _ H).
Definition zsubset_2 `{H : @FSetSpecs A St HA F} :=
  @subset_2 _ _ _ _ (@FFSetSpecs_subset _ _ _ _ H).
Definition zis_empty_2 `{H : @FSetSpecs A St HA F} :=
  @is_empty_2 _ _ _ _ (@FFSetSpecs_is_empty _ _ _ _ H).
Definition zadd_3 `{H : @FSetSpecs A St HA F} :=
  @add_3 _ _ _ _ (@FFSetSpecs_add _ _ _ _ H).
Definition zremove_3 `{H : @FSetSpecs A St HA F} :=
  @remove_3 _ _ _ _ (@FFSetSpecs_remove _ _ _ _ H).
Definition zsingleton_1 `{H : @FSetSpecs A St HA F} :=
  @singleton_1 _ _ _ _ (@FFSetSpecs_singleton _ _ _ _ H).
Definition zinter_1 `{H : @FSetSpecs A St HA F} :=
  @inter_1 _ _ _ _ (@FFSetSpecs_inter _ _ _ _ H).
Definition zinter_2 `{H : @FSetSpecs A St HA F} :=
  @inter_2 _ _ _ _ (@FFSetSpecs_inter _ _ _ _ H).
Definition zdiff_1 `{H : @FSetSpecs A St HA F} :=
  @diff_1 _ _ _ _ (@FFSetSpecs_diff _ _ _ _ H).
Definition zdiff_2 `{H : @FSetSpecs A St HA F} :=
  @diff_2 _ _ _ _ (@FFSetSpecs_diff _ _ _ _ H).
Definition zfilter_1 `{H : @FSetSpecs A St HA F} :=
  @filter_1 _ _ _ _ (@FFSetSpecs_filter _ _ _ _ H).
Definition zfilter_2 `{H : @FSetSpecs A St HA F} :=
  @filter_2 _ _ _ _ (@FFSetSpecs_filter _ _ _ _ H).
Definition zfor_all_2 `{H : @FSetSpecs A St HA F} :=
  @for_all_2 _ _ _ _ (@FFSetSpecs_for_all _ _ _ _ H).
Definition zexists_2 `{H : @FSetSpecs A St HA F} :=
  @exists_2 _ _ _ _ (@FFSetSpecs_exists _ _ _ _ H).
Definition zelements_2 `{H : @FSetSpecs A St HA F} :=
  @elements_2 _ _ _ _ (@FFSetSpecs_elements _ _ _ _ H).
(* Definition zmin_elt_1 `{H : @FSetSpecs A St HA F} := *)
  (* @min_elt_1 _ _ _ _ (@FFSetSpecs_min_elt _ _ _ _ H). *)
(* Definition zmin_elt_2 `{H : @FSetSpecs A St HA F} := *)
  (* @min_elt_2 _ _ _ _ (@FFSetSpecs_min_elt _ _ _ _ H). *)
(* Definition zmin_elt_3 `{H : @FSetSpecs A St HA F} := *)
  (* @min_elt_3 _ _ _ _ (@FFSetSpecs_min_elt _ _ _ _ H). *)
(* Definition zmax_elt_1 `{H : @FSetSpecs A St HA F} := *)
  (* @max_elt_1 _ _ _ _ (@FFSetSpecs_max_elt _ _ _ _ H). *)
(* Definition zmax_elt_2 `{H : @FSetSpecs A St HA F} := *)
  (* @max_elt_2 _ _ _ _ (@FFSetSpecs_max_elt _ _ _ _ H). *)
(* Definition zmax_elt_3 `{H : @FSetSpecs A St HA F} := *)
  (* @max_elt_3 _ _ _ _ (@FFSetSpecs_max_elt _ _ _ _ H). *)

Hint Resolve @zmem_1 @zequal_1 @zsubset_1 @zempty_1
  @zis_empty_1 @zchoose_1 @zchoose_2 @zadd_1 @zadd_2 @zremove_1
  @zremove_2 @zsingleton_2 @zunion_1 @zunion_2 @zunion_3
  @zinter_3 @zdiff_3 @zfold_1 @zfilter_3 @zfor_all_1 @zexists_1
    @zpartition_1 @zpartition_2 @zelements_1 @zelements_3w
 (* @zelements_3 *)
    : set.
Hint Immediate @zIn_1 @zmem_2 @zequal_2 @zsubset_2 @zis_empty_2 @zadd_3
  @zremove_3 @zsingleton_1 @zinter_1 @zinter_2 @zdiff_1 @zdiff_2
  @zfilter_1 @zfilter_2 @zfor_all_2 @zexists_2 @zelements_2
    (*@zmin_elt_1 @zmin_elt_2 @zmin_elt_3 @zmax_elt_1 @zmax_elt_2 @zmax_elt_3*)
    : set.
(* Typeclasses Opaque set. *)
