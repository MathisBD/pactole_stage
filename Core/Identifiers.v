(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     P. Courtieu, L. Rieg, X. Urbain                                        
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence       
                                                                          *)
(**************************************************************************)


Require Import SetoidDec SetoidList.
Require Import Arith_base.
Require Import Omega.
Require Import Pactole.Util.Coqlib.


Set Implicit Arguments.
Typeclasses eauto := (bfs).


(* TODO: should we add a fold operator? *)
(* FIXME: change the equalities to use equiv and the Setoid class *)

(** Finite sets as a prefix of natural numbers. *)
Notation "'fin' N" := {n : nat | n < N} (at level 10).

Lemma subset_dec : forall N (x y : fin N), {x = y} + {x <> y}.
Proof using .
intros N [x Hx] [y Hy]. destruct (Nat.eq_dec x y).
+ subst. left. f_equal. apply le_unique.
+ right. intro Habs. inv Habs. auto.
Qed.

Lemma eq_proj1 : forall N (x y : fin N), proj1_sig x = proj1_sig y -> x = y.
Proof using . intros N [x Hx] [y Hy] ?. simpl in *. subst. f_equal. apply le_unique. Qed.

Program Fixpoint build_enum N k (Hle : k <= N) acc : list (fin N) :=
  match k with
    | 0 => acc
    | S m => @build_enum N m _ (exist (fun x => x < N) m _ :: acc)
  end.
Next Obligation.
omega.
Qed.

(** A list containing all elements of [fin N]. *)
Definition enum N : list (fin N) := build_enum (Nat.le_refl N) nil.

(** Specification of [enum]. *)
Lemma In_build_enum : forall N k (Hle : k <= N) l x, In x (build_enum Hle l) <-> In x l \/ proj1_sig x < k.
Proof using .
intros N k. induction k; intros Hle l x; simpl.
+ intuition.
+ rewrite IHk. simpl. split; intro Hin.
  - destruct Hin as [[Hin | Hin] | Hin]; intuition; [].
    subst. simpl. right. omega.
  - destruct Hin as [Hin | Hin]; intuition; [].
    assert (Hcase : proj1_sig x < k \/ proj1_sig x = k) by omega.
    destruct Hcase as [Hcase | Hcase]; intuition; [].
    subst. do 2 left. destruct x; f_equal; simpl in *. apply le_unique.
Qed.

Lemma In_enum : forall N x, In x (enum N) <-> proj1_sig x < N.
Proof using . intros. unfold enum. rewrite In_build_enum. simpl. intuition. Qed.

(** Length of [enum]. *)
Lemma build_enum_length : forall N k (Hle : k <= N) l, length (build_enum Hle l) = k + length l.
Proof using .
intros N k. induction k; intros Hle l; simpl.
+ reflexivity.
+ rewrite IHk. simpl. omega.
Qed.

Lemma enum_length : forall N, length (enum N) = N.
Proof using . intro. unfold enum. now rewrite build_enum_length. Qed.

(** [enum] does not contain duplicates. *)
Lemma build_enum_NoDup : forall N k (Hle : k <= N) l,
  (forall x, In x l -> k <= proj1_sig x) -> NoDup l -> NoDup (build_enum Hle l).
Proof using .
intros N k. induction k; intros Hle l Hin Hl; simpl; auto; [].
apply IHk.
+ intros x [Hx | Hx].
  - now subst.
  - apply Hin in Hx. omega.
+ constructor; trivial; [].
  intro Habs. apply Hin in Habs. simpl in Habs. omega.
Qed.

Lemma enum_NoDup : forall N, NoDup (enum N).
Proof using . intro. unfold enum. apply build_enum_NoDup; simpl; intuition; constructor. Qed.

(** [enum] is sorted in increasing order. *)
Notation Flt := (fun x y => lt (proj1_sig x) (proj1_sig y)).

Lemma build_enum_Sorted : forall N k (Hle : k <= N) l,
  (forall x, In x l -> k <= proj1_sig x) -> Sorted Flt l -> Sorted Flt (build_enum Hle l).
Proof using .
intros N k. induction k; intros Hle l Hin Hl; simpl; auto; [].
apply IHk.
+ intros x [Hx | Hx].
  - now subst.
  - apply Hin in Hx. omega.
+ constructor; trivial; [].
  destruct l; constructor; []. simpl. apply Hin. now left.
Qed.

Lemma enum_Sorted : forall N, Sorted Flt (enum N).
Proof using . intro. unfold enum. apply build_enum_Sorted; simpl; intuition. Qed.

(** Extensional equality of functions is decidable over finite domains. *)
Lemma build_enum_app_nil : forall N k (Hle : k <= N) l,
  build_enum Hle l = build_enum Hle nil ++ l.
Proof using .
intros N k. induction k; intros Hle l; simpl.
+ reflexivity.
+ now rewrite (IHk _ (_ :: nil)), IHk, <- app_assoc.
Qed.

Theorem build_enum_eq : forall {A} eqA N (f g : fin N -> A) k (Hle : k <= N) l,
  eqlistA eqA (List.map f (build_enum Hle l)) (List.map g (build_enum Hle l)) ->
  forall x, proj1_sig x < k -> eqA (f x) (g x).
Proof using .
intros A eqA N f g k. induction k; intros Hle l Heq x Hx; simpl.
* destruct x; simpl in *; omega.
* assert (Hlt : k <= N) by omega.
  assert (Hcase : proj1_sig x < k \/ proj1_sig x = k) by omega.
  destruct Hcase as [Hcase | Hcase].
  + apply IHk with (x := x) in Heq; auto.
  + subst k. simpl in Heq. rewrite build_enum_app_nil, map_app, map_app in Heq.
    destruct (eqlistA_app_split _ _ _ _ Heq) as [_ Heq'].
    - now do 2 rewrite map_length, build_enum_length.
    - simpl in Heq'. inv Heq'.
      assert (Heqx : x = exist (fun x => x < N) (proj1_sig x) Hle).
      { clear. destruct x; simpl. f_equal. apply le_unique. }
      now rewrite Heqx.
Qed.

Corollary enum_eq : forall {A} eqA N (f g : fin N -> A),
  eqlistA eqA (List.map f (enum N)) (List.map g (enum N)) -> forall x, eqA (f x) (g x).
Proof using .
unfold enum. intros A eqA N f g Heq x.
apply build_enum_eq with (x := x) in Heq; auto; []. apply proj2_sig.
Qed.

(** Cutting [enum] after some number of elements. *)
Lemma firstn_build_enum_le : forall N k (Hle : k <= N) l k' (Hk : k' <= N), k' <= k ->
  firstn k' (build_enum Hle l) = @build_enum N k' Hk nil.
Proof using .
intros N k. induction k; intros Hk l k' Hk' Hle.
* assert (k' = 0) by omega. now subst.
* rewrite build_enum_app_nil, firstn_app, build_enum_length.
  replace (k' - (S k + length (@nil (fin N)))) with 0 by omega.
  rewrite app_nil_r.
  destruct (Nat.eq_dec k' (S k)) as [Heq | Heq].
  + subst k'. rewrite firstn_all2.
    - f_equal. apply le_unique.
    - rewrite build_enum_length. simpl. omega.
  + simpl build_enum. erewrite IHk.
    - f_equal.
    - omega.
Qed.

Lemma firstn_build_enum_lt : forall N k (Hle : k <= N) l k', k <= k' ->
  firstn k' (build_enum Hle l) = build_enum Hle (firstn (k' - k) l).
Proof using .
intros N k. induction k; intros Hle l k' Hk.
+ now rewrite Nat.sub_0_r.
+ rewrite build_enum_app_nil, firstn_app, build_enum_length, Nat.add_0_r.
  rewrite firstn_all2, <- build_enum_app_nil; trivial; [].
  rewrite build_enum_length. simpl. omega.
Qed.

Lemma firstn_enum_le : forall N k (Hle : k <= N), firstn k (enum N) = build_enum Hle nil.
Proof using . intros. unfold enum. now apply firstn_build_enum_le. Qed.

Lemma firstn_enum_lt : forall N k, N <= k -> firstn k (enum N) = enum N.
Proof using . intros. unfold enum. now rewrite firstn_build_enum_lt, firstn_nil. Qed.

Lemma firstn_enum_spec : forall N k x, In x (firstn k (enum N)) <-> proj1_sig x < k.
Proof using .
intros N k x. destruct (le_lt_dec k N) as [Hle | Hlt].
+ rewrite (firstn_enum_le Hle), In_build_enum. simpl. intuition.
+ rewrite (firstn_enum_lt (lt_le_weak _ _ Hlt)).
  split; intro Hin.
  - transitivity N; trivial; []. apply proj2_sig.
  - apply In_enum, proj2_sig.
Qed.

(** Removing some number of elements from the head of [enum]. *)
Lemma skipn_build_enum_lt : forall N k (Hle : k <= N) l k', k <= k' ->
  skipn k' (build_enum Hle l) = skipn (k' - k) l.
Proof using .
intros N k Hle l k' Hk'. apply app_inv_head with (firstn k' (build_enum Hle l)).
rewrite firstn_skipn, firstn_build_enum_lt; trivial; [].
rewrite (build_enum_app_nil Hle (firstn _ _)).
now rewrite build_enum_app_nil, <- app_assoc, firstn_skipn.
Qed.

Lemma skipn_enum_lt : forall N k, N <= k -> skipn k (enum N) = nil.
Proof using . intros. unfold enum. now rewrite skipn_build_enum_lt, skipn_nil. Qed.

Lemma skipn_enum_spec : forall N k x, In x (skipn k (enum N)) <-> k <= proj1_sig x < N.
Proof using .
intros N k x. split; intro Hin.
+ assert (Hin' : ~In x (firstn k (enum N))).
  { intro Habs. rewrite <- InA_Leibniz in *. revert x Habs Hin. apply NoDupA_app_iff; autoclass; [].
    rewrite firstn_skipn. rewrite NoDupA_Leibniz. apply enum_NoDup. }
  rewrite firstn_enum_spec in Hin'. split; auto with zarith; []. apply proj2_sig.
+ assert (Hin' : In x (enum N)) by apply In_enum, proj2_sig.
  rewrite <- (firstn_skipn k), in_app_iff, firstn_enum_spec in Hin'. intuition omega.
Qed.

(** ** Byzantine Robots *)

(** We have finitely many robots. Some are good, others are Byzantine.
    Both are represented by an abtract type that can be enumerated. *)
Class Names := {
  (** Number of good and Byzantine robots *)
  nG : nat;
  nB : nat;
  (** Types representing good and Byzantine robots *)
  G : Type;
  B : Type;
  (** Enumerations of robots *)
  Gnames : list G;
  Bnames : list B;
  (** The enumerations are complete and without duplicates *)
  In_Gnames : forall g : G, In g Gnames;
  In_Bnames : forall b : B, In b Bnames;
  Gnames_NoDup : NoDup Gnames;
  Bnames_NoDup : NoDup Bnames;
  (** There is the right amount of robots *)
  Gnames_length : length Gnames = nG;
  Bnames_length : length Bnames = nB;
  (** We can tell robots apart *)
  Geq_dec : forall g g' : G, {g = g'} + {g <> g'};
  Beq_dec : forall b b' : B, {b = b'} + {b <> b'};
  (** Being a finite type, extensional function equality is decidable *)
  fun_Gnames_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f Gnames) (List.map g Gnames) -> forall x, eqA (f x) (g x);
  fun_Bnames_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f Bnames) (List.map g Bnames) -> forall x, eqA (f x) (g x)}.

Global Opaque In_Gnames In_Bnames Gnames_NoDup Bnames_NoDup
              Gnames_length Bnames_length Geq_dec Beq_dec fun_Gnames_eq fun_Bnames_eq.

(** Identifiers make good and Byzantine robots undistinguishable.
    They have their own enumeration without duplicates,
    and both equality and extensional function equality are decidable. *)
Inductive ident `{Names} : Type :=
  | Good (g : G)
  | Byz (b : B).

Definition names `{Names} : list ident := List.map Good Gnames ++ List.map Byz Bnames.

Lemma In_names `{Names} : forall r : ident, In r names.
Proof using .
intro r. cbn. unfold names. rewrite in_app_iff. destruct r as [g | b].
- left. apply in_map, In_Gnames.
- right. apply in_map, In_Bnames.
Qed.

Lemma names_NoDup `{Names} : NoDup names.
Proof using .
unfold names. rewrite <- NoDupA_Leibniz. apply (NoDupA_app _).
+ apply (map_injective_NoDupA _ _).
  - now repeat intro; hnf in *; subst.
  - intros ? ? Heq. now inversion Heq.
  - rewrite NoDupA_Leibniz. apply Gnames_NoDup.
+ apply (map_injective_NoDupA _ _).
  - now repeat intro; hnf in *; subst.
  - intros ? ? Heq. now inversion Heq.
  - rewrite NoDupA_Leibniz. apply Bnames_NoDup.
+ intros id HinA HinB. rewrite (InA_map_iff _ _) in HinA. rewrite (InA_map_iff _ _) in HinB.
  - destruct HinA as [? [? ?]], HinB as [? [? ?]]. subst. discriminate.
  - now repeat intro; hnf in *; subst.
  - now repeat intro; hnf in *; subst.
Qed.

Lemma names_length `{Names} : length names = nG + nB.
Proof using . unfold names. now rewrite app_length, map_length, map_length, Gnames_length, Bnames_length. Qed.

Lemma names_eq_dec `{Names} : forall id id' : ident, {id = id'} + { id <> id'}.
Proof using .
intros id id'.
destruct id as [g | b], id' as [g' | b']; try (now right; discriminate); [|].
+ destruct (Geq_dec g g').
  - left; subst; auto.
  - right; intro Habs. now injection Habs.
+ destruct (Beq_dec b b').
  - left; subst; auto.
  - right; intro Habs. now injection Habs.
Qed.

Instance ident_Setoid `{Names} : Setoid ident := { equiv := eq; setoid_equiv := eq_equivalence }.
Instance ident_EqDec `{Names} : EqDec ident_Setoid := names_eq_dec.

Instance fun_refl `{Names} : forall A (f : ident -> A) R,
  Reflexive R -> Proper (@SetoidClass.equiv ident _ ==> R) f.
Proof using . intros A f R HR ? ? Heq. simpl in Heq. now subst. Qed.

Instance list_ident_Setoid `{Names} : Setoid (list ident) := { equiv := eq; setoid_equiv := eq_equivalence }.
Instance list_ident_Eqdec `{Names} : EqDec list_ident_Setoid := list_eq_dec ident_EqDec.

Lemma fun_names_eq `{Names} : forall {A : Type} eqA f g,
  @eqlistA A eqA (List.map f names) (List.map g names) -> forall x, eqA (f x) (g x).
Proof using .
intros A eqA f h Heq id.
unfold names in Heq. repeat rewrite ?map_app, map_map in Heq. apply eqlistA_app_split in Heq.
+ destruct id as [g | b].
  - change (eqA ((fun x => f (Good x)) g) ((fun x => h (Good x)) g)). apply fun_Gnames_eq, Heq.
  - change (eqA ((fun x => f (Byz x)) b) ((fun x => h (Byz x)) b)). apply fun_Bnames_eq, Heq.
+ now do 2 rewrite map_length.
Qed.

(** Given a number of good and byzntine robots, we can build canonical names.
    It is not declared as a global instance to avoid creating spurious settings. *)
Definition Robots (n m : nat) : Names.
Proof.
refine {|
  nG := n;
  nB := m;
  G := fin n;
  B := fin m;
  Gnames := enum n;
  Bnames := enum m |}.
+ abstract (intro g; apply In_enum, proj2_sig).
+ abstract (intro b; apply In_enum, proj2_sig).
+ apply enum_NoDup.
+ apply enum_NoDup.
+ apply enum_length.
+ apply enum_length.
+ apply subset_dec.
+ apply subset_dec.
+ intros ? ?. apply enum_eq.
+ intros ? ?. apply enum_eq.
Defined.

Global Opaque G B.
