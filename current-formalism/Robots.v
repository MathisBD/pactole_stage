(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
   C. Auger, P. Courtieu, L. Rieg, X. Urbain                                
                                                                            
   PACTOLE project                                                          
                                                                            
   This file is distributed under the terms of the CeCILL-C licence         
                                                                          *)
(**************************************************************************)

Require Import Utf8.
Require Import Morphisms.
Require Import Arith_base.
Require Import Omega.
Require Import SetoidList.
Require Import Eqdep.
Require Import Pactole.Preliminary.


Open Scope list_scope.
Set Implicit Arguments.

(* Taken fron CoLoR *)
Scheme le_ind_dep := Induction for le Sort Prop.
Lemma le_unique : forall n m (h1 h2 : le n m), h1 = h2.
Proof.
intro n.
assert (forall m : nat, forall h1 : le n m, forall p : nat, forall h2 : le n p,
  m=p -> eq_dep nat (le n) m h1 p h2).
 intros m h1; elim h1 using le_ind_dep.
  intros p h2; case h2; intros.
   auto.
   subst n. absurd (S m0 <= m0); auto with arith.
 intros m0 l Hrec p h2.
  case h2; intros.
   subst n; absurd (S m0 <= m0); auto with arith.
   assert (m0=m1); auto ; subst m0.
   replace l0 with l; auto.
   apply eq_dep_eq; auto.
 intros; apply eq_dep_eq; auto.
Qed.

Lemma subset_dec : forall N (x y : {n : nat | n < N}), {x = y} + {x <> y}.
Proof.
intros N [x Hx] [y Hy]. destruct (Nat.eq_dec x y).
+ subst. left. f_equal. apply le_unique.
+ right. intro Habs. inv Habs. auto.
Qed.

Program Fixpoint build_enum N k (Hle : k <= N) acc : list {n : nat | n < N} :=
  match k with
    | 0 => acc
    | S m => @build_enum N m _ (exist (fun x => x < N) m _ :: acc)
  end.
Next Obligation.
omega.
Qed.
 
Definition enum N : list {n : nat | n < N} := build_enum (Nat.le_refl N) nil.

Lemma In_build_enum : forall N k (Hle : k <= N) l x, In x (build_enum Hle l) <-> In x l \/ proj1_sig x < k.
Proof.
intros N k. induction k; intros Hle l x; simpl.
+ intuition. destruct x; omega.
+ rewrite IHk. simpl. split; intro Hin.
  - destruct Hin as [[Hin | Hin] | Hin]; intuition; [].
    subst. simpl. right. omega.
  - destruct Hin as [Hin | Hin]; intuition; [].
    assert (Hcase : proj1_sig x < k \/ proj1_sig x = k) by omega.
    destruct Hcase as [Hcase | Hcase]; intuition; [].
    subst. do 2 left. destruct x; f_equal; simpl in *. apply le_unique.
Qed.

Lemma In_enum : forall N x, In x (enum N) <-> proj1_sig x < N.
Proof. intros. unfold enum. rewrite In_build_enum. simpl. intuition. Qed.

Lemma build_enum_length : forall N k (Hle : k <= N) l, length (build_enum Hle l) = k + length l.
Proof.
intros N k. induction k; intros Hle l; simpl.
+ reflexivity.
+ rewrite IHk. simpl. omega.
Qed.

Lemma enum_length : forall N, length (enum N) = N.
Proof. intro. unfold enum. now rewrite build_enum_length. Qed.

Lemma build_enum_NoDup : forall N k (Hle : k <= N) l,
  (forall x, In x l -> k <= proj1_sig x) ->  NoDup l -> NoDup (build_enum Hle l).
Proof.
intros N k. induction k; intros Hle l Hin Hl; simpl; auto; [].
apply IHk.
+ intros x [Hx | Hx].
  - now subst.
  - apply Hin in Hx. omega.
+ constructor; trivial; [].
  intro Habs. apply Hin in Habs. simpl in Habs. omega.
Qed.

Lemma enum_NoDup : forall N, NoDup (enum N).
Proof. intros. unfold enum. apply build_enum_NoDup; simpl; intuition; constructor. Qed.

Lemma build_enum_app_nil : forall N k (Hle : k <= N) l,
  build_enum Hle l = build_enum Hle nil ++ l.
Proof.
intros N k. induction k; intros Hle l; simpl.
+ reflexivity.
+ setoid_rewrite IHk. now rewrite <- app_assoc.
Qed.

Theorem build_enum_eq : forall {A} eqA N (f g : {n : nat | n < N} -> A) k (Hle : k <= N) l,
  eqlistA eqA (List.map f (build_enum Hle l)) (List.map g (build_enum Hle l)) ->
  forall x, proj1_sig x < k -> eqA (f x) (g x).
Proof.
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
      assert (Heqx : x = exist (λ x : nat, x < N) (proj1_sig x) Hle).
      { clear. destruct x; simpl. f_equal. apply le_unique. }
      now rewrite Heqx.
Qed.

Corollary enum_eq : forall {A} eqA N (f g : {n : nat | n < N} -> A),
  eqlistA eqA (List.map f (enum N)) (List.map g (enum N)) -> forall x, eqA (f x) (g x).
Proof.
unfold enum. intros A eqA N f g Heq x.
apply build_enum_eq with (x := x) in Heq; auto; []. apply proj2_sig.
Qed.

(** *  Identification of robots  **)

(** The number of good and byzantine robots *)
Module Type Size.
  Parameter nG : nat.
  Parameter nB : nat.
End Size.

Inductive identifier {G} {B} : Type :=  Good : G → identifier | Byz : B → identifier.

Module Type Robots(N : Size).
  
  (** We have finetely many robots. Some are good, others are byzantine. *)
  Definition G := {n : nat | n < N.nG}.
  Definition B := {n : nat | n < N.nB}.
  
  (** Disjoint union of both kinds of robots is obtained by a sum type. *)
  (* TODO: replace this by (G ⊎ B). *)
  Definition ident := @identifier G B.
  
  (** Names of robots **)
  Definition Gnames : list G := enum N.nG.
  Definition Bnames : list B := enum N.nB.
  Definition names : list identifier := map Good Gnames ++ map Byz Bnames.
  
  Parameter In_Gnames : forall g : G, In g Gnames.
  Parameter In_Bnames : forall b : B, In b Bnames.
  Parameter In_names : forall id : ident, In id names.
  
  Parameter Gnames_NoDup : NoDup Gnames.
  Parameter Bnames_NoDup : NoDup Bnames.
  Parameter names_NoDup : NoDup names.
  
  Parameter Gnames_length : length Gnames = N.nG.
  Parameter Bnames_length : length Bnames = N.nB.
  Parameter names_length : length names = N.nG + N.nB.
  Parameter eq_dec: forall n m: ident, {n=m}+{n<>m}.
  
  Parameter fun_Gnames_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f Gnames) (List.map g Gnames) -> forall x, eqA (f x) (g x).
  Parameter fun_Bnames_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f Bnames) (List.map g Bnames) -> forall x, eqA (f x) (g x).
  Parameter fun_names_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f names) (List.map g names) -> forall x, eqA (f x) (g x).
End Robots.


Module Make(N : Size) : Robots(N).
  Definition G := {n : nat | n < N.nG}.
  Definition B := {n : nat | n < N.nB}.
  Definition ident := @identifier G B.

  Definition Gnames : list G := enum N.nG.
  Definition Bnames : list B := enum N.nB.
  Definition names : list identifier := map Good Gnames ++ map Byz Bnames.
  
  Lemma In_Gnames : forall g : G, In g Gnames.
  Proof. intro g. unfold Gnames, G. rewrite In_enum. apply proj2_sig. Qed.
  
  Lemma In_Bnames : forall b : B, In b Bnames.
  Proof. intro b. unfold Bnames, B. rewrite In_enum. apply proj2_sig. Qed.
  
  Lemma In_names : forall id, In id names.
  Proof.
  intro id. unfold names. rewrite in_app_iff. destruct id as [g | b].
  - left. apply in_map, In_Gnames.
  - right. apply in_map, In_Bnames.
  Qed.
  
  Lemma Gnames_NoDup : NoDup Gnames.
  Proof. unfold Gnames. apply enum_NoDup. Qed.
  
  Lemma Bnames_NoDup : NoDup Bnames.
  Proof. unfold Bnames. apply enum_NoDup. Qed.
  
  Lemma names_NoDup : NoDup names.
  Proof.
  unfold names. rewrite <- NoDupA_Leibniz. apply (NoDupA_app _).
  + apply (map_injective_NoDupA _ _).
    - now repeat intro; subst.
    - intros ? ? H. now inversion H.
    - rewrite NoDupA_Leibniz. apply Gnames_NoDup.
  + apply (map_injective_NoDupA _ _).
    - now repeat intro; subst.
    - intros ? ? H. now inversion H.
    - rewrite NoDupA_Leibniz. apply Bnames_NoDup.
  + intros id HinA HinB. rewrite (InA_map_iff _ _) in HinA. rewrite (InA_map_iff _ _) in HinB.
    - destruct HinA as [? [? ?]], HinB as [? [? ?]]. subst. discriminate.
    - now repeat intro; subst.
    - now repeat intro; subst.
  Qed.
  
  Lemma Gnames_length : length Gnames = N.nG.
  Proof. unfold Gnames. apply enum_length. Qed.
  
  Lemma Bnames_length : length Bnames = N.nB.
  Proof. unfold Bnames. apply enum_length. Qed.
  
  Lemma names_length : length names = N.nG + N.nB.
  Proof.
  unfold names. rewrite app_length, map_length, map_length.
  now rewrite Gnames_length, Bnames_length.
  Qed.
  
  Lemma eq_dec: forall n m: ident, {n = m} + {n <> m}.
  Proof.
  intros id id'.
  destruct id as [g | b], id' as [g' | b']; try (now right; discriminate); [|].
  + destruct (subset_dec g g').
    - left; subst; auto.
    - right; intro Habs. now injection Habs.
  + destruct (subset_dec b b').
    - left; subst; auto.
    - right; intro Habs. now injection Habs.
  Qed.
  
  Lemma fun_Gnames_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f Gnames) (List.map g Gnames) -> forall x, eqA (f x) (g x).
  Proof. intros. now apply enum_eq. Qed.
  
  Lemma fun_Bnames_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f Bnames) (List.map g Bnames) -> forall x, eqA (f x) (g x).
  Proof. intros. now apply enum_eq. Qed.
  
  Lemma fun_names_eq : forall {A : Type} eqA f g,
    @eqlistA A eqA (List.map f names) (List.map g names) -> forall x, eqA (f x) (g x).
  Proof.
  intros A eqA f h Heq id.
  unfold names in Heq. repeat rewrite ?map_app, map_map in Heq. apply eqlistA_app_split in Heq.
  + destruct id as [g | b].
    - change (eqA ((fun x => f (Good x)) g) ((fun x => h (Good x)) g)). apply fun_Gnames_eq, Heq.
    - change (eqA ((fun x => f (Byz x)) b) ((fun x => h (Byz x)) b)). apply fun_Bnames_eq, Heq.
  + now do 2 rewrite map_length.
  Qed.
End Make.
