(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require MMapWeakList. (* to build an actual implementation of multisets *)
Require Import Utf8_core.
Require Import Arith_base.
Require Import Omega.
Require Import SetoidList.
Require Import MMultisetInterface.
Require Import MMultisetFacts.
Require Import MMultisetWMap.
Require Import Pactole.Preliminary.
Require Robots.
Require Import Positions.


Module Make(Location : MetricSpace)(N : Robots.Size) <: Spectrum (Location)(N).

Module Names := Robots.Make(N).
Module Pos := Positions.Make(Location)(N)(Names).

(** Definition of spectra as multisets of locations. *)
Module Mraw := MMultisetWMap.FMultisets MMapWeakList.Make Location.
Module M := MMultisetFacts.Make Location Mraw.

Notation "m1  ≡  m2" := (M.eq m1 m2) (at level 70).
Notation "m1  ⊆  m2" := (M.Subset m1 m2) (at level 70).
Notation "m1  [=]  m2" := (M.eq m1 m2) (at level 70, only parsing).
Notation "m1  [c=]  m2" := (M.Subset m1 m2) (at level 70, only parsing).

Lemma eq_refl_left : forall e A (a b:A), (if Location.eq_dec e e then a else b) = a.
Proof.
  intros e A a b.
  destruct (Location.eq_dec e e).
  - reflexivity.
  - elim n.
    reflexivity.
Qed.


(** **  Building multisets from lists  **)

(* TODO: should be replaced by M.from_elements *)
Definition multiset l := fold_left (fun acc x => M.add x 1 acc) l M.empty.

Lemma multiset_nil : multiset nil [=] M.empty.
Proof. reflexivity. Qed.

Lemma multiset_cons_aux : forall l x m,
  List.fold_left (fun acc y => M.add y 1 acc) (x :: l) m [=]
  M.add x 1 (List.fold_left (fun acc x => M.add x 1 acc) l m).
Proof.
intro l. induction l; intros x m.
+ reflexivity.
+ simpl. intro.
  assert (Hf : Proper (M.eq ==> eq ==> M.eq) (fun acc y => M.add y 1 acc)).
  { clear. intros s1 s2 Hs x y Hxy. now rewrite Hxy, Hs. }
  rewrite (@fold_left_start _ _ Logic.eq M.eq _ _ _ Hf l _ (M.add x 1 (M.add a 1 m)) (M.add_comm _ _ _ _ _)).
  apply IHl.
Qed.

Lemma multiset_cons : forall x l, multiset (x :: l) [=] M.add x 1 (multiset l).
Proof. intros x l y. unfold multiset. now rewrite multiset_cons_aux. Qed.

Lemma multiset_empty : forall l, multiset l [=] M.empty <-> l = nil.
Proof.
intro l. split; intro H.
+ destruct l as [| x l]. reflexivity. rewrite multiset_cons in H.
  specialize (H x). rewrite M.add_spec, M.empty_spec in H.
  rewrite eq_refl_left in H.
  exfalso;omega.
+ subst l. apply multiset_nil.
Qed.

Lemma multiset_app : forall l l', multiset (l ++ l') [=] M.union (multiset l) (multiset l').
Proof.
induction l as [| e l]; intros l'; simpl.
+ now rewrite M.union_empty_l.
+ do 2 rewrite multiset_cons. intro x. destruct (Location.eq_dec x e) as [Heq | Heq].
  - rewrite Heq, M.add_spec, IHl. repeat rewrite M.union_spec. rewrite M.add_spec.
    repeat rewrite eq_refl_left.
    omega.
  - rewrite M.add_other, IHl; auto. repeat rewrite M.union_spec. rewrite M.add_other; auto.
Qed.

Lemma location_neq_sym: forall x y, ~ Location.eq x y -> ~ Location.eq y x.
Proof.
  intros x y H.
  intro abs.
  symmetry in abs.
  contradiction.
Qed.

Instance multiset_compat : Proper (PermutationA Location.eq ==> M.eq) multiset.
Proof.
intro l1. induction l1 as [| x l1]; intros l2 Hperm.
+ apply (PermutationA_nil _) in Hperm. now subst.
+ assert (Hx := @PermutationA_InA_inside _ _ _ x _ _ Hperm).
  destruct Hx as [l1' [y [l2' [Hxy Heq]]]]. now left. subst l2.
  intro z. rewrite multiset_app, M.union_spec. do 2 rewrite multiset_cons.
  destruct (Location.eq_dec x z) as [Heq | Hneq].
  - rewrite <- Heq, <- Hxy. repeat rewrite M.add_spec.
    repeat rewrite eq_refl_left.
    rewrite plus_assoc. f_equal.
    rewrite <- M.union_spec, <- multiset_app. apply IHl1.
    rewrite <- (PermutationA_middle _), Hxy in Hperm. revert Hperm. apply (PermutationA_cons_inv _).
  - apply location_neq_sym in Hneq.
    rewrite <- Hxy. repeat rewrite M.add_other; trivial. rewrite <- M.union_spec, <- multiset_app.
    apply IHl1. rewrite <- (PermutationA_middle _), Hxy in Hperm. revert Hperm. apply (PermutationA_cons_inv _).
Qed.

Lemma multiset_PermutationA : forall x l n, M.multiplicity x (multiset l) = n ->
  exists l', ~InA Location.eq x l' /\ PermutationA Location.eq l (alls x n ++ l').
Proof.
intros x l. induction l; intros n Hin.
  exists nil. split. now auto. rewrite multiset_nil, M.empty_spec in Hin. subst n. simpl. reflexivity.
  rewrite multiset_cons in Hin. destruct (Location.eq_dec x a) as [Heq | Heq].
  - setoid_rewrite <- Heq. rewrite <- Heq in Hin. rewrite M.add_spec in Hin. destruct n.
    + rewrite eq_refl_left in Hin.
      omega.
    + rewrite eq_refl_left in Hin.
      rewrite plus_comm in Hin. simpl in Hin. apply eq_add_S in Hin. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
    exists l'. split. assumption. simpl. now constructor.
  - rewrite M.add_other in Hin; auto. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
    exists (a :: l'). split. intro Hin; inversion_clear Hin; contradiction.
    transitivity (a :: alls x n ++ l'); now constructor || apply (PermutationA_middle _).
Qed.

Lemma multiset_alls : forall x n, multiset (alls x n) [=] M.singleton x n.
Proof.
intros x n. induction n; simpl.
+ now rewrite M.singleton_0, multiset_nil.
+ rewrite multiset_cons. rewrite IHn. intro y. rewrite M.singleton_spec.
  destruct (Location.eq_dec y x) as [Heq | Heq].
  - rewrite Heq, M.add_spec, M.singleton_spec. destruct (Location.eq_dec x x) as [_ | Helim]. omega. now elim Helim.
  - rewrite M.add_other; auto. rewrite M.singleton_spec. destruct (Location.eq_dec y x); trivial. contradiction.
Qed.

Corollary multiset_In : forall x l, M.multiplicity x (multiset l) > 0 <-> InA Location.eq x l.
Proof.
intros x l. split; intro Hl.
+ destruct (multiset_PermutationA _ _ _ (eq_refl (M.multiplicity x (multiset l)))) as [l' [Hl' Hperm]].
  rewrite Hperm. rewrite (InA_app_iff _). left. destruct (M.multiplicity x (multiset l)). omega. now left.
+ induction l. now inversion Hl. rewrite multiset_cons. destruct (Location.eq_dec a x) as [Heq | Hneq].
  - rewrite Heq. rewrite M.add_spec. 
    rewrite eq_refl_left.
    omega.
  - apply location_neq_sym in Hneq.
    rewrite M.add_other; trivial. apply IHl. inversion_clear Hl; auto. now elim Hneq.
Qed.

Theorem multiset_map : forall f, Proper (Location.eq ==> Location.eq) f ->
  forall l, multiset (map f l) [=] M.map f (multiset l).
Proof.
intros f Hf l.
induction l; simpl.
+ rewrite (@M.map_compat f Hf (multiset nil)), multiset_nil. now rewrite M.map_empty. now apply multiset_nil.
+ do 2 rewrite multiset_cons. now rewrite M.map_add, IHl.
Qed.

Theorem cardinal_multiset : forall l, M.cardinal (multiset l) = length l.
Proof.
induction l; simpl.
+ now rewrite multiset_nil, M.cardinal_empty.
+ rewrite multiset_cons, M.cardinal_add. apply f_equal, IHl.
Qed.

Theorem multiset_spec : forall x l, M.multiplicity x (multiset l) = countA_occ _ Location.eq_dec x l.
Proof.
intros x l. induction l; simpl.
+ rewrite multiset_nil. now apply M.empty_spec.
+ rewrite multiset_cons. destruct (Location.eq_dec a x) as [Heq | Hneq].
  - rewrite Heq. rewrite M.add_spec. rewrite IHl.
    rewrite eq_refl_left.
    omega.
  - apply location_neq_sym in Hneq. rewrite M.add_other. now apply IHl. assumption.
Qed.
(*
Lemma multiset_remove : forall x l,
  multiset (remove Rdec x l) [=] M.remove x (M.multiplicity x (multiset l)) (multiset l).
Proof.
intros x l y. induction l as[| a l]; simpl.
+ rewrite multiset_nil. do 2 rewrite M.empty_spec. now rewrite M.remove_0, M.empty_spec.
+ rewrite multiset_cons. destruct (Rdec y x). 
  - subst y. Rdec_full.
      subst a. rewrite IHl. rewrite M.add_spec. do 2 rewrite M.remove_spec. rewrite M.add_spec. omega.
      rewrite multiset_cons. rewrite M.add_other; auto. rewrite IHl. do 2 rewrite M.remove_spec. omega.
  - Rdec_full.
      subst a. rewrite IHl. rewrite M.add_spec. repeat rewrite M.remove_spec'; auto. rewrite M.add_other; auto.
      rewrite multiset_cons. rewrite M.remove_spec'; auto. destruct (Rdec a y).
        subst a. do 2 rewrite M.add_spec. rewrite IHl. now rewrite M.remove_spec'.
        repeat rewrite M.add_other; trivial. rewrite IHl. rewrite M.remove_spec'; auto.
Qed.
*)

Lemma multiset_support : forall x l, InA Location.eq x (M.support (multiset l)) <-> InA Location.eq x l.
Proof.
intros x l. split; intro Hl.
* induction l.
  + cut (M.support (multiset nil) = nil).
    - intro Heq. unfold M.elt in *. now rewrite <- Heq.
    - apply (PermutationA_nil Location.eq_equiv). now rewrite multiset_nil, M.support_empty.
  + rewrite multiset_cons in Hl. rewrite M.support_add in Hl; try omega.
    destruct (M.In_dec a (multiset l)).
    - right. now apply IHl.
    - inversion_clear Hl. now left. right. now apply IHl.
* induction l.
  + inversion Hl.
  + rewrite M.support_spec. unfold M.In. rewrite multiset_cons. destruct (Location.eq_dec a x) as [Heq | Hneq].
    - rewrite Heq. rewrite M.add_spec.
      rewrite eq_refl_left. omega.
    - apply location_neq_sym in Hneq.
      rewrite M.add_other; trivial. change (M.In x (multiset l)).
      rewrite <- M.support_spec. apply IHl. inversion_clear Hl; trivial. elim Hneq. now symmetry.
Qed.


(** Building a spectrum from a position *)
Include M.

Definition from_config pos : t := multiset (Pos.list pos).

Instance from_config_compat : Proper (Pos.eq ==> eq) from_config.
Proof.
intros pos1 pos2 Hpos x. unfold from_config. do 2 f_equiv.
apply eqlistA_PermutationA_subrelation, Pos.list_compat. assumption.
Qed.

Definition is_ok s pos := forall l,
  M.multiplicity l s = countA_occ _ Location.eq_dec l (Pos.list pos).

Theorem from_config_spec : forall pos, is_ok (from_config pos) pos.
Proof. unfold from_config, is_ok. intros. apply multiset_spec. Qed.

Lemma from_config_map : forall f, Proper (Location.eq ==> Location.eq) f ->
  forall pos, eq (map f (from_config pos)) (from_config (Pos.map f pos)).
Proof. repeat intro. unfold from_config. now rewrite Pos.list_map, multiset_map. Qed.

Theorem cardinal_from_config : forall conf, cardinal (from_config conf) = N.nG + N.nB.
Proof. intro. unfold from_config. now rewrite cardinal_multiset, Pos.list_length. Qed.

Property pos_in_config : forall conf id, In (conf id) (from_config conf).
Proof.
intros conf id. unfold from_config.
unfold In. rewrite multiset_spec. rewrite (countA_occ_pos _).
rewrite Pos.list_InA. now exists id.
Qed.

Property from_config_In : forall config l, In l (from_config config) <-> exists id, Location.eq (config id) l.
Proof.
intros config l. split; intro Hin.
+ unfold In in Hin. rewrite from_config_spec, (countA_occ_pos _), Pos.list_spec in Hin.
  rewrite (InA_map_iff _ _) in Hin.
  - firstorder.
  - repeat intro. now subst.
+ destruct Hin as [id Hid]. rewrite <- Hid. apply pos_in_config.
Qed.
End Make.
