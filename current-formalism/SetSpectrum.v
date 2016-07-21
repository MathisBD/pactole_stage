(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Utf8_core.
Require Import Omega.
Require Import SetoidList.
Require Import MSets.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.


Module Make(Loc : RealMetricSpace)(N : Size) <: Spectrum (Loc)(N).

Module Names := Robots.Make(N).
Module Config := Configurations.Make(Loc)(N)(Names).

(** Definition of spectra as sets of locations. *)
Module M := MSetWeakList.Make(Loc).
Module Mdec := Decide(M).
Module MProp := EqProperties(M).
Export Mdec.

Notation "m1  ≡  m2" := (M.eq m1 m2) (at level 70).
Notation "m1  ⊆  m2" := (M.Subset m1 m2) (at level 70).
Notation "m1  [=]  m2" := (M.eq m1 m2) (at level 70, only parsing).
Notation "m1  [c=]  m2" := (M.Subset m1 m2) (at level 70, only parsing).

(** **  Building sets from lists  **)

Definition set l := fold_left (fun acc x => M.add x acc) l M.empty.

Lemma set_nil : set nil [=] M.empty.
Proof. reflexivity. Qed.

Lemma set_cons_aux : forall l x m,
  List.fold_left (fun acc y => M.add y acc) (x :: l) m [=]
  M.add x (List.fold_left (fun acc x => M.add x acc) l m).
Proof.
intro l. induction l; intros x m.
+ reflexivity.
+ simpl. intro.
  assert (Hf : Proper (M.eq ==> eq ==> M.eq) (fun acc y => M.add y acc)).
  { clear. intros s1 s2 Hs x y Hxy. now rewrite Hxy, Hs. }
  rewrite (@fold_left_start _ _ Logic.eq M.eq _ _ _ Hf l _ (M.add x (M.add a m))).
  apply IHl. intro. fsetdec.
Qed.

Lemma set_cons : forall x l, set (x :: l) [=] M.add x (set l).
Proof. intros x l y. unfold set. now rewrite set_cons_aux. Qed.

Lemma set_empty : forall l, set l [=] M.empty <-> l = nil.
Proof.
intro l. split; intro H.
+ destruct l as [| x l]. reflexivity. rewrite set_cons in H.
  specialize (H x). rewrite M.add_spec in H. elim (@M.empty_spec x). rewrite <- H. now left.
+ subst l. apply set_nil.
Qed.

Lemma set_app : forall l l', set (l ++ l') [=] M.union (set l) (set l').
Proof.
induction l as [| e l]; intros l'; simpl.
+ intro. fsetdec. 
+ do 2 rewrite set_cons. intro x. destruct (Loc.eq_dec x e) as [Heq | Heq].
  - rewrite Heq, M.add_spec, IHl. repeat rewrite M.union_spec. rewrite M.add_spec. tauto.
  - rewrite M.add_spec, IHl; auto. repeat rewrite M.union_spec. rewrite M.add_spec; tauto.
Qed.

Instance set_compat : Proper (PermutationA Loc.eq ==> M.eq) set.
Proof.
intro l1. induction l1 as [| x l1]; intros l2 Hperm.
+ apply (PermutationA_nil _) in Hperm. now subst.
+ assert (Hx := @PermutationA_InA_inside _ _ _ x _ _ Hperm).
  destruct Hx as [l1' [y [l2' [Hxy Heq]]]]. now left. subst l2.
  intro z. rewrite set_app, M.union_spec. do 2 rewrite set_cons.
  destruct (Loc.eq_dec x z) as [Heq | Hneq].
  - rewrite <- Heq, <- Hxy. repeat rewrite M.add_spec. intuition.
  - rewrite <- (PermutationA_middle _), Hxy in Hperm. apply (PermutationA_cons_inv _) in Hperm.
    repeat rewrite M.add_spec. rewrite (IHl1 _ Hperm). rewrite set_app, M.union_spec, <- Hxy. intuition.
Qed.

Lemma set_PermutationA : forall x l,
  exists l' n, ~InA Loc.eq x l' /\ PermutationA Loc.eq l (alls x n ++ l').
Proof.
intros x l. induction l.
* exists nil, 0. split. now auto. simpl. reflexivity.
* destruct IHl as [l' [n [Hin Hperm]]]. destruct (Loc.eq_dec a x) as [Heq | Heq].
  + exists l', (S n). split; trivial. simpl. apply PermutationA_cons; assumption.
  + exists (a :: l'), n. split.
    - intro Habs. inversion_clear Habs. elim Heq. now symmetry. contradiction.
    - rewrite Hperm. apply (PermutationA_middle _).
Qed.

Lemma set_alls : forall x n, 0 < n -> set (alls x n) [=] M.singleton x.
Proof.
intros x n Hn. induction n; simpl.
+ inversion Hn.
+ rewrite set_cons. destruct n.
  - simpl. rewrite set_nil. intro. fsetdec.
  - rewrite IHn. intro. fsetdec. omega.
Qed.

Theorem set_spec : forall x l, M.In x (set l) <-> InA Loc.eq x l.
Proof.
intros x l. induction l.
+ rewrite set_nil. intuition.
+ rewrite set_cons, M.add_spec. intuition. inversion_clear H1; auto.
Qed.

Theorem cardinal_set : forall l, M.cardinal (set l) <= length l.
Proof.
induction l as [| x l]; simpl.
+ now rewrite set_nil.
+ rewrite set_cons. destruct (M.mem x (set l)) eqn:Hmem.
  - apply MProp.add_cardinal_1 in Hmem. omega.
  - apply MProp.add_cardinal_2 in Hmem. omega.
Qed.


Instance elements_compat : Proper (M.eq ==> PermutationA Loc.eq) M.elements.
Proof.
  intros s1 s2 Heq.
  assert (Equivalence Loc.eq).
  auto with typeclass_instances.
  apply NoDupA_equivlistA_PermutationA. assumption.
  now apply M.elements_spec2w. now apply M.elements_spec2w.
  intro x. do 2 rewrite M.elements_spec1.
  now rewrite Heq.
Qed.


(** Building a spectrum from a configuration *)

(** Inclusion is not possible because M already contains a function [is_ok]. *)
Definition t := M.t.
Definition eq := M.eq.
Definition eq_equiv := M.eq_equiv.
Definition eq_dec := M.eq_dec.
Definition In := M.In.

Definition from_config conf : M.t := set (Config.list conf).

Instance from_config_compat : Proper (Config.eq ==> M.eq) from_config.
Proof.
repeat intro. unfold from_config. do 2 f_equiv.
apply eqlistA_PermutationA_subrelation, Config.list_compat. assumption.
Qed.

Definition is_ok s conf := forall l, In l s <-> exists id : Names.ident, Loc.eq l (conf id).

Theorem from_config_spec : forall conf, is_ok (from_config conf) conf.
Proof. unfold from_config, is_ok. intros. rewrite set_spec, Config.list_InA. reflexivity. Qed.

Definition map f m := M.fold (fun x acc => M.add (f x) acc) m M.empty.

Instance fold_compat :
    forall f, Proper (Loc.eq ==> eq ==> eq) f -> transpose eq f ->
    forall a, Proper (eq ==> eq) (fun x => M.fold f x a).
Proof.
  intros f Hf Ht a m1 m2 Heq.
  do 2 rewrite M.fold_spec.
  rewrite fold_left_symmetry_PermutationA.
  + reflexivity.
  + now apply Loc.eq_equiv.
  + apply eq_equiv.
  + repeat intro. now apply Hf; rewrite H || rewrite H0.
  + intros. apply Ht.
  + apply NoDupA_equivlistA_PermutationA.
    - now apply Loc.eq_equiv.
    - eapply NoDupA_strengthen; try apply M.elements_spec2w. apply subrelation_refl.
    - eapply NoDupA_strengthen; try apply M.elements_spec2w. apply subrelation_refl.
    - clear -Heq. intros x. now rewrite Heq.
  + apply eq_equiv.
Qed.
  
Instance map_compat : forall f, Proper (Loc.eq ==> Loc.eq) f -> Proper (eq ==> eq) (map f).
Proof.
  intros f Hf m₁ m₂ Hm. unfold map.
  apply fold_compat.
  - repeat intro. rewrite H0. now rewrite H.
  - repeat intro. now rewrite MProp.MP.add_add.
  - assumption.
Qed.

Lemma map_empty : forall f, Proper (Loc.eq ==> Loc.eq) f -> map f M.empty [=] M.empty.
Proof.
  intros f Hf. unfold map.
  unfold M.fold. unfold M.Raw.fold.
  now simpl.
Qed.

Lemma map_In : forall f, Proper (Loc.eq ==> Loc.eq) f -> forall x m,
      M.In x m -> M.In (f x) (map f m).
Proof.
  intros f Hf x m.
  unfold map.  
  apply MProp.MP.fold_rec_bis.
  + intros s s' a Heq IH Hin.
    apply IH.
    now rewrite Heq.
  + intro Hin.
    apply MProp.MP.Dec.F.empty_iff in Hin.
    elim Hin.
  + intros a s s' Hina Hnotinta IH Hinx.
    destruct (Loc.eq_dec x a).
    - rewrite e. now apply F.add_1.
    - apply F.add_2.
      apply IH.
      apply F.add_3 with (x := a).
      intro Heq. apply n. now rewrite Heq.
      assumption.
Qed.
      
Lemma map_add : forall f, Proper (Loc.eq ==> Loc.eq) f -> forall x m, map f (M.add x m) [=] M.add (f x) (map f m).
Proof.
  intros f Hf x m y.
  destruct (MSetDecideAuxiliary.dec_In x m).
  + unfold map at 1. rewrite MProp.MP.add_fold.
    - assert (M.In (f x) (map f m)).
      { now apply map_In. }
      now rewrite MProp.MP.add_equal.
    - apply eq_equiv.
    - repeat intro. now rewrite H0, H1.
    - repeat intro. now rewrite MProp.MP.add_add.
    - assumption.
  + unfold map at 1. rewrite MProp.MP.fold_add.
    - reflexivity.
    - apply eq_equiv.
    - repeat intro. now rewrite H0, H1.
    - repeat intro. now rewrite MProp.MP.add_add.
    - assumption.
Qed.

Theorem set_map : forall f, Proper (Loc.eq ==> Loc.eq) f ->
                            forall l, set (List.map f l) [=] map f (set l).
Proof.
intros f Hf l.
induction l; simpl.
+ now rewrite set_nil, map_empty.
+ do 2 rewrite set_cons. now rewrite map_add, IHl.
Qed.


Lemma from_config_map : forall f, Proper (Loc.eq ==> Loc.eq) f ->
  forall conf, eq (map f (from_config conf)) (from_config (Config.map f conf)).
Proof. repeat intro. unfold from_config.
       now rewrite Config.list_map, set_map.
Qed.


End Make.
