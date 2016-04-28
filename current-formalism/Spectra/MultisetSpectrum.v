(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require MMapWeakList. (* to build an actual implementation of multisets *)
Require Import Utf8_core.
Require Import Arith_base.
Require Import Omega.
Require Import SetoidList.
Require MMultisetInterface.
Require MMultisetExtraOps.
Require MMultisetWMap.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Spectra.Definition.
Require Import Pactole.Spaces.RealMetricSpaces.


Context {loc : Type}.
Context {Sloc : Setoid loc}.
Context {ESloc : EqDec Sloc}.
Context {RMS : @RealMetricSpace loc Sloc ESloc}.
Context {Ndef : NamesDef}.
Context {N : Names}.
Context {Spect : @Spectrum loc Sloc ESloc Ndef N}.


Module Location : Equalities.DecidableType with Definition t := loc
                                           with Definition eq := @equiv loc _
                                           with Definition eq_dec := @equiv_dec loc _ _.
  Definition t := loc.
  Definition eq := @equiv loc _.
  Definition eq_dec := @equiv_dec loc _ _.
  Definition eq_equiv := @setoid_equiv _ _.
End Location.


Instance Make : Spectrum loc.

(** Definition of spectra as multisets of locations. *)
Module SpectRaw := MMultisetWMap.FMultisets MMapWeakList.Make Location.
Module Spect := MMultisetExtraOps.Make Location SpectRaw.

Notation "m1  ≡  m2" := (Spect.eq m1 m2) (at level 70).
Notation "m1  ⊆  m2" := (Spect.Subset m1 m2) (at level 70).
Notation "m1  [=]  m2" := (Spect.eq m1 m2) (at level 70, only parsing).
Notation "m1  [c=]  m2" := (Spect.Subset m1 m2) (at level 70, only parsing).

Lemma eq_refl_left : forall e A (a b:A), (if Location.eq_dec e e then a else b) = a.
Proof.
  intros e A a b.
  destruct (Location.eq_dec e e).
  - reflexivity.
  - elim n.
    reflexivity.
Qed.


(** **  Building multisets from lists  **)

(* TODO: should be replaced by Spect.from_elements *)
Definition multiset l := Spect.from_elements (List.map (fun x => (x, 1)) l).

Lemma multiset_nil : multiset nil [=] Spect.empty.
Proof. reflexivity. Qed.

Lemma multiset_cons : forall x l, multiset (x :: l) [=] Spect.add x 1 (multiset l).
Proof. reflexivity. Qed.

Lemma multiset_empty : forall l, multiset l [=] Spect.empty <-> l = nil.
Proof.
intro l. unfold multiset. rewrite Spect.from_elements_empty.
destruct l; cbn.
- intuition.
- split; intro Hl; inv Hl. discriminate.
Qed.

Lemma multiset_app : forall l l', multiset (l ++ l') [=] Spect.union (multiset l) (multiset l').
Proof. intros. unfold multiset. now rewrite map_app, Spect.from_elements_append. Qed.

Lemma location_neq_sym: forall x y, ~ Location.eq x y -> ~ Location.eq y x.
Proof.
  intros x y H.
  intro abs.
  symmetry in abs.
  contradiction.
Qed.

Instance multiset_compat : Proper (PermutationA Location.eq ==> Spect.eq) multiset.
Proof.
intros ? ? ?. unfold multiset. f_equiv. eapply PermutationA_map; eauto.
- autoclass.
- repeat intro. split; hnf; auto.
Qed.

Lemma multiset_PermutationA : forall x l n, Spect.multiplicity x (multiset l) = n ->
  exists l', ~InA Location.eq x l' /\ PermutationA Location.eq l (alls x n ++ l').
Proof.
intros x l. induction l; intros n Hin.
  exists nil. split. now auto. rewrite multiset_nil, Spect.empty_spec in Hin. subst n. simpl. reflexivity.
  rewrite multiset_cons in Hin. destruct (Location.eq_dec x a) as [Heq | Heq].
  - setoid_rewrite <- Heq. rewrite <- Heq in Hin. rewrite Spect.add_spec in Hin. destruct n.
    + rewrite eq_refl_left in Hin.
      omega.
    + rewrite eq_refl_left in Hin.
      rewrite plus_comm in Hin. cbn in Hin. apply eq_add_S in Hin. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
    exists l'. split. assumption. simpl. now constructor.
  - rewrite Spect.add_other in Hin; auto. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
    exists (a :: l'). split. intro Hin; inversion_clear Hin; contradiction.
    transitivity (a :: alls x n ++ l'); now constructor || apply (PermutationA_middle _).
Qed.

Lemma multiset_alls : forall x n, multiset (alls x n) [=] Spect.singleton x n.
Proof.
intros x n. induction n; simpl.
+ now rewrite Spect.singleton_0, multiset_nil.
+ rewrite multiset_cons. rewrite IHn. intro y. rewrite Spect.singleton_spec.
  destruct (Location.eq_dec y x) as [Heq | Heq].
  - rewrite Heq, Spect.add_spec, Spect.singleton_spec.
    destruct (Location.eq_dec x x) as [_ | Helim]. omega. now elim Helim.
  - rewrite Spect.add_other; auto. rewrite Spect.singleton_spec.
    destruct (Location.eq_dec y x); trivial; []. contradiction.
Qed.

Corollary multiset_In : forall x l, Spect.In x (multiset l) <-> InA Location.eq x l.
Proof.
intros x l. unfold multiset. rewrite Spect.from_elements_In.
setoid_rewrite InA_map_iff; autoclass.
+ split; intro Hin.
  - destruct Hin as [n [[y [[Heq _] Hy]] Hn]]. hnf in *. cbn in *. now rewrite <- Heq.
  - exists 1. firstorder.
+ intros ? ? Heq. now split.
Qed.

Theorem multiset_map : forall f, Proper (Location.eq ==> Location.eq) f ->
  forall l, multiset (map f l) [=] Spect.map f (multiset l).
Proof. intros. unfold multiset. now rewrite Spect.map_from_elements, map_map, map_map. Qed.

Theorem multiset_filter : forall f, Proper (Location.eq ==> Logic.eq) f ->
  forall l, multiset (filter f l) [=] Spect.filter f (multiset l).
Proof.
intros f Hf l. induction l as [| e l]; simpl.
+ rewrite (@Spect.filter_compat f Hf (multiset nil)), multiset_nil.
  now rewrite Spect.filter_empty. now apply multiset_nil.
+ destruct (f e) eqn:Htest.
  - do 2 rewrite multiset_cons. rewrite Spect.filter_add, Htest, IHl; trivial; reflexivity || omega.
  - rewrite multiset_cons, Spect.filter_add, Htest, IHl; trivial; reflexivity || omega.
Qed.

Theorem cardinal_multiset : forall l, Spect.cardinal (multiset l) = length l.
Proof.
induction l; simpl.
+ now rewrite multiset_nil, Spect.cardinal_empty.
+ rewrite multiset_cons, Spect.cardinal_add. apply f_equal, IHl.
Qed.

Theorem multiset_spec : forall x l, Spect.multiplicity x (multiset l) = countA_occ _ Location.eq_dec x l.
Proof.
intros x l. induction l; simpl.
+ rewrite multiset_nil. now apply Spect.empty_spec.
+ rewrite multiset_cons. destruct (Location.eq_dec a x) as [Heq | Hneq].
  - rewrite Heq. rewrite Spect.add_spec. rewrite IHl.
    rewrite eq_refl_left.
    omega.
  - apply location_neq_sym in Hneq. rewrite Spect.add_other. now apply IHl. assumption.
Qed.

Lemma multiset_remove : forall x l,
  multiset (removeA Location.eq_dec x l) [=] Spect.remove x (Spect.multiplicity x (multiset l)) (multiset l).
Proof.
intros x l y. induction l as [| a l]; simpl.
* rewrite multiset_nil. do 2 rewrite Spect.empty_spec. now rewrite Spect.remove_0, Spect.empty_spec.
* rewrite multiset_cons. destruct (Location.eq_dec y x) as [Hyx | Hyx], (Location.eq_dec x a) as [Hxa | Hxa].
  + rewrite Hyx, Hxa in *. rewrite IHl. setoid_rewrite Spect.remove_same. setoid_rewrite Spect.add_same. omega.
  + rewrite Hyx in *. rewrite multiset_cons, Spect.add_other; auto.
    rewrite IHl. do 2 rewrite Spect.remove_same. omega.
  + rewrite Hxa in *. rewrite IHl, Spect.add_same.
    repeat rewrite Spect.remove_other; auto. rewrite Spect.add_other; auto.
  + rewrite multiset_cons. rewrite Spect.remove_other; auto. destruct (Location.eq_dec y a) as [Hya | Hya].
    - rewrite Hya in *. do 2 rewrite Spect.add_same. rewrite IHl. now rewrite Spect.remove_other.
    - repeat rewrite Spect.add_other; trivial. rewrite IHl. rewrite Spect.remove_other; auto.
Qed.

Lemma multiset_support : forall x l, InA Location.eq x (Spect.support (multiset l)) <-> InA Location.eq x l.
Proof.
intros x l. rewrite Spect.support_spec. unfold Spect.In.
rewrite multiset_spec. apply countA_occ_pos. autoclass.
Qed.

(** Building a spectrum from a configuration *)

Instance multiset_spectrum : Spectrum loc := {|
  spectrum := Spect.t;
  SpectSetoid := {| equiv := Spect.eq |};
  SpectEqDec := Spect.MProp.eq_dec;
  
  spect_from_config conf := multiset (config_list conf);
  spect_is_ok s conf := forall l, Spect.multiplicity l s = countA_occ _ Location.eq_dec l (config_list conf) |}.
Proof.
* autoclass.
* intros conf1 conf2 Hconf x. unfold spect_from_config. do 2 f_equiv.
  apply eqlistA_PermutationA_subrelation. apply config_list_compat. assumption.
* unfold spect_from_config, spect_is_ok. intros. apply multiset_spec.
Defined.

Lemma spect_from_config_map  : forall f, Proper (equiv ==> equiv) f ->
  forall config : configuration,
  @equiv spectrum SpectSetoid (Spect.map f (spect_from_config config)) (spect_from_config (map_config f config)).
Proof. repeat intro. unfold spect_from_config. cbn. now rewrite config_list_map, multiset_map. Qed.

Theorem cardinal_spect_from_config : forall conf, Spect.cardinal (spect_from_config conf) = nG + nB.
Proof. intro. unfold spect_from_config. cbn. now rewrite cardinal_multiset, config_list_length. Qed.

Property pos_in_config : forall conf id, Spect.In (conf id) (spect_from_config conf).
Proof.
intros conf id. cbn. unfold Spect.In.
rewrite multiset_spec. rewrite (countA_occ_pos _).
unfold Location.eq. rewrite config_list_InA. now exists id.
Qed.

Property spect_from_config_In : forall config l,
  Spect.In l (spect_from_config config) <-> exists id, equiv (config id) l.
Proof.
intros config l. split; intro Hin.
+ unfold Spect.In in Hin. assert (Heq := spect_from_config_spec config). cbn in Heq.
  rewrite Heq, (countA_occ_pos _), config_list_spec in Hin.
  rewrite (InA_map_iff _ _) in Hin.
  - firstorder.
  - repeat intro. cbn in *. now subst.
+ destruct Hin as [id Hid]. rewrite <- Hid. apply pos_in_config.
Qed.

