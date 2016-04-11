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
Require MMultisetInterface.
Require MMultisetExtraOps.
Require MMultisetWMap.
Require Import Pactole.Preliminary.
Require Pactole.Robots.
Require Import Pactole.Configurations.


Module Make(Location : RealMetricSpace)(N : Robots.Size) <: Spectrum (Location)(N).

Module Names := Robots.Make(N).
Module Config := Configurations.Make(Location)(N)(Names).

Instance Loc_compat : Proper (Config.eq_RobotConf ==> Location.eq) Config.Loc.
Proof. intros [] [] []. now cbn. Qed.

Instance Sta_compat : Proper (Config.eq_RobotConf ==> eq) Config.Sta.
Proof. intros [] [] []. now cbn. Qed.

(** Definition of spectra as multisets of locations. *)
Module Mraw := MMultisetWMap.FMultisets MMapWeakList.Make Location.
Module M := MMultisetExtraOps.Make Location Mraw.

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

Definition multiset l := M.from_elements (List.map (fun x => (x, 1)) l).

Lemma multiset_nil : multiset nil [=] M.empty.
Proof. reflexivity. Qed.

Lemma multiset_cons : forall x l, multiset (x :: l) [=] M.add x 1 (multiset l).
Proof. reflexivity. Qed.

Lemma multiset_empty : forall l, multiset l [=] M.empty <-> l = nil.
Proof.
intro l. unfold multiset. rewrite M.from_elements_empty.
destruct l; simpl; split; intro H; inversion_clear H; intuition; discriminate.
Qed.

Lemma multiset_app : forall l l', multiset (l ++ l') [=] M.union (multiset l) (multiset l').
Proof. intros. unfold multiset. now rewrite map_app, M.from_elements_append. Qed.

Lemma location_neq_sym: forall x y, ~ Location.eq x y -> ~ Location.eq y x.
Proof. intros x y H Habs. now symmetry in Habs. Qed.

Instance multiset_compat : Proper (PermutationA Location.eq ==> M.eq) multiset.
Proof.
intros l1 l2 Hl. eapply M.from_elements_compat, PermutationA_map; eauto; refine _; [].
repeat intro; now split.
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
      rewrite plus_comm in Hin. cbn in Hin. apply eq_add_S in Hin. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
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
Proof. intros f Hf l x. unfold multiset. now rewrite map_map, M.map_from_elements, map_map. Qed.

Theorem multiset_filter : forall f, Proper (Location.eq ==> Logic.eq) f ->
  forall l, multiset (filter f l) [=] M.filter f (multiset l).
Proof.
intros f Hf l. induction l as [| e l]; simpl.
+ rewrite (@M.filter_compat f Hf (multiset nil)), multiset_nil. now rewrite M.filter_empty. now apply multiset_nil.
+ destruct (f e) eqn:Htest.
  - do 2 rewrite multiset_cons. rewrite M.filter_add, Htest, IHl; trivial; reflexivity || omega.
  - rewrite multiset_cons, M.filter_add, Htest, IHl; trivial; reflexivity || omega.
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

Lemma multiset_remove : forall x l,
  multiset (removeA Location.eq_dec x l) [=] M.remove x (M.multiplicity x (multiset l)) (multiset l).
Proof.
intros x l y. induction l as [| a l]; simpl.
* rewrite multiset_nil. do 2 rewrite M.empty_spec. now rewrite M.remove_0, M.empty_spec.
* rewrite multiset_cons. destruct (Location.eq_dec y x) as [Hyx | Hyx], (Location.eq_dec x a) as [Hxa | Hxa].
  + rewrite Hyx, Hxa in *. rewrite IHl. setoid_rewrite M.remove_same. setoid_rewrite M.add_same. omega.
  + rewrite Hyx in *. rewrite multiset_cons, M.add_other; auto. rewrite IHl. do 2 rewrite M.remove_same. omega.
  + rewrite Hxa in *. rewrite IHl, M.add_same. repeat rewrite M.remove_other; auto. rewrite M.add_other; auto.
  + rewrite multiset_cons. rewrite M.remove_other; auto. destruct (Location.eq_dec y a) as [Hya | Hya].
    - rewrite Hya in *. do 2 rewrite M.add_same. rewrite IHl. now rewrite M.remove_other.
    - repeat rewrite M.add_other; trivial. rewrite IHl. rewrite M.remove_other; auto.
Qed.

Lemma multiset_support : forall x l, InA Location.eq x (M.support (multiset l)) <-> InA Location.eq x l.
Proof. intros x l. rewrite M.support_spec. unfold M.In. rewrite multiset_spec. apply countA_occ_pos. refine _. Qed.


(** Building a spectrum from a configuration *)
Include M.

Definition from_config conf : t := multiset (List.map Config.Loc (Config.list conf)).

Instance from_config_compat : Proper (Config.eq ==> eq) from_config.
Proof.
intros conf1 conf2 Hconf x. unfold from_config. do 2 f_equiv.
apply eqlistA_PermutationA_subrelation, (map_extensionalityA_compat Location.eq_equiv Loc_compat).
apply Config.list_compat. assumption.
Qed.

Definition is_ok s conf := forall l,
  M.multiplicity l s = countA_occ _ Location.eq_dec l (List.map Config.Loc (Config.list conf)).

Theorem from_config_spec : forall conf, is_ok (from_config conf) conf.
Proof. unfold from_config, is_ok. intros. apply multiset_spec. Qed.

Lemma from_config_map : forall f, Proper (Location.eq ==> Location.eq) f ->
  forall conf, eq (map f (from_config conf))
  (from_config (Config.map (fun x => {| Config.Loc := f (Config.Loc x); Config.Sta := Config.Sta x|}) conf)).
Proof.
intros f Hf config. unfold from_config. rewrite Config.list_map.
- now rewrite <- multiset_map, map_map, map_map.
- intros ? ? Heq. hnf. split; cbn; try apply Hf; apply Heq.
Qed.

Theorem cardinal_from_config : forall conf, cardinal (from_config conf) = N.nG + N.nB.
Proof. intro. unfold from_config. now rewrite cardinal_multiset, map_length, Config.list_length. Qed.

Property pos_in_config : forall (config : Config.t) id, In (Config.Loc (config id)) (from_config config).
Proof.
intros conf id. unfold from_config.
unfold In. rewrite multiset_spec. rewrite (countA_occ_pos _).
rewrite InA_map_iff; autoclass. exists (conf id). split; try reflexivity; [].
setoid_rewrite Config.list_InA. now exists id.
Qed.

Property from_config_In : forall config l,
  In l (from_config config) <-> exists id, Location.eq (Config.Loc (config id)) l.
Proof.
intros config l. split; intro Hin.
+ unfold In in Hin. rewrite from_config_spec, (countA_occ_pos _), Config.list_spec in Hin.
  rewrite (InA_map_iff _ _) in Hin; [setoid_rewrite (InA_map_iff _ _) in Hin |]; try autoclass; [].
  destruct Hin as [? [Hl [id [? Hid]]]]. exists id. rewrite <- Hl. now f_equiv.
+ destruct Hin as [id Hid]. rewrite <- Hid. apply pos_in_config.
Qed.
End Make.
