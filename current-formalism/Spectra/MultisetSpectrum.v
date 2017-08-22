(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require Import Utf8_core.
Require Import Arith_base.
Require Import Omega.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.FMaps.FMapList.
Require Import Pactole.Util.MMultiset.MMultisetWMap.
Require Export Pactole.Util.MMultiset.MMultisetInterface.
Require Export Pactole.Util.MMultiset.MMultisetFacts.
Require Export Pactole.Util.MMultiset.MMultisetExtraOps.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Close Scope R_scope.
Set Implicit Arguments.
Set Default Proof Using "All".


Existing Instance multiplicity_compat.


Section MultisetSpectrum.

Context {loc : Type}.
Context {Sloc : Setoid loc} {Eloc : EqDec Sloc}.
Context {RMS : RealMetricSpace loc}.

Existing Instance FMOps_WMap.
Existing Instance MakeFMultisetsFacts.


Lemma eq_refl_left : forall (e : loc) A (a b:A), (if equiv_dec e e then a else b) = a.
Proof.
intros e A a b.
destruct (equiv_dec e e) as [| Hneq].
- reflexivity.
- now elim Hneq.
Qed.


(** **  Building multisets from lists  **)

Definition make_multiset l := from_elements (List.map (fun x => (x, 1)) l).

Lemma make_multiset_nil : make_multiset nil == empty.
Proof. reflexivity. Qed.

Lemma make_multiset_cons : forall x l, make_multiset (x :: l) == MMultisetInterface.add x 1 (make_multiset l).
Proof. reflexivity. Qed.

Lemma make_multiset_empty : forall l, make_multiset l == empty <-> l = nil.
Proof.
intro l. unfold make_multiset. rewrite from_elements_empty.
destruct l; cbn.
- intuition.
- split; intro Hl; inv Hl. discriminate.
Qed.

Lemma make_multiset_app : forall l l', make_multiset (l ++ l') == union (make_multiset l) (make_multiset l').
Proof. intros. unfold make_multiset. now rewrite List.map_app, from_elements_append. Qed.

Lemma nequiv_sym : forall x y, ~x == y -> ~y == x.
Proof.
intros x y H.
intro abs.
symmetry in abs.
contradiction.
Qed.

Instance make_multiset_compat : Proper (PermutationA equiv ==> equiv) make_multiset.
Proof.
intros ? ? ?. unfold make_multiset. f_equiv. eapply PermutationA_map; eauto.
- autoclass.
- repeat intro. split; hnf; auto.
Qed.

Lemma make_multiset_PermutationA : forall x l n, (make_multiset l)[x] = n ->
  exists l', ~InA equiv x l' /\ PermutationA equiv l (alls x n ++ l').
Proof.
intros x l. induction l; intros n Hin.
exists nil. split. now auto. rewrite make_multiset_nil, empty_spec in Hin. subst n. simpl. reflexivity.
rewrite make_multiset_cons in Hin. destruct (equiv_dec x a) as [Heq | Heq].
- setoid_rewrite <- Heq. rewrite <- Heq in Hin. rewrite add_spec in Hin. destruct n.
  + rewrite eq_refl_left in Hin.
    omega.
  + rewrite eq_refl_left in Hin.
    rewrite plus_comm in Hin. cbn in Hin. apply eq_add_S, IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
  exists l'. split. assumption. simpl. now constructor.
- rewrite add_other in Hin; auto. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
  exists (a :: l'). split. intro Hin; inversion_clear Hin; contradiction.
  transitivity (a :: alls x n ++ l'); now constructor || apply (PermutationA_middle _).
Qed.

Lemma make_multiset_alls : forall x n, make_multiset (alls x n) == singleton x n.
Proof.
intros x n. induction n.
+ now rewrite singleton_0, make_multiset_nil.
+ simpl alls. rewrite make_multiset_cons. rewrite IHn. intro y. rewrite singleton_spec.
  destruct (equiv_dec y x) as [Heq | Heq].
  - rewrite Heq, add_spec, singleton_spec.
    destruct (equiv_dec x x) as [_ | Helim]. omega. now elim Helim.
  - rewrite add_other; auto. rewrite singleton_spec.
    destruct (equiv_dec y x); trivial; []. contradiction.
Qed.

Corollary make_multiset_In : forall x l, In x (make_multiset l) <-> InA equiv x l.
Proof.
intros x l. unfold make_multiset. rewrite from_elements_In.
setoid_rewrite InA_map_iff; autoclass.
+ split; intro Hin.
  - destruct Hin as [n [[y [[Heq _] Hy]] Hn]]. hnf in *. cbn in *. now rewrite <- Heq.
  - exists 1. split; try omega; []. now exists x.
+ intros ? ? Heq. now split.
Qed.

Theorem make_multiset_map : forall f, Proper (equiv ==> equiv) f ->
  forall l, make_multiset (List.map f l) == map f (make_multiset l).
Proof. intros. unfold make_multiset. now rewrite map_from_elements, map_map, map_map. Qed.

Theorem make_multiset_filter : forall f, Proper (equiv ==> Logic.eq) f ->
  forall l, make_multiset (List.filter f l) == filter f (make_multiset l).
Proof.
intros f Hf l. induction l as [| e l].
+ intro. rewrite (filter_compat Hf), make_multiset_nil; try apply make_multiset_nil; [].
  now rewrite filter_empty.
+ simpl List.filter. destruct (f e) eqn:Htest.
  - do 2 rewrite make_multiset_cons. rewrite filter_add, Htest, IHl; trivial; reflexivity || omega.
  - rewrite make_multiset_cons, filter_add, Htest, IHl; trivial; reflexivity || omega.
Qed.

Theorem cardinal_make_multiset : forall l, cardinal (make_multiset l) = length l.
Proof.
induction l.
+ now rewrite make_multiset_nil, cardinal_empty.
+ rewrite make_multiset_cons, cardinal_add. simpl. apply f_equal, IHl.
Qed.

Theorem make_multiset_spec : forall x l, (make_multiset l)[x] = countA_occ _ equiv_dec x l.
Proof.
intros x l. induction l.
+ rewrite make_multiset_nil. now rewrite empty_spec.
+ rewrite make_multiset_cons. simpl countA_occ. destruct (equiv_dec a x) as [Heq | Hneq].
  - rewrite <- Heq at 1. rewrite add_spec, eq_refl_left, Heq, IHl. omega.
  - apply nequiv_sym in Hneq. rewrite add_other. now apply IHl. assumption.
Qed.

Lemma make_multiset_remove : forall x l,
  make_multiset (removeA equiv_dec x l) == remove x (make_multiset l)[x] (make_multiset l).
Proof.
intros x l y. induction l as [| a l].
* rewrite make_multiset_nil. rewrite empty_spec. now rewrite remove_0, empty_spec.
* rewrite make_multiset_cons. simpl removeA.
  destruct (equiv_dec y x) as [Hyx | Hyx], (equiv_dec x a) as [Hxa | Hxa].
  + rewrite Hyx, Hxa in *. rewrite IHl. setoid_rewrite remove_same. rewrite Hxa, add_same. omega.
  + rewrite Hyx in *. rewrite make_multiset_cons, add_other; auto.
    rewrite IHl. do 2 rewrite remove_same. simpl. omega.
  + rewrite IHl. repeat rewrite remove_other; auto; [].
    rewrite Hxa in *. rewrite add_other; auto.
  + rewrite make_multiset_cons. rewrite remove_other; auto. destruct (equiv_dec y a) as [Hya | Hya].
    - rewrite Hya in *. do 2 rewrite add_same. rewrite IHl. now rewrite remove_other.
    - repeat rewrite add_other; trivial. rewrite IHl. rewrite remove_other; auto.
Qed.

Lemma make_multiset_support : forall x l, InA equiv x (support (make_multiset l)) <-> InA equiv x l.
Proof.
intros x l. rewrite support_spec. unfold In.
rewrite make_multiset_spec. apply countA_occ_pos. autoclass.
Qed.

(** Building a spectrum from a configuration *)

Context {info: Type}.
Context {Sinfo : Setoid info} {Einfo : EqDec Sinfo}.
Context {Info : Information loc info}.
Context {Robots : Names}.

Notation configuration := (@configuration loc info _ _ _ _ _ _ _).
Notation map_config := (@map_config loc info _ _ _ _ _ _ _).
Notation config_list := (@config_list loc info _ _ _ _ Info Robots _).


Global Instance multiset_spectrum : Spectrum loc info := {
  spectrum := @multiset loc _ _ _;
  spectrum_Setoid := @MMultiset_Setoid loc _ _ _;
  spectrum_EqDec := @MMultisetEqDec loc _ _ _ _;
  
  spect_from_config config := make_multiset (List.map fst (config_list config));
  spect_is_ok s config := forall l, s[l] = countA_occ _ equiv_dec l (List.map fst (config_list config)) }.
Proof.
(* BUG?: bullet forbidden here? *)
{ intros conf1 conf2 Hconf x. unfold spect_from_config. do 2 f_equiv.
  apply eqlistA_PermutationA_subrelation, (@map_eqlistA_compat _ _ equiv equiv _ fst).
  - now repeat intros [].
  - apply config_list_compat. assumption. }
+ unfold spect_from_config, spect_is_ok. intros. apply make_multiset_spec.
Defined.

Notation spectrum := (@spectrum loc info _ _ _ _ _ _ _).
Notation spect_from_config := (@spect_from_config loc info _ _ _ _ _ _ multiset_spectrum).


Lemma spect_from_config_map  : forall f, Proper (equiv ==> equiv) f ->
  forall config : configuration,
  map f (spect_from_config config) == spect_from_config (map_config f config).
Proof.
repeat intro. unfold spect_from_config, multiset_spectrum.
now rewrite config_list_map, map_map, <- make_multiset_map, map_map.
Qed.

Theorem cardinal_spect_from_config : forall conf, cardinal (spect_from_config conf) = nG + nB.
Proof.
intro. unfold spect_from_config, multiset_spectrum.
now rewrite cardinal_make_multiset, map_length, config_list_length.
Qed.

Property pos_in_config : forall conf id, In (fst (conf id)) (spect_from_config conf).
Proof.
intros conf id. cbn. unfold In.
rewrite make_multiset_spec. rewrite (countA_occ_pos _).
rewrite InA_map_iff. 
- eexists. split; auto; []. apply config_list_InA. now exists id.
- autoclass.
- autoclass.
- now repeat intros [].
Qed.

Property spect_from_config_In : forall config l,
  In l (spect_from_config config) <-> exists id, fst (config id) == l.
Proof.
intros config l. split; intro Hin.
+ assert (Heq := spect_from_config_spec config).
  unfold spect_is_ok, spect_from_config, multiset_spectrum in *.
  unfold In in Hin. rewrite Heq, (countA_occ_pos _), config_list_spec in Hin.
  rewrite map_map, (InA_map_iff _ _) in Hin.
  - firstorder.
  - repeat intro. cbn in *. now subst.
+ destruct Hin as [id Hid]. rewrite <- Hid. apply pos_in_config.
Qed.

End MultisetSpectrum.

Global Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
