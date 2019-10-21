(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)

Require Import Utf8_core.
Require Import Omega.
Require Import SetoidList.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.FSets.FSetList.
Require Export Pactole.Util.FSets.FSetInterface.
Require Export Pactole.Util.FSets.FSetFacts.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.Configurations.
Require Import Pactole.Core.RobotInfo.
Require Import Pactole.Observations.Definition.


Section SetConstruction.

Context {loc : Type}.
Context `{EqDec loc}.

(* FIXME: tauto introduces spurious axioms: Eq_dep.eq_rect_eq and excluded middle. *)
Ltac fsetdec := set_iff; tauto.

(** **  Building sets from lists  **)

Definition make_set l := fold_left (fun acc x => add x acc) l empty.

Lemma make_set_nil : make_set nil == empty.
Proof. reflexivity. Qed.

Lemma make_set_cons_aux : forall l x m,
  List.fold_left (fun acc y => add y acc) (x :: l) m ==
  add x (List.fold_left (fun acc x => add x acc) l m).
Proof.
intro l. induction l as [| e l]; intros x s.
+ reflexivity.
+ simpl fold_left.
  assert (Hf : Proper (equiv ==> equiv ==> equiv) (fun acc y => add y acc)).
  { clear x. intros s1 s2 Hs x y Hxy. now rewrite Hxy, Hs. }
  rewrite (@fold_left_start _ _ equiv equiv _ _ Hf l _ (add x (add e s))).
  apply IHl. intro. fsetdec.
Qed.

Lemma make_set_cons : forall x l, make_set (x :: l) == add x (make_set l).
Proof. intros x l. unfold make_set. now rewrite make_set_cons_aux. Qed.

Lemma make_set_empty : forall l, make_set l == empty <-> l = nil.
Proof.
intro l. split; intro Hl.
+ destruct l as [| x l]. reflexivity. rewrite make_set_cons in Hl.
  specialize (Hl x). rewrite add_spec, empty_spec in Hl.
  exfalso. rewrite <- Hl. now left.
+ subst l. apply make_set_nil.
Qed.

Lemma make_set_app : forall l l', make_set (l ++ l') == union (make_set l) (make_set l').
Proof.
induction l as [| e l]; intros l'.
+ rewrite make_set_nil. simpl. intro. fsetdec.
+ simpl List.app. rewrite 2 make_set_cons, IHl. intro. fsetdec.
Qed.

Instance make_set_compat : Proper (PermutationA equiv ==> equiv) make_set.
Proof.
intro l1. induction l1 as [| x l1]; intros l2 Hperm.
+ apply (PermutationA_nil _) in Hperm. now subst.
+ assert (Hx := @PermutationA_InA_inside _ _ _ x _ _ Hperm).
  destruct Hx as [l1' [y [l2' [Hxy Heq]]]]. now left. subst l2.
  intro z. rewrite make_set_app, union_spec, 2 make_set_cons.
  destruct (x =?= z) as [Heq | Hneq].
  - rewrite Heq in *. rewrite <- Hxy. repeat rewrite add_spec. intuition.
  - rewrite <- (PermutationA_middle _), Hxy in Hperm. apply (PermutationA_cons_inv _) in Hperm.
    repeat rewrite add_spec. rewrite (IHl1 _ Hperm). rewrite make_set_app, Hxy. fsetdec.
Qed.

Lemma make_set_PermutationA : forall x l,
  exists l' n, ~InA equiv x l' /\ PermutationA equiv l (alls x n ++ l').
Proof.
intros x l. induction l as [| e l].
* exists nil, 0. split. now auto. simpl. reflexivity.
* destruct IHl as [l' [n [Hin Hperm]]]. destruct (e =?= x) as [Heq | Heq].
  + exists l', (S n). split; trivial. simpl. apply PermutationA_cons; assumption.
  + exists (e :: l'), n. split.
    - intro Habs. inversion_clear Habs. elim Heq. now symmetry. contradiction.
    - rewrite Hperm. apply (PermutationA_middle _).
Qed.

Lemma make_set_alls : forall x n, 0 < n -> make_set (alls x n) == singleton x.
Proof.
intros x n Hn. induction n; simpl alls.
+ inversion Hn.
+ rewrite make_set_cons. destruct n.
  - simpl alls. rewrite make_set_nil. intro. fsetdec.
  - rewrite IHn. intro. fsetdec. omega.
Qed.

Theorem make_set_spec : forall x l, In x (make_set l) <-> InA equiv x l.
Proof.
intros x l. induction l.
+ rewrite make_set_nil, InA_nil. fsetdec.
+ rewrite make_set_cons, add_spec, IHl, InA_cons. split; intros [|]; auto.
Qed.

Theorem cardinal_make_set : forall l, cardinal (make_set l) <= length l.
Proof.
induction l as [| x l]; simpl.
+ now rewrite make_set_nil, cardinal_empty.
+ transitivity (S (cardinal (make_set l))); try omega; [].
  rewrite make_set_cons, 2 cardinal_spec.
  change (S (length (elements (make_set l))))
    with (length (x :: elements (make_set l))).
  apply NoDupA_inclA_length with equiv.
  - autoclass.
  - apply elements_NoDupA.
  - apply elements_add_incl.
Qed.

Theorem cardinal_NoDupA_make_set : forall l, NoDupA equiv l -> cardinal (make_set l) = length l.
Proof.
intros l Hl. induction l as [| x l]; simpl.
- now rewrite make_set_nil, cardinal_empty.
- inv Hl. rewrite <- IHl; trivial; [].
  rewrite make_set_cons, cardinal_add; trivial; [].
  now rewrite make_set_spec.
Qed.

Theorem make_set_map : forall f, Proper (equiv ==> equiv) f ->
  forall l, make_set (List.map f l) == map f (make_set l).
Proof.
intros f Hf l. induction l; simpl List.map.
+ now rewrite make_set_nil, map_empty.
+ do 2 rewrite make_set_cons. now rewrite map_add, IHl.
Qed.

End SetConstruction.

(** Building an observation from a configuration *)

Require Pactole.Spaces.RealMetricSpace.

Section SetObservation.

Context `{State}.
Context `{Names}.

Implicit Type config : configuration.

Global Instance set_observation : Observation := {
  observation := set location;
  
  obs_from_config config pt := make_set (List.map get_location (config_list config));
  obs_is_ok s config pt :=
    forall l, In l s <-> InA equiv l (List.map get_location (config_list config)) }.
Proof.
+ repeat intro.
  apply make_set_compat, eqlistA_PermutationA_subrelation,
        (@map_eqlistA_compat _ _ equiv equiv _ get_location).
  - autoclass.
  - apply config_list_compat. assumption.
+ unfold obs_from_config, obs_is_ok. intros. apply make_set_spec.
Defined.
(* TODO: remove the use of classical logic
Print Assumptions  set_observation.
Print Assumptions make_set_spec. *)

Notation obs_from_config := (@obs_from_config _ _ _ _ set_observation).

Lemma obs_from_config_ignore_snd : forall ref_state config state,
  obs_from_config config state == obs_from_config config ref_state.
Proof. reflexivity. Qed.

Lemma obs_from_config_map : forall f Pf, Proper (equiv ==> equiv) f ->
  forall config pt,
  map f (obs_from_config config pt)
  == obs_from_config (map_config (lift (existT _ f Pf)) config) (lift (existT _ f Pf) pt).
Proof.
repeat intro. unfold obs_from_config, set_observation.
rewrite config_list_map, map_map, <- make_set_map, map_map.
+ apply make_set_compat, eqlistA_PermutationA_subrelation.
  assert (Hequiv : (@equiv info _ ==> @equiv location _)%signature
                     (fun x => f (get_location x)) (fun x => get_location (lift (existT _ f Pf) x))).
  { intros pt1 pt2 Heq. now rewrite get_location_lift, Heq. }
  now apply (map_extensionalityA_compat _ Hequiv).
+ assumption.
+ now apply lift_compat.
Qed.

Theorem cardinal_obs_from_config : forall config state,
  cardinal (obs_from_config config state) <= nG + nB.
Proof.
intros. unfold obs_from_config, set_observation.
etransitivity; try apply cardinal_make_set; [].
now rewrite map_length, config_list_length.
Qed.

Property pos_in_config : forall config state id,
  In (get_location (config id)) (obs_from_config config state).
Proof.
intros config state id. unfold obs_from_config. simpl.
rewrite make_set_spec, InA_map_iff; autoclass; [].
eexists. split; auto; []. apply config_list_InA. now exists id.
Qed.

Property obs_from_config_In : forall config pt l,
  In l (obs_from_config config pt) <-> exists id, get_location (config id) == l.
Proof.
intros config pt l. split; intro Hin.
+ assert (Heq := obs_from_config_spec config pt).
  unfold obs_is_ok, obs_from_config, set_observation in *.
  rewrite Heq, config_list_spec, map_map, (InA_map_iff _ _) in Hin.
  - firstorder.
  - repeat intro. cbn in *. now subst.
+ destruct Hin as [id Hid]. rewrite <- Hid. apply pos_in_config.
Qed.

End SetObservation.
