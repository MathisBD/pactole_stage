(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(** Mechanised Framework for Local Interactions & Distributed Algorithms    
    T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                          
                                                                            
    PACTOLE project                                                         
                                                                            
    This file is distributed under the terms of the CeCILL-C licence      *)
(**************************************************************************)

Require Import Utf8_core.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Rbase.
Require Import Pactole.Util.FSets.FSetInterface.
Require Import Pactole.Util.FSets.FSetFacts.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Core.Identifiers.
Require Import Pactole.Core.State.
Require Import Pactole.Core.Configuration.
Require Import Pactole.Observations.Definition.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.
Require Pactole.Observations.SetObservation.
Coercion Bijection.section : Bijection.bijection >-> Funclass.


Section LimitedSetObservation.

Context `{State}.
Context (RVS : @RealVectorSpace _ _ (location_EqDec)).
Context {RMS : @RealMetricSpace _ _ _ RVS}.
Context `{Names}.

Implicit Type config : configuration.

Instance limited_set_observation (radius : R) : Observation.
simple refine {|
  observation := set location;
  obs_from_config config state :=
    SetObservation.make_set (List.filter
                               (fun x => Rle_bool (dist x (get_location state)) radius)
                               (List.map get_location (config_list config)));
  obs_is_ok s config state :=
    forall l, In l s <-> InA equiv l (List.map get_location (config_list config))
                         /\ (dist l (get_location state) <= radius)%R |}; autoclass; [|].
Proof.
* intros config1 config2 Hconfig pt1 pt2 Hpt.
  apply SetObservation.make_set_compat, eqlistA_PermutationA_subrelation.
  f_equiv.
  + intros ? ? Heq. now rewrite Heq, Hpt.
  + apply (@map_eqlistA_compat _ _ equiv equiv _ get_location); autoclass; [].
    now apply config_list_compat.
* intros config pt x. rewrite SetObservation.make_set_spec, filter_InA, Rle_bool_true_iff.
  + reflexivity.
  + intros ? ? Heq. f_equal. now rewrite Heq.
Defined.

Local Notation "'from_config' radius" := (@obs_from_config _ _ _ _ (limited_set_observation radius)) (at level 1).

Lemma obs_from_config_map : forall radius (sim : similarity location),
  forall Psim config pt,
  map (sim_f sim) (from_config radius config pt)
  == from_config (Similarity.zoom sim * radius)
                 (map_config (lift (existT precondition sim Psim)) config)
                 ((lift (existT precondition sim Psim)) pt).
Proof using .
repeat intro. unfold obs_from_config, limited_set_observation.
rewrite config_list_map; try (now apply lift_compat; simpl; apply Bijection.section_compat); [].
rewrite map_map, 2 filter_map, <- SetObservation.make_set_map, map_map; autoclass; [].
apply SetObservation.make_set_compat, eqlistA_PermutationA_subrelation.
assert (Hequiv : (@equiv _ state_Setoid ==> @equiv _ location_Setoid)%signature
          (fun x => sim (get_location x)) (fun x => get_location (lift (existT precondition sim Psim) x))).
{ intros pt1 pt2 Heq. now rewrite get_location_lift, Heq. }
apply (map_extensionalityA_compat _ Hequiv). f_equiv.
intros ? ? Heq. rewrite 2 get_location_lift. simpl.
rewrite sim.(Similarity.dist_prop), Heq, Rle_bool_mult_l; trivial; [].
apply Similarity.zoom_pos.
Qed.

Property pos_in_config : forall radius config state id,
  ((dist (get_location (config id)) (get_location state)) <= radius)%R ->
  In (get_location (config id)) (from_config radius config state).
Proof using .
intros radius config state id. unfold obs_from_config. simpl.
rewrite SetObservation.make_set_spec, filter_InA, InA_map_iff; autoclass; [|].
+ intro Hle. repeat esplit; auto; [|].
  - apply config_list_InA. now exists id.
  - now rewrite Rle_bool_true_iff.
+ intros ? ? Heq. now rewrite Heq.
Qed.

Property obs_from_config_In : forall radius config state l,
  In l (from_config radius config state)
  <-> exists id, get_location (config id) == l /\ (dist l (get_location state) <= radius)%R.
Proof using .
intros radius config state l. split; intro Hin.
+ unfold obs_is_ok, obs_from_config, limited_set_observation in *. simpl in *.
  rewrite SetObservation.make_set_spec, filter_InA in Hin.
  - rewrite config_list_spec, map_map, InA_map_iff, Rle_bool_true_iff in Hin;
    autoclass || firstorder.
  - intros ? ? Heq. now rewrite Heq.
+ destruct Hin as [id [Hid Hle]]. rewrite <- Hid. apply pos_in_config. now rewrite Hid.
Qed.

End LimitedSetObservation.
