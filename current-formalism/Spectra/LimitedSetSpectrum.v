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

Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Utf8_core.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Rbase.
Require Import Pactole.Util.FSets.FSetInterface.
Require Import Pactole.Util.FSets.FSetFacts.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.Configurations.
Require Import Pactole.Core.RobotInfo.
Require Import Pactole.Spectra.Definition.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.
Require Pactole.Spectra.SetSpectrum.


Section LimitedSetSpectrum.

Context `{State}.
Context (RVS : @RealVectorSpace _ _ (location_EqDec)).
Context {RMS : @RealMetricSpace _ _ _ RVS}.
Context `{Names}.

Implicit Type config : configuration.

Global Instance limited_set_spectrum (radius : R) : Spectrum := {
  spectrum := set location;
  spect_from_config config pt :=
    SetSpectrum.make_set (List.filter (fun x => Rle_bool (dist x pt) radius)
                                      (List.map get_location (config_list config)));
  spect_is_ok s config pt :=
    forall l, In l s <-> InA equiv l (List.map get_location (config_list config)) /\ (dist l pt <= radius)%R }.
Proof.
(* BUG?: bullet forbidden here *)
{ intros config1 config2 Hconfig pt1 pt2 Hpt.
  apply SetSpectrum.make_set_compat, eqlistA_PermutationA_subrelation.
  f_equiv.
  + intros ? ? Heq. now rewrite Heq, Hpt.
  + apply (@map_eqlistA_compat _ _ equiv equiv _ get_location); autoclass; [].
    now apply config_list_compat. }
* intros config pt x. rewrite SetSpectrum.make_set_spec, filter_InA, Rle_bool_true_iff.
  + reflexivity.
  + intros ? ? Heq. f_equal. now rewrite Heq.
Defined.

(* Notation spectrum := (@spectrum loc info _ _ _ _ _ _ _). *)
Local Notation "'from_config' radius" := (@spect_from_config _ _ _ _ (limited_set_spectrum radius)) (at level 1).

Lemma spect_from_config_ignore_snd : forall config pt,
  spect_from_config config pt == spect_from_config config origin.
Proof. reflexivity. Qed.

Lemma spect_from_config_map : forall sim : similarity location,
  forall radius config pt,
  map sim (from_config radius config pt)
  == from_config (sim.(Similarity.zoom) * radius) (map_config (lift sim) config) (sim pt).
Proof.
repeat intro. unfold spect_from_config, limited_set_spectrum.
rewrite config_list_map, map_map, 2 filter_map, <- SetSpectrum.make_set_map, map_map; autoclass; [].
apply SetSpectrum.make_set_compat, Preliminary.eqlistA_PermutationA_subrelation.
assert (Hequiv : (@equiv _ state_Setoid ==> @equiv _ location_Setoid)%signature
          (fun x => sim (get_location x)) (fun x => get_location (lift sim x))).
{ intros pt1 pt2 Heq. now rewrite get_location_lift, Heq. }
apply (map_extensionalityA_compat _ Hequiv). f_equiv.
intros ? ? Heq. rewrite get_location_lift, sim.(Similarity.dist_prop), Heq, Rle_bool_mult_l; trivial; [].
apply Similarity.zoom_pos.
Qed.

Property pos_in_config : forall radius config pt id,
  ((dist (get_location (config id)) pt) <= radius)%R ->
  In (get_location (config id)) (from_config radius config pt).
Proof.
intros radius config pt id. unfold spect_from_config. simpl.
rewrite SetSpectrum.make_set_spec, filter_InA, InA_map_iff; autoclass; [|].
+ intro Hle. repeat esplit; auto; [|].
  - apply config_list_InA. now exists id.
  - now rewrite Rle_bool_true_iff.
+ intros ? ? Heq. now rewrite Heq.
Qed.

Property spect_from_config_In : forall radius config pt l,
  In l (from_config radius config pt) <-> exists id, get_location (config id) == l /\ (dist l pt <= radius)%R.
Proof.
intros radius config pt l. split; intro Hin.
* unfold spect_is_ok, spect_from_config, limited_set_spectrum in *. simpl in *.
  rewrite SetSpectrum.make_set_spec, filter_InA in Hin.
  + rewrite config_list_spec, map_map, InA_map_iff, Rle_bool_true_iff in Hin; autoclass; [|].
    - decompose [ex and] Hin. eauto.
    - intros ? ? Heq. now rewrite Heq.
  + intros ? ? Heq. now rewrite Heq.
* destruct Hin as [id [Hid Hle]]. rewrite <- Hid. apply pos_in_config. now rewrite Hid.
Qed.

End LimitedSetSpectrum.
