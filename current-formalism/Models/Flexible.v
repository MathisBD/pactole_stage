(**************************************************************************)
(*  Mechanised Framework for Local Interactions & Distributed Algorithms  *)
(*  T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                        *)
(*  PACTOLE project                                                       *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence.     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(** Mechanised Framework for Local Interactions & Distributed Algorithms    
                                                                            
    T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                          
                                                                            
    PACTOLE project                                                         
                                                                            
    This file is distributed under the terms of the CeCILL-C licence.       
                                                                          *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import SetoidDec.
Require Import Reals.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.


(** Flexible demons are a special case of demons with the additional property that
    the updated location of the robot is not necessarily the one chosen by the robogram,
    but lies on the segment delimited by the current and target locations.
    To avoid Zenon-based paradoxes, we require the robot to move at least a given distance δ. *)
Section FlexibleFormalism.

Context `{Spectrum}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}. (* for dist *)
Variable T1 T2 T3 : Type.
Context {Frame : frame_choice T1}.
Context {Inactive : inactive_choice T3}.

Class FlexibleChoice `{update_choice T2} := {
  move_ratio : T2 -> ratio;
  move_ratio_compat :> Proper (@equiv T2 update_choice_Setoid ==> @equiv _ sig_Setoid) move_ratio }.

(** Flexible moves are parametrized by the minimum distance [delta] that robots must move when they are activated. *)
Class FlexibleSetting `{FlexibleChoice} {Update : update_functions T2 T3} (delta : R) := {
  (** [move_ratio] is the ratio between the achieved and the planned move distances. *)
  ratio_spec : forall (config : configuration) g trajectory choice,
    let pt := get_location (config (Good g)) in
    let pt' := get_location (update config g trajectory choice) in
    (* either we reach the target *)
    pt' == trajectory ratio_1
    (* or we only move part of the way but the robot has moved a distance at least [delta]. *)
    \/ pt' == trajectory (move_ratio choice)
       /\ delta <= dist pt pt' }.

(** If the robot is not trying to move, then it does not, no metter what the demon chooses. *)
Lemma update_no_move `{FlexibleSetting} : forall (config : configuration) (g : G) (pt : location) (choice : T2),
  get_location (update config g (straight_path pt pt) choice) == pt.
Proof.
intros config g pt choice.
destruct (ratio_spec config g (straight_path pt pt) choice) as [Heq | [Heq Hle]];
rewrite Heq; simpl; now rewrite add_opp, mul_origin, add_origin.
Qed.

End FlexibleFormalism.

Section OnlyFlexibleSetting.

Context `{Location}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}. (* for dist *)
Context `{Names}.

Instance St : State location := OnlyLocation.

(** Specialized definition where the only choice made by the demon is the movement ratio. *)
Instance OnlyFlexible : update_choice ratio := {|
  update_choice_Setoid := ratio_Setoid;
  update_choice_EqDec := _ |}.

Global Instance OnlyFlexibleChoice : @FlexibleChoice _ OnlyFlexible := {| move_ratio := Datatypes.id |}.

Instance FlexibleUpdate {T} `{inactive_choice T} (delta : R) (f : configuration → ident → T → location)
                        (Hf : Proper (equiv ==> eq ==> equiv ==> equiv) f) : update_functions ratio _.
refine {|
  update := fun config g traj ρ => if Rle_dec delta (dist (get_location (config (Good g))) (get_location (traj ρ)))
                                   then traj ρ else traj ratio_1;
  inactive := f |}.
Proof.
intros config1 config2 Hconfig gg g ? traj1 traj2 Htraj ρ1 ρ2 Hρ. subst gg.
assert (Heq : get_location (traj1 ρ1) == get_location (traj2 ρ2)).
{ apply get_location_compat. now f_equiv. }
do 2 destruct_match; rewrite Heq in *;
solve [ reflexivity
      | now f_equiv
      | exfalso; revert_one not; intro Hgoal; apply Hgoal;
        revert_all; rewrite Hconfig; intro Hle; apply Hle ].
Defined.

Global Instance FlexibleChoiceFlexibleUpdate `{inactive_choice} f Hf delta
  : FlexibleSetting (Update := FlexibleUpdate delta f Hf) delta.
Proof. split.
intros config g traj choice pt pt'.
simpl update in *. unfold pt'. destruct_match; now left + right.
Qed.

End OnlyFlexibleSetting.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
