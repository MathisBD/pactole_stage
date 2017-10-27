(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
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


Typeclasses eauto := (bfs).


Section SimilarityCenter.

Context {loc info T : Type}.
Context `{IsLocation loc info}.
Context {RMS : RealMetricSpace loc}.
Context {N : Names}.
Context {Spect : Spectrum loc info}.
Context `{second_demonic_choice T}.

(* Similarities as a first choice, inside real metric spaces *)
Global Instance FirstChoiceSimilarity : first_demonic_choice (similarity loc) := {|
  first_choice_bijection := @sim_f loc _ _ _;
  first_choice_Setoid := similarity_Setoid loc;
  first_choice_bijection_compat := f_compat |}.

(** When using similarities to change the frame of reference, we need to ensure that
    the center of the similarity is the location of the robot. *)
Definition similarity_da := { sim_da : @demonic_action loc info (similarity loc) T _ _ _ _ _ _ _ _ |
  forall config g, center (change_frame sim_da config g) == get_location (config (Good g)) }.

Instance similarity_da_Setoid : Setoid similarity_da := sig_Setoid.

Definition proj_sim_da : similarity_da -> demonic_action := @proj1_sig _ _.

Global Instance proj_sim_da_compat : Proper (equiv ==> equiv) proj_sim_da.
Proof. intros ? ? Heq. apply Heq. Qed.

Definition similarity_center : forall da config g,
  center (change_frame (proj_sim_da da) config g) == get_location (config (Good g))
  := @proj2_sig _ _.

(** Demons are now stream of [similarity_da]s.*)
Definition similarity_demon := Stream.t similarity_da.

CoFixpoint similarity_demon2demon (d : similarity_demon) : demon :=
  Stream.cons (proj_sim_da (Stream.hd d)) (similarity_demon2demon (Stream.tl d)).

Global Instance similarity_demon2demon_compat :
  Proper (@equiv _ Stream.stream_Setoid ==> @equiv _ Stream.stream_Setoid) similarity_demon2demon.
Proof.
cofix Hrec. intros [] [] [Hda Heq]. constructor.
+ apply Hda.
+ simpl Stream.tl. apply Hrec, Heq.
Qed.

Lemma similarity_demon_hd : forall d, Stream.hd (similarity_demon2demon d) = proj_sim_da (Stream.hd d).
Proof. now intros []. Qed.

Lemma similarity_demon_tl : forall d, Stream.tl (similarity_demon2demon d) = similarity_demon2demon (Stream.tl d).
Proof. now intros []. Qed.

End SimilarityCenter.

Coercion proj_sim_da : similarity_da >-> demonic_action.
Coercion similarity_demon2demon : similarity_demon >-> demon.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
