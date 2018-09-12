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
Require Import Pactole.Setting.
Require Import Pactole.Spaces.RealMetricSpace.
Require Import Pactole.Spaces.Similarity.


Typeclasses eauto := (bfs).


Section SimilarityCenter.

Context `{Spectrum}.
Context {VS : RealVectorSpace location}.
Context {RMS : RealMetricSpace location}.
Context `{update_choice}.
Context `{inactive_choice}.

(** Similarities as a frame choice, inside real metric spaces *)
Global Instance FrameChoiceSimilarity : frame_choice (similarity location) := {|
  frame_choice_bijection := @sim_f location _ _ _ _;
  frame_choice_Setoid := similarity_Setoid location;
  frame_choice_bijection_compat := f_compat |}.

Definition similarity_da_prop da :=
  forall config g, center (change_frame da config g) == get_location (config (Good g)).

(** When using similarities to change the frame of reference, we need to ensure that
    the center of the similarity is the location of the robot. *)
Definition similarity_da := { sim_da : demonic_action | similarity_da_prop sim_da }.

Instance similarity_da_Setoid : Setoid similarity_da := sig_Setoid.

Definition proj_sim_da : similarity_da -> demonic_action := @proj1_sig _ _.

Global Instance proj_sim_da_compat : Proper (equiv ==> equiv) proj_sim_da.
Proof. intros ? ? Heq. apply Heq. Qed.

Definition similarity_center : forall da config g,
  center (change_frame (proj_sim_da da) config g) == get_location (config (Good g))
  := @proj2_sig _ _.


(** Demons are now stream of [similarity_da]s.*)
Definition similarity_demon := Stream.t similarity_da.


(** From a [similarity_demon], we can recover the demon] and its property [similarity_da_prop]. *)
Definition similarity_demon2demon : similarity_demon -> demon := Stream.map proj_sim_da.

Definition similarity_demon2prop : forall d,
  Stream.forever (Stream.instant similarity_da_prop) (similarity_demon2demon d).
Proof. coinduction Hcorec. simpl. unfold proj_sim_da. apply proj2_sig. Defined.

Global Instance similarity_demon2demon_compat :
  Proper (@equiv _ Stream.stream_Setoid ==> @equiv _ Stream.stream_Setoid) similarity_demon2demon.
Proof. unfold similarity_demon2demon. autoclass. Qed.

Lemma similarity2demon_hd : forall d, Stream.hd (similarity_demon2demon d) = proj_sim_da (Stream.hd d).
Proof. now intros []. Qed.

Lemma similarity2demon_tl : forall d, Stream.tl (similarity_demon2demon d) = similarity_demon2demon (Stream.tl d).
Proof. now intros []. Qed.

Lemma similarity2demon_cons : forall da d,
  @equiv _ Stream.stream_Setoid
    (similarity_demon2demon (Stream.cons da d))
    (Stream.cons (proj_sim_da da) (similarity_demon2demon d)).
Proof. intros. unfold similarity_demon2demon. now rewrite Stream.map_cons. Qed.

(** Conversely, from a [demon] and a proof that [similarity_da_prop] is always true,
    we can build a [similarity_demon]. *)

CoFixpoint demon2similarity_demon : forall (d : demon) (Hd : Stream.forever (Stream.instant similarity_da_prop) d),
  similarity_demon := fun d Hd =>
  Stream.cons
    (exist _ (Stream.hd d) match Hd with | Stream.Always x _ => x end)
    (@demon2similarity_demon (Stream.tl d) (match Hd with | Stream.Always _ x => x end)).

Arguments demon2similarity_demon d Hd : clear implicits.

Lemma demon2similarity_hd : forall d Hd,
  Stream.hd (demon2similarity_demon d Hd) == exist _ (Stream.hd d) (match Hd with Stream.Always x _ => x end).
Proof. now intros [] []. Qed.

Lemma demon2similarity_tl : forall d Hd,
  Stream.tl (demon2similarity_demon d Hd) == demon2similarity_demon (Stream.tl d) (match Hd with Stream.Always _ x => x end).
Proof. now intros [] []. Qed.

Theorem demon2demon : forall d Hd,
  @equiv _ Stream.stream_Setoid (similarity_demon2demon (demon2similarity_demon d Hd)) d.
Proof. coinduction Hcorec. unfold Stream.instant2. now rewrite similarity2demon_hd, demon2similarity_hd. Qed.

End SimilarityCenter.

Coercion proj_sim_da : similarity_da >-> demonic_action.
Coercion similarity_demon2demon : similarity_demon >-> demon.

(*
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 117 ***
 *** End: ***
 *)
