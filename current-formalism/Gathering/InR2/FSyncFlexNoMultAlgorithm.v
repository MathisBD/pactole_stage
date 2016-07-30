(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Omega Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Pactole.CommonFormalism.
Require Pactole.FlexibleFormalism.
Require Import Pactole.SetSpectrum.
Require Import Pactole.Lexprod.
Require Import Pactole.Gathering.InR2.R2geometry.
Require Import Pactole.Gathering.FlexDefinitions.


Import Permutation.
Set Implicit Arguments.


(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot.
    We call a [configuration] a function from robots to configuration.
    An [execution] is an infinite (coinductive) stream of [configuration]s.
    A [demon] is an infinite stream of [demonic_action]s. *)

Module GatheringinR2.

(** **  Framework of the correctness proof: a finite set with at least three elements  **)

Parameter nG: nat.
Hypothesis Hyp_nG : (2 <= nG)%nat.

(** There are nG good robots and no byzantine ones. *)
Module N : Size with Definition nG := nG with Definition nB := 0%nat.
  Definition nG := nG.
  Definition nB := 0%nat.
End N.

(** We instantiate in our setting the generic definitions of the gathering problem. *)
Module Defs := FlexDefinitions.FlexGatheringDefs(R2)(N).
Import Defs.

Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.

Lemma Config_list_alls : forall pt, Spect.Config.list (fun _ => pt) = alls pt N.nG.
Proof.
intro. rewrite Config.list_spec, map_cst.
setoid_rewrite Spect.Names.names_length. unfold N.nB. now rewrite plus_0_r.
Qed.

Definition Spect_map f s := Spect.M.fold (fun e acc => Spect.M.add (f e) acc) s Spect.M.empty.

Lemma map_sim_support : forall (sim : Sim.t) s,
  Permutation (Spect.M.elements (Spect_map sim s)) (map sim (Spect.M.elements s)).
Proof.
(* intros sim s. rewrite <- PermutationA_Leibniz. apply Spect.map_injective_support. *)
(* - intros ? ? Heq. now rewrite Heq. *)
(* - apply Sim.injective. *)
(* Qed. *)
Admitted.
  
(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall conf, ~Spect.eq (!! conf) Spect.M.empty.
Proof. apply spect_non_nil. assert (Hle := Hyp_nG). unfold N.nG. omega. Qed.

Lemma support_non_nil : forall config, Spect.M.elements (!! config) <> nil.
Proof.
  (* intros config Habs. *)
  (* rewrite <- Spect.set_empty in Habs. apply (spect_non_nil _ Habs). Qed. *)
Admitted.
  
Lemma gathered_at_dec : forall conf pt, {gathered_at pt conf} + {~gathered_at pt conf}.
Proof.
intros conf pt.
destruct (forallb (fun id => R2dec_bool (conf id) pt) Names.names) eqn:Hall.
+ left. rewrite forallb_forall in Hall. intro g. rewrite <- R2dec_bool_true_iff. apply Hall. apply Names.In_names.
+ right. rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall. destruct Hall as [id [Hin Heq]].
  destruct id as [g | b]; try now apply Fin.case0; exact b. intro Habs. specialize (Habs g).
  rewrite negb_true_iff, R2dec_bool_false_iff in Heq. contradiction.
Qed.

(*
(* FIXME: These three definitions: gathered_at, gather and WillGather
   should be shared by all our proofs about gathering (on Q, R, R2,
   for impossibility and possibility proofs). Shouldn't they be in a
   module? We could even add a generic notion of forbidden
   configurations. *)


(** [gathered_at conf pt] means that in configuration [conf] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : R2.t) (conf : Config.t) := forall g : Names.G, conf (Good g) = pt.

Instance gathered_at_compat : Proper (eq ==> Config.eq ==> iff) gathered_at.
Proof.
intros ? pt ? config1 config2 Hconfig. subst. unfold gathered_at.
split; intros; rewrite <- (H g); idtac + symmetry; apply Hconfig.
Qed.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
Definition gather (pt : R2.t) (e : execution) : Prop := Streams.forever (Streams.instant (gathered_at pt)) e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Definition willGather (pt : R2.t) (e : execution) : Prop := Streams.eventually (gather pt) e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these configurations as [forbidden]. *)
Definition forbidden (config : Config.t) :=
  Nat.Even N.nG /\ N.nG >=2 /\ let m := Spect.from_config(config) in
  exists pt1 pt2, ~pt1 = pt2 /\ m[pt1] = Nat.div2 N.nG /\ m[pt2] = Nat.div2 N.nG.

(** [FullSolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration, will *eventually* be [Gather]ed.
    This is the statement used for the impossiblity proof. *)
Definition FullSolGathering (r : robogram) (d : demon) :=
  forall config, exists pt : R2.t, willGather pt (execute r d config).

(** [ValidsolGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    configuration not [forbidden], will *eventually* be [Gather]ed.
    This is the statement used for the correctness proof of the algorithm. *)
Definition ValidSolGathering (r : robogram) (d : demon) :=
  forall config, ~forbidden config -> exists pt : R2.t, willGather pt (execute r d config).


Instance forbidden_compat : Proper (Config.eq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [HnG [? [pt1 [pt2 [Hneq Hpt]]]]];(split;[|split]); trivial ||
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.
*)

(** **  Definition of the robogram  **)

Open Scope R_scope.

(** The robogram solving the gathering problem in R². *)
Definition ffgatherR2_pgm (s : Spect.t) : R2.t :=
  let spect := Spect.M.elements s in
  match spect with
    | nil => (0, 0) (* no robot *)
    | pt :: nil => pt (* gathered *)
    | _ :: _ :: _ =>
      barycenter spect
  end.

Instance ffgatherR2_pgm_compat : Proper (Spect.eq ==> R2.eq) ffgatherR2_pgm.
Proof.
intros s1 s2 Hs. unfold ffgatherR2_pgm.
assert (Hsize : length (Spect.M.elements s1) = length (Spect.M.elements s2)).
{ f_equiv. now do 2 f_equiv. }
destruct (Spect.M.elements s1) as [| pt1 [| ? ?]] eqn:Hs1,
         (Spect.M.elements s2) as [| pt2 [| ? ?]] eqn:Hs2;
simpl in Hsize; omega || clear Hsize.
+ reflexivity.
+ apply Spect.elements_compat in Hs. rewrite Hs1, Hs2 in Hs.
  rewrite PermutationA_Leibniz in Hs. apply Permutation_length_1_inv in Hs. now inversion Hs.
+ apply Spect.elements_compat in Hs.
  apply barycenter_compat.
  rewrite Hs1 in Hs.
  rewrite Hs2 in Hs.
  assumption.  
Qed.

Definition ffgatherR2 : robogram := {| pgm := ffgatherR2_pgm |}.

Close Scope R_scope.


(** **  Decreasing measure ensuring termination  **)

(** ***  Global decreasing measure  **)

(** It is a lexicographic order on the index of the type of config + the number of robots that should move. *)
(**
  -  ]   Gathered: no need
  - 0]   Regular case
*)

Open Scope R_scope.

(* Coercion Spect.Names.names : list Spect.Names.Internals.ident >-> list Spect.Names.ident. *)

Definition max_dist_R2_pt_list (pt: R2.t) (l: list R2.t) : R :=
  fold_right (fun pt1 max => Rmax (R2.dist pt pt1) max) 0 l.


(* Lemma max_dist_R2_pt_list_compat : Proper (R2.eq ==> PermutationA R2.eq ==> Logic.eq) max_dist_R2_pt_list. *)
(* Proof. *)
  
  
Lemma max_dist_R2_pt_list_le :
  forall pt l pt1,
    In pt1 l -> R2.dist pt pt1 <= max_dist_R2_pt_list pt l.
Proof.
  intros pt l pt1 Hin1.
  induction l.
  + elim Hin1.
  + destruct Hin1.
    - subst. unfold max_dist_R2_pt_list.
      simpl.
      apply Rmax_l.
    - unfold max_dist_R2_pt_list. simpl.
      unfold max_dist_R2_pt_list in IHl. apply IHl in H.
      apply (Rle_trans _ _ _ H).
      apply Rmax_r.
Qed.

Lemma max_dist_not_first :
  forall pt pt1 l,
    max_dist_R2_pt_list pt (pt1 :: l) <> R2.dist pt pt1 ->
    l <> nil /\
    max_dist_R2_pt_list pt (pt1 :: l) = max_dist_R2_pt_list pt l.
Proof.
  intros pt pt1 l Hnotfirst.
  unfold max_dist_R2_pt_list in Hnotfirst.
  simpl in Hnotfirst.
  unfold Rmax at 1 in Hnotfirst.
  unfold max_dist_R2_pt_list at 1. simpl.
  unfold Rmax at 1.
  destruct (Rle_dec (R2.dist pt pt1)
                  (fold_right (fun (pt1 : R2.t) (max : R) => Rmax (R2.dist pt pt1) max) 0 l)).
  split.
  intro.
  apply Hnotfirst.
  rewrite H in *.
  simpl in *.
  assert (0 <= R2.dist pt pt1).
  apply R2.dist_pos.
  destruct H0.
  assert (R2.dist pt pt1 < R2.dist pt pt1).
  now apply Rle_lt_trans with (r2 := 0).
  exfalso.
  apply (Rlt_irrefl _ H1).
  assumption.
  reflexivity.
  now elim Hnotfirst.
Qed.
  
Lemma max_dist_R2_pt_list_ex :
  forall pt l,
    l <> nil ->
    exists pt1, In pt1 l /\ R2.dist pt pt1 = max_dist_R2_pt_list pt l.
Proof.
  intros pt l Hl.
  induction l.
  + now elim Hl.
  + destruct (Req_dec (R2.dist pt a) (max_dist_R2_pt_list pt (a :: l))).
    - exists a.
      split.
      now left.
      assumption.
    - assert (Hmax: max_dist_R2_pt_list pt (a::l) = max_dist_R2_pt_list pt l).
      { apply max_dist_not_first.
        intro. apply H. now rewrite H0. }
      assert (Hlnotnil: l <> nil).
      { generalize (max_dist_not_first pt a l).
        intro.
        apply H0.
        intro. apply H. now rewrite H1. }
      destruct (IHl Hlnotnil). destruct H0.
      exists x.
      split.
      now right.
      now rewrite Hmax.
Qed.      
      
Definition max_dist_R2_list_list (l1: list R2.t) (l2: list R2.t): R :=
  fold_right (fun pt0 max => Rmax max (max_dist_R2_pt_list pt0 l2)) 0 l1.

Lemma max_dist_R2_list_list_le :
  forall pt1 l1 pt2 l2,
    In pt1 l1 -> In pt2 l2 -> R2.dist pt1 pt2 <= max_dist_R2_list_list l1 l2.
Proof.
  intros pt1 l1 pt2 l2 Hin1 Hin2.
  induction l1.
  + elim Hin1.
  + destruct Hin1.
    - subst. unfold max_dist_R2_list_list. simpl.
      apply Rle_trans with (r2 := max_dist_R2_pt_list pt1 l2).
      now apply max_dist_R2_pt_list_le.
      now apply Rmax_r.
    - unfold max_dist_R2_list_list. simpl.
      apply IHl1 in H.
      apply (Rle_trans _ _ _ H).
      now apply Rmax_l.
Qed.

Lemma max_dist_R2_list_list_ex :
  forall l1 l2,
    l1 <> nil ->
    l2 <> nil ->
    exists pt1 pt2, In pt1 l1 /\ In pt2 l2 /\ R2.dist pt1 pt2 = max_dist_R2_list_list l1 l2.
Proof.
  intros l1 l2 Hl1notnil Hl2notnil.
  induction l1.
  + now elim Hl1notnil.
  + unfold max_dist_R2_list_list.
    simpl.
    unfold Rmax at 1.
    destruct (Rle_dec (fold_right (fun (pt0 : R2.t) (max : R) => Rmax max (max_dist_R2_pt_list pt0 l2)) 0 l1)
         (max_dist_R2_pt_list a l2)).
    - exists a.
      destruct (max_dist_R2_pt_list_ex a Hl2notnil) as [? [? ?]].
      exists x. split.
      now left.
      now split.
    - clear Hl1notnil.
      assert (Hl1notnil: l1 <> nil).
      { intro. apply n. subst. simpl.
        induction l2.
        unfold max_dist_R2_pt_list. simpl. apply Rle_refl.
        simpl. apply Rle_trans with (r2 := R2.dist a a0).
        apply R2.dist_pos.
        apply Rmax_l. }
      destruct (IHl1 Hl1notnil) as [? [? [? [? ?]]]].
      exists x, x0.
      split.
      now right.
      now split.
Qed.

(* Lemma max_dist_spect: *)
(*   forall (spect: Spect.t), *)
(*     Spect.support spect <> nil -> *)
(*     exists (dm: R), *)
(*       (forall pt0 pt1, In pt0 (Spect.support spect) -> *)
(*                        In pt1 (Spect.support spect) -> *)
(*                        R2.dist pt0 pt1 <= dm) *)
(*       /\ *)
(*       (exists pt0 pt1, In pt0 (Spect.support spect) *)
(*                        /\ In pt1 (Spect.support spect) *)
(*                        /\ R2.dist pt0 pt1 = dm). *)
(* Proof. *)
(*   intros. *)
(*   exists (max_dist_R2_list_list (Spect.support spect) (Spect.support spect)). *)
(*   split. *)
(*   + intros pt0 pt1 Hin0 Hin1. *)
(*     now apply max_dist_R2_list_list_le. *)
(*   + now apply max_dist_R2_list_list_ex. *)
(* Qed. *)

Definition max_dist_spect (spect: Spect.t) : R :=
  max_dist_R2_list_list (Spect.M.elements spect) (Spect.M.elements spect).

Lemma max_dist_spect_le :
  forall (spect: Spect.t) pt0 pt1,
    In pt0 (Spect.M.elements spect) ->
    In pt1 (Spect.M.elements spect) ->
    R2.dist pt0 pt1 <= max_dist_spect spect.
Proof. intros. now apply max_dist_R2_list_list_le. Qed.
  
Lemma max_dist_spect_ex :
  forall (spect: Spect.t),
    Spect.M.elements spect <> nil ->
    exists pt0 pt1, 
      In pt0 (Spect.M.elements spect)
      /\ In pt1 (Spect.M.elements spect)
      /\ R2.dist pt0 pt1 = max_dist_spect spect.
Proof. intros. now apply max_dist_R2_list_list_ex. Qed.

(* Lemma max_dist_exists : *)
(*   forall (conf: Config.t), *)
(*   exists (dm: R), *)
(*     forall r1 r2, R2.dist (conf r1) (conf r2) <= dm /\ exists r1 r2, R2.dist (conf r1) (conf r2) = dm. *)
(* Proof. *)
(*   intros. *)
(*   set (rlist := (*Spect.Names.Internals.fin_map*) Spect.Names.names). *)
(*   set (dm_candidate := fold_left (fun max r0 => *)
(*                                     Rmax (fold_left (fun max r1 => Rmax (R2.dist (conf r0) (conf r1)) max) rlist 0) max) *)
(*                                  rlist 0). *)
(*   assert (forall r1 r2, In r1 rlist -> In r2 rlist -> R2.dist (conf r1) (conf r2) <= dm_candidate). *)
(*   induction rlist. *)
(*   intros ? ? Hin; elim Hin. *)
(*   intros r1 r2 Hin1 Hin2. *)
(*   destruct (Spect.Names.eq r1 a). *)
  
(*   exists (fold_left (fun max r0 => *)
(*                        Rmax (fold_left (fun max r1 => Rmax (R2.dist (conf r0) (conf r1)) max) rlist 0) max) *)
(*                     rlist 0). *)
(*   intros. *)
(*   split. *)
  

(* Function measure (s : Spect.t) : nat * nat := *)
(*   match Spect.support (Spect.max s) with *)
(*     | nil => (0, 0) (* no robot *) *)
(*     | pt :: nil => (0, N.nG -  s[pt]) (* majority *) *)
(*     | _ :: _ :: _ => *)
(*       match on_SEC (Spect.support s) with *)
(*         | nil | _ :: nil => (0, 0) (* impossible cases *) *)
(*         | pt1 :: pt2 :: nil => (* diameter case *) *)
(*             if is_clean s then (1, measure_clean s) else (2, measure_dirty s) *)
(*         | pt1 :: pt2 :: pt3 :: nil => (* triangle case *) *)
(*             if is_clean s then (3, measure_clean s) else (4, measure_dirty s) *)
(*         | _ => (* general case *) if is_clean s then (5, measure_clean s) else (6, measure_dirty s) *)
(*       end *)
(*   end. *)

(* Instance max_dist_compat : Proper (Spect.eq ==> Logic.eq) max_dist_spect. *)
(* Proof. *)
(*   intros s1 s2 Hs. unfold max_dist_spect. *)
(*   assert (Hsize : length (Spect.support s1) = length (Spect.support s2)). *)
(*   { f_equiv. now do 2 f_equiv. } *)
(*   destruct (Spect.support s1) as [| pt1 [| ? ?]] eqn:Hs1, *)
(*            (Spect.support s2) as [| pt2 [| ? ?]] eqn:Hs2; *)
(*   simpl in Hsize; omega || clear Hsize. *)
(*   + reflexivity. *)
(*   + *)
(*     repeat f_equal. *)
(*     rewrite Hs. repeat f_equal. *)
(*   rewrite <- (PermutationA_1 _). rewrite <- Hs1, <- Hs2. rewrite Hs. reflexivity. *)
(* + clear -Hs. *)
(*   assert (Hperm : Permutation (on_SEC (Spect.support s1)) (on_SEC (Spect.support s2))). *)
(*   { now rewrite <- PermutationA_Leibniz, Hs. } *)
(*   destruct (on_SEC (Spect.support s1)) as [| a1 [| a2 [| a3 [| ? ?]]]] eqn:Hs1. *)
(*   - apply Permutation_nil in Hperm. now rewrite Hperm. *)
(*   - apply Permutation_length_1_inv in Hperm. now rewrite Hperm. *)
(*   - apply Permutation_length_2_inv in Hperm. *)
(*     destruct Hperm as [Hperm | Hperm]; rewrite Hperm; trivial; *)
(*     rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs. *)
(*   - assert (length (on_SEC (Spect.support s2)) =3%nat) by now rewrite <- Hperm. *)
(*     destruct (on_SEC (Spect.support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega. *)
(*     rewrite Hs. destruct (is_clean s2); f_equal; now rewrite Hs. *)
(*   - assert (length (on_SEC (Spect.support s2)) = 4 + length l)%nat by now rewrite <- Hperm. *)
(*     destruct (on_SEC (Spect.support s2)) as [| b1 [| b2 [| b3 [| ? ?]]]]; simpl in *; try omega. *)
(*     rewrite Hs; destruct (is_clean s2); f_equal; now rewrite Hs. *)
(* Qed. *)

(** **  Main result for termination: the measure decreases after a step where a robot moves  *)

Definition measure (conf: Config.t) : R :=
  max_dist_spect (!! conf).

Lemma fold_mult_plus_distr : forall (f: R2.t -> R) (coeff: R) (E: list R2.t) (init: R),
    fold_left (fun acc pt => acc + coeff * (f pt)) E (coeff * init) =
    coeff * (fold_left (fun acc pt => acc + (f pt)) E init).
Proof.  
  intros f coeff E.
  induction E; intro init.
  + now simpl.
  + simpl.
    rewrite <- Rmult_plus_distr_l.
    now apply IHE.
Qed.    
  
Lemma barycenter_sim : forall (sim : Sim.t) m,
    m <> nil ->
    R2.eq (barycenter (map sim m)) (sim (barycenter m)).
Proof.
  intros sim m Hm. eapply barycenter_n_unique.  
  + apply barycenter_n_spec.
  + intro p.
    unfold sqr_dist_sum, sqr_dist_sum_aux.
    change p with (Sim.id p).
    rewrite <- (Sim.compose_inverse_r sim) with (x := p) by apply R2.eq_equiv.
    change ((Sim.compose sim (sim ⁻¹)) p) with (sim ((sim ⁻¹) p)).

    assert (Hfold_dist_prop: forall pt init,
              fold_left
                (fun (acc : R) (pt' : R2.t) => acc + (R2.dist (sim pt) pt')²)
                (map sim m) (* ((sim.(Sim.zoom))² * init) *) init
              =
              fold_left
                (fun (acc : R) (pt' : R2.t) => acc + (sim.(Sim.zoom))² * (R2.dist pt pt')²)
                m init).
    { intro pt. induction m; intro init.
      + now elim Hm.
      + clear Hm. destruct m.
        * simpl.
          now rewrite sim.(Sim.dist_prop), R_sqr.Rsqr_mult.
        * remember (t::m) as mm.
          simpl.
          rewrite sim.(Sim.dist_prop), R_sqr.Rsqr_mult.
          rewrite IHm.
          reflexivity.
          subst. discriminate.
    }
    do 2 rewrite Hfold_dist_prop.
    rewrite <- Rmult_0_r with (r := (Sim.zoom sim)²).
    rewrite <- Rmult_0_r with (r := (Sim.zoom sim)²) at 2.
    do 2 rewrite fold_mult_plus_distr.
    apply Rmult_le_compat_l.
    - apply Rle_0_sqr.
    - rewrite Rmult_0_r.
      generalize (barycenter_n_spec m).
      intro Hbary_spec.
      unfold is_barycenter_n, sqr_dist_sum, sqr_dist_sum_aux in Hbary_spec.
      now apply Hbary_spec.
Qed.

Lemma dist_prop_retraction:
  forall (sim: Sim.t) (x y : R2.t),
    R2.dist ((Sim.sim_f (sim ⁻¹)) x) ((Sim.sim_f (sim ⁻¹)) y) =
    /(Sim.zoom sim) * R2.dist x y.
Proof.
  intros sim x y.
  (* assert (forall x, R2.eq x (sim (sim ⁻¹ (x)))). *)
  (* { intro z. simpl. rewrite Similarity.section_retraction. reflexivity. apply R2.eq_equiv. } *)
  (* rewrite (H x) at 2. *)
  (* rewrite (H y) at 2. *)
  rewrite Sim.dist_prop.
  now simpl.
Qed.
  
(* Multiplicateur par zoom à ajouter par exemple dans le test par rapport à delta.
   Cela dépend d'une question : cette distance minimale de delta est-elle dans le
   référentiel global ou le référentiel local ? *)
Theorem round_simplify : forall da conf delta,
    Config.eq (round delta ffgatherR2 da conf)
              (fun id => match da.(step) id with
                         | None => conf id
                         | Some (f, r) =>
                           let s := !! conf in
                           match Spect.M.elements s with
                           | nil => conf id (* only happen with no robots *)
                           | pt :: nil => pt (* done *)
                           | _ => let move := (r * (barycenter (Spect.M.elements s) - (conf id)))%R2 in
                                  if Rle_bool delta (R2norm move)
                                  then ((conf id) + move)%R2
                                  else barycenter (Spect.M.elements s)
                           end
                         end).
Proof.
intros da conf delta id. hnf. unfold round.
assert (supp_nonempty:=support_non_nil conf).
destruct (step da id) as [[f r] |] eqn:Hstep; trivial.
destruct id as [g | b]; try now eapply Fin.case0; exact b.
remember (conf (Good g)) as pt. remember (f pt) as sim.
assert (Hsim : Proper (R2.eq ==> R2.eq) sim). { intros ? ? Heq. now rewrite Heq. }
simpl pgm. unfold ffgatherR2_pgm.
assert (Hperm : Permutation (map sim (Spect.M.elements (!! conf)))
                            (Spect.M.elements (!! (Config.map sim conf))))
  by (now rewrite <- map_sim_support, <- PermutationA_Leibniz, Spect.from_config_map).
assert (Hlen := Permutation_length Hperm).
destruct (Spect.M.elements (!! conf)) as [| pt1 [| pt2 l]] eqn:Hmax,
         (Spect.M.elements (!! (Config.map sim conf))) as [| pt1' [| pt2' l']];
simpl in Hlen; discriminate || clear Hlen.
- elim (support_non_nil _ Hmax).
- simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm.
  subst pt1'.
  destruct (Rle_bool delta (R2.dist ((Common.Sim.sim_f (sim ⁻¹)) (r * sim pt1)%R2) pt)).
  * assert (Hpt: pt = pt1).
    { generalize (Spect.from_config_spec conf).
      intros Hok.
      assert (Spect.In pt (!! conf)).
      { unfold Spect.is_ok in Hok.
        unfold Spect.In.
        rewrite (Hok pt).
        now exists (Good g).
      }
      apply Spect.Mdec.F.elements_1 in H.
      rewrite Hmax in H.
      now rewrite InA_singleton in H.
    }
    rewrite <- Hpt in *. clear Hpt.
    generalize (Sim.center_prop sim).
    intro Hzero.
    apply step_center with (c := pt) in Hstep.
    simpl in Hstep.
    rewrite <- Heqsim in Hstep.
    rewrite <- Hstep.
    rewrite Hzero.
    rewrite R2.mul_origin.
    simpl.
    rewrite <- Similarity.Inversion.
    now rewrite Hzero.
  * now apply Sim.compose_inverse_l.

- assert (Hbarysim: R2.eq (barycenter (pt1' :: pt2' :: l')) (sim (barycenter (pt1 :: pt2 :: l)))).
  { rewrite <- barycenter_sim.
    apply barycenter_compat.
    now rewrite PermutationA_Leibniz.
    discriminate. }
  repeat rewrite Hbarysim.
  clear Hperm Hbarysim.
  remember (pt1 :: pt2 :: l) as E.

  assert (pt = (sim ⁻¹) (sim pt)).
  { simpl. rewrite Similarity.retraction_section. reflexivity. apply R2.eq_equiv. }
  rewrite H at 1.
  (* simpl. *)
  rewrite dist_prop_retraction.
  rewrite R2norm_mul.
  rewrite <- R2norm_dist.
  assert (R2.eq (sim pt) (r * (sim pt))).
  { generalize (Sim.center_prop sim).
    intro Hzero.
    apply step_center with (c := pt) in Hstep.
    simpl in Hstep.
    rewrite <- Heqsim in Hstep.
    rewrite <- Hstep.
    rewrite Hzero.
    rewrite R2.mul_origin.
    reflexivity.
  }
  rewrite H0.
  rewrite R2mul_dist.
  rewrite <- Rmult_assoc.
  pattern (/ Sim.zoom sim * Rabs r).
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite <- dist_prop_retraction.
  rewrite <- H.
  simpl.
  rewrite Similarity.retraction_section.

  destruct (Rle_bool delta (Rabs r * R2.dist (barycenter E) pt)).
  + apply Similarity.Inversion. admit.
  + rewrite Similarity.retraction_section; [reflexivity | apply R2.eq_equiv].
  + apply R2.eq_equiv.

Admitted.
    
(*   rewrite <- (step_center da (Good g) pt Hstep) at 4. *)
(*   simpl fst. *)
  
(*   assert (Hcond: Rle_bool delta (R2.dist (barycenter (pt1 :: pt2 :: l)) pt) *)
(*                  = Rle_bool delta (R2.dist (r * sim (barycenter (pt1 :: pt2 :: l))) pt)). *)
(*   { *)
  
(*   assert (Hbary: R2.eq (barycenter (pt1 :: pt2 :: l) - pt) *)
(*                        (r * (barycenter (pt1' :: pt2' :: l')) - pt)). *)
(*   { rewrite <- PermutationA_Leibniz in Hperm. *)
(*     rewrite <- (barycenter_compat Hperm). *)
(*     unfold barycenter. *)
(*     rewrite map_length. *)
(*     rewrite R2.mul_morph. *)
(*     rewrite Rmult_comm. *)
(*     rewrite <- R2.mul_morph. *)
(*     apply R2mul_reg_eq_l. *)
    
(* Admitted. *)
    
(* - simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm. *)
(*   subst pt1'. *)
(*   destruct (Rle_bool delta (R2.dist (r * sim pt1) pt)). *)
(*   * assert (Hpt: pt = pt1). *)
(*     { generalize (Spect.from_config_spec conf). *)
(*       intros Hok. *)
(*       assert (Spect.In pt (!! conf)). *)
(*       { unfold Spect.is_ok in Hok. *)
(*         unfold Spect.In. *)
(*         rewrite (Hok pt). *)
(*         now exists (Good g). *)
(*       } *)
(*       apply Spect.Mdec.F.elements_1 in H. *)
(*       rewrite Hmax in H. *)
(*       now rewrite InA_singleton in H. *)
(*     } *)
(*     rewrite <- Hpt in *. clear Hpt. *)
(*     generalize (Sim.center_prop sim). *)
(*     intro Hzero. *)
(*     apply step_center with (c := pt) in Hstep. *)
(*     simpl in Hstep. *)
(*     rewrite <- Heqsim in Hstep. *)
(*     rewrite <- Hstep. *)
(*     rewrite Hzero. *)
(*     rewrite R2.mul_origin. *)
(*     simpl. *)
(*     rewrite <- Similarity.Inversion. *)
(*     now rewrite Hzero. *)
(*   * now apply Sim.compose_inverse_l. *)
(* - assert (Hbarysim: R2.eq (barycenter (pt1' :: pt2' :: l')) (sim (barycenter (pt1 :: pt2 :: l)))). *)
(*   { rewrite <- barycenter_sim. *)
(*     apply barycenter_compat. *)
(*     now rewrite PermutationA_Leibniz. *)
(*     discriminate. } *)
(*   repeat rewrite Hbarysim. *)
(*   clear Hperm Hbarysim. *)
(*   remember (pt1 :: pt2 :: l) as E. *)

  (* simpl. *)
  (* rewrite <- sim.(Similarity.Inversion). *)
  (* rewrite R2norm_mul. *)
  (* rewrite <- R2norm_dist.   *)
  (* rewrite <- (step_center da (Good g) pt Hstep) at 4. *)
  (* simpl fst. *)
  
  (* assert (Hcond: Rle_bool delta (R2.dist (barycenter (pt1 :: pt2 :: l)) pt) *)
  (*                = Rle_bool delta (R2.dist (r * sim (barycenter (pt1 :: pt2 :: l))) pt)). *)
  (* {  *)
  
  (* assert (Hbary: R2.eq (barycenter (pt1 :: pt2 :: l) - pt) *)
  (*                      (r * (barycenter (pt1' :: pt2' :: l')) - pt)). *)
  (* { rewrite <- PermutationA_Leibniz in Hperm. *)
  (*   rewrite <- (barycenter_compat Hperm). *)
  (*   unfold barycenter. *)
  (*   rewrite map_length. *)
  (*   rewrite R2.mul_morph. *)
  (*   rewrite Rmult_comm. *)
  (*   rewrite <- R2.mul_morph. *)
  (*   apply R2mul_reg_eq_l. *)

(* Proof. *)
(* intros da conf delta id. hnf. unfold round. *)
(* assert (supp_nonempty:=support_non_nil conf). *)
(* destruct (step da id) as [[f r] |] eqn:Hstep; trivial. *)
(* destruct id as [g | b]; try now eapply Fin.case0; exact b. *)
(* remember (conf (Good g)) as pt. remember (f pt) as sim. *)
(* assert (Hsim : Proper (R2.eq ==> R2.eq) sim). { intros ? ? Heq. now rewrite Heq. } *)
(* simpl pgm. unfold ffgatherR2_pgm. *)
(* assert (Hperm : Permutation (map sim (Spect.support (!! conf))) *)
(*                             (Spect.support (!! (Config.map sim conf)))) *)
(*   by (now rewrite <- map_sim_support, <- PermutationA_Leibniz, Spect.from_config_map). *)
(* assert (Hlen := Permutation_length Hperm). *)
(* destruct (Spect.support (!! conf)) as [| pt1 [| pt2 l]] eqn:Hmax, *)
(*          (Spect.support (!! (Config.map sim conf))) as [| pt1' [| pt2' l']]; *)
(* simpl in Hlen; discriminate || clear Hlen. *)
(* - rewrite Spect.support_nil in Hmax. elim (spect_non_nil _ Hmax). *)
(* - simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm. *)
(*   subst pt1'. *)
(*   destruct (Rle_bool delta (R2.dist (r * sim pt1) pt)). *)
(*   assert (Hpt: pt = pt1). *)
(*   { generalize (Spect.from_config_spec conf). *)
(*     intros Hok. *)
(*     assert (Spect.In pt (!! conf)). *)
(*     { unfold Spect.is_ok in Hok. *)
(*       unfold Spect.In. *)
(*       rewrite (Hok pt). *)
(*       assert ((!! conf)[pt] > 0)%nat. *)
(*       { rewrite Hok. *)
(*         assert (InA R2.eq pt (Spect.Config.list conf)). *)
(*         { rewrite Config.list_InA. *)
(*           now exists (Good g). } *)
(*         rewrite countA_occ_pos; [ assumption | apply R2.eq_equiv ]. *)
(*       }         *)
(*       now rewrite <- Hok. *)
(*     } *)
(*     rewrite <- Spect.support_spec in H. *)
(*     rewrite Hmax in H. *)
(*     now rewrite InA_singleton in H. *)
(*   } *)
(*   rewrite Hpt in *. *)
(*   (* CONTINUE HERE. *) *)
  
(*   now apply Sim.compose_inverse_l. *)
(* - rewrite <- Spect.from_config_map, is_clean_morph; trivial. *)
(*   + destruct (is_clean (!! conf)). *)
(*     * rewrite <- Spect.from_config_map, target_morph; trivial; auto. *)
(*       now apply Sim.compose_inverse_l. *)
(*     * rewrite <- (Sim.center_prop sim). rewrite Heqsim at 3. rewrite (step_center da _ _ Hstep). *)
(*       assert (Hperm' : PermutationA eq (SECT (!! (Config.map sim conf))) (map sim (SECT (!! conf)))). *)
(*       { rewrite PermutationA_Leibniz, <- SECT_morph;auto. *)
(*         f_equiv. now rewrite Spect.from_config_map. } *)
(*     rewrite Hperm'. rewrite (mem_injective_map _); trivial; try (now apply Sim.injective); []. *)
(*     destruct (mem R2.eq_dec pt (SECT (!! conf))). *)
(*       -- rewrite <- (Sim.center_prop sim), Heqsim, (step_center _ _ _ Hstep). now apply Sim.compose_inverse_l. *)
(*       -- simpl. rewrite <- sim.(Similarity.Inversion), <- target_morph;auto. *)
(*          f_equiv. now apply Spect.from_config_map. *)
(* Qed. *)

Theorem round_lt_config : forall d conf delta,
    delta > 0 ->
    FullySynchronous d ->
    moving delta ffgatherR2 (Streams.hd d) conf <> nil ->
    measure conf > delta ->
    measure (round delta ffgatherR2 (Streams.hd d) conf) <= measure conf - delta.
Proof.
  intros d conf delta Hdelta HFSync Hmove Hnotdone.
  destruct (Spect.M.elements (!! conf)) as [| pt [| pt' ?]] eqn:Hmax.
  - (* No robots *)
    exfalso. now apply (support_non_nil conf). 
  - (* Done *)
    exfalso. clear Hdelta.
    unfold moving in Hmove.
    apply Hmove. clear Hmove.
    induction Names.names.
    + now simpl.
    + simpl.
      rewrite (round_simplify (Streams.hd d) conf delta).
      simpl.
      destruct (step (Streams.hd d) a).
      * rewrite Hmax. destruct p.
        generalize (Spect.from_config_spec conf).
        intro Hok. unfold Spect.is_ok in Hok.
        assert (Heq: R2.eq (conf a) (conf a)) by reflexivity.
        assert (exists gooda, R2.eq (conf a) (conf gooda)).
        { exists a. reflexivity. }
        rewrite <- Hok in H.
        rewrite <- Spect.M.elements_spec1 in H.
        rewrite Hmax in H.
        inversion H; subst.
        rewrite H1.
        destruct (Spect.MProp.MP.FM.eq_dec pt pt).
        -- apply IHl.
        -- exfalso; now apply n.
        -- inversion H1.
      * destruct (Spect.MProp.MP.FM.eq_dec (conf a) (conf a)).
        -- apply IHl.
        -- exfalso; now apply n.
  - (* Now to some real work. *)
    remember (Streams.hd d) as da.
    remember (Spect.M.elements (!! conf)) as elems.
    set (C := barycenter elems).
    remember (Spect.M.elements (!! (round delta ffgatherR2 da conf))) as nxt_elems.
    assert (Hantec: forall KP, In KP nxt_elems -> exists Pid, In (conf Pid) elems /\ round delta ffgatherR2 da conf Pid = KP).
    { intros KP HinKP.
      rewrite Heqnxt_elems in HinKP.
      apply (In_InA R2.eq_equiv) in HinKP.
      rewrite Spect.M.elements_spec1 in HinKP.
      generalize (Spect.from_config_spec (round delta ffgatherR2 da conf)).
      intro Hok. unfold Spect.is_ok in Hok.
      rewrite Hok in HinKP. clear Hok.
      destruct HinKP as (Pid, HPid).
      exists Pid.
      split; [|now rewrite HPid].
      generalize (Spect.from_config_spec conf).
      intro Hok. unfold Spect.is_ok in Hok.
      destruct (Hok (conf Pid)) as [_ Hex].
      apply InA_Leibniz.
      rewrite Heqelems.
      apply Spect.M.elements_spec1.
      apply Hex.
      now exists Pid.
    }

    assert (Hrobot_move_less_than_delta:
              forall Pid,
                In (conf Pid) elems ->
                delta > R2.dist (conf Pid) C ->
                round delta ffgatherR2 da conf Pid = C).
    { intros Pid HinP HdeltaP.
      rewrite round_simplify.
      remember (step da Pid) as Pact.
      destruct Pact.
      + simpl.
        destruct (Spect.M.elements (!! conf)) as [| q [| q' ?]].
        - subst elems. inversion Hmax.
        - subst elems. inversion Hmax.
        - rewrite <- Heqelems.
          destruct p.
          unfold Rle_bool.
          destruct (Rle_dec delta (R2norm (r * (barycenter elems - conf Pid)))) as [ Hdmove | Hdmove ].
          * assert (Hr: 0 <= snd (t, r) <= 1).
            { apply (step_flexibility da Pid). now symmetry. } simpl in Hr.
            destruct Hr as [Hr0 Hr1].
            destruct Hr1.
            ++ exfalso.
               rewrite R2norm_mul in Hdmove.
               rewrite <- R2norm_dist in Hdmove.
               rewrite R2.dist_sym in Hdmove.
               apply Rlt_irrefl with (r := delta).
               apply (Rle_lt_trans _ _ _ Hdmove).
               apply Rgt_lt in HdeltaP.
               apply Rlt_trans with (r2 := R2.dist (conf Pid) C);
                 [ | assumption].
               rewrite <- Rmult_1_l.
               apply Rmult_lt_compat_r.
               -- apply Rlt_le_trans with (r2 := delta).
                  ** now apply Rgt_lt.
                  ** apply (Rle_trans _ _ _ Hdmove).
                     rewrite <- Rmult_1_l.
                     apply Rmult_le_compat_r.
                     +++ apply R2.dist_pos.
                     +++ apply Rabs_le.
                         split.
                     --- apply Rle_trans with (r2 := -0).
                         apply Ropp_ge_le_contravar.
                         apply Rle_ge.
                         apply Rle_0_1.
                         now rewrite Ropp_0.                         
                     --- now left.
               -- apply Rabs_def1. assumption. apply Rlt_le_trans with (r2 := 0).
                  apply Rlt_le_trans with (r2 := -0).
                  apply Ropp_gt_lt_contravar.
                  apply Rlt_gt.
                  apply Rlt_0_1.
                  now rewrite Ropp_0.  assumption.
            ++ subst r. rewrite R2.mul_1.
               rewrite R2.add_assoc.
               pattern (conf Pid + barycenter elems)%R2.
               rewrite R2.add_comm.
               rewrite <- R2.add_assoc.
               rewrite R2.add_opp.
               rewrite R2.add_origin.
               now subst C.
          * now subst C.
      + unfold FullySynchronous in HFSync.
        unfold FullySynchronousInstant in HFSync.
        destruct d.
        simpl in Heqda.
        destruct HFSync.
        destruct (H Pid).
        simpl.
        subst d.
        now symmetry.
    }
          
    assert (Hrobot_move:
              forall Pid,
                In (conf Pid) elems ->
                delta <= R2.dist (conf Pid) C ->
                exists k, round delta ffgatherR2 da conf Pid =
                          (conf Pid + k * (C - (conf Pid)))%R2
                          /\
                          0 <= k <= 1
                          /\
                          delta <= R2norm (k * (C - (conf Pid)))).
    { intros Pid HinP HdeltaP.
      remember (round delta ffgatherR2 da conf Pid) as KP.
      rewrite round_simplify in HeqKP.
      remember (step da Pid) as Pact.
      destruct Pact.
      + simpl in HeqKP.
        destruct (Spect.M.elements (!! conf)) as [| q [| q' ?]].
        - subst elems. inversion Hmax.
        - subst elems. inversion Hmax.
        - rewrite <- Heqelems in HeqKP.
          destruct p.
          unfold Rle_bool in HeqKP.
          destruct (Rle_dec delta (R2norm (r * (barycenter elems - conf Pid)))) as [ Hdmove | Hdmove ].
          * assert (Hr: 0 <= snd (t, r) <= 1).
            { apply (step_flexibility da Pid). now symmetry. } simpl in Hr.
            exists r.
            repeat split; tauto.
          * exists 1.
            repeat split.
            ++ rewrite R2.mul_1.
               rewrite R2.add_comm.
               rewrite <- R2.add_assoc.
               pattern (- conf Pid + conf Pid)%R2.
               rewrite R2.add_comm.
               rewrite R2.add_opp.
               rewrite R2.add_origin.
               tauto.
            ++ apply Rle_0_1.
            ++ apply Rle_refl.
            ++ rewrite R2.mul_1.
               rewrite <- R2norm_dist.
               now rewrite R2.dist_sym.
      + unfold FullySynchronous in HFSync.
        unfold FullySynchronousInstant in HFSync.
        destruct d.
        simpl in Heqda.
        destruct HFSync.
        destruct (H Pid).
        simpl.
        subst d.
        now symmetry.
    }
        
    assert (MainArgument: forall KP KQ, In KP nxt_elems -> In KQ nxt_elems -> R2.dist KP KQ <= max_dist_spect (!! conf) - delta).
    { intros KP KQ HinKP HinKQ.
      apply Hantec in HinKP.
      apply Hantec in HinKQ.
      destruct HinKP as [Pid [HinP HroundP]].
      destruct HinKQ as [Qid [HinQ HroundQ]].

      destruct (Rle_dec delta (R2.dist (conf Pid) C)), (Rle_dec delta (R2.dist (conf Qid) C)).
      + generalize HinP.
        apply Hrobot_move in HinP; [|assumption].
        intro HinPP.
        generalize HinQ.
        apply Hrobot_move in HinQ; [|assumption].
        intro HinQQ.
        destruct HinP as [kp [kp_def [Hkple1 Hkplow]]].
        destruct HinQ as [kq [kq_def [Hkqle1 Hkqlow]]].
        rewrite kp_def in HroundP.
        rewrite kq_def in HroundQ.

        assert (HPnotC: ~ R2.eq (conf Pid) C).
        { intro.
          apply (Rlt_irrefl 0).
          apply Rlt_le_trans with (r2 := delta).
          assumption.
          apply R2.dist_defined in H.
          rewrite H in r.
          assumption. }
        assert (HQnotC: ~ R2.eq (conf Qid) C).
        { intro.
          apply (Rlt_irrefl 0).
          apply Rlt_le_trans with (r2 := delta).
          assumption.
          apply R2.dist_defined in H.
          rewrite H in r0.
          assumption. }
          
        destruct (Rle_dec kp kq).
        - apply Rle_trans with (r2 := (1 - kp) * (max_dist_spect (!! conf))).
          * subst KP KQ.
            apply distance_after_move; try assumption.
            apply Lemme2 with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            clear r1.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            destruct (Rlt_dec 0 kp); try assumption.
            exfalso.
            apply n.
            destruct Hkple1 as [[Hkplt0 | Hkpeq0] _].
            assumption.
            subst kp.
            apply Rlt_le_trans with (r2 := delta).
            assumption.
            rewrite R2.mul_0 in Hkplow.
            rewrite R2norm_origin in Hkplow.
            assumption.
            now destruct Hkqle1.
          * rewrite Rmult_comm.
            rewrite Rmult_minus_distr_l.
            rewrite Rmult_1_r.
            apply Rplus_le_compat_l.
            apply Ropp_ge_le_contravar.
            apply Rle_ge.
            apply (Rle_trans _ _ _ Hkplow).
            rewrite R2norm_mul.
            rewrite Rabs_pos_eq.
            rewrite Rmult_comm.
            apply Rmult_le_compat_r.
            now destruct Hkple1.
            rewrite <- R2norm_dist.
            rewrite R2.dist_sym.
            apply Lemme2 with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            now destruct Hkple1.
        - apply Rle_trans with (r2 := (1 - kq) * (max_dist_spect (!! conf))).
          * subst KP KQ.
            rewrite R2.dist_sym.
            apply distance_after_move; try assumption.
            apply Lemme2 with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            clear n.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            destruct (Rlt_dec 0 kq); try assumption.
            exfalso.
            apply n0.
            destruct Hkqle1 as [[Hkqlt0 | Hkqeq0] _].
            assumption.
            subst kq.
            apply Rlt_le_trans with (r2 := delta).
            assumption.
            rewrite R2.mul_0 in Hkqlow.
            rewrite R2norm_origin in Hkqlow.
            assumption.
            left. now apply Rnot_le_lt.            
            now destruct Hkple1.
          * rewrite Rmult_comm.
            rewrite Rmult_minus_distr_l.
            rewrite Rmult_1_r.
            apply Rplus_le_compat_l.
            apply Ropp_ge_le_contravar.
            apply Rle_ge.
            apply (Rle_trans _ _ _ Hkqlow).
            rewrite R2norm_mul.
            rewrite Rabs_pos_eq.
            rewrite Rmult_comm.
            apply Rmult_le_compat_r.
            now destruct Hkqle1.
            rewrite <- R2norm_dist.
            rewrite R2.dist_sym.
            apply Lemme2 with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            now destruct Hkqle1.

      + generalize HinP.
        apply Hrobot_move in HinP; [|assumption].
        intro HinPP.
        generalize HinQ.
        apply Hrobot_move_less_than_delta in HinQ.
        intro HinQQ.
        destruct HinP as [kp [kp_def [Hkple1 Hkplow]]].
        rewrite kp_def in HroundP.
        rewrite HinQ in HroundQ.

        subst KQ.
        apply Rle_trans with (r2 := R2.dist (conf Pid) C - delta).
        subst KP.
        rewrite R2norm_dist.
        assert (conf Pid + kp * (C - conf Pid) - C = (1 + - kp) * (conf Pid - C))%R2.
        { symmetry. rewrite <- R2.add_morph.
          rewrite R2.mul_1.
          replace (conf Pid - C)%R2 with (- (C - conf Pid))%R2 at 2.
          rewrite R2.mul_opp.
          rewrite R2.minus_morph.
          rewrite R2.opp_opp.
          rewrite <- R2.add_assoc.
          rewrite R2.add_comm with (u := (-C)%R2).
          now rewrite R2.add_assoc.
          rewrite R2.opp_distr_add.
          rewrite R2.opp_opp.
          now rewrite R2.add_comm.
        }
        rewrite H.
        rewrite R2norm_mul.
        rewrite R2norm_dist.
        rewrite Rabs_pos_eq.
        rewrite Rmult_plus_distr_r.
        rewrite Rmult_1_l.
        apply Rplus_le_compat_l.
        rewrite <- Ropp_mult_distr_l.
        apply Ropp_ge_le_contravar.
        apply Rle_ge.
        rewrite <- R2norm_dist.
        rewrite R2.dist_sym.
        rewrite R2norm_dist.
        rewrite <- Rabs_pos_eq with (x := kp).
        now rewrite <- R2norm_mul.
        now destruct Hkple1.
        apply Rplus_le_reg_r with (r := kp).
        rewrite Rplus_0_l.
        rewrite Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        now destruct Hkple1.
        apply Rplus_le_compat_r.
        apply Lemme2 with (E := elems).
        subst elems.
        rewrite Hmax; intro; discriminate.
        intros. apply max_dist_spect_le.
        now subst elems.
        now subst elems.
        now subst C.
        assumption.      
        now apply Rnot_le_gt.

      + generalize HinQ.
        apply Hrobot_move in HinQ; [|assumption].
        intro HinQQ.
        generalize HinP.
        apply Hrobot_move_less_than_delta in HinP.
        intro HinPP.
        destruct HinQ as [kq [kq_def [Hkqle1 Hkqlow]]].
        rewrite kq_def in HroundQ.
        rewrite HinP in HroundP.

        subst KP.
        apply Rle_trans with (r2 := R2.dist (conf Qid) C - delta).
        subst KQ.
        rewrite R2.dist_sym.
        rewrite R2norm_dist.
        assert (conf Qid + kq * (C - conf Qid) - C = (1 + - kq) * (conf Qid - C))%R2.
        { symmetry. rewrite <- R2.add_morph.
          rewrite R2.mul_1.
          replace (conf Qid - C)%R2 with (- (C - conf Qid))%R2 at 2.
          rewrite R2.mul_opp.
          rewrite R2.minus_morph.
          rewrite R2.opp_opp.
          rewrite <- R2.add_assoc.
          rewrite R2.add_comm with (u := (-C)%R2).
          now rewrite R2.add_assoc.
          rewrite R2.opp_distr_add.
          rewrite R2.opp_opp.
          now rewrite R2.add_comm.
        }
        rewrite H.
        rewrite R2norm_mul.
        rewrite R2norm_dist.
        rewrite Rabs_pos_eq.
        rewrite Rmult_plus_distr_r.
        rewrite Rmult_1_l.
        apply Rplus_le_compat_l.
        rewrite <- Ropp_mult_distr_l.
        apply Ropp_ge_le_contravar.
        apply Rle_ge.
        rewrite <- R2norm_dist.
        rewrite R2.dist_sym.
        rewrite R2norm_dist.
        rewrite <- Rabs_pos_eq with (x := kq).
        now rewrite <- R2norm_mul.
        now destruct Hkqle1.
        apply Rplus_le_reg_r with (r := kq).
        rewrite Rplus_0_l.
        rewrite Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        now destruct Hkqle1.
        apply Rplus_le_compat_r.
        apply Lemme2 with (E := elems).
        subst elems.
        rewrite Hmax; intro; discriminate.
        intros. apply max_dist_spect_le.
        now subst elems.
        now subst elems.
        now subst C.
        assumption.      
        now apply Rnot_le_gt.

      + apply Hrobot_move_less_than_delta in HinP.
        apply Hrobot_move_less_than_delta in HinQ.
        subst KP KQ.
        rewrite HinP, HinQ.
        assert (R2.dist C C = 0).
        { rewrite R2.dist_defined. apply R2.eq_equiv. }
        rewrite H.
        left.
        apply Rplus_lt_reg_r with (r := delta).
        rewrite Rplus_0_l.
        assert (max_dist_spect (!! conf) - delta + delta = max_dist_spect (!! conf)) by ring.
        rewrite H0.
        unfold measure in Hnotdone.
        now apply Rlt_gt.
        now apply Rnot_le_gt.
        now apply Rnot_le_gt.
    }

    unfold measure.
    generalize (max_dist_spect_ex (!!(round delta ffgatherR2 da conf))).
    intros Hmax_dist_ex.
    assert (Hspect_non_nil: nxt_elems <> nil).
    { rewrite Heqnxt_elems.
      apply support_non_nil. }
    rewrite <- Heqnxt_elems in Hmax_dist_ex.
    destruct (Hmax_dist_ex Hspect_non_nil) as [pt0 [pt1 [Hin0 [Hin1 Hdist]]]].
    rewrite <- Hdist.
    now auto.
    
Qed.

Definition lt_config delta x y :=
  lt (Z.to_nat (up (measure x / delta))) (Z.to_nat (up (measure y / delta))).

Lemma wf_lt_conf (delta: R) (Hdeltapos: delta > 0) : well_founded (lt_config delta).
Proof.
  unfold lt_config.
  apply wf_inverse_image.
  apply lt_wf.
Qed.


(** ***  With the termination, the rest of the proof is easy  **)

Lemma gathered_precise : forall config pt,
  gathered_at pt config -> forall id, gathered_at (config id) config.
Proof.
intros config pt Hgather id id'. transitivity pt.
- apply Hgather.
- symmetry. destruct id as [? | b]. apply Hgather. apply Fin.case0. exact b.
Qed.

Corollary not_gathered_generalize : forall config id,
  ~gathered_at (config id) config -> forall pt, ~gathered_at pt config.
Proof. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall config pt,
  ~ gathered_at pt config -> exists id, config id <> pt.
Proof.
intros config pt Hgather.
destruct (forallb (fun x => R2dec_bool (config x) pt) Names.names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite R2dec_bool_true_iff in Hall. hnf. repeat rewrite Hall; trivial; apply Names.In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']]. rewrite negb_true_iff, R2dec_bool_false_iff in Hid'. now exists id'.
Qed.

(* (** [FirstMove r d config] gives the number of rounds before one robot moves. *) *)
(* Inductive FirstMove r d config : Prop := *)
(*   | MoveNow : moving r (Streams.hd d) config <> nil -> FirstMove r d config *)
(*   | MoveLater : moving r (Streams.hd d) config = nil -> *)
(*                 FirstMove r (Streams.tl d) (round r (Streams.hd d) config) -> FirstMove r d config. *)

(* Instance FirstMove_compat : Proper (req ==> deq ==> Config.eq ==> iff) FirstMove. *)
(* Proof. *)
(* intros r1 r2 Hr d1 d2 Hd c1 c2 Hc. split; intro Hfirst. *)
(* * revert r2 d2 c2 Hr Hd Hc. induction Hfirst; intros r2 d2 c2 Hr Hd Hc. *)
(*   + apply MoveNow. now rewrite <- Hr, <- Hd, <- Hc. *)
(*   + apply MoveLater. *)
(*     - rewrite <- Hr, <- Hd, <- Hc. assumption. *)
(*     - destruct Hd. apply IHHfirst; trivial. now apply round_compat. *)
(* * revert r1 d1 c1 Hr Hd Hc. induction Hfirst; intros r1 d1 c1 Hr Hd Hc. *)
(*   + apply MoveNow. now rewrite Hr, Hd, Hc. *)
(*   + apply MoveLater. *)
(*     - rewrite Hr, Hd, Hc. assumption. *)
(*     - destruct Hd. apply IHHfirst; trivial. now apply round_compat. *)
(* Qed. *)

(* (** Correctness proof: given a non-gathered, non forbidden configuration, then some robot will move some day. *) *)
(* Theorem OneMustMove : forall config id, ~ forbidden config -> ~gathered_at (config id) config -> *)
(*   exists gmove, forall da, In gmove (active da) -> In gmove (moving gatherR2 da config). *)
(* Proof. *)
(* intros config id Hforbidden Hgather. *)
(* destruct (Spect.support (Spect.max (!! config))) as [| pt [| pt' lmax]] eqn:Hmax. *)
(* * elim (support_max_non_nil _ Hmax). *)
(* * rewrite <- MajTower_at_equiv in Hmax. *)
(*   apply not_gathered_generalize with _ _ pt in Hgather. *)
(*   apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove]. *)
(*   exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec. *)
(*   rewrite (round_simplify_Majority _ Hmax). destruct (step da gmove); auto; now elim Hactive. *)
(* * (* No majority tower *) *)
(*   get_case config. *)
(*   destruct (is_clean (!! config)) eqn:Hclean. *)
(*   + (* clean case *) *)
(*     apply not_gathered_generalize with _ _ (target (!! config)) in Hgather. *)
(*     apply not_gathered_exists in Hgather. destruct Hgather as [gmove Hmove]. *)
(*     exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec. *)
(*     rewrite round_simplify_clean; trivial. *)
(*     destruct (step da gmove); try (now elim Hactive); []. *)
(*     intuition. *)
(*   + (* dirty case *) *)
(*     assert (Hclean' := Hclean). unfold is_clean in Hclean'. clear Hmax pt pt' lmax. *)
(*     destruct (inclA_bool _ R2.eq_dec (Spect.support (!! config)) (SECT (!! config))) eqn:Hincl; *)
(*     try discriminate; []. *)
(*     rewrite inclA_bool_false_iff, (not_inclA _ R2.eq_dec) in Hincl. *)
(*     destruct Hincl as [pt [Hin Hin']]. *)
(*     rewrite Spect.support_In, Spect.from_config_In in Hin. *)
(*     destruct Hin as [gmove Hmove]. *)
(*     exists gmove. intros da Hactive. rewrite active_spec in Hactive. rewrite moving_spec. *)
(*     rewrite round_simplify_dirty; trivial. *)
(*     destruct (step da gmove); try (now elim Hactive); []. *)
(*     destruct (mem R2.eq_dec (config gmove) (SECT (!! config))) eqn:Htest. *)
(*     - rewrite mem_true_iff, Hmove in Htest. *)
(*       contradiction. *)
(*     - rewrite mem_false_iff, Hmove in Htest. *)
(*       assert (Htarget : InA R2.eq (target (!! config)) (SECT (!! config))) by now left. *)
(*       intro Habs. rewrite Habs, Hmove in *. *)
(*       contradiction. *)
(* Qed. *)

(* (** Given a k-fair demon, in any non gathered, non forbidden configuration, a robot will be the first to move. *) *)
(* Theorem Fair_FirstMove : forall d, Fair d -> *)
(*   forall config id, ~forbidden config -> ~gathered_at (config id) config -> FirstMove gatherR2 d config. *)
(* Proof. *)
(* intros d Hfair config id Hforbidden Hgathered. *)
(* destruct (OneMustMove id Hforbidden Hgathered) as [gmove Hmove]. *)
(* destruct Hfair as [locallyfair Hfair]. *)
(* revert config Hforbidden Hgathered Hmove Hfair. *)
(* specialize (locallyfair gmove). *)
(* induction locallyfair; intros config Hforbidden Hgathered Hmove Hfair. *)
(* + apply MoveNow. intro Habs. rewrite <- active_spec in H. apply Hmove in H. rewrite Habs in H. inversion H. *)
(* + destruct (moving gatherR2 (Streams.hd d) config) eqn:Hnil. *)
(*   - apply MoveLater. exact Hnil. *)
(*     rewrite (no_moving_same_conf _ _ _ Hnil). *)
(*     apply (IHlocallyfair); trivial. *)
(*     now destruct Hfair. *)
(*   - apply MoveNow. rewrite Hnil. discriminate. *)
(* Qed. *)

(** Define one robot to get the location whenever they are gathered. *)
Definition g1 : Fin.t nG.
Proof.
destruct nG eqn:HnG. abstract (pose(Hle := Hyp_nG); omega).
apply (@Fin.F1 n).
Defined.

Lemma singleton_characterization: forall (A:Type) (Aeq_dec: forall (a b: A), {a=b} + {a<>b}) (l: list A) (a: A),
    NoDup l ->
    In a l ->
    (forall b, ~ a = b -> ~ In b l) ->
    l = a :: nil.
Proof.
  intros A Aeq_dec l a Hnodup Hin Hnotin.
  destruct l.
  + inversion Hin.
  + destruct (Aeq_dec a a0).
    - subst. f_equal.
      destruct l.
      * reflexivity.
      * exfalso. apply (Hnotin a).
        inversion Hnodup.
        intro Heq.
        apply H1.
        subst.
        left.
        reflexivity.
        right.
        left.
        reflexivity.
    - exfalso.
      apply (Hnotin a0).
      assumption.
      left.
      reflexivity.
Qed.
      
Lemma gathered_at_forever : forall delta da conf pt, gathered_at pt conf -> gathered_at pt (round delta ffgatherR2 da conf).
Proof.
intros delta da conf pt Hgather. rewrite round_simplify.
intro g. destruct (step da (Good g)).

assert (Hptinspect: Spect.M.In pt (!!conf)).
{ unfold Spect.from_config.
  rewrite Spect.set_spec.
  rewrite Spect.Config.list_spec.

  assert (Spect.Names.names <> nil).
  { intro. 
    assert (length Spect.Names.names = nG).
    { rewrite Names.names_length. unfold N.nG, N.nB. omega. }
      rewrite <- length_zero_iff_nil in H.
    generalize Hyp_nG. omega.
  }

  destruct Spect.Names.names.  
  - exfalso; now apply H.
  - simpl. destruct i.
    * pattern (conf (Good g0)); rewrite Hgather.
      apply InA_cons_hd.
      apply R2.eq_equiv.
    * exfalso; apply (Fin.case0 _ b).
}

assert (Hnotpt_notinspect: forall q, ~ R2.eq q pt -> ~Spect.M.In q (!!conf)).
{ intros q Hnoteq.
  unfold Spect.from_config.
  rewrite Spect.set_spec.
  rewrite Spect.Config.list_spec.

  intro HinA.
  apply Hnoteq.
  generalize (@InA_map_iff Spect.Names.ident R2.t Logic.eq R2.eq).
  intro HInMapIff.  
  rewrite HInMapIff in HinA.
  destruct HinA as [x [Heq Hin]].
  rewrite <- Heq.
  destruct x.
  rewrite Hgather.
  reflexivity.
  exfalso; apply (Fin.case0 _ b).
  apply eq_equivalence.
  apply R2.eq_equiv.
  intros x y Heq.
  subst. apply R2.eq_equiv.
}

assert (Hspect: Spect.M.elements (!!conf) = pt :: nil).
{ apply singleton_characterization.
  apply R2.eq_dec.
  apply NoDupA_Leibniz.
  apply Spect.M.elements_spec2w.
  apply InA_Leibniz.  
  apply Spect.M.elements_spec1.
  assumption.
  intros b Hnoteq Hinb.
  apply (Hnotpt_notinspect b).
  intro.
  apply Hnoteq.
  rewrite H.
  reflexivity.
  rewrite <-  Spect.M.elements_spec1.
  apply InA_Leibniz.  
  assumption.
}  

simpl.
rewrite Hspect.
destruct p.
reflexivity.

rewrite Hgather.
reflexivity.

Qed.
    
Lemma gathered_at_OK : forall delta d conf pt, gathered_at pt conf -> Gather pt (execute delta ffgatherR2 d conf).
Proof.
cofix Hind. intros delta d conf pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind. now apply gathered_at_forever.
Qed.

(* Lemma move_to_barycenter: *)
(*   forall delta da conf g, *)
(*     round delta ffgatherR2 da conf g = barycenter (Spect.M.elements (!! conf)). *)
(* Proof. *)
(*   intros delta da conf g. *)
(*   rewrite round_simplify. *)
(*   simpl. *)
(*   remember (step da g) as Pact. *)
(*   destruct Pact. *)
(*   + destruct p. *)
(*     remember (Spect.M.elements (!! conf)) as elems. *)
(*     destruct elems. *)
(*     * exfalso. *)
(*       now apply (support_non_nil conf). *)
(*     * destruct elems. *)
(*       - unfold barycenter. simpl. destruct e. *)
(*         rewrite Rinv_1. *)
(*         rewrite R2.mul_1. *)
(*         f_equiv; ring. *)
(*       -  *)
    

Lemma not_barycenter_moves:
  forall delta d conf gid,
    delta > 0 ->
    FullySynchronous d ->
    ~R2.eq (conf gid) (barycenter (Spect.M.elements (!! conf))) ->
    ~R2.eq (round delta ffgatherR2 (Streams.hd d) conf gid) (conf gid).
Proof.
  intros delta d conf gid Hdelta HFSync Hnotbary Hnotmove.
  apply Hnotbary. clear Hnotbary.
  rewrite round_simplify in Hnotmove.
  remember (step (Streams.hd d) gid) as Pact.
  destruct Pact.
  - destruct p. simpl in Hnotmove.
    remember (Spect.M.elements (!! conf)) as elems.
    destruct elems.
    + exfalso. now apply (support_non_nil conf).
    + destruct elems.
      * unfold barycenter. simpl. destruct e.
        rewrite Rinv_1.
        rewrite R2.mul_1.
        do 2 rewrite Rplus_0_l.
        now rewrite <- Hnotmove.
      * remember (e :: e0 :: elems) as elems'.
        unfold Rle_bool in Hnotmove.
        destruct (Rle_dec delta (R2norm (r * (barycenter elems' - conf gid)))).
        -- rewrite <- R2.add_origin with (u := conf gid) in Hnotmove at 3.
           apply R2.add_reg_l in Hnotmove.
           apply R2.mul_integral in Hnotmove.
           destruct Hnotmove as [Hr0 | Heq].
           ++ exfalso.
              subst r.
              rewrite R2norm_mul in r0.
              rewrite Rabs_R0 in r0.
              rewrite Rmult_0_l in r0.
              apply Rlt_irrefl with delta.
              now apply (Rle_lt_trans _ _ _ r0).
           ++ now rewrite R2sub_origin in Heq.
        -- now symmetry.
  - unfold FullySynchronous in HFSync.
    unfold FullySynchronousInstant in HFSync.
    destruct d.
    simpl in HeqPact.
    destruct HFSync.
    destruct (H gid).
    simpl.
    now symmetry.
Qed.
           
           
(** The final theorem. *)
Theorem FSGathering_in_R2 :
  forall delta d, delta > 0 -> FullySynchronous d -> FullSolGathering ffgatherR2 d delta.
Proof.
intros delta d Hdelta HFS conf. revert d HFS. pattern conf.
apply (well_founded_ind (wf_lt_conf Hdelta)). clear conf.
intros conf Hind d HFS.
(* Are we already gathered? *)
destruct (gathered_at_dec conf (conf (Good g1))) as [Hmove | Hmove].
* (* If so, not much to do *)
  exists (conf (Good g1)). now apply Streams.Now, gathered_at_OK.
* (* Otherwise, we need to make an induction on fairness to find the first robot moving *)
  destruct d as (da, d).
  destruct (Hind (round delta ffgatherR2 da conf)) with d as [pt Hpt].
  + unfold lt_config.
    generalize (round_lt_config conf Hdelta HFS).
    simpl.
    assert (Hmoving: moving delta ffgatherR2 da conf <> nil).
    { intro Hmoving. apply Hmove.
      clear Hmove.
      unfold moving in Hmoving.
      assert (Hnoonemoves: forall g, R2.eq (round delta ffgatherR2 da conf (Good g)) (conf (Good g))).
      { intro g.
        destruct (R2.eq_dec (round delta ffgatherR2 da conf (Good g)) (conf (Good g))).
        + assumption.
        + exfalso.
          assert (Hing: In (Good g) Names.names).
          { unfold Names.names. unfold Names.Internals.names. apply in_or_app. left.
            apply in_map. unfold Names.Internals.Gnames.
            apply (@Names.Internals.In_fin_map nG Names.Internals.G g (fun x => x)).
          }
          assert (Hchoice: (if Spect.MProp.MP.FM.eq_dec (round delta ffgatherR2 da conf (Good g)) (conf (Good g)) then false else true) = true).
          { destruct (Spect.MProp.MP.FM.eq_dec (round delta ffgatherR2 da conf (Good g)) (conf (Good g))).
            + exfalso. apply n. assumption.
            + reflexivity.
          }
          assert (Hinnil: In (Good g) (filter
              (fun id : Spect.Names.ident =>
               if Spect.MProp.MP.FM.eq_dec (round delta ffgatherR2 da conf id) (conf id) then false else true)
              Names.names)).
          { apply filter_In. split; assumption. }
          rewrite Hmoving in Hinnil.
          inversion Hinnil.
      }
      unfold gathered_at.
      intro g.
      destruct (R2.eq_dec (conf (Good g)) (conf (Good g1))).
      + assumption.
      + exfalso.
        assert (~ (R2.eq (conf (Good g)) (barycenter (Spect.M.elements (!! conf))) /\ R2.eq (conf (Good g1)) (barycenter (Spect.M.elements (!! conf))))).
        { intro Hbar. apply n.
          destruct Hbar as [Hbarg Hbarg1].
          rewrite Hbarg, Hbarg1.
          reflexivity.
        }
        clear n.

        assert (~ R2.eq (conf (Good g)) (barycenter (Spect.M.elements (!! conf))) \/ ~ R2.eq (conf (Good g1)) (barycenter (Spect.M.elements (!! conf)))).
        { admit.
          (* Classical (or change the previous assert) *)
        }

        destruct H0.
        now apply (not_barycenter_moves conf (Good g) Hdelta HFS).
        now apply (not_barycenter_moves conf (Good g1) Hdelta HFS).
    }
        
    destruct (Rgt_dec (measure conf) delta).
    - intro Hroundlt.
      apply Hroundlt in Hmoving; [|assumption].
      clear Hroundlt r Hmove HFS.
      
      admit.
      (* Now it is only arithmetic. *)

    - intro Hroundlt. clear Hroundlt.
      
      assert (Hnxt: (measure (round delta ffgatherR2 da conf) = 0)%R).
      { unfold measure.
        remember (Spect.M.elements (!! conf)) as elems.
        set (C := barycenter elems).
        remember (Spect.M.elements (!! (round delta ffgatherR2 da conf))) as nxt_elems.
        assert (Hantec: forall KP, In KP nxt_elems -> exists Pid, In (conf Pid) elems /\ round delta ffgatherR2 da conf Pid = KP).
        { intros KP HinKP.
          rewrite Heqnxt_elems in HinKP.
          apply (In_InA R2.eq_equiv) in HinKP.
          rewrite Spect.M.elements_spec1 in HinKP.
          generalize (Spect.from_config_spec (round delta ffgatherR2 da conf)).
          intro Hok. unfold Spect.is_ok in Hok.
          rewrite Hok in HinKP. clear Hok.
          destruct HinKP as (Pid, HPid).
          exists Pid.
          split; [|now rewrite HPid].
          generalize (Spect.from_config_spec conf).
          intro Hok. unfold Spect.is_ok in Hok.
          destruct (Hok (conf Pid)) as [_ Hex].
          apply InA_Leibniz.
          rewrite Heqelems.
          apply Spect.M.elements_spec1.
          apply Hex.
          now exists Pid.
        }

        assert (HonlyC: forall KP, In KP nxt_elems -> R2.eq KP C).
        { intros KP HinKP.
          destruct (Hantec KP HinKP) as [Pid [HinP HroundP]].
          subst KP.
          rewrite round_simplify.
          remember (step da Pid) as Pact.
          destruct Pact.
          - destruct p. simpl.
            rewrite <- Heqelems.
            destruct elems.
            + inversion HinP.
            + destruct elems.
              * unfold C. unfold barycenter.
                simpl. rewrite Rinv_1.
                rewrite R2.mul_1.
                destruct e.
                now do 2 rewrite Rplus_0_l.
              * remember (e :: e0 :: elems) as elems'.
                unfold Rle_bool.
                destruct (Rle_dec delta (R2norm (r * (barycenter elems' - conf Pid)))).
                -- assert (Hr: 0 <= snd (t, r) <= 1).
                   { apply step_flexibility with da Pid. now symmetry. }
                   simpl in Hr.
                   destruct Hr as [Hr0 Hr1].
                   destruct Hr1 as [Hrlt1 | Hreq1].
                   ++ exfalso.
                      apply Rlt_irrefl with delta.
                      apply (Rle_lt_trans _ _ _ r0).
                      rewrite R2norm_mul.
                      rewrite (Rabs_pos_eq _ Hr0).
                      rewrite <- R2norm_dist.
                      assert (Hd: measure conf <= delta).
                      { apply Rnot_gt_le. assumption. }
                      assert (R2.dist (barycenter elems') (conf Pid) <= delta).
                      { rewrite R2.dist_sym.
                        apply Rle_trans with (measure conf).
                        apply Lemme2 with elems'.
                        rewrite Heqelems'. discriminate.
                        unfold measure.
                        intros. apply max_dist_spect_le.
                        now rewrite <- Heqelems. now rewrite <- Heqelems.
                        reflexivity.
                        assumption.
                        assumption.
                      }

                      (* There should be a lemma for this in standard library. *)
                      rewrite <- Rmult_1_l.
                      destruct H.
                      ** apply Rmult_le_0_lt_compat; try assumption.
                         apply R2.dist_pos.
                      ** subst delta.
                         apply Rmult_lt_compat_r.
                         now apply Rlt_gt.
                         assumption.
                                               
                   ++ subst r.
                      rewrite R2.mul_1.
                      rewrite R2.add_comm.
                      rewrite <- R2.add_assoc.
                      pattern (- conf Pid + conf Pid)%R2.
                      rewrite R2.add_comm.
                      rewrite R2.add_opp.
                      rewrite R2.add_origin.
                      now unfold C.

                -- now unfold C.

          - unfold FullySynchronous in HFS.
            inversion HFS.
            unfold FullySynchronousInstant in H.
            destruct (H Pid).
            simpl.
            now symmetry.
        }

        destruct (max_dist_spect_ex (!! (round delta ffgatherR2 da conf)))
        as [pt0 [pt1 [Hinpt0 [Hinpt1 Hdist]]]].
        apply support_non_nil.
        rewrite <- Hdist.
        rewrite HonlyC.
        rewrite (HonlyC pt1).
        now apply R2.dist_defined.
        now subst nxt_elems.
        now subst nxt_elems.
 
      }

      assert (Hcurrent: measure conf > 0).
      { admit.
        (* Sinon, pas rassemblés. *)
      }      
      
      admit.
      (* 0 < 1 *)

  + unfold FullySynchronous in HFS.
    inversion HFS.
    simpl in H0.
    now unfold FullySynchronous.

  + exists pt.
    unfold WillGather.
    apply Streams.Later.
    unfold execute.
    simpl.
    apply Hpt.

Admitted.
    
Print Assumptions FSGathering_in_R2.


(* (* Let us change the assumption over the demon, it is no longer fair *)
(*    but instead activates at least a robot that should move at each round *) *)
(* CoInductive OKunfair r (d : demon) config : Prop := *)
(*   AlwaysOKunfair : moving r (Streams.hd d) config <> nil ->  *)
(*   OKunfair r (Streams.tl d) (round gatherR2 (Streams.hd d) config) -> OKunfair r d config. *)

(* Theorem unfair_Gathering_in_R2 : forall d config, *)
(*   OKunfair gatherR2 d config -> ~forbidden config -> *)
(*   exists pt, WillGather pt (execute gatherR2 d config). *)
(* Proof. *)
(* intros d config Hunfair. revert d Hunfair. pattern config. *)
(* apply (well_founded_ind wf_lt_conf). clear config. *)
(* intros config Hind d Hunfair Hok. *)
(* (* Are we already gathered? *) *)
(* destruct (gathered_at_dec config (config (Good g1))) as [Hmove | Hmove]. *)
(* + (* If so, not much to do *) *)
(*   exists (config (Good g1)). now apply Streams.Now, gathered_at_OK. *)
(* + (* Otherwise, by assumption on the demon, a robot should move *)
(*      so we can use our well-founded induction hypothesis. *) *)
(*   destruct Hunfair as [Hstep Hunfair]. *)
(*   destruct (Hind (round gatherR2 (Streams.hd d) config)) with (Streams.tl d) as [pt Hpt]. *)
(*   - apply round_lt_config; assumption. *)
(*   - assumption. *)
(*   - now apply never_forbidden. *)
(*   - exists pt. apply Streams.Later. rewrite execute_tail. apply Hpt. *)
(* Qed. *)

End GatheringinR2.
