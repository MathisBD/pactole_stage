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
    assert (forall KP KQ, In KP nxt_elems -> In KQ nxt_elems -> R2.dist KP KQ <= max_dist_spect (!! conf) - delta).
    { intros KP KQ HinKP HinKQ.
      apply Hantec in HinKP.
      apply Hantec in HinKQ.
      destruct HinKP as [Pid [HinP HroundP]].
      destruct HinKQ as [Qid [HinQ HroundQ]].

      rewrite round_simplify in HroundP.
      remember (step da Pid) as Pact.
      destruct Pact.
      + simpl in HroundP.
        destruct (Spect.M.elements (!! conf)) as [| q [| q' ?]].
        - subst elems. inversion Hmax.
        - subst elems. inversion Hmax.
        - rewrite <- Heqelems in HroundP.
          destruct p.
          destruct (Rle_bool delta (R2norm (r * (barycenter elems - conf Pid)))).
          * assert (Hr: 0 <= snd (t, r) <= 1).
            { apply (step_flexibility da Pid). now symmetry. } simpl in Hr.
            
            
            
        generalize 
    
    
        simpl.
        assumption.
        inversion H1.
      
    assert(Htarget_pt: forall id, round delta ffgatherR2 da conf id = pt).
    { intro.
      unfold round.
      destruct (step da id).
      + destruct p. destruct id.
        assert (conf (Good g) = pt).
        { generalize (Spect.from_config_spec conf).
          intro Hok. unfold Spect.is_ok in Hok.
          assert (Heq: R2.eq (conf (Good g)) (conf (Good g))) by reflexivity.
          assert (exists goodg, R2.eq (conf (Good g)) (conf goodg)).
          { exists (Good g). reflexivity. }
          rewrite <- Hok in H.
          rewrite <- Spect.M.elements_spec1 in H.
          rewrite Hmax in H.
          inversion H; subst.
          assumption.
          inversion H1.
        }          
        rewrite H in *.
        assert (R2.eq (ffgatherR2 (!! (Config.map (Common.Sim.sim_f (t pt)) conf))) pt).
        { rewrite <- Spect.from_config_map.
        
        destruct (R2.eq_dec (conf (Good g)) pt).
          + auto.
          + 
            
          rewrite <- Hok.
          rewrite Spect.from_config_spec in Hmax.
          unfold Spect.M.elements in Hmax.

        * destruct (Rle_bool delta
                             (R2.dist
                                ((Common.Sim.sim_f (t (conf (Good g)) ⁻¹))
                                   (r * ffgatherR2 (!! (Config.map (Common.Sim.sim_f (t (conf (Good g)))) conf)))%R2)
                                (conf (Good g)))).
          - assert (conf (Good g) = pt).
        

Admitted.

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

Lemma gathered_at_forever : forall delta da conf pt, gathered_at pt conf -> gathered_at pt (round delta ffgatherR2 da conf).
Proof.
intros delta da conf pt Hgather. rewrite round_simplify.
intro g. destruct (step da (Good g)).
assert (Hspect: Spect.M.elements (!!conf) = pt :: nil).
{ unfold Spect.M.elements, Spect.M.Raw.elements, Spect.M.this, Spect.from_config.
  unfold Spect.set.
  rewrite Spect.Config.list_spec.


  assert (Spect.Names.names <> nil).
  { intro. 
    assert (length Spect.Names.names = nG).
    { rewrite Names.names_length. unfold N.nG, N.nB. omega. }
      rewrite <- length_zero_iff_nil in H.
    generalize Hyp_nG. omega.
  }
  
  induction Spect.Names.names.
  - exfalso. tauto.
  - 
    
(*   unfold map. *)
  
(*   unfold gathered_at in Hgather. *)
  
  
(* assert (Hpt: forall e, InA R2.eq e (Spect.M.elements (!!conf)) -> R2.eq e pt). *)
(* intros. apply (Hgather ). *)

(* assert (Hbary: R2.eq (barycenter (Spect.M.elements (!!conf))) pt). *)
(* unfold gathered_at in Hgather. *)
(* rewrite Hgather. *)


(* + intro g. destruct (step da (Good g)); reflexivity || apply Hgather. *)
(* + intros pt' Hdiff. *)
(*   assert (H0 : (!! conf)[pt'] = 0). *)
(*   { rewrite Spect.from_config_spec, Spect.Config.list_spec. *)
(*     induction Spect.Names.names as [| id l]. *)
(*     + reflexivity. *)
(*     + cbn. R2dec_full. *)
(*       - elim Hdiff. rewrite <- Heq. destruct id as [g | b]. apply Hgather. apply Fin.case0. exact b. *)
(*       - apply IHl. } *)
(*   rewrite H0. specialize (Hgather g1). rewrite <- Hgather. apply Spect.pos_in_config. *)
(* Qed. *)
Admitted.
    
Lemma gathered_at_OK : forall delta d conf pt, gathered_at pt conf -> Gather pt (execute delta ffgatherR2 d conf).
Proof.
cofix Hind. intros delta d conf pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind. now apply gathered_at_forever.
Qed.

(** The final theorem. *)
Theorem Gathering_in_R2 :
  forall delta d, delta > 0 -> FullySynchronous d -> ValidSolGathering ffgatherR2 d delta.
Proof.
intros delta d Hfair conf. revert d Hfair. pattern conf.
apply (well_founded_ind wf_lt_conf). clear conf.
intros conf Hind d Hfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec conf (conf (Good g1))) as [Hmove | Hmove].
* (* If so, not much to do *)
  exists (conf (Good g1)). now apply Streams.Now, gathered_at_OK.
* (* Otherwise, we need to make an induction on fairness to find the first robot moving *)
  apply (Fair_FirstMove Hfair (Good g1)) in Hmove; trivial.
  induction Hmove as [d conf Hmove | d conf Heq Hmove Hrec].
  + (* Base case: we have first move, we can use our well-founded induction hypothesis. *)
    destruct (Hind (round gatherR2 (Streams.hd d) conf)) with (Streams.tl d) as [pt Hpt].
    - apply round_lt_config; assumption.
    - now destruct Hfair.
    - now apply never_forbidden.
    - exists pt. apply Streams.Later. rewrite execute_tail. apply Hpt.
  + (* Inductive case: we know by induction hypothesis that the wait will end *)
    apply no_moving_same_conf in Heq.
    destruct Hrec as [pt Hpt].
    - setoid_rewrite Heq. apply Hind.
    - now destruct Hfair.
    - rewrite Heq. assumption.
    - exists pt. apply Streams.Later. rewrite execute_tail. apply Hpt.
Qed.

Print Assumptions Gathering_in_R2.


(* Let us change the assumption over the demon, it is no longer fair
   but instead activates at least a robot that should move at each round *)
CoInductive OKunfair r (d : demon) config : Prop :=
  AlwaysOKunfair : moving r (Streams.hd d) config <> nil -> 
  OKunfair r (Streams.tl d) (round gatherR2 (Streams.hd d) config) -> OKunfair r d config.

Theorem unfair_Gathering_in_R2 : forall d config,
  OKunfair gatherR2 d config -> ~forbidden config ->
  exists pt, WillGather pt (execute gatherR2 d config).
Proof.
intros d config Hunfair. revert d Hunfair. pattern config.
apply (well_founded_ind wf_lt_conf). clear config.
intros config Hind d Hunfair Hok.
(* Are we already gathered? *)
destruct (gathered_at_dec config (config (Good g1))) as [Hmove | Hmove].
+ (* If so, not much to do *)
  exists (config (Good g1)). now apply Streams.Now, gathered_at_OK.
+ (* Otherwise, by assumption on the demon, a robot should move
     so we can use our well-founded induction hypothesis. *)
  destruct Hunfair as [Hstep Hunfair].
  destruct (Hind (round gatherR2 (Streams.hd d) config)) with (Streams.tl d) as [pt Hpt].
  - apply round_lt_config; assumption.
  - assumption.
  - now apply never_forbidden.
  - exists pt. apply Streams.Later. rewrite execute_tail. apply Hpt.
Qed.

End GatheringinR2.
