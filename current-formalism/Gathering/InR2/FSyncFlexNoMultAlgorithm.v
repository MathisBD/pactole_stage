
(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
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

(** **  Framework of the correctness proof: a finite set with at least two elements  **)

Parameter nG: nat.
Axiom Hyp_nG : (2 <= nG)%nat.

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
intros sim s. rewrite <- PermutationA_Leibniz. apply Spect.map_injective_elements.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall conf, ~Spect.eq (!! conf) Spect.M.empty.
Proof. apply spect_non_nil. assert (Hle := Hyp_nG). unfold N.nG. omega. Qed.

Lemma support_non_nil : forall config, Spect.M.elements (!! config) <> nil.
Proof.
intros config Habs.
rewrite <- Spect.MProp.MP.elements_Empty in Habs.
apply Spect.MProp.MP.empty_is_empty_1 in Habs.
apply (spect_non_nil _ Habs).
Qed.

Lemma gathered_at_dec : forall conf pt, {gathered_at pt conf} + {~gathered_at pt conf}.
Proof.
intros conf pt.
destruct (forallb (fun id => R2dec_bool (conf id) pt) Names.names) eqn:Hall.
+ left. rewrite forallb_forall in Hall. intro g. rewrite <- R2dec_bool_true_iff. apply Hall. apply Names.In_names.
+ right. rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall. destruct Hall as [id [Hin Heq]].
  destruct id as [g | b]; try now apply Fin.case0; exact b. intro Habs. specialize (Habs g).
  rewrite negb_true_iff, R2dec_bool_false_iff in Heq. contradiction.
Qed.

(** Define one robot to get their location whenever they are gathered. *)
Definition g1 : Fin.t nG.
Proof.
destruct nG eqn:HnG. abstract (pose(Hle := Hyp_nG); omega).
apply (@Fin.F1 n).
Defined.

(** **  Description of similarities  **)

(** Similarities can be described by [sim x = r A x + t] with:
    - [0 < r] the ratio
    - [t] the translation vector
    - [A] an orthogonal matrix *)
(* NB: To have less parameters, [r] is integrated into [A]. *)
Open Scope R_scope.

Theorem similarity_in_R2 : forall sim : Sim.t,
  exists u v t, R2norm u = sim.(Sim.zoom) /\ R2norm v = sim.(Sim.zoom) /\ perpendicular u v /\
    forall pt, sim pt = R2.add (R2.add (R2.mul (product u pt) u) (R2.mul (product v pt) v)) t.
Proof.
intros sim. exists (sim (1, 0) - sim (0, 0))%R2, (sim (0, 1) - sim (0, 0))%R2, (sim (0, 0)).
repeat split.
* rewrite <- R2norm_dist, sim.(Sim.dist_prop), <- Rmult_1_r. f_equal.
  unfold R2.dist, R2def.dist, Rsqr. cbn.
  ring_simplify ((1 - 0) * (1 - 0) + (0 - 0) * (0 - 0)). apply sqrt_1.
* rewrite <- R2norm_dist, sim.(Sim.dist_prop), <- Rmult_1_r. f_equal.
  unfold R2.dist, R2def.dist, Rsqr. cbn.
  ring_simplify ((0 - 0) * (0 - 0) + (1 - 0) * (1 - 0)). apply sqrt_1.
* assert (Hproduct : forall x y, 2 * product x y = (R2norm x)² + (R2norm y)² - (R2norm (x - y))²).
  { intros x y. rewrite R2norm_sub. ring. }
  unfold perpendicular. apply Rmult_eq_reg_l with 2; try lra.
  rewrite Hproduct, Rmult_0_r.
  repeat rewrite <- R2norm_dist. rewrite R2add_dist. repeat rewrite sim.(Sim.dist_prop).
  repeat rewrite R_sqr.Rsqr_mult, square_dist_simpl. unfold Rsqr. cbn. ring.
* intros [x y].
  
Admitted.

Corollary sim_add : forall (sim : Sim.t) x y, (sim (x + y) = sim x + sim y - sim R2.origin)%R2.
Proof.
intros sim x y. destruct (similarity_in_R2 sim) as [u [v [t [Hu [Hv [Huv Heq]]]]]].
repeat rewrite Heq, ?product_origin_r, ?product_add_r, <- ?R2.add_morph, ?R2.mul_0.
rewrite R2.add_origin, (R2.add_comm R2.origin t), R2.add_origin.
repeat rewrite <- R2.add_assoc. rewrite R2.add_opp, R2.add_origin. f_equal.
rewrite (R2.add_comm t). repeat rewrite R2.add_assoc. do 2 f_equal. apply R2.add_comm.
Qed.

Corollary sim_opp : forall (sim : Sim.t) x, (sim (- x) = 2 * sim R2.origin - sim x)%R2.
Proof.
intros sim x. apply (R2.add_reg_l (sim x)). apply (R2.add_reg_r (- sim R2.origin)).
rewrite <- sim_add, R2.add_opp.
setoid_rewrite R2.add_comm at 3. rewrite R2.add_assoc, R2.add_opp.
setoid_rewrite R2.add_comm at 2. rewrite R2.add_origin.
setoid_rewrite <- R2.mul_1 at 8. rewrite <- R2.minus_morph, R2.add_morph.
ring_simplify (2 + -1). now rewrite R2.mul_1.
Qed.

Corollary sim_mul : forall (sim : Sim.t) k x, (sim (k * x) = k * sim x + (1 - k) * sim R2.origin)%R2.
Proof.
intros sim k x. destruct (similarity_in_R2 sim) as [u [v [t [Hu [Hv [Huv Heq]]]]]].
repeat rewrite Heq, ?product_origin_r, ?product_mul_r, <- ?R2.add_morph, ?R2.mul_0.
rewrite R2.add_origin, (R2.add_comm R2.origin t), R2.add_origin.
repeat rewrite R2.mul_distr_add, ?R2.mul_morph. repeat rewrite <- R2.add_assoc. do 2 f_equal.
rewrite R2.add_morph. ring_simplify (k + (1 - k)). now rewrite R2.mul_1.
Qed.


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


Open Scope R_scope.

(* Coercion Spect.Names.names : list Spect.Names.Internals.ident >-> list Spect.Names.ident. *)

Definition max_dist_R2_pt_list (pt: R2.t) (l: list R2.t) : R :=
  fold_right (fun pt1 max => Rmax (R2.dist pt pt1) max) 0 l.


(* Lemma max_dist_R2_pt_list_compat : Proper (R2.eq ==> PermutationA R2.eq ==> Logic.eq) max_dist_R2_pt_list. *)

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

Lemma max_dist_R2_pt_list_0 : forall pt l, max_dist_R2_pt_list pt l = 0 <-> forall x, In x l -> x = pt.
Proof.
intros pt l. destruct l as [| pt' l].
* cbn. tauto.
* split; intro H.
  + intros x Hin. assert (Hle := max_dist_R2_pt_list_le pt (pt' :: l) x Hin).
    rewrite H in Hle. symmetry. rewrite <- R2.dist_defined. apply antisymmetry; trivial. apply R2.dist_pos.
  + destruct (@max_dist_R2_pt_list_ex pt (pt' :: l) ltac:(discriminate)) as [? [Hin Heq]].
    apply H in Hin. subst. rewrite <- Heq. apply R2_dist_defined_2.
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

Lemma max_dist_R2_list_list_cons_le : forall pt l,
  max_dist_R2_list_list l l <= max_dist_R2_list_list (pt :: l) (pt :: l).
Proof.
intros pt [| pt' l].
- cbn. rewrite R2_dist_defined_2. now repeat rewrite Rmax_left.
- destruct (@max_dist_R2_list_list_ex (pt' :: l) (pt' :: l)) as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]]; try discriminate; [].
  rewrite <- Heq. apply max_dist_R2_list_list_le; now right.
Qed.

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


(** **  Main result for termination: the measure decreases after a step where a robot moves  *)

Definition measure (conf: Config.t) : R :=
  max_dist_spect (!! conf).

Lemma measure_nonneg : forall config, 0 <= measure config.
Proof.
intros config. unfold measure.
destruct (Spect.M.elements (!! config)) as [| pt l] eqn:Heq.
+ elim (support_non_nil _ Heq).
+ rewrite <- (R2_dist_defined_2 pt). apply max_dist_spect_le; rewrite Heq; now left.
Qed.

Lemma gathered_support : forall config pt,
  gathered_at pt config <-> PermutationA eq (Spect.M.elements (!! config)) (pt :: nil).
Proof.
intros config pt. split; intro H.
* apply NoDupA_equivlistA_PermutationA; autoclass.
  + apply Spect.M.elements_spec2w.
  + repeat constructor. intro Hin. inv Hin.
  + intro pt'. split; intro Hin.
    - rewrite Spect.M.elements_spec1, (Spect.from_config_spec config pt') in Hin.
      destruct Hin as [id Hid]. destruct id as [id | b]; try apply (Fin.case0 _ b); [].
      specialize (H id). rewrite H in Hid. rewrite Hid. now left.
    - inv Hin; try inv H1; [].
      rewrite Spect.M.elements_spec1, (Spect.from_config_spec config pt).
      exists (Good g1). symmetry. apply H.
* intro id.
  assert (Hin : InA eq (config (Good id)) (Spect.M.elements (!! config))).
  { rewrite Spect.M.elements_spec1. apply (Spect.from_config_spec config). eexists; reflexivity. }
  rewrite H in Hin. now inv Hin.
Qed.

Lemma gathered_measure : forall config, measure config = 0 <-> exists pt, gathered_at pt config.
Proof.
intros config. split; intro H.
* unfold measure, max_dist_spect in *.
  assert (Hnil := support_non_nil config).
  assert (Hdup := Spect.M.elements_spec2w (!! config)).
  setoid_rewrite gathered_support.
  induction (Spect.M.elements (!! config)) as [| pt l]; try tauto; [].
  exists pt. destruct l; try reflexivity.
  inv Hdup. destruct IHl; discriminate || auto.
  + apply antisymmetry.
    - rewrite <- H. apply max_dist_R2_list_list_cons_le.
    - rewrite <- (R2_dist_defined_2 e). apply max_dist_R2_list_list_le; now left.
  + assert (l = nil).
    { rewrite <- length_zero_iff_nil.
      cut (length (e :: l) = length (x :: nil)); try (simpl; omega).
      f_equiv; eauto. }
    subst. rewrite PermutationA_1 in H0; autoclass; []. subst.
    elim H2. left.
    cbn in H. do 2 rewrite R2_dist_defined_2 in H.
    cbn in H. setoid_rewrite (Rmax_comm 0) in H. rewrite (Rmax_left 0 0) in H; try reflexivity; [].
    rewrite R2.dist_sym in H. repeat (rewrite (Rmax_left (R2.dist pt x) 0) in H; try apply R2.dist_pos).
    rewrite Rmax_left in H; try reflexivity; [].
    now rewrite <- R2.dist_defined.
* destruct H as [pt Hgather]. unfold measure.
  destruct (max_dist_spect_ex (!! config) (support_non_nil config)) as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]].
  rewrite <- Heq, R2.dist_defined. rewrite gathered_support in Hgather. rewrite <- InA_Leibniz, Hgather in *.
  now inv Hpt1; inv Hpt2.
Qed.

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
Proof. intros sim x y. rewrite Sim.dist_prop. now simpl. Qed.

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
* elim (support_non_nil _ Hmax).
* simpl in Hperm. rewrite <- PermutationA_Leibniz, (PermutationA_1 _) in Hperm.
  subst pt1'.
  destruct (Rle_bool delta (R2.dist ((Common.Sim.sim_f (sim ⁻¹)) (r * sim pt1)%R2) pt)).
  + assert (Hpt: pt = pt1).
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
  + now apply Sim.compose_inverse_l.

* assert (Hbarysim: R2.eq (barycenter (pt1' :: pt2' :: l')) (sim (barycenter (pt1 :: pt2 :: l)))).
  { rewrite <- barycenter_sim.
    apply barycenter_compat.
    now rewrite PermutationA_Leibniz.
    discriminate. }
  repeat rewrite Hbarysim.
  clear Hperm Hbarysim.
  remember (pt1 :: pt2 :: l) as E.

  assert (Heq_pt : pt = (sim ⁻¹) (sim pt)).
  { simpl. rewrite Similarity.retraction_section; autoclass. }
  rewrite Heq_pt at 1.
  rewrite dist_prop_retraction.
  rewrite R2norm_mul.
  rewrite <- R2norm_dist.
  assert (Hsim_pt : R2.eq (sim pt) (r * (sim pt))).
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
  rewrite Hsim_pt.
  rewrite R2mul_dist.
  rewrite <- Rmult_assoc.
  pattern (/ Sim.zoom sim * Rabs r).
  rewrite Rmult_comm.
  rewrite Rmult_assoc.
  rewrite <- dist_prop_retraction.
  rewrite <- Heq_pt.
  simpl.
  rewrite Similarity.retraction_section; autoclass; [].

  destruct (Rle_bool delta (Rabs r * R2.dist (barycenter E) pt)).
  + apply Similarity.Inversion.
    rewrite sim_add, sim_mul, sim_add, sim_opp.
    do 2 rewrite R2.mul_distr_add.
    assert (Hsim_pt_0 : R2.eq (sim pt) R2.origin).
    { apply (step_center da (Good g) pt) in Hstep.
      rewrite <- sim.(Sim.center_prop), <- Hstep. cbn. now subst sim. }
    rewrite Hsim_pt_0.
    rewrite (R2.add_comm R2.origin), R2.add_origin.
    setoid_rewrite <- R2.add_origin at 25. repeat rewrite <- R2.add_assoc. f_equiv.
    rewrite R2.opp_origin, R2.add_origin.
    setoid_rewrite <- R2.mul_1 at 9 15. repeat rewrite <- ?R2.minus_morph, ?R2.mul_morph, ?R2.add_morph.
    ring_simplify (r * 2 + (r * -1 + (1 - r + -1))). apply R2.mul_0.
  + rewrite Similarity.retraction_section; autoclass.
Qed.


(* FIXME: cleanup! *)
Theorem round_lt_config : forall d conf delta,
    delta > 0 ->
    FullySynchronous d ->
    delta <= measure conf ->
    measure (round delta ffgatherR2 (Streams.hd d) conf) <= measure conf - delta.
Proof.
  intros d conf delta Hdelta HFSync Hnotdone.
  destruct (Spect.M.elements (!! conf)) as [| pt [| pt' ?]] eqn:Hmax.
  - (* No robots *)
    exfalso. now apply (support_non_nil conf).
  - (* Done *)
    assert (Habs : measure conf = 0).
    { rewrite gathered_measure. exists pt. now rewrite gathered_support, Hmax. }
    rewrite Habs in *. elim (Rlt_irrefl delta). now apply Rle_lt_trans with 0.
  - (* Now to some real work. *)
    remember (Streams.hd d) as da.
    remember (Spect.M.elements (!! conf)) as elems.
    set (C := barycenter elems).
    remember (Spect.M.elements (!! (round delta ffgatherR2 da conf))) as nxt_elems.
    assert (Hantec: forall KP, In KP nxt_elems ->
              exists Pid, In (conf Pid) elems /\ round delta ffgatherR2 da conf Pid = KP).
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

    assert (MainArgument: forall KP KQ, In KP nxt_elems -> In KQ nxt_elems ->
            R2.dist KP KQ <= max_dist_spect (!! conf) - delta).
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
        apply Rplus_le_reg_r with (r := delta).
        rewrite Rplus_0_l.
        assert (max_dist_spect (!! conf) - delta + delta = max_dist_spect (!! conf)) by ring.
        rewrite H0.
        apply Hnotdone.
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

(* FIXME: cleanup! *)
Theorem round_last_step : forall d conf delta,
    delta > 0 ->
    FullySynchronous d ->
    measure conf <= delta ->
    measure (round delta ffgatherR2 (Streams.hd d) conf) = 0.
Proof.
intros [da d] conf delta Hdelta HFS Hlt.
unfold measure.
remember (Spect.M.elements (!! conf)) as elems.
set (C := barycenter elems).
remember (Spect.M.elements (!! (round delta ffgatherR2 da conf))) as nxt_elems.
assert (Hantec: forall KP, In KP nxt_elems ->
                  exists Pid, In (conf Pid) elems /\ round delta ffgatherR2 da conf Pid = KP).
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
simpl. rewrite <- Hdist.
rewrite HonlyC.
rewrite (HonlyC pt1).
now apply R2.dist_defined.
now subst nxt_elems.
now subst nxt_elems.
Qed.

Definition lt_config delta x y :=
  lt (Z.to_nat (up (measure x / delta))) (Z.to_nat (up (measure y / delta))).

Lemma wf_lt_conf (delta: R) (Hdeltapos: delta > 0) : well_founded (lt_config delta).
Proof.
  unfold lt_config.
  apply wf_inverse_image.
  apply lt_wf.
Qed.

Lemma lt_config_decrease : forall delta config1 config2, 0 < delta ->
  measure config1 <= measure config2 - delta -> lt_config delta config1 config2.
Proof.
intros delta config1 config2 Hdelta Hle. unfold lt_config.
rewrite <- Z2Nat.inj_lt.
+ apply Zup_lt. field_simplify; try lra. unfold Rdiv. apply Rmult_le_compat.
  - apply measure_nonneg.
  - apply Rlt_le. now apply Rinv_0_lt_compat.
  - lra.
  - reflexivity.
+ apply le_IZR. transitivity (measure config1 / delta).
  - simpl. apply Rdiv_le_0_compat; trivial. apply measure_nonneg.
  - apply Rlt_le, (proj1 (archimed _)).
+ apply le_IZR. transitivity (measure config2 / delta).
  - simpl. apply Rdiv_le_0_compat; trivial. apply measure_nonneg.
  - apply Rlt_le, (proj1 (archimed _)).
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

Lemma gathered_at_forever : forall delta da conf pt,
  gathered_at pt conf -> gathered_at pt (round delta ffgatherR2 da conf).
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
intros conf Hind [da d] HFS. 
(* Are we already gathered? *)
destruct (gathered_at_dec conf (conf (Good g1))) as [Hmove | Hmove];
[| destruct (gathered_at_dec (round delta ffgatherR2 da conf)
                             (round delta ffgatherR2 da conf (Good g1))) as [Hmove' | Hmove']].
* (* If we are already gathered, not much to do *)
  exists (conf (Good g1)). now apply Streams.Now, gathered_at_OK.
* (* If we are gathered at the next step, not much to do either. *)
  exists (round delta ffgatherR2 da conf (Good g1)). now apply Streams.Later, Streams.Now, gathered_at_OK.
* (* General case, use [round_lt_config] *)
  assert (delta <= measure conf).
  { apply Rnot_lt_le. intro Habs. eapply Rlt_le, round_last_step in Habs; eauto; [].
    rewrite gathered_measure in Habs. destruct Habs as [pt Habs]. simpl in Habs.
    apply Hmove'. apply (gathered_precise Habs (Good g1)). }
  destruct (Hind (round delta ffgatherR2 da conf)) with d as [pt Hpt].
  + apply lt_config_decrease; trivial; [].
    change da with (Streams.hd (Streams.cons da d)).
    now apply round_lt_config.
  + now destruct HFS.
  + exists pt. apply Streams.Later. apply Hpt.
Qed.


Print Assumptions FSGathering_in_R2.


End GatheringinR2.
