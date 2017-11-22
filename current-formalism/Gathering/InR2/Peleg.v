(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
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
Require Import Pactole.MultisetSpectrum.
Require Import Pactole.Lexprod.
Require Import Pactole.Gathering.InR2.R2geometry.
Require Import Pactole.Gathering.FlexDefinitionsMultiset.


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
Module Defs := FlexDefinitionsMultiset.FlexGatheringDefs(R2)(N).
Import Defs.

Lemma no_byz : forall (id : Names.ident) P, (forall g, P (Good g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. unfold N.nB in *. omega.
Qed.

Lemma no_byz_eq : forall config1 config2 : Config.t,
  (forall g, R2.eq (Config.loc (config1 (Good g))) (Config.loc (config2 (Good g)))) -> Config.eq config1 config2.
Proof. intros config1 config2 Heq id. apply no_info, (no_byz id). intro g. apply Heq. Qed.

Lemma Config_list_alls : forall pt, Config.list (fun _ => pt) = alls pt N.nG.
Proof.
intro. rewrite Config.list_spec, map_cst.
setoid_rewrite Names.names_length. unfold N.nB. now rewrite plus_0_r.
Qed.

Definition Spect_map f s := Spect.M.fold (fun e acc => Spect.M.add (f e) acc) s Spect.M.empty.

Lemma map_sim_support : forall (sim : Sim.t) s,
  Permutation (Spect.M.support (Spect_map sim s)) (map sim (Spect.M.support s)).
Proof.
intros sim s. rewrite <- PermutationA_Leibniz. apply Spect.map_injective_support.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

Lemma map_sim_elements : forall (sim : Sim.t) s,
  PermutationA Spect.Mraw.eq_pair (Spect.M.elements (Spect_map sim s))
              (map (fun xn => (sim (fst xn), snd xn)) (Spect.M.elements s)).
Proof.
intros sim s. apply Spect.map_injective_elements.
- intros ? ? Heq. now rewrite Heq.
- apply Sim.injective.
Qed.

(** Spectra can never be empty as the number of robots is non null. *)
Lemma spect_non_nil : forall conf, ~Spect.eq (!! conf) Spect.M.empty.
Proof. apply spect_non_nil. assert (Hle := Hyp_nG). unfold N.nG. omega. Qed.

Lemma support_non_nil : forall config, Spect.M.support (!! config) <> nil.
Proof.
intros config Habs.
rewrite Spect.M.support_nil in Habs.
apply (spect_non_nil _ Habs).
Qed.

Lemma gathered_at_dec : forall config pt, {gathered_at pt config} + {~gathered_at pt config}.
Proof.
intros config pt.
destruct (forallb (fun id => R2dec_bool (config id) pt) Names.names) eqn:Hall.
+ left. rewrite forallb_forall in Hall. intro g. rewrite <- R2dec_bool_true_iff. apply Hall, Names.In_names.
+ right. rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall. destruct Hall as [id [Hin Heq]].
  revert Hin Heq. apply (no_byz id). clear id. intros g Hin Heq Habs. specialize (Habs g).
  rewrite negb_true_iff, R2dec_bool_false_iff in Heq. contradiction.
Qed.

(** Define one robot to get their location whenever they are gathered. *)
Definition g1 : Names.G.
Proof.
exists 0. unfold N.nG. abstract (pose(Hle := Hyp_nG); omega).
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
  assert (H01 : ~R2.eq (0, 1) R2.origin).
  { compute. intro Habs. inv Habs. now apply R1_neq_R0. }
  rewrite (decompose_on H01 (x, y)) at 1.
Admitted. (* similarity_in_R2 *)

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
Check Spect.multiplicity.
(** The robogram solving the gathering problem in R². *)
Definition ffgatherR2_pgm (s : Spect.t) : R2.t :=
  wbarycenter (List.map (fun xn => (fst xn, INR (snd xn))) (Spect.M.elements s)).

Instance ffgatherR2_pgm_compat : Proper (Spect.eq ==> R2.eq) ffgatherR2_pgm.
Proof.
intros ? ? Heq. unfold ffgatherR2_pgm. apply wbarycenter_compat.
apply Spect.elements_compat in Heq.
assert (Proper (Spect.eq_pair ==> R2.eq * eq) (fun xn : Spect.M.elt * nat => (fst xn, INR (snd xn)))).
{ intros [] [] []. hnf in *; simpl in *. subst. split; reflexivity. }
apply (Preliminary.PermutationA_map _ H Heq).
Qed.

Definition ffgatherR2 : robogram := {| pgm := ffgatherR2_pgm |}.

Close Scope R_scope.


(** **  Decreasing measure ensuring termination  **)

(** ***  Global decreasing measure  **)


Open Scope R_scope.

(* Coercion Spect.Names.names : list Spect.Names.Internals.ident >-> list Spect.Names.ident. *)

Definition max_dist_R2_pt_list (pt: R2.t) (l: list R2.t) : R :=
  fold_right (fun pt1 max => Rmax (R2.dist pt pt1) max) 0 l.


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
- destruct (@max_dist_R2_list_list_ex (pt' :: l) (pt' :: l))
    as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]]; try discriminate; [].
  rewrite <- Heq. apply max_dist_R2_list_list_le; now right.
Qed.

Definition max_dist_spect (spect: Spect.t) : R :=
  max_dist_R2_list_list (Spect.support spect) (Spect.M.support spect).

Lemma max_dist_spect_le :
  forall (spect: Spect.t) pt0 pt1,
    InA R2.eq pt0 (Spect.support spect) ->
    InA R2.eq pt1 (Spect.support spect) ->
    R2.dist pt0 pt1 <= max_dist_spect spect.
Proof. setoid_rewrite InA_Leibniz. intros. now apply max_dist_R2_list_list_le. Qed.

Lemma max_dist_spect_ex :
  forall (spect: Spect.t),
    Spect.M.support spect <> nil ->
    exists pt0 pt1, 
      In pt0 (Spect.M.support spect)
      /\ In pt1 (Spect.M.support spect)
      /\ R2.dist pt0 pt1 = max_dist_spect spect.
Proof. intros. now apply max_dist_R2_list_list_ex. Qed.


(** **  Main result for termination: the measure decreases after a step where a robot moves  *)

Definition measure (conf: Config.t) : R :=
  max_dist_spect (!! conf).

Lemma measure_nonneg : forall config, 0 <= measure config.
Proof.
intros config. unfold measure.
destruct (Spect.M.support (!! config)) as [| pt l] eqn:Heq.
+ elim (support_non_nil _ Heq).
+ rewrite <- (R2_dist_defined_2 pt). apply max_dist_spect_le; rewrite Heq; now left.
Qed.

Lemma gathered_support : forall config pt,
  gathered_at pt config <-> PermutationA R2.eq (Spect.M.support (!! config)) (pt :: nil).
Proof.
intros config pt. split; intro H.
* apply NoDupA_equivlistA_PermutationA; autoclass.
  + apply Spect.M.support_NoDupA.
  + repeat constructor. intro Hin. inv Hin.
  + intro pt'. split; intro Hin.
    - rewrite Spect.M.support_In, (Spect.from_config_In config pt') in Hin.
      destruct Hin as [id Hid]. revert Hid. apply (no_byz id). clear id; intros g Hid.
      specialize (H g). rewrite H in Hid. rewrite Hid. now left.
    - inv Hin; try inv H1; [].
      rewrite Spect.M.support_In, (Spect.from_config_In config pt).
      exists (Good g1). apply H.
* intro id.
  assert (Hin : InA eq (Config.loc (config (Good id))) (Spect.M.support (!! config))).
  { rewrite Spect.M.support_In. apply (Spect.from_config_In config). eexists; reflexivity. }
  rewrite H in Hin. now inv Hin.
Qed.

Lemma gathered_measure : forall config, measure config = 0 <-> exists pt, gathered_at pt config.
Proof.
intros config. split; intro H.
* unfold measure, max_dist_spect in *.
  assert (Hnil := support_non_nil config).
  assert (Hdup := Spect.M.support_NoDupA (!! config)).
  setoid_rewrite gathered_support.
  induction (Spect.M.support (!! config)) as [| pt l]; try tauto; [].
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
    rewrite (Rmax_left 0 0) in H; try reflexivity; [].
    rewrite R2.dist_sym in H.
    match type of H with Rmax ?x ?x = 0 => rewrite (Rmax_left x) in H; try reflexivity end.
    rewrite (Rmax_right 0), Rmax_left in H.
    - now rewrite R2.dist_defined in H.
    - apply R2.dist_pos.
    - rewrite Rmax_left; apply R2.dist_pos.
* destruct H as [pt Hgather]. unfold measure.
  destruct (max_dist_spect_ex (support_non_nil config)) as [pt1 [pt2 [Hpt1 [Hpt2 Heq]]]].
  rewrite <- Heq, R2.dist_defined. rewrite gathered_support in Hgather. rewrite <- InA_Leibniz, Hgather in *.
  now inv Hpt1; inv Hpt2.
Qed.

Lemma fold_mult_plus_distr : forall (f : R2.t -> R) coeff E init,
  fold_left (fun acc pt => acc + snd pt * coeff * (f (fst pt))) E (coeff * init) =
  coeff * (fold_left (fun acc pt => acc + snd pt * (f (fst pt))) E init).
Proof.
  intros f coeff E.
  induction E; intro init.
  + now simpl.
  + simpl. rewrite <- IHE. f_equal. ring.
Qed.

Lemma wbarycenter_sim : forall (sim : Sim.t) m,
    m <> nil ->
    R2.eq (wbarycenter (map (fun xn => (sim (fst xn), snd xn)) m)) (sim (wbarycenter m)).
Proof.
  intros sim m Hm. eapply wbarycenter_n_unique.
  + apply wbarycenter_n_spec.
  + intro p.
    unfold weighted_sqr_dist_sum.
    change p with (Sim.id p).
    rewrite <- (Sim.compose_inverse_r sim) with (x := p) by apply R2.eq_equiv.
    change ((Sim.compose sim (sim ⁻¹)) p) with (sim ((sim ⁻¹) p)).

    assert (Hfold_dist_prop: forall pt init,
              fold_left (fun acc pt' => acc + snd pt'* (R2.dist (sim pt) (fst pt'))²)
                        (map (fun xn => (Bijection.section (Common.Sim.sim_f sim) (fst xn), snd xn)) m) init
            = fold_left (fun acc pt' => acc + snd pt' * (sim.(Sim.zoom))² * (R2.dist pt (fst pt'))²) m init).
    { intro pt. induction m as [| p1 m]; intro init.
      + now elim Hm.
      + clear Hm. destruct m as [| p2 m].
        * simpl.
          rewrite sim.(Sim.dist_prop), R_sqr.Rsqr_mult. ring.
        * remember (p2 :: m) as mm.
          simpl.
          rewrite sim.(Sim.dist_prop), R_sqr.Rsqr_mult.
          rewrite IHm.
          - f_equal. ring.
          - subst. discriminate.
    }
    do 2 rewrite Hfold_dist_prop.
    rewrite <- Rmult_0_r with (r := (Sim.zoom sim)²).
    rewrite (fold_mult_plus_distr (fun x => (R2.dist (wbarycenter m) x)²)),
            (fold_mult_plus_distr (fun x => (R2.dist (Bijection.section (Common.Sim.sim_f (sim ⁻¹)) p) x)²)).
    apply Rmult_le_compat_l.
    - apply Rle_0_sqr.
    - generalize (wbarycenter_n_spec m).
      intro Hbary_spec.
      unfold is_wbarycenter_n, weighted_sqr_dist_sum in Hbary_spec.
      now apply Hbary_spec.
Qed.

Lemma dist_prop_retraction:
  forall (sim: Sim.t) (x y : R2.t),
    R2.dist ((Sim.sim_f (sim ⁻¹)) x) ((Sim.sim_f (sim ⁻¹)) y) =
    /(Sim.zoom sim) * R2.dist x y.
Proof. intros sim x y. rewrite Sim.dist_prop. now simpl. Qed.

Theorem round_simplify : forall da config delta,
    Config.eq (round delta ffgatherR2 da config)
              (fun id => match da.(step) id with
                         | None => config id
                         | Some (f, r) =>
                           let bary := wbarycenter (List.map (fun xn => (fst xn, INR (snd xn)))
                                                             (Spect.elements (!! config))) in
                           let move := (r * (bary - (config id)))%R2 in
                             mk_info (if Rle_bool delta (R2norm move)
                                      then ((config id) + move)%R2
                                      else bary)
                         end).
Proof.
intros da config delta. apply no_byz_eq. intro g. hnf. unfold round.
assert (supp_nonempty:=support_non_nil config).
destruct (step da (Good g)) as [[f r] |] eqn:Hstep; trivial.
remember (Config.loc (config (Good g))) as pt. remember (f pt) as sim.
assert (Hsim : Proper (R2.eq ==> R2.eq) sim). { intros ? ? Heq. now rewrite Heq. }
simpl pgm. unfold ffgatherR2_pgm.
assert (Hperm : PermutationA (R2.eq * eq)%signature
                             (map (fun xn => (sim (fst xn), snd xn)) (Spect.M.elements (!! config)))
                             (Spect.M.elements (!! (Config.map (Config.app sim) config)))).
{ now rewrite <- map_sim_elements, Spect.from_config_map. }
change Common.Sim.sim_f with Sim.sim_f.
remember (List.map (fun xn => (fst xn, INR (snd xn))) (Spect.M.elements (!! config))) as E.
remember (List.map (fun xn => (fst xn, INR (snd xn)))
                   (Spect.M.elements (!! (Config.map (Config.app sim) config)))) as E'.
rewrite R2norm_mul, <- R2norm_dist.
assert (Hsimbary : (sim ⁻¹) (wbarycenter E') = wbarycenter E).
{ rewrite HeqE' in *.
  rewrite <- wbarycenter_sim.
  + apply wbarycenter_compat.
    rewrite map_map. simpl.
    rewrite <- (map_map (fun xn => (Bijection.retraction (Common.Sim.sim_f sim) (fst xn), snd xn))
                        (fun xn => (fst xn, INR (snd xn)))).
    rewrite HeqE. apply (PermutationA_map (eqA := R2.eq * eq)%signature);
    autoclass; try (now intros [] [] []; hnf in *; simpl in * |-; split; subst); [].
    rewrite <- Spect.map_injective_elements; autoclass.
    - rewrite Spect.from_config_map, Config.map_merge; autoclass; [].
      do 2 f_equiv.
      rewrite <- (Config.map_id config) at 2. f_equiv.
      intros x y Hxy.
      rewrite <- (Config.app_id y); try reflexivity; [].
      change (Config.app id y) with (Config.app Sim.id y).
      rewrite <- (Sim.compose_inverse_l sim).
      symmetry. simpl. apply Config.app_compose; autoclass; now symmetry.
    - change (Bijection.retraction sim) with (Bijection.section (sim ⁻¹)).
      apply Sim.injective.
  + rewrite <- length_zero_iff_nil, map_length, <- Spect.from_config_map; autoclass.
    rewrite Spect.map_injective_elements; autoclass; try apply Sim.injective.
    rewrite map_length, length_zero_iff_nil, Spect.elements_nil. apply spect_non_nil. }
assert (Htest : Rle_bool delta (R2.dist ((sim ⁻¹) (r * wbarycenter E')%R2) pt)
                = Rle_bool delta (Rabs r * R2.dist (wbarycenter E) pt)).
{ f_equal.
  assert (Heq_pt : pt = (sim ⁻¹) (sim pt)).
  { simpl. rewrite Bijection.retraction_section; autoclass. }
  assert (Hsim_pt : R2.eq (sim pt) (r * (sim pt))).
  { generalize (Sim.center_prop sim).
    intro Hzero.
    apply step_center with (c := pt) in Hstep.
    simpl in Hstep. rewrite <- Heqsim in Hstep.
    now rewrite <- Hstep, Hzero, R2.mul_origin. }
  rewrite Heq_pt at 1.
  rewrite dist_prop_retraction, Hsim_pt, R2mul_dist, <- Rmult_assoc.
  pattern (/ Sim.zoom sim * Rabs r).
  rewrite Rmult_comm, Rmult_assoc. f_equal.
  rewrite <- dist_prop_retraction, <- Heq_pt. f_equal. assumption. }
rewrite Htest.
destruct (Rle_bool delta (Rabs r * R2.dist (wbarycenter E) pt)); trivial; [].
apply Bijection.Inversion.
simpl Bijection.retraction. change Common.Sim.sim_f with Sim.sim_f.
rewrite sim_add, sim_mul, sim_add, sim_opp.
do 2 rewrite R2.mul_distr_add.
assert (Hsim_pt_0 : R2.eq (sim pt) R2.origin).
{ apply (step_center da (Good g) pt) in Hstep.
  rewrite <- sim.(Sim.center_prop), <- Hstep. cbn. now subst sim. }
rewrite Hsim_pt_0.
rewrite (R2.add_comm R2.origin), R2.add_origin.
setoid_rewrite <- R2.add_origin at 25. repeat rewrite <- R2.add_assoc. f_equiv.
+ f_equiv. rewrite Bijection.Inversion. apply Hsimbary.
+ rewrite R2.opp_origin, R2.add_origin.
  setoid_rewrite <- R2.mul_1 at 9 15. repeat rewrite <- ?R2.minus_morph, ?R2.mul_morph, ?R2.add_morph.
  ring_simplify (r * 2 + (r * -1 + (1 - r + -1))). apply R2.mul_0.
Qed.


(* FIXME: cleanup! *)
Theorem round_lt_config : forall d conf delta,
    delta > 0 ->
    FullySynchronous d ->
    delta <= measure conf ->
    measure (round delta ffgatherR2 (Stream.hd d) conf) <= measure conf - delta.
Proof.
  assert (Proper (Spect.eq_pair ==> R2.eq * eq) (fun xn => (fst xn, INR (snd xn)))).
  { clear. intros [] [] []. hnf in *; simpl in *. now subst. }
  intros d conf delta Hdelta HFSync Hnotdone.
  destruct (Spect.elements (!! conf)) as [| [pt n] [| [pt' n'] ?]] eqn:Hmax.
  - (* No robots *)
    exfalso. apply (support_non_nil conf), (@PermutationA_nil _ R2.eq _).
    now rewrite Spect.support_map_elements, Hmax.
  - (* Done *)
    assert (Habs : measure conf = 0).
    { rewrite gathered_measure. exists pt. rewrite gathered_support.
      now rewrite Spect.support_map_elements, Hmax. }
    rewrite Habs in *. elim (Rlt_irrefl delta). now apply Rle_lt_trans with 0.
  - (* Now to some real work *)
    remember (Stream.hd d) as da.
    remember (Spect.elements (!! conf)) as elems.
    remember (map (fun xn => (fst xn, INR (snd xn))) elems) as relems.
    set (C := wbarycenter relems).
    remember (Spect.elements (!! (round delta ffgatherR2 da conf))) as nxt_elems.
    assert (Hantec: forall KP, InA Spect.eq_elt KP nxt_elems ->
              exists Pid k, InA Spect.eq_elt (Config.loc (conf Pid), k) elems
                         /\ R2.eq (round delta ffgatherR2 da conf Pid) (fst KP)).
    { intros [KP k'] HinKP.
      rewrite Heqnxt_elems in HinKP.
      rewrite Spect.elements_In in HinKP.
      generalize (Spect.from_config_In (round delta ffgatherR2 da conf)).
      intro Hok. rewrite Hok in HinKP. clear Hok.
      destruct HinKP as (Pid, HPid).
      exists Pid, k'.
      split; [|now rewrite HPid].
      rewrite Heqelems, Spect.elements_In, Spect.from_config_In.
      now exists Pid.
    }

    assert (Hrobot_move_less_than_delta:
              forall Pid k,
                InA Spect.eq_elt (Config.loc (conf Pid), k) elems ->
                delta > R2.dist (conf Pid) C ->
                R2.eq (round delta ffgatherR2 da conf Pid) C).
    { intros Pid k HinP HdeltaP.
      rewrite (round_simplify _ _ _ Pid).
      destruct (step da Pid) eqn:HeqPact.
      + simpl.
        destruct (Spect.M.elements (!! conf)) as [| q [| q' ?]].
        - subst elems. inversion Hmax.
        - subst elems. inversion Hmax.
        - rewrite <- Heqelems, <- Heqrelems.
          destruct p.
          unfold Rle_bool.
          destruct (Rle_dec delta (R2norm (r * (wbarycenter relems - conf Pid)))) as [ Hdmove | Hdmove ].
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
               pattern (conf Pid + wbarycenter relems)%R2.
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
        destruct (H0 Pid).
        simpl.
        subst d.
        now symmetry.
    }

    assert (Hrobot_move:
              forall Pid k,
                InA Spect.eq_elt (Config.loc (conf Pid), k) elems ->
                delta <= R2.dist (conf Pid) C ->
                exists k, R2.eq (round delta ffgatherR2 da conf Pid)
                                (conf Pid + k * (C - (conf Pid)))%R2
                       /\ 0 <= k <= 1
                       /\ delta <= R2norm (k * (C - (conf Pid)))).
    { intros Pid HinP HdeltaP.
      setoid_rewrite (round_simplify _ _ _ Pid).
      remember (step da Pid) as Pact.
      destruct Pact.
      + destruct (Spect.M.elements (!! conf)) as [| q [| q' ?]].
        - subst elems. inversion Hmax.
        - subst elems. inversion Hmax.
        - rewrite <- Heqelems, <- Heqrelems.
          destruct p.
          unfold Rle_bool.
          destruct (Rle_dec delta (R2norm (r * (wbarycenter relems - conf Pid)))) as [ Hdmove | Hdmove ].
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
               now rewrite R2.add_comm, R2.add_opp, R2.add_origin.
            ++ apply Rle_0_1.
            ++ apply Rle_refl.
            ++ now rewrite R2.mul_1, <- R2norm_dist, R2.dist_sym.
      + unfold FullySynchronous in HFSync.
        unfold FullySynchronousInstant in HFSync.
        destruct d.
        simpl in Heqda.
        destruct HFSync.
        destruct (H0 Pid).
        simpl.
        subst d.
        now symmetry.
    }

    assert (MainArgument: forall KP KQ, InA Spect.eq_elt KP nxt_elems -> InA Spect.eq_elt KQ nxt_elems ->
            R2.dist (fst KP) (fst KQ) <= max_dist_spect (!! conf) - delta).
    { intros KP KQ HinKP HinKQ.
      apply Hantec in HinKP.
      apply Hantec in HinKQ.
      destruct HinKP as [Pid [kP [HinP HroundP]]],
               HinKQ as [Qid [kQ [HinQ HroundQ]]].

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
          apply R2.dist_defined in H0.
          rewrite H0 in r.
          assumption. }
        assert (HQnotC: ~ R2.eq (conf Qid) C).
        { intro.
          apply (Rlt_irrefl 0).
          apply Rlt_le_trans with (r2 := delta).
          assumption.
          apply R2.dist_defined in H0.
          rewrite H0 in r0.
          assumption. }

        destruct (Rle_dec kp kq).
        - apply Rle_trans with (r2 := (1 - kp) * (max_dist_spect (!! conf))).
          * rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
            apply distance_after_move; try assumption.
            ** subst C. change (conf Pid) with (fst (conf Pid, INR kP)).
               eapply (@wbarycenter_dist_decrease relems (max_dist_spect (!! conf)))
                 with (p := (Config.loc (conf Pid), INR kP)).
               ++ subst relems elems. intro Habs. apply map_eq_nil in Habs.
                  rewrite Habs, InA_nil in *. tauto.
               ++ subst relems elems. intro.
                  rewrite (InA_map_iff (eqA := Spect.eq_pair)); autoclass; [].
                  intros [[pta na] [Heq Hin]]. rewrite Spect.elements_spec in Hin.
                  destruct p, Heq. simpl in *. subst. now apply lt_0_INR.
               ++ intros p1 p2 Hin1 Hin2. subst relems elems.
                  rewrite InA_map_iff in Hin1, Hin2; autoclass; [].
                  apply max_dist_spect_le.
                  -- rewrite Spect.support_map_elements, InA_map_iff; autoclass; [].
                     destruct Hin1 as [p1' [Heq1 Hin1]].
                     exists p1'. split; trivial; []. destruct p1', Heq1 as [Heq1 _].
                     now hnf in *; simpl in *.
                  -- rewrite Spect.support_map_elements, InA_map_iff; autoclass; [].
                     destruct Hin2 as [p2' [Heq2 Hin2]].
                     exists p2'. split; trivial; []. destruct p2', Heq2 as [Heq2 _].
                     now hnf in *; simpl in *.
               ++ subst relems. rewrite (@InA_map_iff _ _ Spect.eq_elt); autoclass.
                  -- now exists (Config.loc (conf Pid), kP).
                  -- clear. intros [] [] ?. now hnf in *; simpl in *.
            ** 
++
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
            apply barycenter_dist_decrease with (E := elems).
            subst elems.
            rewrite Hmax; intro; discriminate.
            intros. apply max_dist_spect_le.
            now subst elems.
            now subst elems.
            now subst C.
            assumption.
            now destruct Hkple1.
        - apply Rle_trans with (r2 := (1 - kq) * (max_dist_spect (!! conf))).
          * rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
            rewrite R2.dist_sym.
            apply distance_after_move; try assumption.
            apply barycenter_dist_decrease with (E := elems).
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
            apply barycenter_dist_decrease with (E := elems).
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

        rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
        apply Rle_trans with (r2 := R2.dist (conf Pid) C - delta).
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
        apply barycenter_dist_decrease with (E := elems).
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

        rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
        apply Rle_trans with (r2 := R2.dist (conf Qid) C - delta).
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
        apply barycenter_dist_decrease with (E := elems).
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
        rewrite <- HroundP in *. rewrite <- HroundQ in *. clear HroundP HroundQ KP KQ.
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
    measure (round delta ffgatherR2 (Stream.hd d) conf) = 0.
Proof.
intros [da d] conf delta Hdelta HFS Hlt.
unfold measure.
remember (Spect.M.elements (!! conf)) as elems.
set (C := wbarycenter (map (fun xn => (fst xn, INR (snd xn))) elems)).
remember (Spect.M.elements (!! (round delta ffgatherR2 da conf))) as nxt_elems.
assert (Hantec: forall KP, In KP nxt_elems ->
                  exists Pid, In (Config.loc (conf Pid)) elems /\ R2.eq (round delta ffgatherR2 da conf Pid) KP).
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
  destruct (Hok (Config.loc (conf Pid))) as [_ Hex].
  apply InA_Leibniz.
  rewrite Heqelems.
  apply Spect.M.elements_spec1.
  apply Hex.
  now exists Pid.
}

assert (HonlyC: forall KP, In KP nxt_elems -> R2.eq KP C).
{ intros KP HinKP.
  destruct (Hantec KP HinKP) as [Pid [HinP HroundP]].
  rewrite <- HroundP in *. clear HroundP KP.
  rewrite (round_simplify _ _ _ Pid).
  destruct (step da Pid) eqn:HeqPact.
  * destruct p. simpl.
    rewrite <- Heqelems.
    unfold Rle_bool.
    destruct (Rle_dec delta (R2norm (r * (barycenter elems - conf Pid)))).
    + assert (Hr: 0 <= snd (t, r) <= 1).
      { apply step_flexibility with da Pid. now symmetry. }
      simpl in Hr.
      destruct Hr as [Hr0 Hr1].
      destruct Hr1 as [Hrlt1 | Hreq1].
      - exfalso.
        apply Rlt_irrefl with delta.
        apply (Rle_lt_trans _ _ _ r0).
        rewrite R2norm_mul.
        rewrite (Rabs_pos_eq _ Hr0).
        rewrite <- R2norm_dist.
        assert (Hle : R2.dist (barycenter elems) (conf Pid) <= delta).
        { rewrite R2.dist_sym.
          apply Rle_trans with (measure conf); trivial; [].
          apply barycenter_dist_decrease with elems; auto; [|].
          - rewrite Heqelems, <- Spect.MProp.MP.elements_Empty.
            intro Hempty. now apply Spect.MProp.MP.empty_is_empty_1, spect_non_nil in Hempty.
          - intros. unfold measure. apply max_dist_spect_le; now rewrite <- Heqelems. }
        (* There should be a lemma for this in standard library. *)
        rewrite <- Rmult_1_l.
        destruct Hle.
        -- apply Rmult_le_0_lt_compat; try assumption.
           apply R2.dist_pos.
        -- subst delta.
           apply Rmult_lt_compat_r.
           now apply Rlt_gt.
           assumption.
      - subst r.
        rewrite R2.mul_1, R2.add_comm, <- R2.add_assoc.
        pattern (- conf Pid + conf Pid)%R2.
        rewrite R2.add_comm, R2.add_opp, R2.add_origin.
        now unfold C.
    + now unfold C.
  * unfold FullySynchronous in HFS.
    inversion HFS.
    unfold FullySynchronousInstant in H.
    destruct (H Pid). now symmetry. }
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
- symmetry. apply (no_byz id), Hgather.
Qed.

Corollary not_gathered_generalize : forall (config : Config.t) id,
  ~gathered_at (config id) config -> forall pt, ~gathered_at pt config.
Proof. intros config id Hnot pt Hgather. apply Hnot. apply (gathered_precise Hgather). Qed.

Lemma not_gathered_exists : forall (config : Config.t) pt,
  ~ gathered_at pt config -> exists id, ~R2.eq (config id) pt.
Proof.
intros config pt Hgather.
destruct (forallb (fun x => R2dec_bool (config x) pt) Names.names) eqn:Hall.
- elim Hgather. rewrite forallb_forall in Hall.
  intro id'. setoid_rewrite R2dec_bool_true_iff in Hall. hnf. repeat rewrite Hall; trivial; apply Names.In_names.
- rewrite <- negb_true_iff, existsb_forallb, existsb_exists in Hall.
  destruct Hall as [id' [_ Hid']]. rewrite negb_true_iff, R2dec_bool_false_iff in Hid'. now exists id'.
Qed.

Lemma gathered_at_forever : forall delta da conf pt,
  gathered_at pt conf -> gathered_at pt (round delta ffgatherR2 da conf).
Proof.
intros delta da conf pt Hgather. rewrite round_simplify.
intro g.
assert (Hpt : R2.eq (conf (Good g)) pt) by now rewrite Hgather.
destruct (step da (Good g)); trivial; [].

assert (Hptinspect: Spect.M.In pt (!! conf)).
{ unfold Spect.from_config, Spect.M.In.
  rewrite Spect.multiset_In, Config.list_spec.

  assert (Names.names <> nil).
  { intro.
    assert (length Names.names = nG).
    { rewrite Names.names_length. unfold N.nG, N.nB. omega. }
      rewrite <- length_zero_iff_nil in H.
    generalize Hyp_nG. omega.
  }

  destruct Names.names.
  - exfalso; now apply H.
  - revert dependent i. intro id. apply (no_byz id). intros g' **.
    now apply InA_cons_hd.
}

assert (Hnotpt_notinspect: forall q, ~ R2.eq q pt -> ~Spect.M.In q (!!conf)).
{ intros q Hnoteq.
  unfold Spect.from_config, Spect.M.In.
  rewrite Spect.multiset_In, Config.list_spec.

  intro HinA.
  apply Hnoteq.
  generalize (@InA_map_iff Names.ident R2.t Logic.eq R2.eq).
  intro HInMapIff.
  rewrite map_map, HInMapIff in HinA; autoclass.
  destruct HinA as [x [Heq Hin]].
  rewrite <- Heq.
  apply (no_byz x), Hgather.
}

assert (Hspect: eqlistA Spect.eq_elt (Spect.elements (!! conf)) ((pt, nG) :: nil)).
{ apply Preliminary.PermutationA_length1, NoDupA_equivlistA_PermutationA; autoclass.
  + apply Spect.elements_NoDupA.
  + repeat constructor. rewrite InA_nil. tauto.
  + intros [x n]. split; intro Hin.
    - left. destruct (Spect.elt_dec (x, n) (pt, nG)) as [? | Habs]; auto; [].
      rewrite Spect.elements_In in Hin.
      now elim (Hnotpt_notinspect x).
    - inv Hin; try (rewrite InA_nil in *; tauto); [].
      rewrite Spect.elements_In. hnf in *; simpl in *. now subst. }

assert (HnG := Spect.cardinal_from_config conf).
rewrite Spect.cardinal_fold_elements in HnG.
unfold N.nG, N.nB in HnG.

destruct (Spect.elements (!! conf)) as [| [pt' n] [| ]].
+ simpl in HnG. generalize Hyp_nG. omega.
+ inv Hspect. hnf in *; simpl in *; subst.
  assert (n = nG) by omega. subst n. clear HnG.
  destruct p.
  unfold wbarycenter. simpl.
  rewrite Rplus_0_r, 3 R2.add_origin.
  rewrite 3 R2.mul_morph.
  assert (HnG := Hyp_nG). apply le_INR in HnG. simpl in HnG.
  replace (1 / INR nG * INR nG) with 1%R by (field; lra). rewrite 3 R2.mul_1.
  rewrite 2 R2.add_opp, 2 R2.mul_origin, R2.add_origin.
  now destruct_match.
+ repeat match goal with H : eqlistA _ _ _ |- _ => inv H end.
Qed.

Lemma gathered_at_OK : forall delta d conf pt, gathered_at pt conf -> Gather pt (execute delta ffgatherR2 d conf).
Proof.
cofix Hind. intros delta d conf pt Hgather. constructor.
+ clear Hind. simpl. assumption.
+ rewrite execute_tail. apply Hind. now apply gathered_at_forever.
Qed.


Lemma not_barycenter_moves:
  forall delta d (config : Config.t) gid,
    delta > 0 ->
    FullySynchronous d ->
    ~R2.eq (config gid) (wbarycenter (map (fun xn => (fst xn, INR (snd xn))) (Spect.M.elements (!! config)))) ->
    ~R2.eq (round delta ffgatherR2 (Stream.hd d) config gid) (config gid).
Proof.
  intros delta d config gid Hdelta HFSync Hnotbary Hnotmove.
  apply Hnotbary. clear Hnotbary.
  rewrite (round_simplify _ _ _ gid) in Hnotmove.
  remember (step (Stream.hd d) gid) as Pact.
  destruct Pact.
  * destruct p. simpl in Hnotmove.
    remember (Spect.M.elements (!! config)) as elems.
    unfold Rle_bool in Hnotmove.
    destruct (Rle_dec delta (R2norm (r * (wbarycenter
                         (map (fun xn : Spect.M.elt * nat => (fst xn, INR (snd xn)))
                            elems) - config gid)))).
    + rewrite <- R2.add_origin with (u := config gid) in Hnotmove at 3.
      apply R2.add_reg_l in Hnotmove.
      apply R2.mul_integral in Hnotmove.
      destruct Hnotmove as [Hr0 | Heq].
      - exfalso.
        subst r.
        rewrite R2norm_mul, Rabs_R0, Rmult_0_l in r0.
        apply Rlt_irrefl with delta.
        now apply (Rle_lt_trans _ _ _ r0).
      - now rewrite R2sub_origin in Heq.
    + now symmetry.
  * unfold FullySynchronous in HFSync.
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
  exists (conf (Good g1)). now apply Stream.Now, gathered_at_OK.
* (* If we are gathered at the next step, not much to do either. *)
  exists (round delta ffgatherR2 da conf (Good g1)).
 apply Stream.Later, Stream.Now. rewrite execute_tail. now apply gathered_at_OK.
* (* General case, use [round_lt_config] *)
  assert (delta <= measure conf).
  { apply Rnot_lt_le. intro Habs. eapply Rlt_le, round_last_step in Habs; eauto; [].
    rewrite gathered_measure in Habs. destruct Habs as [pt Habs]. simpl in Habs.
    apply Hmove'. apply (gathered_precise Habs (Good g1)). }
  destruct (Hind (round delta ffgatherR2 da conf)) with d as [pt Hpt].
  + apply lt_config_decrease; trivial; [].
    change da with (Stream.hd (Stream.cons da d)).
    now apply round_lt_config.
  + now destruct HFS.
  + exists pt. apply Stream.Later. apply Hpt.
Qed.

Print Assumptions FSGathering_in_R2.

End GatheringinR2.
