(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Reals.
Require Import Omega.
Require Import Psatz.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.CommonGraphFormalism.


Module DGF.


(** * Projection function*)

Open Scope R_scope.

(** we define a function from R to ]0;1\[ to represent the percentage of the edge already done *)
Definition project_p (p : R) : R :=
  if Rle_dec p 0 then Rpower 2 (p-1) else (2 - (Rpower 2 (-p)))/2.

Lemma project_p_image : forall p, (0 < project_p p < 1).
Proof.
intros p.
unfold project_p.
assert (Hln: 0< ln 2). rewrite <- ln_1. apply ln_increasing; lra.
destruct (Rle_dec p 0).
split;
unfold Rpower. apply exp_pos.
rewrite <- exp_0 at 4.
apply exp_increasing.
assert (Hp : (p-1) < 0). lra.
replace 0 with ((p-1) * 0) by lra.
apply (Rmult_lt_gt_compat_neg_l (p-1)); assumption.
assert (e : 0<p) by lra;
unfold Rpower.
split.
replace ((2 - exp (- p * ln 2)) / 2) with (/2*((2 - exp (- p * ln 2)))) by lra.
rewrite Rmult_minus_distr_l.
apply Rlt_Rminus.
replace (/2*2) with 1 by lra.
replace (/2) with (Rpower 2 (-1)). unfold Rpower.
rewrite <- exp_0 at 6.
rewrite <- exp_plus.
apply exp_increasing.
assert (H1 : -1*(ln 2)<0) by lra.
assert (H' : 0< p*(ln 2)).
apply Rmult_lt_0_compat; assumption.
assert (H2 : -p*(ln 2)<0) by lra.
lra.
rewrite Rpower_Ropp,Rpower_1. reflexivity.
lra.
replace ((2 - exp (- p * ln 2)) / 2) with (/2*((2 - exp (- p * ln 2)))) by lra.
rewrite Rmult_minus_distr_l.
replace (/2*2) with 1 by lra.
apply Rminus_lt.
replace (1 - / 2 * exp (- p * ln 2) - 1) with (- / 2 * exp (- p * ln 2)) by lra.
replace (/2) with (Rpower 2 (-1)). unfold Rpower.
replace (- exp (-1 * ln 2) * exp (- p * ln 2)) with (- (exp (-1 * ln 2) * exp (- p * ln 2))) by lra.
rewrite <- exp_plus.
apply Ropp_lt_gt_0_contravar.
apply exp_pos.
rewrite Rpower_Ropp,Rpower_1. reflexivity.
lra.
Qed.

(** this function is the inverse of project_p *)
Definition project_p_inv (q:R) : R :=
  if Rle_dec q (1/2) then 1+ ln(q)/ln(2) else - ( 1 + ln(1-q)/ln 2).

Lemma inv_pro : forall p, (0 < p < 1)%R -> p = project_p (project_p_inv p).
Proof.
intros p Hp. unfold project_p, project_p_inv, Rpower.
assert (aux_ln : 0 < /ln 2).
generalize ln_lt_2; intros Hl2.
assert (Hl0 : 0 < ln 2). lra.
apply Rinv_0_lt_compat.
lra.
destruct (Rle_dec p (1 / 2)).
+ destruct (Rle_dec (1 + ln p / ln 2) 0).
  - replace ((1 + ln p / ln 2 - 1) * ln 2) with (ln p). now rewrite exp_ln.
    replace (1 + ln p / ln 2 - 1) with (ln p / ln 2) by lra.
    replace (ln p / ln 2 * ln 2) with ((/ln 2 * ln 2) * ln p) by lra.
    rewrite <- (Rinv_l_sym (ln 2)).
    lra. assert (Hlra := ln_lt_2).
    lra.
  - destruct (Rdec (1/2) p).
    rewrite <- e.
    replace (1/2) with (/2) by lra.
    rewrite ln_Rinv.
    replace (- (1 + - ln 2 / ln 2)) with 0.
    replace (0 * ln 2) with 0 by lra.
    rewrite exp_0. lra.
    replace (- ln 2 / ln 2) with (-1). lra.
    replace (- ln 2 / ln 2) with (-(ln 2 / ln 2)) by lra.
    replace (ln 2 / ln 2) with (ln 2 * / ln 2) by lra.
    rewrite <- Rinv_r_sym. reflexivity.
    assert (Hlra := ln_lt_2). lra.
    lra.
    destruct n.
    replace (1 + ln p / ln 2) with (ln p / ln 2 - (-1)) by lra.
    apply Rle_minus.
    assert (ln p / ln 2 <= ln (1/2) / ln 2).
    assert (Hlra := ln_lt_2).
    apply Rmult_le_compat_r. lra.
    destruct Hp as (Hp0, Hp1).
    assert (Hp' : p < 1/2) by lra.
    assert (Hl := ln_increasing p (1/2) Hp0 Hp').
    lra.
    replace (ln (1/2) / ln 2) with (-1) in H. assumption.
    replace (ln (1 / 2)) with (ln (1*/2)) by lra.
    rewrite ln_mult; try lra. rewrite ln_1.
    replace (0 + ln (/ 2)) with (ln (/2)) by lra.
    rewrite ln_Rinv.
    replace (- ln 2 / ln 2) with (-1). lra.
    replace (- ln 2 / ln 2) with (-(ln 2 / ln 2)) by lra.
    replace (ln 2 / ln 2) with (ln 2 * / ln 2) by lra.
    rewrite <- Rinv_r_sym. reflexivity.
    assert (Hlra := ln_lt_2).
    lra. lra.
+ assert (Hlra := ln_lt_2).
  assert (Hln2 : ln 2 / ln 2  = 1).
  replace (ln 2 / ln 2) with (ln 2 * / ln 2) by lra.
  rewrite <- Rinv_r_sym. reflexivity.
  lra.
  destruct (Rle_dec (- (1 + ln (1 - p) / ln 2)) 0).
  - destruct (Rdec p (/2)). lra.
    destruct n.
    replace(- (1 + ln (1 - p) / ln 2)) with ( -ln (1 - p) / ln 2 -1) in r by lra.
    apply Rminus_le in r.
    replace (-ln (1 - p) / ln 2) with (-ln (1 - p) * / ln 2) in r by lra.
    assert (- ln (1 - p) <= ln 2).
    apply (Rmult_le_compat_r (ln 2)) in r.
    replace (- ln (1 - p) * / ln 2 * ln 2) 
    with (- ln (1 - p) * (ln 2 / ln 2)) in r by lra.
    rewrite Hln2 in r.
    lra. lra.
    assert (ln (1-p) >= - ln 2) by lra.
    rewrite <- ln_Rinv in H0; try lra.
    destruct (Rdec (ln (1 - p)) (ln (/ 2))).
    apply ln_inv in e; lra.
    assert (ln (1 - p) > ln (/ 2)) by lra.
    apply ln_lt_inv in H1; try lra.
  - replace (- - (1 + ln (1 - p) / ln 2) * ln 2) with
    (ln 2 + (ln (1-p) * (ln 2 / ln 2))) by lra.
    rewrite Hln2.
    rewrite exp_plus.
    replace (ln (1 - p) * 1) with (ln (1 - p)) by lra.
    rewrite exp_ln; try lra.
    rewrite exp_ln; try lra.
Qed.

Lemma pro_inv : forall p, p = project_p_inv (project_p p).
Proof.
intros p. unfold project_p_inv, project_p, Rpower.
assert (Hl2 := ln_lt_2). 
assert (Hln2 : ln 2 / ln 2  = 1).
  replace (ln 2 / ln 2) with (ln 2 * / ln 2) by lra.
  rewrite <- Rinv_r_sym. reflexivity.
  lra.
destruct (Rle_dec p 0).
+ destruct (Rle_dec (exp ((p - 1) * ln 2)) (1 / 2)).
  - rewrite ln_exp.
    replace ((p - 1) * ln 2 / ln 2) with ((p - 1) * (ln 2 / ln 2)) by lra.
    rewrite Hln2.
    lra.
  - destruct (Rdec p 0).
    rewrite e; simpl in *.
    replace ((0 - 1) * ln 2) with (-ln 2) by lra.
    rewrite exp_Ropp, exp_ln; try lra.
    replace (1-/2) with (/2) by lra.
    rewrite ln_Rinv; try lra.
    destruct n.
    replace ((p - 1) * ln 2) with ((p * ln 2) + ( - ln 2)) by lra.
    rewrite exp_plus, exp_Ropp, exp_ln; try lra.
    assert (Haux : forall a b, a <= b -> a/2<=b/2).
    intros a b Hab. lra.
    apply Haux.
    rewrite <- (exp_ln 1) at 3; try lra.
    apply Rlt_le.
    apply exp_increasing.
    rewrite ln_1.
    assert (Hf: 0 < ln 2) by lra.
    assert (Hp : p < 0) by lra.
    assert (Haux2 : forall a b, -a * b > 0 -> a * b < 0).
    intros a b; lra.
    apply Haux2.
    apply Rmult_lt_0_compat; lra.
+ destruct(Rle_dec ((2 - exp (- p * ln 2)) / 2) (1 / 2)).
  - destruct n.
    replace ((2 - exp (- p * ln 2)) / 2) with (1 - exp (-p*ln 2) / 2) in r by lra.
    replace (-p*ln 2) with (-(p*ln 2)) in r by lra.
    rewrite exp_Ropp in r.
    apply Rle_minus in r.
    replace (1 - / exp (p * ln 2) / 2 - 1 / 2) 
    with (/2 - /exp (p * ln 2) / 2) in r by lra.
    apply Rminus_le in r.
    assert (1 <= / exp (p * ln 2)) by lra.
    apply Rinv_le_contravar in H; try lra.
    replace (/ / exp (p * ln 2)) with (exp (p * ln 2)) in H.
    replace (/1) with 1 in H by lra.
    destruct (Rdec (exp (p * ln 2)) 1).
    rewrite <- (exp_ln 1) in e at 3; try lra.
    apply exp_inv in e.
    rewrite ln_1 in e.
    assert (Hl : ln 2 > 0) by lra.
    replace 0 with (0 * ln 2) in e by lra.
    apply Rmult_eq_reg_r in e; try lra.
    assert (exp (p * ln 2) < 1) by lra.
    rewrite <- (exp_ln 1) in H0 at 3; try lra.
    apply exp_lt_inv in H0.
    rewrite ln_1 in H0.
    assert (Hl : ln 2 > 0) by lra.
    replace 0 with (0 * ln 2) in H0 by lra.
    apply Rmult_lt_reg_r in H0; try lra.
    do 2 rewrite <- exp_Ropp.
    now replace (- - (p * ln 2)) with (p * ln 2) by lra.
  - replace ((2 - exp (- p * ln 2)) / 2) with (1 - exp (-p*ln 2) / 2) by lra.
    replace (-p*ln 2) with (-(p*ln 2)) by lra.
    replace (1 - (1 - exp (-(p * ln 2)) / 2))
    with (exp ( -(p * ln 2)) * / 2) by lra.
    rewrite ln_mult; try lra; try apply exp_pos.
    rewrite ln_exp.
    replace ((- (p * ln 2) + ln (/ 2)) / ln 2)
    with (- (p * (ln 2/ ln 2)) + ln (/ 2) / ln 2) by lra.
    rewrite Hln2, ln_Rinv; try lra.
Qed.

Lemma subj_proj : forall p q, 0 < p < 1 -> p = project_p q <-> project_p_inv p = q.
Proof.
intros p q H; split; intros Hp.
+ rewrite Hp. symmetry; apply pro_inv.
+ rewrite <- Hp. now apply inv_pro.
Qed.

(** * definition of space *)
(** a robot can be on a node (Loc) or on an edge (Mvt) *)

Inductive location :=
  | Loc (l : Graph.V)
  | Mvt (e : Graph.E) (p : R).


Definition loc_eq l l' :=
  match l, l' with
    | Loc l, Loc l' => Graph.Veq l l'
    | Mvt e p, Mvt e' p' => Graph.Eeq e e' /\ p = p'
    | _, _ => False
  end.

(* never used if we start from a good conf*)
Axiom e_default : Graph.E.

Module Location : DecidableType with Definition t := location with Definition eq := loc_eq.
  Definition t := location.
  Definition eq := loc_eq.
  
  Lemma eq_equiv : Equivalence eq.
  Proof.
  split.
  + intros x. unfold eq, loc_eq. destruct x. reflexivity. split; reflexivity.
  + intros x y Hxy. unfold eq, loc_eq in *. destruct x, y;
    try auto. now symmetry. split; now symmetry.
  + intros x y z Hxy Hyz. destruct x, y, z; unfold eq, loc_eq in *; try auto.
    now transitivity l0. exfalso; auto. exfalso; auto. 
    split. now transitivity e0. now transitivity (p0).
  Qed.
  
  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof.
  intros l l'.
  destruct l, l'; unfold eq, loc_eq; auto. apply Graph.Veq_dec.
  destruct (Graph.Eeq_dec e e0), (Rdec (p) (p0));
  intuition.
  Qed.
End Location.



Module Config := Configurations.Make (Location)(N)(Names).

  Definition project (config : Config.t) : Config.t :=
    fun id =>
      match Config.loc (config id) with
        | Loc l => config id
        | Mvt e p => {| Config.loc := Loc (if Rle_dec (project_p p) (Graph.threshold e) 
                                               then Graph.src e else Graph.tgt e);
                           Config.robot_info := Config.robot_info (config id) |}
      end.
      
  Instance project_compat : Proper (Config.eq ==> Config.eq) project.
  Proof.
  intros c1 c2 Hc id. unfold project. repeat try (split; simpl);
  destruct (Hc id) as (Hloc, (Hsrc, Htgt)); unfold loc_eq in *;
  destruct (Config.loc (c1 id)) eqn : Hloc1, (Config.loc (c2 id)) eqn : Hloc2,
  (Config.source (Config.robot_info (c1 id))) eqn : Hsrc1,
  (Config.source (Config.robot_info (c2 id))) eqn : Hsrc2,
  (Config.target (Config.robot_info (c1 id))) eqn : Htgt1,
  (Config.target (Config.robot_info (c2 id))) eqn : Htgt2; simpl;
  try rewrite Hloc1 in *; try rewrite Hloc2 in *; try rewrite Hsrc1 in *;
  try rewrite Hsrc2 in *; try rewrite Htgt1 in *; try rewrite Htgt2 in *;
  unfold loc_eq in *; try (now exfalso); try assumption;
  destruct Hloc;
  destruct (Rle_dec (project_p p) (Graph.threshold e)),(Rle_dec (project_p p0) (Graph.threshold e0));
  try (apply (Graph.src_compat e e0 H)); (try now rewrite H ,H0 in r); (try now rewrite H, H0 in n);
  try now apply Graph.tgt_compat.
  Qed.



  Definition projectS_loc (loc : Location.t) : Graph.V :=
     match loc with
       | Loc l =>  l
       | Mvt e p => 
         (if Rle_dec (project_p p) (Graph.threshold e)
            then Graph.src e 
            else Graph.tgt e)
     end.

  Instance projectS_loc_compat : Proper (Location.eq ==> Graph.Veq) projectS_loc.
  Proof.
  intros x y Hxy. simpl in *. unfold Location.eq, loc_eq in *.
  unfold projectS_loc. destruct x,y.
   - assumption.
   - exfalso; assumption.
   - exfalso; assumption.
   - destruct Hxy as (Hexy, Hpxy), (Rle_dec (project_p p) (Graph.threshold e)) eqn : Hx,
     (Rle_dec (project_p p0) (Graph.threshold e0)) eqn:Hy.
     + now apply Graph.src_compat.
     + assert (Ht := Graph.threshold_compat e e0 Hexy).
       assert (Hr : ((project_p p) <= Graph.threshold e)%R) by assumption.
       now rewrite Ht, Hpxy in Hr.
     + assert (Hr : ((project_p p0) <= Graph.threshold e0)%R) by assumption.
       assert (Ht := Graph.threshold_compat e e0 Hexy).
       now rewrite <- Ht, <- Hpxy in Hr.
     + now apply Graph.tgt_compat.
  Qed.

  Definition projectS (config : Config.t) : View.t :=
    fun id =>
      {| ConfigA.loc := (projectS_loc (Config.loc (config id)));
          ConfigA.robot_info := 
      {| ConfigA.source := (projectS_loc (Config.source (Config.robot_info (config id))));
          ConfigA.target := (projectS_loc (Config.target (Config.robot_info (config id)))) |} |}.

  Instance projectS_compat : Proper (Config.eq ==> ConfigA.eq) projectS.
  Proof.
  intros c1 c2 Hc id. destruct (Hc id) as (Hl, (Hs, Ht)). unfold projectS.
  split; simpl. now apply projectS_loc_compat. split; simpl; now apply projectS_loc_compat.
  Qed.

  (** the spectrum is what the robots see*)
  Module Spect : Spectrum(Location)(N)(Names)(Config) with Definition t := View.t 
  with Definition from_config := (fun x => projectS x) with Definition eq := View.eq.

    Definition t := ConfigA.t.
    Definition eq := ConfigA.eq.
    Definition eq_equiv := ConfigA.eq_equiv.
    Definition eq_dec := ConfigA.eq_dec.


    Definition from_config := fun x => (projectS x).
    Instance from_config_compat : Proper (Config.eq ==> View.eq) from_config.
    Proof.
    intros x y Hxy. unfold from_config. now apply projectS_compat.
    Defined.
    Definition is_ok : t -> Config.t -> Prop := fun t c => if (eq_dec t (projectS c)) 
                                                then True else False.
    Definition from_config_spec : forall config, is_ok (from_config config) config.
    Proof.
    intro.
    unfold is_ok, from_config. destruct (eq_dec (projectS config) (projectS config)); auto.
    destruct n. reflexivity.
    Defined.

  End Spect.

  (** * robogram *)

  Record robogram := {
    pgm :> Spect.t -> Location.t;
    pgm_compat : Proper (Spect.eq ==> Location.eq) pgm;
    pgm_loc : forall spect, exists l, pgm spect = Loc l;
    pgm_range : forall (spect: Spect.t) g sloc,
              Graph.Veq (ConfigA.loc (spect (Good g))) sloc ->
              exists l e, pgm spect = Loc l /\ Graph.find_edge sloc l = Some e }.
  
  Global Existing Instance pgm_compat.
  
  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.
  
  Instance req_equiv : Equivalence req.
  Proof. split.
  + intros [robogram Hrobogram] x y Heq; simpl. rewrite Heq. reflexivity.
  + intros r1 r2 H x y Heq. rewrite <- (H _ _ (reflexivity _)). now apply (pgm_compat r1).
  + intros r1 r2 r3 H1 H2 x y Heq.
    rewrite (H1 _ _ (reflexivity _)), (H2 _ _ (reflexivity _)). now apply (pgm_compat r3).
  Qed.
  
  (** * Executions *)
  
  (** Now we can [execute] some robogram from a given configuration with a [demon] *)
  CoInductive execution :=
    NextExecution : Config.t -> execution -> execution.
  
  
  (** *** Destructors for demons *)
  
  Definition execution_head (e : execution) : Config.t :=
    match e with NextExecution conf _ => conf end.
  
  Definition execution_tail (e : execution) : execution :=
    match e with NextExecution _ e => e end.
  
  CoInductive eeq (e1 e2 : execution) : Prop :=
    | Ceeq : Config.eq (execution_head e1) (execution_head e2) ->
             eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.
  
  Instance eeq_equiv : Equivalence eeq.
  Proof. split.
  + coinduction eeq_refl. reflexivity.
  + coinduction eeq_sym. symmetry. now inversion H. now inversion H.
  + coinduction eeq_trans. 
    - inversion H. inversion H0. now transitivity (execution_head y).
    - apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
      now inversion H. now inversion H0.
  Qed.
  
  Instance eeq_bisim : Bisimulation execution.
  Proof. exists eeq. apply eeq_equiv. Qed.
  
  Instance execution_head_compat : Proper (eeq ==> Config.eq) execution_head.
  Proof. intros e1 e2 He id. subst. inversion He. intuition. Qed.
  
  Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
  Proof. intros e1 e2 He. now inversion He. Qed.

  (** ** Demonic schedulers *)

  (** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)


  Inductive Active_or_Moving := 
    | Moving (dist :R)         (* moving ratio *)
    | Active (sim : unit).     (* change of referential *)

  Definition Aom_eq (a1 a2: Active_or_Moving) :=
    match a1, a2 with
      | Moving d1, Moving d2 => d1 = d2
      | Active sim1, Active sim2 => (Logic.eq)%signature sim1 sim2
      | _, _ => False
    end.


  Instance Active_compat : Proper (Logic.eq ==> Aom_eq) Active.
  Proof. intros ? ? ?. auto. Qed.

  Instance Aom_eq_reflexive : Reflexive Aom_eq.
  Proof. intros x. unfold Aom_eq. now destruct x. Qed.

  Instance Aom_eq_Symmetric : Symmetric Aom_eq.
  Proof.
  intros x y H. unfold Aom_eq in *. destruct x, y; auto.
  Qed.

  Instance Aom_eq_Transitive : Transitive Aom_eq.
  Proof.
  intros [] [] [] H12 H23; unfold Aom_eq in *; congruence || easy || auto.
  Qed.


  Record demonic_action := {
    relocate_byz : Names.B -> Location.t;
    step : Names.ident -> Config.RobotConf -> Active_or_Moving;
    step_delta : forall g Rconfig sim, (step (Good g) Rconfig) = (Active sim) ->
         ((exists l, Location.eq Rconfig.(Config.loc) (Loc l)) /\
         Location.eq Rconfig.(Config.loc) Rconfig.(Config.robot_info).(Config.target));
    step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step;
    step_flexibility : forall id config r,(step id config) = (Moving r) -> (0 <= r <= 1)%R}.
  Set Implicit Arguments.


  Definition da_eq (da1 da2 : demonic_action) :=
    (forall id config, (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
    (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

  Instance da_eq_equiv : Equivalence da_eq.
  Proof. split.
  + split; intuition.
  + intros da1 da2 [Hda1 Hda2]. repeat split; repeat intro; try symmetry; auto.
  + intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
    repeat split; intros; try etransitivity; eauto.
  Qed.

  Instance step_da_compat : Proper (da_eq ==> eq ==> Config.eq_RobotConf ==> Aom_eq) step.
  Proof.
  intros da1 da2 [Hd1 Hd2] p1 p2 Hp x y Hxy. subst.
  etransitivity.
  - apply Hd1.
  - apply (step_compat da2); auto.
  Qed.

  Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Location.eq) relocate_byz.
  Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

  Lemma da_eq_step_Moving : forall da1 da2, da_eq da1 da2 -> 
                          forall id config r, step da1 id config = (Moving r) <-> 
                                              step da2 id config = (Moving r).
  Proof.
  intros da1 da2 Hda id config r.
  assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
  split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step; reflexivity || elim Hopt_eq; auto.
  Qed.

  (** A [demon] is just a stream of [demonic_action]s. *)
  CoInductive demon :=
    NextDemon : demonic_action -> demon -> demon.

  (** Destructors for demons, getting the head demonic action or the
      tail of the demon. *)

  Definition demon_head (d : demon) : demonic_action :=
    match d with NextDemon da _ => da end.

  Definition demon_tail (d : demon) : demon :=
    match d with NextDemon _ d => d end.

  CoInductive deq (d1 d2 : demon) : Prop :=
    | Cdeq : da_eq (demon_head d1) (demon_head d2) ->
             deq (demon_tail d1) (demon_tail d2) -> deq d1 d2.

  Instance deq_equiv : Equivalence deq.
  Proof. split.
  + coinduction deq_refl. reflexivity.
  + coinduction deq_sym. symmetry. now inversion H. now inversion H.
  + coinduction deq_trans.
    - inversion H. inversion H0. now transitivity (demon_head y).
    - apply (deq_trans (demon_tail x) (demon_tail y) (demon_tail z)).
        now inversion H.
        now inversion H0.
  Qed.

  Instance demon_head_compat : Proper (deq ==> da_eq) demon_head.
  Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.

  Instance demon_tail_compat : Proper (deq ==> deq) demon_tail.
  Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.
  
  Definition is_Active aom :=
  match aom with
    | Active _ => true
    | _ => false
  end.

Instance is_Active_compat : Proper (Aom_eq ==> eq) is_Active.
Proof.
intros a1 a2 Haom.
unfold is_Active, Aom_eq in *.
destruct a1,a2; auto.
exfalso; auto.
Qed.

Inductive LocallyFairForOne id (d : demon) : Prop :=
  | ImmediatelyFair : forall config, is_Active (step (demon_head d) id (config id)) = true -> 
                                      LocallyFairForOne id d
  | LaterFair : forall config, is_Active (step (demon_head d) id (config id)) = false ->
                                 LocallyFairForOne id (demon_tail d) -> LocallyFairForOne id d.

CoInductive Fair (d : demon) : Prop :=
  AlwaysFair : (forall g, LocallyFairForOne g d) -> Fair (demon_tail d) ->
               Fair d.

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k conf, is_Active (step (demon_head d) g (conf g)) = true -> Between g h d k
| kReduce : forall k conf, is_Active (step (demon_head d) g (conf g)) = false ->
                            is_Active (step (demon_head d) h (conf g)) = true ->
                      Between g h (demon_tail d) k -> Between g h d (S k)
| kStall : forall k conf, is_Active (step (demon_head d) g (conf g)) = false ->
                           is_Active (step (demon_head d) h (conf g)) = false ->
                     Between g h (demon_tail d) k -> Between g h d k.

(* k-fair: every robot g is activated within at most k activation of any other robot h *)
CoInductive kFair k (d : demon) : Prop :=
  AlwayskFair : (forall g h, Between g h d k) -> kFair k (demon_tail d) ->
                kFair k d.

Lemma LocallyFairForOne_compat_aux : forall g d1 d2, deq d1 d2 -> 
                                     LocallyFairForOne g d1 -> LocallyFairForOne g d2.
Proof.
intros g d1 d2 Hd Hfair. revert d2 Hd. induction Hfair; intros d2 Hd.
 + assert (Heq : is_Active (step (demon_head d2) g (config g)) = true) by now rewrite <- Hd, H.
   destruct (step (demon_head d2) g) eqn:?; simpl in Heq.
   - easy.
   - constructor 1 with config.
     unfold is_Active.
     rewrite Heqa; auto.
 + assert (Heq : is_Active (step (demon_head d2) g (config g)) = false) by now rewrite <- Hd, H.
   destruct (step (demon_head d2) g) eqn:?; simpl in Heq.
   - constructor 2 with config.
     unfold is_Active.
     rewrite Heqa.
     assumption.
     apply IHHfair.
     now f_equiv.
   - apply IHHfair.
     assert (Hneq:= Bool.diff_true_false).
     exfalso; auto.
 Qed.
 

Instance LocallyFairForOne_compat : Proper (eq ==> deq ==> iff) LocallyFairForOne.
Proof. repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

Lemma Fair_compat_aux : forall d1 d2, deq d1 d2 -> Fair d1 -> Fair d2.
Proof.
cofix be_fair. intros d1 d2 Heq Hfair. destruct Hfair as [Hnow Hlater]. constructor.
+ intro. now rewrite <- Heq.
+ eapply be_fair; try eassumption. now f_equiv.
Qed.

Instance Fair_compat : Proper (deq ==> iff) Fair.
Proof. repeat intro. split; intro; now eapply Fair_compat_aux; eauto. Qed.

Lemma Between_compat_aux : forall g h k d1 d2, deq d1 d2 -> Between g h d1 k -> Between g h d2 k.
Proof.
intros g h k d1 d2 Heq bet. revert d2 Heq. induction bet; intros d2 Heq.
+ assert (Heqa : is_Active (step (demon_head d2) g (conf g)) = true) by now rewrite <- Heq, H.
  destruct (step (demon_head d2) g (conf g)) eqn:?; simpl in Heqa.
   - easy.
   - constructor 1 with conf. unfold is_Active. rewrite Heqa0; auto.
+ assert (Heqa : is_Active (step (demon_head d2) h (conf g)) = true) by now rewrite <- Heq, H0.
  destruct (step (demon_head d2) h (conf g)) eqn:?; simpl in Heq.
  - easy.
  - constructor 2 with conf.
    * unfold is_Active in *. destruct (step (demon_head d2) g (conf g)) eqn:?,
      (step (demon_head d) g (conf g)) eqn:?; intuition.
      rewrite <- da_eq_step_Moving with (da1 := (demon_head d2)) in *. 
      rewrite Heqa1 in Heqa2. discriminate.
      symmetry.
      apply Heq.
    * rewrite Heqa0; assumption.
    * apply IHbet; now f_equiv.
+ constructor 3 with conf.
  - unfold is_Active in *.
    destruct (step (demon_head d2) g (conf g)) eqn:?, (step (demon_head d) g (conf g)) eqn:?; intuition.
    rewrite <- da_eq_step_Moving with (da1 := (demon_head d2)) in *.
    rewrite Heqa in Heqa0; discriminate.
    symmetry; apply Heq.
  - unfold is_Active in *.
    destruct (step (demon_head d2) h (conf g)) eqn:?, (step (demon_head d) h (conf g)) eqn:?; intuition.
    rewrite <- da_eq_step_Moving with (da1 := (demon_head d2)) in *.
    rewrite Heqa in Heqa0; discriminate. symmetry; apply Heq.
  - apply IHbet. now f_equiv.
Qed.

Instance Between_compat : Proper (eq ==> eq ==> deq ==> eq ==> iff) Between.
Proof. repeat intro. subst. split; intro; now eapply Between_compat_aux; eauto. Qed.

Lemma kFair_compat_aux : forall k d1 d2, deq d1 d2 -> kFair k d1 -> kFair k d2.
Proof.
cofix be_fair. intros k d1 d2 Heq Hkfair. destruct Hkfair as [Hnow Hlater]. constructor.
+ intros. now rewrite <- Heq.
+ eapply be_fair; try eassumption. now f_equiv.
Qed.

Instance kFair_compat : Proper (eq ==> deq ==> iff) kFair.
Proof. repeat intro. subst. split; intro; now eapply kFair_compat_aux; eauto. Qed.

Lemma Between_LocallyFair : forall g (d : demon) h k,
  Between g h d k -> LocallyFairForOne g d.
Proof.
  intros g h d k Hg. induction Hg.
  now constructor 1 with conf.
  constructor 2 with conf. apply H. apply IHHg.
  constructor 2 with conf. apply H. apply IHHg.
Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof.
  intros g d k Hd. induction Hd.
  now constructor 1 with config.
  now constructor 3 with config.
Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof.
  coinduction kfair_is_fair.
  destruct H as [Hbetween H]. intro. apply Between_LocallyFair with g k. now apply Hbetween.
  apply (kfair_is_fair k). now destruct H.
Qed.

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall g h (d : demon) k,
  Between g h d k -> forall k', (k <= k')%nat -> Between g h d k'.
Proof.
  intros g h d k Hd. induction Hd; intros k' Hk.
  now constructor 1 with conf.
  destruct k'.
    now inversion Hk.
    constructor 2 with conf; assumption || now (apply IHHd; omega).
  constructor 3 with conf; assumption || now (apply IHHd; omega).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mon : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
  coinduction fair; destruct H.
  - intros. now apply Between_mon with k.
  - now apply (fair k).
Qed.


(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the demon never
  return a null reference. *)


(** A demon is fully synchronous for one particular good robot g at the first
    step. *)
Inductive FullySynchronousForOne g d:Prop :=
  ImmediatelyFair2: forall conf,
    is_Active (step (demon_head d) g (conf g)) = true -> 
                      FullySynchronousForOne g d.

(** A demon is fully synchronous if it is fully synchronous for all good robots
    at all step. *)
CoInductive FullySynchronous d :=
  NextfullySynch:
    (forall g, FullySynchronousForOne g d)
    -> FullySynchronous (demon_tail d)
    -> FullySynchronous d.


(** A locally synchronous demon is fair *)
Lemma local_fully_synchronous_implies_fair:
  forall g d, FullySynchronousForOne g d -> LocallyFairForOne g d.
Proof. induction 1. now (constructor 1 with conf). Qed.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_fair: forall d, FullySynchronous d -> Fair d.
Proof.
  coinduction fully_fair.
  - intro. apply local_fully_synchronous_implies_fair. apply X.
  - now inversion X.
Qed.



  (** [round r da conf] return the new configuration of robots (that is a function
      giving the configuration of each robot) from the previous one [conf] by applying
      the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
      is used for byzantine robots. *)


  Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
    (** for a given robot, we compute the new configuration *)
    fun id =>
      let conf := config id in
      let pos := conf.(Config.loc) in
      match da.(step) id conf with (** first see whether the robot is activated *)
        | Moving mv_ratio =>
          match pos, id with
            | Mvt e p, Good g => if Rle_dec 1%R ((project_p p) + mv_ratio)
                then {| Config.loc := Loc (Graph.tgt e); Config.robot_info := Config.robot_info conf |}
                else {| Config.loc := if Rdec mv_ratio 0 
                                      then Mvt e p
                                      else Mvt e (project_p_inv ((project_p p) + mv_ratio));
                        Config.robot_info := Config.robot_info conf |}
            | Loc l, Good g =>
                if Rdec mv_ratio 0%R then conf else
                if Rdec mv_ratio 1%R then {| Config.loc := Config.target (Config.robot_info conf);
                                             Config.robot_info := Config.robot_info conf |} else
                let new_pos := match Config.target (Config.robot_info conf) with
                                 | Loc l => l
                                 | Mvt e _ => Graph.src e (* never used if we start from a "good conf" *)
                               end in
                if Graph.Veq_dec l new_pos then conf
                else 
                let e := match Graph.find_edge l new_pos with
                           | Some e => e
                           | None => e_default (* ici *)
                         end in
                         {| Config.loc := Mvt e (project_p_inv mv_ratio);
                            Config.robot_info := Config.robot_info conf |}
           | _, Byz b => conf
          end
        | Active sim => 
        (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
          match id with 
          | Byz b => {| Config.loc := da.(relocate_byz) b ; 
                        Config.robot_info := Config.robot_info conf |}
          | Good g =>
            let local_conf := project config in
            let target := r (Spect.from_config local_conf)
            in
             {| Config.loc := pos ; 
                Config.robot_info := {| Config.source := pos ; Config.target := target|} |}
        end
      end.
 
Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof.
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
unfold req in Hr.
unfold round.
assert (Hrconf : Config.eq_RobotConf (conf1 id) (conf2 id)). 
apply Hconf.
assert (Hstep := step_da_compat Hda (reflexivity id) Hrconf).
assert (Hsim: Aom_eq (step da1 id (conf1 id)) (step da1 id (conf2 id))).
apply step_da_compat; try reflexivity.
apply Hrconf.
destruct (step da1 id (conf1 id)) eqn : He1, (step da2 id (conf2 id)) eqn:He2,
(step da1 id (conf2 id)) eqn:He3, id as [ g| b]; try now elim Hstep.
+ unfold Aom_eq in *.
  destruct (Config.loc (conf1 (Good g))) eqn: Hloc1, (Config.loc (conf2 (Good g))) eqn : Hloc2.
  * destruct (Rdec dist 0), (Rdec dist0 0).
    - apply Hrconf.
    - now rewrite Hstep in e.
    - now rewrite Hstep in n.
    - destruct (Rdec dist 1), (Rdec dist0 1).
      -- f_equiv; apply Hrconf.
      -- now rewrite Hstep in e.
      -- now rewrite Hstep in n1.
      -- destruct (Config.target (Config.robot_info (conf1 (Good g)))) eqn : Htgt1,
         (Config.target (Config.robot_info (conf2 (Good g)))) eqn : Htgt2,
         (Config.source (Config.robot_info (conf1 (Good g)))) eqn : Hsrc1,
         (Config.source (Config.robot_info (conf2 (Good g)))) eqn : Hsrc2;
         destruct Hrconf as (Hloc, (Hsrc, Htgt)); rewrite Htgt1, Htgt2 in Htgt;
         rewrite Hloc1, Hloc2 in Hloc; rewrite Hsrc1, Hsrc2 in Hsrc; unfold loc_eq in *;
         try (now exfalso).
         ++ destruct (Graph.Veq_dec l l1), (Graph.Veq_dec l0 l2).
            ** apply Hconf.
            ** now rewrite Hloc, Htgt in v.
            ** now rewrite Hloc, Htgt in n3.
            ** repeat try (split; simpl); try apply Hconf.
               assert (Hcp := Graph.find_edge_compat l l0 Hloc l1 l2 Htgt).
               now destruct (Graph.find_edge l l1), (Graph.find_edge l0 l2).
               now rewrite Hstep.
         ++ destruct (Graph.Veq_dec l l1), (Graph.Veq_dec l0 l2).
            ** apply Hconf.
            ** now rewrite Hloc, Htgt in v.
            ** now rewrite Hloc, Htgt in n3.
            ** repeat try (split; simpl); try apply Hconf.
               assert (Hcp := Graph.find_edge_compat l l0 Hloc l1 l2 Htgt).
               now destruct (Graph.find_edge l l1), (Graph.find_edge l0 l2).
               now rewrite Hstep.
         ++ destruct Htgt as (Hte_eq, Htp_eq).
            assert (Htsrc: Graph.Veq (Graph.src e) (Graph.src e0)) by now apply Graph.src_compat.
            destruct (Graph.Veq_dec l (Graph.src e)), (Graph.Veq_dec l0 (Graph.src e0));
            try (rewrite Htsrc, Hloc in *; contradiction).
            apply Hconf.
            assert (opt_eq Graph.Eeq (Graph.find_edge l (Graph.src e))
                           (Graph.find_edge l0 (Graph.src e0))) by
            now apply Graph.find_edge_compat.
            destruct (Graph.find_edge l (Graph.src e)), (Graph.find_edge l0 (Graph.src e0));
            try (now simpl in *). simpl in *.
            try repeat (split; simpl); auto.
            now rewrite Hstep.
            apply Hconf.
            apply Hconf.
            try repeat (split; simpl).
            reflexivity.
            now rewrite Hstep.
            apply Hconf.
            apply Hconf.
         ++ destruct Htgt as (Hte_eq, Htp_eq).
            assert (Htsrc: Graph.Veq (Graph.src e) (Graph.src e0)) by now apply Graph.src_compat.
            destruct (Graph.Veq_dec l (Graph.src e)), (Graph.Veq_dec l0 (Graph.src e0));
            try (rewrite Htsrc, Hloc in *; contradiction).
            apply Hconf.
            assert (opt_eq Graph.Eeq (Graph.find_edge l (Graph.src e))
                           (Graph.find_edge l0 (Graph.src e0))) by
            now apply Graph.find_edge_compat.
            destruct (Graph.find_edge l (Graph.src e)), (Graph.find_edge l0 (Graph.src e0));
            try (now simpl in *). simpl in *.
            try repeat (split; simpl); auto.
            now rewrite Hstep.
            apply Hconf.
            apply Hconf.
            try repeat (split; simpl).
            reflexivity.
            now rewrite Hstep.
            apply Hconf.
            apply Hconf.
 * destruct Hrconf as (Hloc, (Hsrc, Htgt)).
   rewrite Hloc1, Hloc2 in Hloc. unfold loc_eq in *; now exfalso.
 * destruct Hrconf as (Hloc, (Hsrc, Htgt)).
   rewrite Hloc1, Hloc2 in Hloc. unfold loc_eq in *; now exfalso.
 * rewrite Hstep. 
   destruct Hrconf as (Hloc, (Hsrc, Htgt)).
   rewrite Hloc1, Hloc2 in Hloc. unfold loc_eq in Hloc. destruct Hloc as (He, Hp).
   rewrite Hp.
   destruct (Rle_dec 1 (project_p p0 + dist0)); 
   repeat try (split;simpl); try apply Hconf.
   - now apply Graph.tgt_compat.
   - destruct (Rdec dist0 0); unfold loc_eq; now split.
+ destruct (Config.loc (conf1 (Byz b))) eqn : HconfB1,
  (Config.loc (conf2 (Byz b))) eqn : HconfB2;
  try apply Hconf.
+ try repeat (split; simpl); try apply Hrconf. apply Hr. f_equiv. apply project_compat, Hconf.
+ try repeat (split; simpl); try apply Hrconf. now rewrite Hda.
  Qed.


  Definition execute (r : robogram): demon -> Config.t -> execution :=
    cofix execute d conf :=
    NextExecution conf (execute (demon_tail d) (round r (demon_head d) conf)).

  (** Decomposition lemma for [execute]. *)
  Lemma execute_tail : forall (r : robogram) (d : demon) (conf : Config.t),
    execution_tail (execute r d conf) = execute r (demon_tail d) (round r (demon_head d) conf).
  Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.

  Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
  Proof.
  intros r1 r2 Hr.
  cofix proof. constructor. simpl. assumption.
  apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
  Qed.

(** * recursive property *)

(** ** starting point 

  we define an initial configuration where all robot are on nodes,
  and their informations [source] and [target] are on the same node. *) 
Definition Conf_init (conf: Config.t) : Prop := forall id, exists l l' e,
Graph.find_edge l l' = Some e /\
Config.eq_RobotConf (conf id)
{| Config.loc := Loc l;
Config.robot_info := {| Config.source := Loc l; Config.target := Loc l'|} |}.


Lemma round_flow : forall rbg da g conf e p,
         loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e p) -> 
         (exists l, loc_eq (Config.loc (conf (Good g))) (Loc l)) \/
         (exists p', (project_p p' <= project_p p)%R /\
                     loc_eq (Config.loc (conf (Good g))) (Mvt e p')).
Proof.
intros rbg da g conf e p Hl.
unfold round in *.
destruct (step da (Good g) (conf (Good g))) eqn : Hstep. simpl in *.
destruct (Config.loc (conf (Good g))). left; now exists l.
destruct (Rle_dec 1 (project_p p0 + dist)); simpl in *; try now exfalso.
destruct (Rdec dist 0). right. exists p0. unfold loc_eq in Hl; destruct Hl.
repeat split. now rewrite H0. auto. right. exists p0.
unfold loc_eq in *. destruct Hl.
repeat split. rewrite <- H0, <- inv_pro;
assert (Hf:=step_flexibility da (Good g) (conf (Good g)) dist Hstep).
lra.
assert (Hp := project_p_image p0). lra. auto.
simpl in *. right. exists p. now split.
Qed.

(** ** if [source] and [target] are on some node, they're still on nodes after a [round] *)

(** defintion of probleme *)
Definition ri_loc_def (conf: Config.t) : Prop :=
  forall g, exists v1 v2,
    loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1) /\
    loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2).


(** it's true starting from the initial configuration *)
Lemma ri_loc_init : forall conf da rbg g,
      Conf_init conf -> exists v1' v2',
      loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1')
   /\ loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2').
Proof.
intros conf da rbg g Hinit.
unfold Conf_init in Hinit.
specialize (Hinit (Good g)).
destruct Hinit as (l, (l', (e, (Hli, (Hl, (Hsi, Hti)))))); simpl in *.
unfold round.
destruct (step da (Good g) (conf (Good g))) eqn: Hstep,
(Config.loc (conf (Good g)))eqn : Hloc; try now simpl in *.
+ destruct (Rdec dist 0). exists l, l'; now split.
  destruct (Rdec dist 1). simpl in *. exists l, l'; now split.
  destruct (Config.target (Config.robot_info (conf (Good g)))) eqn : Ht; try now simpl in *.
  unfold loc_eq in Hti, Hli.
  exists l, l'. simpl in *.
  assert (Hnal := Graph.NoAutoLoop e).
  assert (Hli_aux : opt_eq Graph.Eeq (Graph.find_edge l l') (Some e)) by now rewrite Hli.
  apply Graph.find2st in Hli_aux.
  destruct Hli_aux as (Hsrc, Htgt).
  rewrite <- Htgt, <- Hsrc in Hnal.
  rewrite <- Hti, <- Hl in Hnal.
  destruct (Graph.Veq_dec l0 l1); try contradiction.
  split; simpl in *.
  assumption.
  rewrite Ht.
  now simpl in *.
+ simpl in *.
assert (Hlp : Graph.Veq (ConfigA.loc (Spect.from_config (project conf) (Good g))) l).
unfold Spect.from_config, projectS, projectS_loc, project. simpl in *.
now do 2 rewrite Hloc.
assert (Hrange := pgm_range rbg (Spect.from_config (project conf)) g l Hlp).
  destruct Hrange as (l'', (_, (Hfin, _))).
  exists l, l''. split. apply Hl. now rewrite Hfin.
Qed.


(** recurrence's hypothesis*)
Lemma ri_loc_always : forall conf v1 v2 da rbg g,
      loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1) ->
      loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2) ->
exists v1' v2',
      loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1')
   /\ loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2').
Proof.
intros conf v1 v2 da rbg g Hs Ht.
unfold round. simpl in *.
destruct (step da (Good g) (conf (Good g))) eqn : Hstep,
(Config.loc (conf (Good g))) eqn : Hloc.
destruct (Rdec dist 0). exists v1, v2. split;assumption.
destruct (Rdec dist 1). simpl. exists v1, v2. split; assumption.
destruct (Graph.Veq_dec l
              match Config.target (Config.robot_info (conf (Good g))) with
              | Loc l0 => l0
              | Mvt e _ => Graph.src e
              end);
exists v1, v2; split;assumption.
destruct (Rle_dec 1 (project_p p + dist)); 
exists v1, v2; split;assumption.
simpl in *. exists l.
assert (Hrbg := pgm_loc rbg (Spect.from_config (project conf))).
destruct Hrbg as (lspect, Hrbg).
assert (Hlp : Graph.Veq (ConfigA.loc (Spect.from_config (project conf) (Good g))) l).
unfold Spect.from_config, projectS, projectS_loc, project. simpl in *.
do 2 rewrite Hloc.
reflexivity.
assert (Hrange := pgm_range rbg (Spect.from_config (project conf)) g l Hlp).
destruct Hrange as (spl, (e, (Hlocs,Hrange))). exists spl. split. reflexivity.
rewrite Hlocs. reflexivity.
simpl in *.
assert (Hfalse := step_delta da g (conf (Good g)) sim Hstep).
destruct Hfalse as ((l,Hfalse), _). rewrite Hloc in Hfalse. now exfalso.
Qed.


CoInductive ri : execution -> Prop :=
PropCons : forall e, ri_loc_def (execution_head e) -> ri (execution_tail e) -> ri e.

Lemma ri_round : forall r da config, ri_loc_def config -> ri_loc_def (round r da config).
Proof.
intros r da config Hinit.
unfold ri_loc_def in *.
intros g.
specialize (Hinit g).
destruct Hinit as (v1, (v2, (Hs, Ht))).
assert (Hfin := ri_loc_always config v1 v2 da r g Hs Ht).
apply Hfin.
Qed.

(** final proof *)
Lemma ri_always : forall r d config, ri_loc_def config -> ri (execute r d config).
Proof.
cofix Hrec.
intros d config r Hinit.
constructor.
+ unfold execute. simpl. assumption.
+ rewrite execute_tail. simpl. apply Hrec. apply ri_round. assumption.
Qed.

Corollary ri_always_bis : forall r d config, Conf_init config -> ri (execute r d config).
Proof. intros. apply ri_always. unfold Conf_init, ri_loc_def in *. firstorder. Qed.

(** ** starting from a good configuration, we stay in a good configuration *)

(** a good conf is :
    - [source] and [target] are on node.
    - if a robot is on a node, it's on its [target] or [source].
    - if a robot is onan edge, it's the edge between its [source] and [target].
    - there is a edge between [source] and [target]. *)
Definition group_good_def (conf: Config.t) : Prop := forall g,
    ri_loc_def conf /\
   (forall v0, loc_eq (Config.loc (conf (Good g))) (Loc v0) -> 
    loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v0) \/
    loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v0)) /\
   (forall v1 v2 e p,
    loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1) ->
    loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2) ->
    loc_eq (Config.loc (conf (Good g))) (Mvt e p) ->
    opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e)) /\
   (forall v1 v2,
    loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1) ->
    loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2) ->
    exists e, (opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e))).

(** initialisation *)
Lemma group_lem_init : forall conf (rbg : robogram) da g v0' v1' v2' e' p',
   Conf_init conf ->
   (loc_eq (Config.loc ((round rbg da conf) (Good g))) (Loc v0') ->
    loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v0') \/
    loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v0')) /\
   (loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1') ->
    loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2') ->
    loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e' p') ->
    opt_eq Graph.Eeq (Graph.find_edge v1' v2') (Some e')).
Proof.
intros conf rbg da g v0' v1' v2' e' p' Hinit.
unfold Conf_init in Hinit.
specialize (Hinit (Good g)).
destruct Hinit as (l, (l', (e, (Hli, (Hl, (Hsi, Hti)))))); simpl in *.
split.
+ intros Hl0. unfold round in *.
  destruct (step da (Good g) (conf (Good g))) eqn: Hstep,
  (Config.loc (conf (Good g)))eqn : Hloc; try now simpl in *.
  - rewrite <- Hl in *.
    simpl in *.
    destruct (Rdec dist 0). rewrite Hloc in Hl0. rewrite <- Hl0. now left.
    destruct (Rdec dist 1). simpl in *. now right.
    destruct (Config.target (Config.robot_info (conf (Good g)))) eqn : Ht; try now simpl in *.
    unfold loc_eq in Hti.
    destruct (Graph.Veq_dec l0 l1); try contradiction.
    rewrite Hloc in Hl0. rewrite <- Hl0. now left.
  - simpl in *. now left.
+ intros Hs' Ht' Hl'. unfold round in *.
  destruct (step da (Good g) (conf (Good g))) eqn: Hstep,
  (Config.loc (conf (Good g)))eqn : Hloc; try now simpl in *.
  destruct (Rdec dist 0). rewrite Hloc in Hl'; now simpl in *.
  destruct (Rdec dist 1). simpl in *. rewrite Ht' in Hl'; now simpl in *.
  destruct (Config.target (Config.robot_info (conf (Good g)))) eqn : Ht''; try now simpl in *.
  unfold loc_eq in Hti, Hl.
  destruct (Graph.Veq_dec l0 l1); try rewrite Hloc in *; try contradiction.
  simpl in *.
  assert (opt_eq Graph.Eeq (Graph.find_edge l0 l1) (Graph.find_edge l l')) by now apply Graph.find_edge_compat.
  rewrite Hli in H.
  destruct (Graph.find_edge l0 l1); try contradiction.
  destruct Hl' as (He,_).
  simpl in *.
  rewrite He in H.
  rewrite Ht'',Hsi in *.
  simpl in *.
  assert (opt_eq Graph.Eeq (Some e) (Some e')) by now simpl in *.
  rewrite <- H0, <- Hli.
  apply Graph.find_edge_compat; try now symmetry. now rewrite <- Ht'.
Qed.

(** recurence *)
Lemma group_lem : forall conf (rbg : robogram) da g,
   ri_loc_def conf ->
   (forall v0, loc_eq (Config.loc (conf (Good g))) (Loc v0) -> 
    loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v0) \/
    loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v0)) ->
   (forall v1 v2 e p,
    loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1) ->
    loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2) ->
    loc_eq (Config.loc (conf (Good g))) (Mvt e p) ->
    opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e)) ->
   (forall v1 v2,
    loc_eq (Config.source (Config.robot_info (conf (Good g)))) (Loc v1) ->
    loc_eq (Config.target (Config.robot_info (conf (Good g)))) (Loc v2) ->
    exists e, (opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e))) ->
   ri_loc_def (round rbg da conf) /\
   (forall v0',
    loc_eq (Config.loc ((round rbg da conf) (Good g))) (Loc v0') ->
    (loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v0') \/
    loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v0'))) /\
   (forall v1' v2' e' p',
    loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1') ->
    loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2') ->
    loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e' p') ->
    opt_eq Graph.Eeq (Graph.find_edge v1' v2') (Some e')) /\
   (forall v1' v2',
    loc_eq (Config.source (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v1') ->
    loc_eq (Config.target (Config.robot_info ((round rbg da conf) (Good g)))) (Loc v2') ->
    exists e, opt_eq Graph.Eeq (Graph.find_edge v1' v2') (Some e)).
Proof.
intros conf rbg da g Hinit Hli Hmi Hex_e.
repeat split.
+ now apply ri_round.
+ intros v0' H. unfold round in *.
  destruct (step da (Good g) (conf (Good g))) eqn: Hstep,
  (Config.loc (conf (Good g))) eqn : Hl.
  - destruct (Rdec dist 0).
    specialize (Hli v0'). apply Hli. now rewrite Hl in H.
    destruct (Rdec dist 1).
    simpl in *. now right.
    destruct (Config.target (Config.robot_info (conf (Good g)))) eqn : Ht.
    * destruct (Graph.Veq_dec l l0).
      specialize (Hli v0'). rewrite Ht. apply Hli. now rewrite Hl in H.
      destruct (Graph.find_edge l l0); now simpl in *.
    * destruct (Graph.Veq_dec l (Graph.src e)).
      specialize (Hli v0').
      destruct Hli.
      now rewrite Hl in H.
      now left.
      now unfold loc_eq in *.
      destruct (Graph.find_edge l (Graph.src e)); now simpl in *.
  - destruct (Rle_dec 1 (project_p p + dist)); simpl in *.
    * destruct (Hinit g) as (v1, (v2, Hri)). specialize (Hmi v1 v2 e p).
      apply Graph.find2st in Hmi.
      assert (Hproof : Graph.Veq (Graph.tgt e) v2).
      now destruct Hmi.
      right. destruct Hri as (Hsri, Htri).
      rewrite Htri. simpl in *. now rewrite <- Hproof.
      apply Hri.
      apply Hri.
      now split.
    * destruct (Rdec dist 0); now simpl in .
  - simpl in *. now left.
  - now simpl in *.
+ intros v1' v2' e' p' Hs0 Ht0 Hl0. unfold round in *.
  destruct (step da (Good g) (conf (Good g))) eqn: Hstep,
  (Config.loc (conf (Good g))) eqn : Hl.
  - destruct (Rdec dist 0). now rewrite Hl in Hl0.
    destruct (Rdec dist 1). simpl in *. now rewrite Ht0 in Hl0.
    destruct (Config.target (Config.robot_info (conf (Good g)))) eqn : Ht.
    * destruct (Graph.Veq_dec l l0).
      now rewrite Hl in Hl0.
      destruct (Graph.find_edge l l0) eqn : Hedge; simpl in *.
      specialize (Hli l). destruct Hli as [Hsi |Hti]. reflexivity.
      destruct Hl0 as (He, Hp).
      assert (Hedge' : opt_eq Graph.Eeq (Graph.find_edge l l0) (Some e')) by now (rewrite Hedge; apply He).
      rewrite Ht in Ht0. unfold loc_eq in Ht0. rewrite Ht0 in Hedge'.
      rewrite Hsi in Hs0. unfold loc_eq in Hs0. now rewrite Hs0 in Hedge'.
      now symmetry in Hti.
      specialize (Hex_e v1' v2').
      assert (exists e : Graph.E, opt_eq Graph.Eeq (Graph.find_edge v1' v2') (Some e)).
      apply Hex_e. apply Hs0. rewrite Ht in Ht0; now simpl in *.
      assert (Hrbg := pgm_range rbg (Spect.from_config (project conf)) g).
      specialize (Hrbg v1').
      destruct H as (e0, Hedge0).
      specialize (Hli l). destruct Hli as [Hsi |Hti]. reflexivity.
      rewrite Hs0 in Hsi; rewrite Ht in Ht0. simpl in Ht0, Hsi.
      rewrite <-Ht0, Hsi in Hedge0.
      now rewrite Hedge in Hedge0.
      now symmetry in Hti.
    * destruct (Hinit g) as (_,(f, (_, Hf))). rewrite Ht in Hf.
      now simpl in *.
  - destruct (Rle_dec 1 (project_p p + dist));try now simpl in *.
    destruct (Rdec dist 0); simpl in *;
    specialize (Hmi v1' v2' e' p);
    now apply Hmi.
  - now simpl in *.
  - now simpl in *.
+ intros v1' v2'.
  unfold round.
  destruct (step da (Good g) (conf (Good g))) as [dist | sim] eqn : Hstep,
           (Config.loc (conf (Good g))) as [l| e p] eqn : Hloc.
  - specialize (Hex_e v1' v2').
    destruct (Rdec dist 0).
    apply Hex_e.
    destruct (Rdec dist 1); simpl in *.
    apply Hex_e.
    destruct (Config.target (Config.robot_info (conf (Good g)))) as [vt| et pt] eqn : Ht.
    destruct (Graph.Veq_dec l vt). rewrite Ht.
    apply Hex_e.
    destruct (Graph.find_edge l vt); simpl in *;
    now rewrite Ht.
    destruct (Hinit g) as (_,(f, (_, Hf))). rewrite Ht in Hf.
    now simpl in *.
  - specialize (Hex_e v1' v2').
    destruct (Rle_dec 1 (project_p p + dist)); simpl in *;
    apply Hex_e.
  - assert ( Hls : loc_eq (Config.source (Config.robot_info (round rbg da conf (Good g))))
    (Config.loc (round rbg da conf (Good g)))).
    { unfold round; rewrite Hloc, Hstep. simpl in *. reflexivity. }
    simpl in *.
    destruct (Hinit g) as (v01,(v02, (Hv01, Hv02))).
    specialize (Hex_e v01 v02).
    assert (Hdelta := step_delta da g (conf (Good g)) sim Hstep).
    destruct Hdelta as (_, Ht_delta).
    assert (Hrbg := pgm_range rbg (Spect.from_config (project conf)) g).
    specialize (Hrbg l).
    unfold project at 1, Spect.from_config at 1, projectS at 1, projectS_loc in Hrbg; simpl in *.
    do 2 rewrite Hloc in Hrbg.
    specialize (Hrbg (reflexivity l)).
    destruct Hrbg as (lr, (er, (Hr' , Hedge'))).
    intros Hl Hr.
    exists er.
    rewrite <- Hedge'.
    rewrite Hr' in Hr.
    apply Graph.find_edge_compat;
    now symmetry.
  - simpl in *. now intro.
Qed.


(** finals proofs*)
CoInductive group : execution -> Prop :=
GroupCons : forall e, group_good_def (execution_head e) -> group (execution_tail e) -> group e.

Lemma group_round : forall r da config, group_good_def config -> group_good_def(round r da config).
Proof.
intros r da config Hinit.
unfold group_good_def in *.
intros g.
destruct (Hinit g) as (Hini, (Hli, (Hmi, Hex_e))).
assert (Hgr := group_lem r da g Hini Hli Hmi Hex_e).
apply Hgr.
Qed.

Lemma group_always : forall r d config, group_good_def config -> group (execute r d config).
Proof.
cofix Hrec.
intros d config r Hinit.
constructor.
+ unfold execute. simpl. assumption.
+ rewrite execute_tail. simpl. apply Hrec. apply group_round. assumption.
Qed.

Corollary group_always_bis : forall r d config, Conf_init config ->
                                                group (execute r d (round r (demon_head d) config)).
Proof.
intros.
apply group_always.
unfold Conf_init, group_good_def in *.
repeat split.
+ apply ri_round.
  unfold ri_loc_def.
  intros g0.
  specialize (H (Good g0)).
  destruct H as (l, (l', (e', (Hl, (Hl',(Hs, Ht)))))).
  exists l, l'.
  destruct (Config.source (Config.robot_info (config (Good g0)))) eqn : Hs',
  (Config.target (Config.robot_info (config (Good g0)))) eqn : Ht'; try now simpl in *.
+ specialize (H (Good g)); destruct H as (l, (l', (e', (Hl, (Hl',(Hs, Ht)))))).
  destruct (Config.source (Config.robot_info (config (Good g)))) eqn : Hs',
  (Config.loc (config (Good g))) eqn : Hl'',
  (Config.target (Config.robot_info (config (Good g)))) eqn : Ht';
  simpl in *; try now exfalso. unfold round.
  destruct (step (demon_head d) (Good g) (config (Good g))) eqn: Hstep,
  (Config.loc (config (Good g))) eqn : Hl0; try discriminate; try (now exfalso).
  - destruct (Rdec dist 0); intros v0 Hl0'.
    left; rewrite Hs', Hl0, Hl'' in *; simpl in *. now rewrite <-Hl0', Hl', Hs.
    destruct (Rdec dist 1); simpl in *. now right.
    rewrite Ht' in *.
    assert (~Graph.Veq l3 l2).
    assert (Hnal := Graph.NoAutoLoop e').
    assert (Haux : opt_eq Graph.Eeq (Graph.find_edge l l') (Some e')) by now rewrite Hl.
    apply Graph.find2st in Haux.
    destruct Haux as (Hls, Hlt).
    assert (Haux2 : loc_eq (Loc l1) (Loc l3)) by now rewrite Hl''.
    simpl in *.
    now rewrite <- Hls, <- Hlt, <- Hl', <- Ht, Haux2 in Hnal.
    destruct (Graph.Veq_dec l3 l2); try contradiction.
  - simpl in *. intros v0 Hv. now left.
+ specialize (H (Good g)); destruct H as (l, (l', (e', (Hl, (Hl',(Hs, Ht)))))).
  destruct (Config.source (Config.robot_info (config (Good g)))) eqn : Hs',
  (Config.loc (config (Good g))) eqn : Hl'',
  (Config.target (Config.robot_info (config (Good g)))) eqn : Ht';
  simpl in *; try now exfalso. unfold round.
  destruct (step (demon_head d) (Good g) (config (Good g))) eqn: Hstep;
  try discriminate; try (now exfalso); intros v1 v2 e p Hs0 Ht0 Hl0; rewrite Hl'' in *.
  - destruct (Rdec dist 0). now rewrite Hl'' in *.
    destruct (Rdec dist 1). simpl in *. now rewrite Ht' in *.
    rewrite Ht' in *.
    assert (~Graph.Veq l1 l2).
    assert (Hnal := Graph.NoAutoLoop e').
    assert (Haux : opt_eq Graph.Eeq (Graph.find_edge l l') (Some e')) by now rewrite Hl.
    apply Graph.find2st in Haux.
    destruct Haux as (Hls, Hlt).
    now rewrite <- Hls, <- Hlt, <- Hl', <- Ht in Hnal.
    destruct (Graph.Veq_dec l1 l2); try contradiction.
    assert (opt_eq Graph.Eeq (Graph.find_edge l1 l2) (Graph.find_edge l l')) by now apply Graph.find_edge_compat.
    rewrite Hl in H0.
    destruct (Graph.find_edge l1 l2); try contradiction.
    simpl in *.
    destruct Hl0 as (Hle,_).
    rewrite Hle in H0.
    assert (Haux : opt_eq Graph.Eeq (Some e) (Some e')) by now simpl in *.
    rewrite Haux.
    rewrite Ht', Hs' in *.
    simpl in *.
    rewrite Hs, Ht in *.
    rewrite <- Hl.
    now apply Graph.find_edge_compat.
  - now simpl in *.
+ specialize (H (Good g)); destruct H as (l, (l', (e', (Hl, (Hl',(Hs, Ht)))))).
  destruct (Config.source (Config.robot_info (config (Good g)))) eqn : Hs',
  (Config.loc (config (Good g))) eqn : Hl'',
  (Config.target (Config.robot_info (config (Good g)))) eqn : Ht';
  simpl in *; try now exfalso. unfold round.
  destruct (step (demon_head d) (Good g) (config (Good g))) eqn: Hstep;
  try discriminate; try (now exfalso); intros v1 v2 Hv1 Hv2;
  rewrite Hl'' in *.
  destruct (Rdec dist 0).
  - rewrite Hs', Ht' in *.
    simpl in *.
    rewrite Hs, Ht in *.
    exists e'; rewrite <- Hl; now apply Graph.find_edge_compat.
  - destruct (Rdec dist 1); simpl in *.
    * rewrite Hs', Ht' in *.
      simpl in *.
      rewrite Hs, Ht in *.
      exists e'; rewrite <- Hl; now apply Graph.find_edge_compat.
    * rewrite Ht' in *.
      assert (~Graph.Veq l1 l2).
      assert (Hnal := Graph.NoAutoLoop e').
      assert (Haux : opt_eq Graph.Eeq (Graph.find_edge l l') (Some e')) by now rewrite Hl.
      apply Graph.find2st in Haux.
      destruct Haux as (Hls, Hlt).
      now rewrite <- Hls, <- Hlt, <- Hl', <- Ht in Hnal.
      destruct (Graph.Veq_dec l1 l2); try contradiction.
      assert (opt_eq Graph.Eeq (Graph.find_edge l1 l2) (Graph.find_edge l l')) by now apply Graph.find_edge_compat.
      rewrite Hl in H0.
      destruct (Graph.find_edge l1 l2); try contradiction.
      simpl in *.
      rewrite Hs', Ht' in *.
      simpl in *.
      rewrite Hs, Ht in *.
      exists e'; rewrite <- Hl; now apply Graph.find_edge_compat.
  - simpl in *.
    assert (Hpgm_aux : Graph.Veq (ConfigA.loc (Spect.from_config (project config) (Good g))) l1).
    { unfold Spect.from_config, project, projectS, projectS_loc; simpl in *.
      now repeat rewrite Hl''. }
    assert (Hpgm := pgm_range r (Spect.from_config (project config)) g l1 Hpgm_aux).
    destruct Hpgm as (l2', (e'', (Hpl, Hedge))).
    rewrite Hpl in *.
    simpl in *.
    exists e''.
    rewrite <- Hedge.
    now apply Graph.find_edge_compat.
 Qed.




End DGF.


