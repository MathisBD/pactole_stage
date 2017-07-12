(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
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
Require Import Pactole.Isomorphism.
Require Import Pactole.CommonIsoGraphFormalism.
Require Import Utf8_core.
Require Import Arith_base.
Require Import SetoidList.
Require Stream.
Require MultisetSpectrum.


Module CGF (Graph : GraphDef)
           (N : Size)
           (Names : Robots(N))
           (LocationA : LocationADef(Graph))
           (MkInfoA : InfoSig(Graph)(LocationA))
           (ConfigA : Configuration (LocationA)(N)(Names)(MkInfoA.Info))
           (SpectA : Spectrum(LocationA)(N)(Names)(MkInfoA.Info)(ConfigA))
           (Import Iso : Iso(Graph)(LocationA)).
  
  Module InfoA := MkInfoA.Info.
  
  (** For spectra *)
  Module View : DecidableType with Definition t := ConfigA.t with Definition eq := ConfigA.eq.
    Definition t := ConfigA.t.
    Definition eq := ConfigA.eq.
    Definition eq_equiv := ConfigA.eq_equiv.
    Definition eq_dec := ConfigA.eq_dec.
  End View.
  
  
  (** * Projection function*)

  Open Scope R_scope.

  (** We define a function from R to (0; 1) to represent the percentage of the edge already done. *)
  (* Excluding 0 and 1 avoids having multiple reprensentation while being on a node. *)
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


  Module Info := SourceTarget(Location).
  Module Config := Configurations.Make (Location)(N)(Names)(Info).
(*
  Definition project (config : Config.t) : Config.t :=
    fun id =>
      match Config.loc (config id) with
      | Loc l => config id
      | Mvt e p => {| Config.loc := Loc (if Rle_dec (project_p p) (Graph.threshold e) 
                                         then Graph.src e else Graph.tgt e);
                      Config.info := Config.info (config id) |}
      end.
  
  Instance project_compat : Proper (Config.eq ==> Config.eq) project.
  Proof.
    intros c1 c2 Hc id. unfold project.
    repeat try (split; simpl);
      destruct (Hc id) as (Hloc, (Hsrc, Htgt)); unfold loc_eq in *;
        destruct
          (Config.loc (c1 id))
          eqn : Hloc1,
                (Config.loc (c2 id))
                  eqn : Hloc2,
                        (Info.source (Config.info (c1 id)))
                          eqn : Hsrc1,
                                (Info.source (Config.info (c2 id)))
                                  eqn : Hsrc2,
                                        (Info.target (Config.info (c1 id)))
                                          eqn : Htgt1,
                                                (Info.target
                                                   (Config.info (c2 id)))
                                                  eqn : Htgt2; simpl;
          try rewrite Hloc1 in *; try rewrite Hloc2 in *; try rewrite Hsrc1 in *;
            try rewrite Hsrc2 in *; try rewrite Htgt1 in *; try rewrite Htgt2 in *;
              unfold loc_eq in *; try (now exfalso); try assumption;
                destruct Hloc;
                destruct (Rle_dec (project_p p) (Graph.threshold e)),
                (Rle_dec (project_p p0) (Graph.threshold e0));
                try (apply (Graph.src_compat e e0 H));
                (try now rewrite H ,H0 in r); (try now rewrite H, H0 in n);
                  try now apply Graph.tgt_compat.
  Qed.

*)

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
    - destruct Hxy as (Hexy, Hpxy),
                      (Rle_dec (project_p p) (Graph.threshold e))
                        eqn : Hx,
                              (Rle_dec (project_p p0) (Graph.threshold e0))
                                eqn : Hy.
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
         ConfigA.info := 
           {| InfoA.source := (projectS_loc (Info.source (Config.info (config id))));
              InfoA.target := (projectS_loc (Info.target (Config.info (config id)))) |}
      |}.

  Instance projectS_compat : Proper (Config.eq ==> ConfigA.eq) projectS.
  Proof.
    intros c1 c2 Hc id. destruct (Hc id) as (Hl, (Hs, Ht)). unfold projectS.
    split; simpl. now apply projectS_loc_compat. split; simpl; now apply projectS_loc_compat.
  Qed.

  Close Scope R_scope.

  (** The spectrum for continuous setting is the same as for the discrete one:
      we simply project robots on edges either to the source or target of the edge
      depending on where they are located compared to the threshold of the edge. *)
  Module Spect <: Spectrum(Location)(N)(Names)(Info)(Config).
    
    Definition t := SpectA.t.
    Definition eq := SpectA.eq.
    Definition eq_equiv := SpectA.eq_equiv.
    Definition eq_dec := SpectA.eq_dec.
    
    Definition from_config conf : t := SpectA.from_config (projectS conf).
    
    Instance from_config_compat : Proper (Config.eq ==> eq) from_config.
    Proof. repeat intro. unfold from_config. now repeat f_equiv. Qed.
    
    Definition is_ok s conf := SpectA.is_ok s (projectS conf).
    
    Theorem from_config_spec : forall conf, is_ok (from_config conf) conf.
    Proof. intro. unfold from_config, is_ok. apply SpectA.from_config_spec. Qed.
    
  End Spect.

  Record robogram :=
    {
      pgm :> Spect.t -> Location.t -> Location.t;
      pgm_compat : Proper (Spect.eq ==> Location.eq ==> Location.eq) pgm;
      pgm_range :  forall (spect: Spect.t) lpre l',
          loc_eq lpre (Loc l') -> 
          exists l e, pgm spect lpre = Loc l
                      /\ (opt_eq Graph.Eeq (Graph.find_edge l' l) (Some e))
    }.

  (* pgm s l a du dens si l est dans dans s (s[l] > 0) *)
  
  Global Existing Instance pgm_compat.

  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq ==> Location.eq)%signature r1 r2.

  Instance req_equiv : Equivalence req.
  Proof. split.
         + intros [robogram Hrobogram] x y Heq g1 g2 Hg; simpl. rewrite Hg, Heq. reflexivity.
         + intros r1 r2 H x y Heq g1 g2 Hg. rewrite Hg, Heq.
           unfold req in H.
           now specialize (H y y (reflexivity y) g2 g2 (reflexivity g2)).
         + intros r1 r2 r3 H1 H2 x y Heq g1 g2 Hg.
           specialize (H1 x y Heq g1 g2 Hg). 
           specialize (H2 y y (reflexivity y) g2 g2 (reflexivity g2)).
           now rewrite H1.
  Qed.
  
  (** * Executions *)
  
  (** Now we can [execute] some robogram from a given configuration with a [demon] *)
  Definition execution := Stream.t Config.t.
  
  Definition eeq (e1 e2 : execution) : Prop :=
    Stream.eq Config.eq e1 e2.
  
  Instance eeq_equiv : Equivalence eeq.
  Proof. split.
         + coinduction eeq_refl. reflexivity.
         + coinduction eeq_sym. symmetry. now inversion H. now inversion H.
         + coinduction eeq_trans. 
         - inversion H. inversion H0. now transitivity (Stream.hd y).
         - apply (eeq_trans (Stream.tl x) (Stream.tl y) (Stream.tl z)).
           now inversion H. now inversion H0.
  Qed.
  
  Instance eeq_hd_compat : Proper (eeq ==> Config.eq) (@Stream.hd _).
  Proof. apply Stream.hd_compat. Qed.
  
  Instance eeq_tl_compat : Proper (eeq ==> eeq) (@Stream.tl _).
  Proof. apply Stream.tl_compat. Qed.

  (** ** Demonic schedulers *)

  (** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)


  Inductive Active_or_Moving := 
  | Moving (dist : R)         (* moving ratio *)
  | Active (sim : Iso.t).     (* change of referential *)

  Definition Aom_eq (a1 a2: Active_or_Moving) :=
    match a1, a2 with
    | Moving d1, Moving d2 => d1 = d2
    | Active sim1, Active sim2 => Iso.eq sim1 sim2
    | _, _ => False
    end.


  Instance Active_compat : Proper (Iso.eq ==> Aom_eq) Active.
  Proof. intros ? ? ?. auto. Qed.

  Instance Aom_eq_equiv : Equivalence Aom_eq.
  Proof. split.
  + now intros [].
  + intros x y H. unfold Aom_eq in *. destruct x, y; auto.
    now symmetry.
  + intros [] [] [] H12 H23; unfold Aom_eq in *; congruence || easy || auto.
    now rewrite H12, H23.
  Qed.

  Record demonic_action :=
    {
      relocate_byz : Names.B -> Config.RobotConf;
      step : Names.ident -> Config.RobotConf -> Active_or_Moving;
      step_delta : forall g Rconfig sim,
          Aom_eq (step (Good g) Rconfig) (Active sim) ->
          ((exists l, Location.eq Rconfig.(Config.loc) (Loc l)) /\
           Location.eq Rconfig.(Config.loc)
                                 Rconfig.(Config.info).(Info.target));
      step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step;
      step_flexibility : forall id config r,
          Aom_eq (step id config) (Moving r) -> (0 <= r <= 1)%R}.
  Set Implicit Arguments.


  Definition da_eq (da1 da2 : demonic_action) :=
    (forall id config,
        (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
    (forall b : Names.B, Config.eq_RobotConf (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

  Instance da_eq_equiv : Equivalence da_eq.
  Proof. split.
  + split; intuition.
  + intros da1 da2 [Hda1 Hda2]. split; repeat intro; try symmetry; auto.
  + intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
    split; intros; try etransitivity; eauto.
  Qed.

  Instance step_da_compat : Proper (da_eq ==> eq ==> Config.eq_RobotConf ==> Aom_eq) step.
  Proof.
    intros da1 da2 [Hd1 Hd2] p1 p2 Hp x y Hxy. subst.
    etransitivity.
    - apply Hd1.
    - apply (step_compat da2); auto.
  Qed.

  Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Config.eq_RobotConf) relocate_byz.
  Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

  Lemma da_eq_step_Moving : forall da1 da2,
      da_eq da1 da2 -> 
      forall id config r, Aom_eq (step da1 id config) (Moving r) <-> 
                          Aom_eq (step da2 id config) (Moving r).
  Proof.
    intros da1 da2 Hda id config r.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
    split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step; reflexivity || elim Hopt_eq; now auto.
  Qed.

  Lemma da_eq_step_Active : forall da1 da2,
      da_eq da1 da2 -> 
      forall id config sim, Aom_eq (step da1 id config) (Active sim) <-> 
                            Aom_eq (step da2 id config) (Active sim).
  Proof.
    intros da1 da2 Hda id config sim.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
    split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step; reflexivity || elim Hopt_eq; now auto.
  Qed.
  
  (** A [demon] is just a stream of [demonic_action]s. *)
  Definition demon :=
    Stream.t demonic_action.

  (** Destructors for demons, getting the head demonic action or the
      tail of the demon. *)

  Definition deq (d1 d2 : demon) : Prop :=
    Stream.eq da_eq d1 d2.
    
  Instance deq_equiv : Equivalence deq.
  Proof. split.
  + coinduction deq_refl. reflexivity.
  + coinduction deq_sym. symmetry. now inversion H. now inversion H.
  + coinduction deq_trans.
    - inversion H. inversion H0. now transitivity (Stream.hd y).
    - apply (deq_trans (Stream.tl x) (Stream.tl y) (Stream.tl z)).
      * now inversion H.
      * now inversion H0.
  Qed.

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

  Definition apply_sim (sim : Iso.t) (infoR : Config.RobotConf) :=
    let fpos := (fun loc => 
    match loc with
    | Mvt e p => 
      Mvt ((Iso.sim_E sim) e) (project_p_inv ((Iso.sim_T sim) (project_p p)))
    | Loc l => Loc ((Iso.sim_V sim) l)
    end) in
    {| Config.loc := fpos (Config.loc infoR);
       Config.info :=
         {| Info.source := fpos (Info.source (Config.info infoR));
            Info.target := fpos (Info.target (Config.info infoR)) |} |}.

  Instance apply_sim_compat : Proper (Iso.eq ==> Config.eq_RobotConf ==>
                                             Config.eq_RobotConf) apply_sim.
  Proof.
    intros sim sim' Hsim conf conf' Hconf.
    unfold apply_sim. hnf.
    repeat split; simpl;
      destruct Hconf as (Hconf, (Hsrc, Htgt)).
    - destruct (Config.loc conf) eqn : Hc, (Config.loc conf') eqn : Hc';
      try contradiction;
      try apply Hsim, Hconf; 
      unfold loc_eq in Hconf; simpl.
      destruct Hconf.
      rewrite H0.
      simpl.
      now rewrite Hsim, H.
    - destruct (Info.source (Config.info conf)),
           (Info.source (Config.info conf')); try contradiction;
        simpl in *.
      * now rewrite Hsim, Hsrc.
      * destruct Hsrc.
        now rewrite Hsim, H, H0.
    - destruct (Info.target (Config.info conf)),
           (Info.target (Config.info conf')); try contradiction;
        simpl in *.
      * now rewrite Hsim, Htgt.
      * destruct Htgt.
        now rewrite Hsim, H, H0.
  Qed.
  Global Notation "s ⁻¹" := (Iso.inverse s) (at level 99).


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
                             then {| Config.loc := Loc (Graph.tgt e); Config.info := Config.info conf |}
                             else {| Config.loc := if Rdec mv_ratio 0 
                                                   then Mvt e p
                                                   else Mvt e (project_p_inv ((project_p p) + mv_ratio));
                                     Config.info := Config.info conf |}
        | Loc l, Good g =>
          let node_of_tgt := match Info.target (Config.info conf) with
                             | Loc lt => lt
                             | Mvt e _ => Graph.src e (* never used if we start from a
                                                                  "good conf" *)
                         end
          in
          if (Graph.Veq_dec node_of_tgt l) then
            conf
          else
          if Rdec mv_ratio 0%R
          then conf
          else
            if Rdec mv_ratio 1%R
            then {| Config.loc := Info.target (Config.info conf);
                                         Config.info := Config.info conf |}
            else
              let e := match Graph.find_edge l node_of_tgt with
                         | Some e => e
                         | None => e_default (* never used if we start from a 
                                                              "good conf" *)
                         end in
                {| Config.loc := Mvt e (project_p_inv mv_ratio);
                   Config.info := Config.info conf |}
        | _, Byz b => conf
        end
      | Active sim => 
        (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
        match id with 
        | Byz b => da.(relocate_byz) b
        | Good g =>
          let local_conf := Config.map (apply_sim sim) config in
          let target :=
              match (r (Spect.from_config local_conf)
                       (Config.loc (local_conf (Good g)))) with
              | Loc l => (sim⁻¹).(Iso.sim_V) l
              | Mvt e _ => (Graph.src e) (* never used : see pgm_range *)
              end
          in
          if (Location.eq_dec (Loc target) pos) then conf else
          {| Config.loc := pos ; 
             Config.info := {| Info.source := pos ; Info.target := Loc target|} |}
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
    destruct (step da1 id (conf1 id)) eqn:He1,
             (step da2 id (conf2 id)) eqn:He2,
             (step da1 id (conf2 id)) eqn:He3,
             id as [ g| b];
      try (now elim Hstep); unfold Aom_eq in *; try now exfalso.
    - assert (Location.eq (Info.target (Config.info (conf1 (Good g))))
                          (Info.target (Config.info (conf2 (Good g)))))
        by now apply Hconf.
      assert (Location.eq (Config.loc (conf1 (Good g)))
                          (Config.loc (conf2 (Good g))))
        by now apply Hconf.
      destruct (Config.loc (conf1 (Good g))) eqn:Hloc1,
               (Config.loc (conf2 (Good g))) eqn:Hloc2,
               (Info.target (Config.info (conf1 (Good g)))) eqn:Htgt1,
               (Info.target (Config.info (conf2 (Good g)))) eqn:Htgt2;
        try easy.
      + destruct (Graph.Veq_dec l1 l), (Graph.Veq_dec l2 l0); simpl in *; try easy.
        now destruct n; rewrite <- H, v, H0.
        now destruct n; rewrite H, H0, <- v.
        destruct (Rdec dist 0), (Rdec dist0 0).
        * apply Hrconf.
        * now rewrite Hstep in e.
        * now rewrite Hstep in n1.
        * destruct (Rdec dist 1), (Rdec dist0 1).
          -- now f_equiv; simpl; try apply Hconf.
          -- now rewrite Hstep in e.
          -- now rewrite Hstep in n3.
          -- destruct (Info.source (Config.info (conf1 (Good g)))) eqn:Hsrc1,
                      (Info.source (Config.info (conf2 (Good g)))) eqn:Hsrc2,
                      Hrconf as (Hloc, (Hsrc, Htgt));
             rewrite Htgt1, Htgt2 in Htgt;
             rewrite Hloc1, Hloc2 in Hloc; rewrite Hsrc1, Hsrc2 in Hsrc;
             unfold loc_eq in *; try (now exfalso).
             ++ repeat try (split; simpl); try apply Hconf.
                assert (Hcp := Graph.find_edge_compat l l0 Hloc l1 l2 Htgt).
                now destruct (Graph.find_edge l l1), (Graph.find_edge l0 l2).
                now rewrite Hstep.
             ++ repeat try (split; simpl); try apply Hconf.
                assert (Hcp := Graph.find_edge_compat l l0 Hloc l1 l2 Htgt).
                now destruct (Graph.find_edge l l1), (Graph.find_edge l0 l2).
                now rewrite Hstep.
      + destruct H as (He, Hp).
        assert (Hsrc_comp := Graph.src_compat e e0 He).
        destruct (Graph.Veq_dec (Graph.src e) l),
        (Graph.Veq_dec (Graph.src e0) l0); simpl in *; try easy.
        now destruct n; rewrite <- Hsrc_comp, v, H0.
        now destruct n; rewrite Hsrc_comp, H0, <- v.
        destruct (Rdec dist 0), (Rdec dist0 0).
        * apply Hrconf.
        * now rewrite Hstep in e1.
        * now rewrite Hstep in n1.
        * destruct (Rdec dist 1), (Rdec dist0 1).
          -- now f_equiv; simpl; try apply Hconf.
          -- now rewrite Hstep in e1.
          -- now rewrite Hstep in n3.
          -- destruct (Info.source (Config.info
                                        (conf1 (Good g))))
                      eqn : Hsrc1,
                            (Info.source (Config.info
                                              (conf2 (Good g))))
                              eqn : Hsrc2;
               destruct Hrconf as (Hloc, (Hsrc, Htgt)); rewrite Htgt1, Htgt2 in Htgt;
                 rewrite Hloc1, Hloc2 in Hloc; rewrite Hsrc1, Hsrc2 in Hsrc;
                   unfold loc_eq in *;
                   try (now exfalso).
             ++ repeat try (split; simpl); try apply Hconf.
                assert (Hcp := Graph.find_edge_compat l l0 Hloc
                                                      (Graph.src e)
                                                      (Graph.src e0) Hsrc_comp).
                now destruct (Graph.find_edge l (Graph.src e)),
                (Graph.find_edge l0 (Graph.src e0)).
                now rewrite Hstep.
             ++ repeat try (split; simpl); try apply Hconf.
                 assert (Hcp := Graph.find_edge_compat l l0 Hloc
                                                      (Graph.src e)
                                                      (Graph.src e0) Hsrc_comp).
                now destruct (Graph.find_edge l (Graph.src e)),
                (Graph.find_edge l0 (Graph.src e0)).
                now rewrite Hstep.
      + rewrite Hstep. 
        destruct Hrconf as (Hloc, (Hsrc, Htgt)).
        rewrite Hloc1, Hloc2 in Hloc.
        unfold loc_eq in Hloc.
        destruct Hloc as (He, Hp).
        rewrite Hp.
        destruct (Rle_dec 1 (project_p p0 + dist0)); 
          repeat try (split;simpl); try apply Hconf.
        * now apply Graph.tgt_compat.
        * destruct (Rdec dist0 0); unfold loc_eq; now split.
      + rewrite Hstep. 
        destruct Hrconf as (Hloc, (Hsrc, Htgt)).
        rewrite Hloc1, Hloc2 in Hloc.
        unfold loc_eq in Hloc.
        destruct Hloc as (He, Hp).
        rewrite Hp.
        destruct (Rle_dec 1 (project_p p0 + dist0)); 
          repeat try (split;simpl); try apply Hconf.
        * now apply Graph.tgt_compat.
        * destruct (Rdec dist0 0); unfold loc_eq; now split.
    - destruct (Config.loc (conf1 (Byz b)))
               eqn : HconfB1,
                     (Config.loc (conf2 (Byz b)))
                       eqn : HconfB2;
        try apply Hconf.
    - destruct (r1
                  (Spect.from_config
                     (Config.map (apply_sim sim) conf1))
                  (Config.loc (Config.map (apply_sim sim) conf1 (Good g))))
               eqn : Hr1.
      destruct (r2
                  (Spect.from_config
                     (Config.map (apply_sim sim0) conf2))
                  (Config.loc (Config.map (apply_sim sim0) conf2 (Good g))))
               eqn : Hr2.
      simpl.
      destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l))
                                 (Config.loc (conf1 (Good g)))),
      (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim0) l0))
                        (Config.loc (conf2 (Good g))));
      try (repeat (split); try apply Hrconf);
        destruct Hrconf as (Hloc, (Hsrc, Htgt)).
      destruct n.
      rewrite <- Hloc.
      rewrite <- e.
      assert (Location.eq
                (r1
                   (Spect.from_config
                      (Config.map (apply_sim sim) conf1))
                   (Config.loc (Config.map (apply_sim sim) conf1 (Good g))))
                (r2
                   (Spect.from_config
                      (Config.map (apply_sim sim0) conf2))
                   (Config.loc (Config.map (apply_sim sim0) conf2 (Good g))))).
      apply Hr.
      f_equiv.
      rewrite Hconf.
      rewrite Hstep.
      reflexivity.
      apply apply_sim_compat.
      apply Hstep.
      apply Hconf.
      unfold Config.map, apply_sim in *.
      rewrite Hr1, Hr2 in H.
      simpl in *.
      rewrite H.
      f_equiv.
      symmetry.
      apply Hstep.
      destruct n.
      rewrite <- Hloc.
      rewrite <- e.
      assert (Location.eq
                (r1
                   (Spect.from_config
                      (Config.map (apply_sim sim) conf1))
                   (Config.loc (Config.map (apply_sim sim) conf1 (Good g))))
                (r2
                   (Spect.from_config
                      (Config.map (apply_sim sim0) conf2))
                   (Config.loc (Config.map (apply_sim sim0) conf2 (Good g))))).
      apply Hr.
      f_equiv.
      rewrite Hconf.
      rewrite Hstep.
      reflexivity.
      apply apply_sim_compat.
      apply Hstep.
      apply Hconf.
      rewrite Hr1, Hr2 in H.
      simpl in *.
      rewrite H.
      f_equiv.
      symmetry.
      apply Hstep.
      destruct n.
      rewrite Hloc.
      rewrite <- e.
      assert (Location.eq
                (r1
                   (Spect.from_config
                      (Config.map (apply_sim sim) conf1))
                   (Config.loc (Config.map (apply_sim sim) conf1 (Good g))))
                (r2
                   (Spect.from_config
                      (Config.map (apply_sim sim0) conf2))
                   (Config.loc (Config.map (apply_sim sim0) conf2 (Good g))))).
      apply Hr.
      f_equiv.
      rewrite Hconf.
      rewrite Hstep.
      reflexivity.
      apply apply_sim_compat.
      apply Hstep.
      apply Hconf.
      rewrite Hr1, Hr2 in H.
      simpl in *.
      rewrite H.
      f_equiv.
      apply Hstep.
           destruct n.
      rewrite Hloc.
      rewrite <- e.
      assert (Location.eq
                (r1
                   (Spect.from_config
                      (Config.map (apply_sim sim) conf1))
                   (Config.loc (Config.map (apply_sim sim) conf1 (Good g))))
                (r2
                   (Spect.from_config
                      (Config.map (apply_sim sim0) conf2))
                   (Config.loc (Config.map (apply_sim sim0) conf2 (Good g))))).
      apply Hr.
      f_equiv.
      rewrite Hconf.
      rewrite Hstep.
      reflexivity.
      apply apply_sim_compat.
      apply Hstep.
      apply Hconf.
      rewrite Hr1, Hr2 in H.
      simpl in *.
      rewrite H.
      f_equiv.
      apply Hstep.
      simpl.
      f_equiv.
      apply Hstep.
      assert (Hspect :
                Spect.eq (Spect.from_config (Config.map (apply_sim sim) conf1))
                         (Spect.from_config (Config.map (apply_sim sim0) conf2))).
      { f_equiv.
        f_equiv.
        apply apply_sim_compat.
        apply Hstep.
        apply Hconf. }
      specialize (Hr (Spect.from_config (Config.map (apply_sim sim) conf1))
                     (Spect.from_config (Config.map (apply_sim sim0) conf2))
                     Hspect).
      assert (Hrloc : Location.eq
                        (Config.loc (Config.map (apply_sim sim) conf1 (Good g))) 
                        (Config.loc (Config.map (apply_sim sim0) conf2 (Good g))))
        by (apply apply_sim_compat; try apply Hstep; try apply Hconf). 
      specialize (Hr (Config.loc (Config.map (apply_sim sim) conf1 (Good g))) 
                     (Config.loc (Config.map (apply_sim sim0) conf2 (Good g)))
                     Hrloc).
      rewrite Hr1, Hr2 in Hr.
      now unfold Location.eq, loc_eq in Hr.
      assert (Hspect :
                Spect.eq (Spect.from_config (Config.map (apply_sim sim) conf1))
                         (Spect.from_config (Config.map (apply_sim sim0) conf2))).
      { f_equiv.
        f_equiv.
        apply apply_sim_compat.
        apply Hstep.
        apply Hconf. }
      specialize (Hr (Spect.from_config (Config.map (apply_sim sim) conf1))
                     (Spect.from_config (Config.map (apply_sim sim0) conf2))
                     Hspect).
      assert (Hrloc : Location.eq
                        (Config.loc (Config.map (apply_sim sim) conf1 (Good g))) 
                        (Config.loc (Config.map (apply_sim sim0) conf2 (Good g))))
        by (apply apply_sim_compat; try apply Hstep; try apply Hconf). 
      specialize (Hr (Config.loc (Config.map (apply_sim sim) conf1 (Good g))) 
                     (Config.loc (Config.map (apply_sim sim0) conf2 (Good g)))
                     Hrloc).
      rewrite Hr1, Hr2 in Hr.
      now unfold Location.eq, loc_eq in Hr.
      destruct (Config.loc (Config.map (apply_sim sim) conf1 (Good g))) eqn : Hlr.
      generalize (pgm_range
                    r1 (Spect.from_config
                          (Config.map (apply_sim sim) conf1))
                    (Config.loc (Config.map (apply_sim sim) conf1 (Good g))) l).
      intros Hrange.
      destruct Hrange as (lr, (_, (Hl, _))).
      now rewrite Hlr.
      rewrite <- Hlr, Hl in Hr1.
      discriminate.
      assert (He1' : Aom_eq (step da1 (Good g) (conf1 (Good g))) (Active sim))
        by now rewrite He1.
      assert (Hfalse := step_delta da1 g (conf1 (Good g)) sim He1').
      destruct Hfalse as ((fl,Hfl),_).
      unfold Config.map, apply_sim in Hlr; simpl in Hlr.
      destruct ( Config.loc (conf1 (Good g))); try discriminate.
      now unfold Location.eq, loc_eq in *.
    - repeat split;simpl; try (now apply (relocate_byz_compat)); try apply Hconf.
  Qed.
  
  
  Definition execute (r : robogram): demon -> Config.t -> execution :=
    cofix execute d conf :=
      Stream.cons conf (execute (Stream.tl d) (round r (Stream.hd d) conf)).
  
  (** Decomposition lemma for [execute]. *)
  Lemma execute_tail : forall (r : robogram) (d : demon) (conf : Config.t),
      Stream.tl (execute r d conf) = execute r (Stream.tl d) (round r (Stream.hd d) conf).
  Proof. intros. destruct d. reflexivity. Qed.
  
  Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
  Proof.
    intros r1 r2 Hr.
    cofix proof. constructor. simpl. assumption.
    apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
  Qed.


  Inductive LocallyFairForOne id (d : demon) : Prop :=
  | ImmediatelyFair : forall config, is_Active (step (Stream.hd d) id (config id)) = true -> 
                                     LocallyFairForOne id d
  | LaterFair : forall config, is_Active (step (Stream.hd d) id (config id)) = false ->
                               LocallyFairForOne id (Stream.tl d) -> LocallyFairForOne id d.

  CoInductive Fair (d : demon) : Prop :=
    AlwaysFair : (forall g, LocallyFairForOne g d) -> Fair (Stream.tl d) ->
                 Fair d.

  (** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
  Inductive Between g h (d : demon) : nat -> Prop :=
  | kReset : forall k conf, is_Active (step (Stream.hd d) g (conf g)) = true -> Between g h d k
  | kReduce : forall k conf, is_Active (step (Stream.hd d) g (conf g)) = false ->
                             is_Active (step (Stream.hd d) h (conf g)) = true ->
                             Between g h (Stream.tl d) k -> Between g h d (S k)
  | kStall : forall k conf, is_Active (step (Stream.hd d) g (conf g)) = false ->
                            is_Active (step (Stream.hd d) h (conf g)) = false ->
                            Between g h (Stream.tl d) k -> Between g h d k.

  (* k-fair: every robot g is activated within at most k activation of any other robot h *)
  (*
  CoInductive kFair k (d : demon) : Prop :=
    AlwayskFair : (forall g h, Between g h d k) -> kFair k (Stream.tl d) ->
                  kFair k d.

  Lemma LocallyFairForOne_compat_aux : forall g d1 d2, deq d1 d2 -> 
                                                       LocallyFairForOne g d1 -> LocallyFairForOne g d2.
  Proof.
    intros g d1 d2 Hd Hfair. revert d2 Hd. induction Hfair; intros d2 Hd.
    + assert (Heq : is_Active (step (Stream.hd d2) g (config g)) = true) by now rewrite <- Hd, H.
      destruct (step (Stream.hd d2) g) eqn:?; simpl in Heq.
    - easy.
    - constructor 1 with config.
      unfold is_Active.
      rewrite Heqa; auto.
      + assert (Heq : is_Active (step (Stream.hd d2) g (config g)) = false) by now rewrite <- Hd, H.
        destruct (step (Stream.hd d2) g) eqn:?; simpl in Heq.
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
    + assert (Heqa : is_Active (step (Stream.hd d2) g (conf g)) = true) by now rewrite <- Heq, H.
      destruct (step (Stream.hd d2) g (conf g)) eqn:?; simpl in Heqa.
    - easy.
    - constructor 1 with conf. unfold is_Active. rewrite Heqa0; auto.
      + assert (Heqa : is_Active (step (Stream.hd d2) h (conf g)) = true) by now rewrite <- Heq, H0.
        destruct (step (Stream.hd d2) h (conf g)) eqn:?; simpl in Heq.
    - easy.
    - constructor 2 with conf.
      * unfold is_Active in *.
        destruct (step (Stream.hd d2) g (conf g)) eqn:?,
                 (step (Stream.hd d) g (conf g)) eqn:?; intuition.
        rewrite <- da_eq_step_Moving with (da1 := (Stream.hd d2)) in *. 
        rewrite Heqa1 in Heqa2. discriminate.
        symmetry.
        apply Heq.
      * rewrite Heqa0; assumption.
      * apply IHbet; now f_equiv.
      + constructor 3 with conf.
    - unfold is_Active in *.
      destruct (step (Stream.hd d2) g (conf g)) eqn:?, (step (Stream.hd d) g (conf g)) eqn:?; intuition.
      rewrite <- da_eq_step_Moving with (da1 := (Stream.hd d2)) in *.
      rewrite Heqa in Heqa0; discriminate.
      symmetry; apply Heq.
    - unfold is_Active in *.
      destruct (step (Stream.hd d2) h (conf g)) eqn:?, (step (Stream.hd d) h (conf g)) eqn:?; intuition.
      rewrite <- da_eq_step_Moving with (da1 := (Stream.hd d2)) in *.
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

  (*
(** A demon is fully synchronous for one particular good robot g at the first
    step. *)
Inductive FullySynchronousForOne g d:Prop :=
  ImmediatelyFair2: forall conf,
    (step (Stream.hd d) g (conf g)) = Moving 1 \/
    is_Active (step (Stream.hd d) g (conf g)) = true -> 
                      FullySynchronousForOne g d.

(** A demon is fully synchronous if it is fully synchronous for all good robots
    at all step. *)
CoInductive FullySynchronous d :=
  NextfullySynch:
    ((forall g, FullySynchronousForOne g d)
     /\ forall g conf aom, (step (Stream.hd d) g (conf g)) = aom)
    -> FullySynchronous (Stream.tl d) 
    -> FullySynchronous d.


(** A locally synchronous demon is fair *)
 Lemma local_fully_synchronous_implies_fair:
  forall g d, FullySynchronousForOne g d -> LocallyFairForOne g d.
 Proof.
   induction 1.
   destruct H.
   constructor 2 with conf.
   rewrite H.
   now unfold is_Active.
   constructor 1 with conf.
   (* normalement si on a [Moving 1], alors a la prochaine étape, 
on aura forcement un [step] qui donnera un [Active].*).
   now (constructor 1 with conf).
Qed.

(** A synchronous demon is fair *)
Lemma fully_synchronous_implies_fair: forall d, FullySynchronous d -> Fair d.
Proof.
  coinduction fully_fair.
  - intro.
    destruct X.
    destruct (f g).
    constructor 1.
    apply local_fully_synchronous_implies_fair. apply X.
  - now inversion X.
Qed.

   *) *)

  
  (** * recursive property *)

  (** ** starting point 

  we define an initial configuration where all robot are on nodes,
  and their informations [source] and [target] are on the same node. *) 
  Definition Conf_init (conf: Config.t) : Prop := forall id, exists l l' e,
        Graph.find_edge l l' = Some e /\
        Config.eq_RobotConf (conf id)
                            {| Config.loc := Loc l;
                               Config.info := {| Info.source := Loc l; Info.target := Loc l'|} |}.


  Lemma round_flow : forall rbg da g conf e p,
      loc_eq (Config.loc ((round rbg da conf) (Good g))) (Mvt e p) -> 
      (exists l, loc_eq (Config.loc (conf (Good g))) (Loc l)) \/
      (exists p', (project_p p' <= project_p p)%R /\
                  loc_eq (Config.loc (conf (Good g))) (Mvt e p')).
  Proof.
    intros rbg da g conf e p Hl.
    unfold round in *.
    destruct (step da (Good g) (conf (Good g))) eqn : Hstep.
    simpl in *.
    destruct (Config.loc (conf (Good g))).
    left; (now exists l).
    destruct (Rle_dec 1 (project_p p0 + dist)); simpl in *; try now exfalso.
    destruct (Rdec dist 0). right. exists p0. unfold loc_eq in Hl; destruct Hl.
    repeat split. now rewrite H0. auto. right. exists p0.
    unfold loc_eq in *. destruct Hl.
    repeat split.
    assert (Hstep' : Aom_eq (step da (Good g) (conf (Good g))) (Moving dist))
      by now rewrite Hstep.
    rewrite <- H0, <- inv_pro;
      assert (Hf:=step_flexibility da (Good g) (conf (Good g)) dist Hstep').
    lra.
    assert (Hp := project_p_image p0). lra. auto.
    destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                  (Config.loc (Config.map (apply_sim sim) conf (Good g))))
    eqn : Hrbg.
    destruct (Location.eq_dec (Loc ((Iso.sim_V (sim ⁻¹)) l))
                (Config.loc (conf (Good g)))).
    simpl in *. right. exists p. now split.
    simpl in *. right. exists p. now split.
    destruct (Location.eq_dec (Loc (Graph.src e0)) (Config.loc (conf (Good g)))).
    simpl in *. right. exists p. now split.
    simpl in *. right. exists p. now split.
  Qed.
  
  (** ** if [source] and [target] are on some node, they're still on nodes after a [round] *)

  (** defintion of probleme *)
  Definition ri_loc_def (conf: Config.t) : Prop := forall g,
      exists v1 v2,
        loc_eq (Info.source (Config.info (conf (Good g)))) (Loc v1) /\
        loc_eq (Info.target (Config.info (conf (Good g)))) (Loc v2).


  (** it's true starting from the initial configuration *)
  Lemma ri_loc_init : forall conf da rbg,
      Conf_init conf ->
      ri_loc_def (round rbg da conf).
  Proof.
    intros conf da rbg Hinit g.
    unfold Conf_init in Hinit.
    specialize (Hinit (Good g)).
    destruct Hinit as (l, (l', (e, (Hli, (Hl, (Hsi, Hti)))))); simpl in *.
    unfold round.
    destruct (step da (Good g) (conf (Good g)))
             eqn: Hstep,
                  (Config.loc (conf (Good g)))
                    eqn : Hloc,
                          (Info.target (Config.info (conf (Good g))))
                            eqn : Htgt;
      try (destruct (Graph.Veq_dec l1 l0));
      try now simpl in *.
    + exists l, l'; now rewrite Htgt; split.
    + destruct (Rdec dist 0). exists l, l'; now rewrite Htgt; split.
      destruct (Rdec dist 1). simpl in *. exists l, l'; now rewrite Htgt; split.
      unfold loc_eq in Hti, Hli.
      exists l, l1.
      split; simpl.
      assumption.
      now rewrite Htgt.
    + simpl.
      rewrite Hloc in *.
      destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Loc ((Iso.sim_V sim) l0))) eqn : Hr.
      destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l2)) (Loc l0)).
      exists l, l'.
      now rewrite Htgt; split.
      simpl.
      exists l0, (Bijection.retraction (Iso.sim_V sim) l2).
      now split.
      generalize (pgm_range rbg (Spect.from_config
                                   (Config.map (apply_sim sim) conf))
                            (Loc ((Iso.sim_V sim) l0))
                             ((Iso.sim_V sim) l0) (reflexivity _)).
      intros Hrange.
      destruct Hrange as (lr, (er, (Hlr, Her))).
      simpl in *.
      rewrite Hr in Hlr.
      discriminate.
    + simpl.
      rewrite Hloc in *.
      destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Loc ((Iso.sim_V sim) l0))) eqn : Hr.
      destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l2)) (Loc l0)).
      exists l, l'.
      now rewrite Htgt; split.
      simpl.
      exists l0, (Bijection.retraction (Iso.sim_V sim) l2).
      now split.
      generalize (pgm_range rbg (Spect.from_config
                                   (Config.map (apply_sim sim) conf))
                            (Loc ((Iso.sim_V sim) l0))
                             ((Iso.sim_V sim) l0) (reflexivity _)).
      intros Hrange.
      destruct Hrange as (lr, (er, (Hlr, Her))).
      rewrite Hr in Hlr.
      discriminate.
  Qed.


  (** recurrence's hypothesis*)
  Lemma ri_loc_always : forall conf da rbg,
      ri_loc_def conf ->
      ri_loc_def (round rbg da conf).
  Proof.
    intros conf da rbg Hs' g.
    unfold ri_loc_def in *.
    destruct (Hs' g) as (v1, (v2, (Hs, Hg))).
    unfold round.
    simpl in *.
    destruct (step da (Good g) (conf (Good g)))
             eqn : Hstep,
                   (Config.loc (conf (Good g)))
                     eqn : Hloc,
                           (Info.target (Config.info (conf (Good g))))
                             eqn : Htgt;
      try easy;
      try (destruct (Graph.Veq_dec l0 l)).
    exists v1, v2; now rewrite Htgt; split.
    destruct (Rdec dist 0). exists v1, v2. now rewrite Htgt; split.
    destruct (Rdec dist 1). simpl. exists v1, v2; now rewrite Htgt; split.
    exists v1, v2. simpl. now rewrite Htgt; split.
    destruct (Rle_dec 1 (project_p p + dist)); 
      try (simpl; exists v1, v2; now rewrite Htgt; split).
    destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Loc ((Iso.sim_V sim) l))).
    destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l1)) (Loc l)).
    exists v1, v2; now rewrite Htgt; split.
    simpl. exists l, (Bijection.retraction (Iso.sim_V sim) l1); now split.
    destruct (Location.eq_dec (Loc (Graph.src e)) (Loc l)).
    exists v1, v2; now rewrite Htgt; split.
    simpl in *. exists l, (Graph.src e); now split.
    destruct (rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Loc ((Iso.sim_V sim) l))).
    destruct (Location.eq_dec (Loc (Bijection.retraction (Iso.sim_V sim) l1)) (Loc l)).
    exists v1, v2; now rewrite Htgt; split.
    simpl. exists l, (Bijection.retraction (Iso.sim_V sim) l1); now split.
    destruct (Location.eq_dec (Loc (Graph.src e)) (Loc l)).
    exists v1, v2; now rewrite Htgt; split.
    simpl in *. exists l, (Graph.src e); now split.
    assert (Hstep' : Aom_eq (step da (Good g) (conf (Good g))) (Active sim))
      by now rewrite Hstep.
    assert (Hfalse := step_delta da g (conf (Good g)) sim Hstep').
    destruct Hfalse as ((l',Hfalse), _). rewrite Hloc in Hfalse. now exfalso.
  Qed.


  CoInductive ri : execution -> Prop :=
    PropCons : forall e, ri_loc_def (Stream.hd e) -> ri (Stream.tl e) -> ri e.

  Lemma ri_round : forall r da config, ri_loc_def config -> ri_loc_def (round r da config).
  Proof.
    intros r da config Hinit g.
    destruct (Hinit g) as (v1, (v2, (Hs, Ht))).
    assert (Hfin := @ri_loc_always config da r).
    now apply Hfin.
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
    - if a robot is on an edge, it's the edge between its [source] and [target].
    - there is a edge between [source] and [target]. *)
  Definition group_good_def (conf: Config.t) : Prop := forall g,(
        ri_loc_def conf /\
        (forall v0, loc_eq (Config.loc (conf (Good g))) (Loc v0) -> 
                    loc_eq (Info.source (Config.info (conf (Good g)))) (Loc v0) \/
                    loc_eq (Info.target (Config.info (conf (Good g)))) (Loc v0)) /\
        (forall v1 v2 e p,
            loc_eq (Info.source (Config.info (conf (Good g)))) (Loc v1) ->
            loc_eq (Info.target (Config.info (conf (Good g)))) (Loc v2) ->
            loc_eq (Config.loc (conf (Good g))) (Mvt e p) ->
            opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e)) /\
        (forall v1 v2,
            loc_eq (Info.source (Config.info (conf (Good g)))) (Loc v1) ->
            loc_eq (Info.target (Config.info (conf (Good g)))) (Loc v2) ->
            exists e, (opt_eq Graph.Eeq (Graph.find_edge v1 v2) (Some e)))

       (* 


changer le cas 2 en (loc conf) = mvt e p -> (src conf) = Loc (src e) /\ (tgt conf) = Loc (tgt e))





/\
         loc = tgt ->
step = move ->
loc round = mvt e ->
find_edge loc tgt = e
        forall conf', (forall r da,
             Config.eq conf (round r da conf')) -> 
            (forall da, exists dist,
                step da (Good g) (conf' (Good g)) = Moving dist /\
            dist <> 0%R /\ dist <> 1%R)
            ->
            (exists l, Location.eq (Config.loc (conf' (Good g))) (Loc l))
            ->
            Location.eq (Info.source (Config.info (conf' (Good g))))
                        (Info.target (Config.info (conf' (Good g))))
            ->
            (exists e ll lt,
                Location.eq (Config.loc (conf' (Good g))) (Loc ll)
                /\
                Location.eq (Info.target (Config.info
                                              (conf' (Good g)))) (Loc lt)
                /\
                opt_eq Graph.Eeq
                       (Graph.find_edge ll lt)
                       (Some e))
            -> Location.eq (Config.loc (conf' (Good g)))
                           (Info.source (Config.info (conf' (Good g))))*)).


  Axiom AutoLoop : forall l, exists e, (Graph.find_edge l l) = Some e.
  
  (** initialisation *)
  Lemma group_lem_init : forall conf (rbg : robogram) da,
      Conf_init conf -> (group_good_def (round rbg da conf)).
  Proof.
    intros conf rbg da (*v0' v1' v2' e' p'*) Hinit g.
    split.
    - now apply ri_loc_init.
    - unfold Conf_init in Hinit.
      specialize (Hinit (Good g)).
      destruct Hinit as (l, (l', (e, (Hli, (Hl, (Hsi, Hti)))))); simpl in *.
      split;
        destruct (step da (Good g) (conf (Good g)))
                 eqn: Hstep,
                      (Config.loc (conf (Good g)))
                        eqn : Hloc,
                              (Info.target (Config.info (conf (Good g))))
                                eqn : Htgt;
        try now unfold round in *; simpl in *.
      intro v0.
      intros Hl0.
      unfold round in *.
      + rewrite <- Hl in *.
        simpl in *.
        rewrite Hstep, Hloc, Htgt in *.
        destruct (Graph.Veq_dec l1 l0).
        rewrite Hloc in Hl0. rewrite <- Hl0.
        now left.
        destruct (Rdec dist 0). rewrite Hloc in Hl0. rewrite <- Hl0. now left.
        destruct (Rdec dist 1).
        simpl in *.
        now rewrite Htgt; right.
        destruct (Info.target (Config.info (conf (Good g)))) eqn : Ht;
          try now simpl in *.
      + unfold round.
        rewrite Hstep in *.
        simpl in *. left.
        rewrite Hloc in *.
        destruct (Location.eq_dec
               (Loc
                  match
                    rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Loc ((Iso.sim_V sim) l0))
                  with
                  | Loc l => Bijection.retraction (Iso.sim_V sim) l
                  | Mvt e _ => Graph.src e
                  end) (Loc l0)).
        rewrite Hsi, Hloc, <- H in *.
        simpl.
        now symmetry.
        now simpl in *.
      + split.
        * unfold round in *.
          rewrite Hstep, Hloc, Htgt in *.
          intros v1 v2 e0 p Hs' Ht' Hl'.
          destruct (Graph.Veq_dec l1 l0). now rewrite Hloc in Hl'.
          destruct (Rdec dist 0). rewrite Hloc in Hl'; now simpl in *.
          destruct (Rdec dist 1). now simpl in *.
          unfold loc_eq in Hti, Hl.
          simpl in *.
          assert (opt_eq Graph.Eeq (Graph.find_edge l0 l1) (Graph.find_edge l l'))
            by now apply Graph.find_edge_compat.
          rewrite Hli in H.
          destruct (Graph.find_edge l0 l1); try contradiction.
          destruct Hl' as (He,_).
          simpl in *.
          rewrite He in H.
          rewrite Htgt, Hsi in *.
          simpl in *.
          assert (opt_eq Graph.Eeq (Some e) (Some e0)) by now simpl in *.
          rewrite <- H0, <- Hli.
          apply Graph.find_edge_compat; try now symmetry. now rewrite <- Ht'.
        * unfold round in *; rewrite Hstep, Hloc, Htgt in *.
          intros v1 v2 Hv1 Hv2.
          destruct (Graph.Veq_dec l1 l0).
          rewrite Htgt, Hv1, Hv2 in *.
          unfold loc_eq in Hsi, Hti.
          exists e.
          rewrite <- Hli.
          now apply Graph.find_edge_compat.
          destruct (Rdec dist 0).
          rewrite Htgt, Hv1, Hv2 in *.
          unfold loc_eq in Hsi, Hti.
          exists e.
          rewrite <- Hli.
          now apply Graph.find_edge_compat.
          destruct (Rdec dist 1). simpl in *.
          rewrite Htgt, Hv1 in *.
          simpl in *.
          rewrite Hv2 in *.
          exists e.
          rewrite <- Hli.
          now apply Graph.find_edge_compat.
          simpl in *.
          rewrite Htgt, Hv1 in *.
          simpl in *;
            rewrite Hv2 in *.
          unfold loc_eq in Hsi, Hti.
          exists e.
          rewrite <- Hli.
          now apply Graph.find_edge_compat.
      + unfold round.
        rewrite Hstep.
        simpl.
        rewrite Hloc.
        destruct (Location.eq_dec
                (Loc
                   match
                     rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                       (Loc ((Iso.sim_V sim) l0))
                   with
                   | Loc l1 => Bijection.retraction (Iso.sim_V sim) l1
                   | Mvt e1 _ => Graph.src e1
                   end) (Loc l0)).
        split; try now simpl in *.
        intros.
        now rewrite Hloc in *.
        intros v1 v2 Hv1 Hv2.
        rewrite Htgt, Hsi, Hti in *.
        simpl in *.
        exists e.
        rewrite <- Hli.
        now apply Graph.find_edge_compat.
        split.
        now intros.
        intros v1 v2 Hv1 Hv2.
        assert (Hrange :=
                  pgm_range rbg (Spect.from_config
                                   (Config.map (apply_sim sim) conf))
                            (Config.loc
                               (Config.map (apply_sim sim) conf (Good g)))
                            ((Iso.sim_V sim) l0)).
        destruct Hrange as (lrange, (erange, (Hlrange, Herange)));
        simpl in *;
        try (now rewrite Hloc).
        simpl in *.
        rewrite Hloc in *.
        rewrite Hlrange in Hv2.
        exists (Bijection.retraction (Iso.sim_E sim) erange).
        assert (HSome_sim : opt_eq Graph.Eeq
          (Graph.find_edge (Graph.src ((Bijection.retraction (Iso.sim_E sim)) erange))
                           (Graph.tgt ((Bijection.retraction (Iso.sim_E sim)) erange)))
          (Some ((Bijection.retraction (Iso.sim_E sim)) erange)))
          by (apply Graph.find_edge_Some).
        rewrite <- HSome_sim.
        apply Graph.find_edge_compat;
        assert (Hmorph := Iso.sim_morphism sim (((Bijection.retraction (Iso.sim_E sim)) erange)));
        destruct Hmorph as (Hms, Hmt);
          rewrite Bijection.Inversion in *;
          rewrite Bijection.section_retraction in *; try apply Graph.Eeq_equiv;
        try (apply Graph.find2st in Herange;
             destruct Herange as (HSs, HSt);
             try (rewrite <- HSs in Hms;
                  rewrite <- Hms;
                  rewrite Bijection.retraction_section;
                  try (now symmetry);
                  try apply Graph.Veq_equiv);
             try (rewrite <- HSt in Hmt; now rewrite <- Hmt)).
  Qed.

  (** recurence *)
  Lemma group_lem : forall conf (rbg : robogram) da,
      ri_loc_def conf ->
      group_good_def conf->
      ri_loc_def (round rbg da conf) /\
      group_good_def (round rbg da conf).
  Proof.
    intros conf rbg da Hinit.
    unfold group_good_def; intros Hgroup; 
      repeat split; try (now apply ri_round);
        destruct (Hgroup g) as (_, (Hli, (Hmi, Hex_e))).
    + intros v0' H. unfold round in *.
      destruct (Hinit g) as (_, (lt' ,(_,Ht')));
      destruct (step da (Good g) (conf (Good g)))
               eqn: Hstep,
                    (Config.loc (conf (Good g)))
                      eqn : Hl,
                            (Info.target (Config.info (conf (Good g))))
                              eqn : Htgt;
      try easy.
    - destruct (Graph.Veq_dec l0 l).
      specialize (Hli v0'). rewrite Htgt in *. apply Hli. now rewrite Hl in H.
      destruct (Rdec dist 0). 
      specialize (Hli v0'). rewrite Htgt in *. apply Hli. now rewrite Hl in H.
      destruct (Rdec dist 1).
      simpl in *. now rewrite Htgt in *; right.
      now simpl in *.
    - destruct (Rle_dec 1 (project_p p + dist)); simpl in *.
      * destruct (Hinit g) as (v1, (v2, Hri)). specialize (Hmi v1 v2 e p).
        apply Graph.find2st in Hmi.
        assert (Hproof : Graph.Veq (Graph.tgt e) v2).
        now destruct Hmi.
        right. destruct Hri as (Hsri, Htri).
        rewrite Htri. simpl in *. now rewrite <- Hproof.
        apply Hri.
        rewrite Htgt in *; apply Hri.
        now split.
      * destruct (Rdec dist 0); now simpl in .
    - destruct (Location.eq_dec
                  (Loc
                     match
                       rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                           (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                     with
                     | Loc l0 => (Iso.sim_V (sim ⁻¹)) l0
                     | Mvt e _ => Graph.src e
                     end) (Loc l)). simpl in *.
      specialize (Hgroup g).
      destruct Hgroup as (_, (Hl_ri,_)).
      now apply (Hl_ri v0').
      now left.
    - destruct (Location.eq_dec
               (Loc
                  match
                    rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                  with
                  | Loc l => (Iso.sim_V (sim ⁻¹)) l
                  | Mvt e0 _ => Graph.src e0
                  end) (Mvt e p)); now simpl in *.
    + intros v1' v2' e' p' Hs0 Ht0 Hl0. unfold round in *.
      destruct (Hinit g) as (_, (lt' ,(_,Ht')));
      destruct (step da (Good g) (conf (Good g)))
               eqn: Hstep,
                    (Config.loc (conf (Good g)))
                      eqn : Hl,
                            (Info.target (Config.info (conf (Good g))))
                              eqn : Htgt;
      try easy.
    - destruct (Graph.Veq_dec l0 l). now rewrite Hl in Hl0.
      destruct (Rdec dist 0). now rewrite Hl in Hl0.
      destruct (Rdec dist 1). now simpl in *.
      simpl in *.
      rewrite Htgt in *.            
      simpl in *.
      destruct (Graph.find_edge l l0) eqn : Hedge; simpl in *.
      specialize (Hli l (reflexivity _)).
      destruct Hli.
      destruct Hl0 as (He, Hp).
      assert (Hedge' : opt_eq Graph.Eeq (Graph.find_edge l l0) (Some e'))
        by now (rewrite Hedge; apply He).
      clear Hgroup Hmi.
      rewrite Ht0 in *.
      rewrite H in Hs0.
      now simpl in Hs0; rewrite Hs0 in Hedge'.
      easy.
      simpl in*.
      specialize (Hex_e v1' l0 Hs0 (reflexivity l0)).
      destruct Hex_e.
      destruct (Hli l (reflexivity _));
        try rewrite Hs0 in *.
      simpl in *.
      rewrite H0 in *.
      now rewrite Hedge in H.
      easy.
    - destruct (Rle_dec 1 (project_p p + dist));try now simpl in *.
      simpl in *.
      destruct (Rdec dist 0); simpl in *;
        specialize (Hmi v1' v2' e' p);
        rewrite Htgt in *;
        apply Hmi; try easy.
    - destruct (Location.eq_dec
                  (Loc
                     match
                       rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                           (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                     with
                     | Loc l => (Iso.sim_V (sim ⁻¹)) l
                     | Mvt e _ => Graph.src e
                     end) (Loc l));
        try (rewrite Hl in Hl0;
             now simpl in * ).
      now simpl in *.
    - destruct (Location.eq_dec
                  (Loc
                     match
                       rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                           (Config.loc (Config.map (apply_sim sim) conf (Good g)))
                     with
                     | Loc l => (Iso.sim_V (sim ⁻¹)) l
                     | Mvt e _ => Graph.src e
                     end) (Mvt e p));
        try (rewrite Hl in Hl0;
             now simpl in * ).
      now simpl in *.
      + intros v1' v2'.
        unfold round; simpl in *.
        destruct (Hinit g) as (_, (lt', (_, Ht')));
        destruct (step da (Good g) (conf (Good g)))
          as [dist | sim]
               eqn : Hstep,
                     (Config.loc (conf (Good g)))
            as [l| e p] eqn : Hloc,
               (Info.target (Config.info (conf (Good g))))
                 as [lt | ? ?] eqn : Htgt;
        try easy
        ; simpl in *.
    - specialize (Hex_e v1' v2').
      destruct (Graph.Veq_dec lt l);
      destruct (Rdec dist 0);
      destruct (Rdec dist 1); simpl in *;
        try rewrite Htgt; 
        try apply Hex_e.
    - specialize (Hex_e v1' v2').
      destruct (Rle_dec 1 (project_p p + dist)); simpl in *;
        rewrite Htgt; apply Hex_e.
    - destruct ( Location.eq_dec
               (Loc
                  match
                    rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Loc ((Iso.sim_V sim) l))
                  with
                  | Loc l0 => Bijection.retraction (Iso.sim_V sim) l0
                  | Mvt e _ => Graph.src e
                  end) (Loc l)).
      destruct (Hgroup g) as (_, (_, (_, Hsome))).
      apply Hsome.
      simpl.
      assert (Hstep' : Aom_eq (step da (Good g) (conf (Good g))) (Active sim))
        by (now rewrite Hstep);
        assert (Hdelta := step_delta da g (conf (Good g)) sim Hstep').
      destruct Hdelta as (Hl_delta, Ht_delta).
      intros Hl Hr.
      rewrite Hloc in Ht_delta.
      destruct (Config.loc (Config.map (apply_sim sim) conf (Good g))) eqn : Hsim_loc.
      assert (Hrange := pgm_range rbg (Spect.from_config (Config.map (apply_sim sim) conf)) (Config.loc (Config.map (apply_sim sim) conf (Good g))) l0).
      destruct Hrange as (l_rbg, (e_rbg, (Hr_loc, Hedge))).
      now rewrite Hsim_loc.
      simpl in *; rewrite Hloc in *.
      rewrite Hsim_loc in *.
      rewrite Hr_loc in Hr.
      exists ((Bijection.retraction (Iso.sim_E sim)) e_rbg).
      assert (Hsim_E := Graph.find_edge_Some ((Bijection.retraction (Iso.sim_E sim)) e_rbg)).
      rewrite <- Hsim_E.
      generalize (Iso.sim_morphism (Iso.inverse sim) e_rbg).
      intros (s,t).
      clear Hmi.
      apply Graph.find_edge_compat.
      simpl in *.
      rewrite <- s.
      assert (Hedge' : opt_eq Graph.Eeq ( Graph.find_edge
                                            l0 l_rbg)
                              (Some e_rbg)) by now rewrite Hedge.
      apply Graph.find2st in Hedge'.
      destruct Hedge' as (s',t').
      rewrite <- s'.
      unfold Config.map, apply_sim, projectS, projectS_loc in *.
      simpl in *.
      assert (Location.eq (Loc ((Iso.sim_V sim) l)) (Loc l0)) by now rewrite Hsim_loc.
      unfold Location.eq, loc_eq in H.
      rewrite <- H.
      rewrite (Bijection.retraction_section).
      now symmetry.
      apply LocationA.eq_equiv.
      rewrite <- Hr.
      simpl in *.
      apply Graph.find2st in Hedge.
      destruct Hedge as (s',t').
      rewrite t'.
      now simpl.
      destruct n.
      simpl in *.
      rewrite Hloc in *.
      now simpl in *.
    - destruct (Location.eq_dec
               (Loc
                  match
                    rbg (Spect.from_config (Config.map (apply_sim sim) conf))
                      (Mvt ((Iso.sim_E sim) e)
                         (project_p_inv ((Iso.sim_T sim) (project_p p))))
                  with
                  | Loc l => Bijection.retraction (Iso.sim_V sim) l
                  | Mvt e0 _ => Graph.src e0
                  end) (Mvt e p)); try now simpl in *.
  Qed.


  (** finals proofs*)
  CoInductive group : execution -> Prop :=
    GroupCons : forall e, group_good_def (Stream.hd e) -> group (Stream.tl e) -> group e.

  Lemma group_round : forall r da config, group_good_def config -> group_good_def (round r da config).
  Proof.
    intros r da config Hinit g.
    apply group_lem.
    now destruct (Hinit g).
    assumption.
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
                                                  group (execute r d (round r (Stream.hd d) config)).
  Proof.
    intros.
    apply group_always.
    now apply group_lem_init. 
  Qed.

End CGF.
