(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, R. Pelle, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import RelationPairs.
Require Import Reals.
Require Import Psatz.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.ContinuousDVGraphFormalism.
Require Import Pactole.DiscreteGraphFormalism.
Require Import Pactole.CommonIsoGraphFormalism.


(* FIXME: The info for robots is currently hard-coded to be (source, target) *)
Module GraphEquivalence (Graph : GraphDef)
                        (N : Size)
                        (Names : Robots(N))
                        (LocationA : LocationADef(Graph))
                        (MkInfoA : InfoSig(Graph)(LocationA))
                        (ConfigA : Configuration (LocationA)(N)(Names)(MkInfoA.Info))
                        (Import Iso : Iso(Graph)(LocationA)).

  Module MapWL := MMapWeakList.Make.
  
  Module Mraw := MMultisetWMap.FMultisets MapWL LocationA.
  Module M := MMultisetExtraOps.Make LocationA Mraw.
  

Module DGF := DGF (Graph)(N)(Names)(LocationA)(MkInfoA)(ConfigA)(Iso)(MapWL)(Mraw)(M).
Module CGF := CGF (Graph)(N)(Names)(LocationA)(MkInfoA)(ConfigA)(Iso)(MapWL)(Mraw)(M).


(** Conversion from Discrete to Continuous settings. *)
Definition RobotConfD2C (robotconfD : DGF.Config.RobotConf) : CGF.Config.RobotConf :=
    {| CGF.Config.loc := CGF.Loc (DGF.Config.loc robotconfD);
       CGF.Config.info := 
      {| CGF.Info.source := CGF.Loc (DGF.Info.source (DGF.Config.info robotconfD));
         CGF.Info.target := CGF.Loc (DGF.Info.target (DGF.Config.info robotconfD)) |} |}.

Definition ConfigD2C (confA : DGF.Config.t) : CGF.Config.t := fun id => RobotConfD2C (confA id).

Instance RobotConfD2C_compat : Proper (DGF.Config.eq_RobotConf ==> CGF.Config.eq_RobotConf) RobotConfD2C.
Proof. intros [? []] [? []] [? []]. simpl in *. now repeat (split; simpl). Qed.

Instance ConfigD2C_compat : Proper (DGF.Config.eq ==> CGF.Config.eq) ConfigD2C.
Proof. intros ca1 ca2 Hca id. apply RobotConfD2C_compat, Hca. Qed.


(** Conversion from Continuous to Discrete settings. *)
Definition LocC2D (locD : CGF.Location.t) : DGF.Location.t :=
      match locD with
        | CGF.Loc l => l
        | CGF.Mvt e p => if Rle_dec (CGF.project_p p) (Graph.threshold e) then Graph.src e else Graph.tgt e
      end.

Definition RobotConfC2D (robotconfC : CGF.Config.RobotConf) : DGF.Config.RobotConf :=
  {| DGF.Config.loc := LocC2D (CGF.Config.loc robotconfC);
     DGF.Config.info := 
       {| DGF.Info.source := LocC2D (CGF.Info.source (CGF.Config.info robotconfC));
          DGF.Info.target := LocC2D (CGF.Info.target (CGF.Config.info robotconfC)) |} |}.

Definition ConfigC2D (ConfD : CGF.Config.t) : DGF.Config.t := fun id => RobotConfC2D (ConfD id).

Instance LocC2D_compat : Proper (CGF.Location.eq ==> DGF.Location.eq) LocC2D.
Proof.
intros ld1 ld2 Hld. unfold LocC2D, DGF.Location.eq, CGF.Location.eq, CGF.loc_eq in *.
destruct ld1, ld2; auto; try (now exfalso).
destruct Hld, (Rle_dec (CGF.project_p p) (Graph.threshold e)),
              (Rle_dec (CGF.project_p p0) (Graph.threshold e0)).
apply Graph.src_compat; assumption. rewrite H0, H in r; contradiction.
rewrite <- H0, <- H in r; contradiction. apply Graph.tgt_compat; assumption.
Qed.

Instance RobotConfC2D_compat : Proper (CGF.Config.eq_RobotConf ==> DGF.Config.eq_RobotConf) RobotConfC2D.
Proof. intros [? []] [? []] [? []]. simpl in *. now repeat split; simpl; apply LocC2D_compat. Qed.

Instance ConfigC2D_compat : Proper (CGF.Config.eq ==> DGF.Config.eq) ConfigC2D.
Proof. intros ? ? Hcd id. specialize (Hcd id). unfold ConfigC2D. now rewrite Hcd. Qed.

Lemma DGF_CGF_DGF_Config : forall confA: DGF.Config.t,  DGF.Config.eq confA
                                                                     (ConfigC2D (ConfigD2C confA)).
Proof.
intros confA id. unfold ConfigC2D, ConfigD2C. now repeat try (split; simpl).
Qed.

Lemma Mraw_equiv : DGF.Spect.t = CGF.Spect.t.
Proof. now unfold DGF.Spect.t, CGF.Spect.t. Qed.

(*
Lemma CGFS_DGF_CGFS_Config : forall SconfD : CGF.Config.t, 
      CGF.Spect.eq (CGF.Spect.from_config SconfD) 
      (CGF.Spect.from_config (ConfigD2C (ConfigC2D SconfD))).
Proof.
intros SconfD. unfold ConfigD2C, ConfigC2D. 
assert CGF.Config.eq (Sconf *)


Definition rbgD2C (rbgA : DGF.robogram) : CGF.robogram.
  refine {| CGF.pgm := fun s loc => CGF.Loc ((DGF.pgm rbgA) s (LocC2D loc)) |}.
Proof.
  - intros SD1 SD2 HSD loc1 loc2 Hloc.
    unfold CGF.Location.eq, CGF.loc_eq, CGF.Spect.eq, LocC2D in *.
    destruct loc1, loc2; try (now exfalso).
    apply (DGF.pgm_compat rbgA). now unfold DGF.Spect.eq. assumption.
    apply (DGF.pgm_compat rbgA). now unfold DGF.Spect.eq.
    destruct Hloc as (He, Hp).
    assert (Ht := Graph.threshold_compat e e0 He).
    rewrite Ht, Hp.
    destruct (Rle_dec (CGF.project_p p0) (Graph.threshold e0));
      try apply Graph.src_compat;
      try apply Graph.tgt_compat;
      apply He.
  - intros s loc loc' Hl.
    assert (Hpgm := DGF.pgm_range rbgA s (LocC2D loc)).
    destruct Hpgm as (l', (e,(Heq, Hedge)));
    exists l', e; split; try assumption.
    unfold LocC2D, CGF.loc_eq in *.
    destruct loc; try (now exfalso).
    now rewrite Heq.
    unfold LocC2D, CGF.loc_eq in *.
    destruct loc; try (now exfalso).
    rewrite <- Hedge.
    now apply Graph.find_edge_compat.
Defined.

Instance rbgD2C_compat : Proper (DGF.req ==> CGF.req) rbgD2C.
Proof.
intros ra1 ra2 Hra. unfold rbgD2C, CGF.req. intros sd1 sd2 Hsd l1 l2 Hl. simpl.
fold DGF.Location.eq. apply Hra. now unfold CGF.Spect.eq, DGF.Spect.eq in *.
now apply LocC2D_compat.
Qed.

Definition rbgC2D (rbgD : CGF.robogram) : DGF.robogram.
refine {| DGF.pgm := fun s loc => LocC2D ((CGF.pgm rbgD) s (CGF.Loc loc)) |}.
Proof.
+ intros SA1 SA2 HSA loc1 loc2 Hloc. unfold DGF.Location.eq, DGF.Spect.eq in *.
  apply LocC2D_compat. apply (CGF.pgm_compat rbgD). now unfold CGF.Spect.eq.
  apply Hloc.
+ intros s l.
  assert (Hrange := CGF.pgm_range rbgD s (CGF.Loc l) l).
  unfold LocC2D.
  destruct Hrange as (l', (e, (Heq,Hedge)));
  try reflexivity;
  rewrite Heq;
  exists l', e.
  split; try left; now simpl.
Defined.

Instance rbgC2D_compat : Proper (CGF.req ==> DGF.req) rbgC2D.
Proof.
intros rd1 rd2 Hrd sa1 sa2 Hsa loc1 loc2 Hloc. unfold rbgC2D, DGF.req. simpl.
apply LocC2D_compat. apply Hrd. now unfold CGF.Spect.eq, DGF.Spect.eq in *.
apply Hloc.
Qed.

Lemma RA_RD_RA_equiv : forall ra, DGF.req ra (rbgC2D (rbgD2C ra)).
Proof.
intros ra. unfold rbgD2C, rbgC2D, DGF.req. simpl.
apply (DGF.pgm_compat ra).
Qed.


Definition rcC2D  (rcD : CGF.Config.RobotConf) : DGF.Config.RobotConf :=
  {| DGF.Config.loc := LocC2D (CGF.Config.loc rcD);
     DGF.Config.info := {| DGF.Info.source := LocC2D (CGF.Info.source (CGF.Config.info rcD));
                           DGF.Info.target := LocC2D (CGF.Info.target (CGF.Config.info rcD)) |} |}.

Instance rcC2D_compat : Proper (CGF.Config.eq_RobotConf ==> DGF.Config.eq_RobotConf) rcC2D.
Proof.
intros rcD1 rcD2 HrcD. unfold rcC2D. repeat try (split;simpl); f_equiv; apply HrcD.
Qed.

Definition rcD2C (rcA : DGF.Config.RobotConf) : CGF.Config.RobotConf :=
{| CGF.Config.loc := CGF.Loc (DGF.Config.loc rcA);
        CGF.Config.info := 
          {| CGF.Info.source := CGF.Loc (DGF.Info.source (DGF.Config.info rcA));
             CGF.Info.target := CGF.Loc (DGF.Info.target (DGF.Config.info rcA)) |} |}.

Instance rcD2C_compat : Proper (DGF.Config.eq_RobotConf ==> CGF.Config.eq_RobotConf) rcD2C.
Proof.
intros rcA1 rcA2 HrcA. unfold rcD2C. repeat try (split;simpl); apply HrcA.
Qed.

Definition daC2D_step daD cD id rcA :=
  if DGF.Config.eq_RobotConf_dec rcA (rcC2D (cD id))
  then match (CGF.step daD) id (cD id) with
         | CGF.Active sim => DGF.Active sim
         | CGF.Moving dist => 
             match (CGF.Config.loc (cD id)) with
               | CGF.Loc _ =>
                   match (Graph.find_edge (DGF.Info.source (DGF.Config.info rcA))
                                          (DGF.Info.target (DGF.Config.info rcA))) with
                     | Some e =>
                         if Rle_dec (dist) (Graph.threshold e) then DGF.Moving false else DGF.Moving true
                     | None => DGF.Moving false
                   end
               | CGF.Mvt e p => if Rle_dec (CGF.project_p p) (Graph.threshold e) then 
                                if Rle_dec (dist + (CGF.project_p p)) (Graph.threshold e) 
                                then DGF.Moving false else DGF.Moving true
                                else DGF.Moving false
             end
       end
  else DGF.Moving false.

Lemma daC2D_step_delta : forall daD cD g Rconfig sim,
  DGF.Aom_eq (daC2D_step daD cD (Good g) Rconfig) (DGF.Active sim) ->
  DGF.Location.eq Rconfig (DGF.Info.target (DGF.Config.info Rconfig)).
Proof.
intros daD cD g rcA sim HrcD. unfold DGF.Aom_eq, daC2D_step in *.
    destruct (DGF.Config.eq_RobotConf_dec rcA (rcC2D (cD (Good g))));
      try easy.
    destruct e as (Hl, (Hs, Ht)).
    (*   assert (Hax1 := CGF.ri_Loc (cD (Good g))).
  destruct Hax1 as (lax1, (lax2, ((Hax_src, Hax_tgt), (eD, HeD)))). *)
    destruct (CGF.step daD (Good g) (cD (Good g)))
             eqn : HstepD, 
                   (Graph.find_edge (DGF.Info.source (DGF.Config.info rcA))
                                    (DGF.Info.target (DGF.Config.info rcA)))
                     eqn : Hedge,
                           (CGF.Config.loc (cD (Good g))) eqn : HlD.
    destruct (Rle_dec (dist) (Graph.threshold e)) eqn : Hthresh; now exfalso.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0)).
    destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e0)); now exfalso.
    now exfalso. now exfalso.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)).
    destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); now exfalso.
    now exfalso.
    unfold rcD2C in *; simpl in *.
    assert (HstepD' : CGF.Aom_eq
                        (CGF.step daD (Good g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    apply CGF.step_delta in HstepD'.
    assert (Heq : exists l, Graph.Veq (DGF.Config.loc rcA) l).
    now (exists (DGF.Config.loc rcA)).
    unfold CGF.Location.eq, DGF.Location.eq, CGF.loc_eq in *.
    unfold LocC2D in *.
    destruct HstepD' as (Hstl, Hstst).
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.info (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.info (cD (Good g))))
                             eqn : HtgtD;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption;
      try (now destruct HstepD').
    unfold rcC2D, LocC2D. simpl in *. 
    unfold LocC2D in *.
    assert (HstepD' : CGF.Aom_eq
                        (CGF.step daD (Good g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    assert (Hdelta := CGF.step_delta daD g (cD (Good g)) sim0 HstepD').
    destruct Hdelta as (Hld, Htd).
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.info (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.info (cD (Good g))))
                             eqn : HtgtD;
      simpl in *;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption; try now destruct Hld.
    assert (HstepD' : CGF.Aom_eq
                        (CGF.step daD (Good g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    apply (CGF.step_delta daD) in HstepD'.
    destruct HstepD'.
    unfold rcC2D, LocC2D in *; simpl in *.
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.info (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.info (cD (Good g))))
                             eqn : HtgtD;
      simpl in *;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption.
    assert (HstepD' : CGF.Aom_eq
                        (CGF.step daD (Good g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    apply (CGF.step_delta daD) in HstepD'.
    destruct HstepD'.
    unfold rcC2D, LocC2D in *; simpl in *.
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.info (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.info (cD (Good g))))
                             eqn : HtgtD;
      simpl in *;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption;
      now destruct H.
Qed.

Lemma daC2D_step_compat daD cD : Proper (eq ==> DGF.Config.eq_RobotConf ==> DGF.Aom_eq) (daC2D_step daD cD).
Proof.
intros id1 id2 Hid rcA1 rcA2 HrcA. unfold DGF.Aom_eq, daC2D_step.
    assert (Graph.Veq (DGF.Info.source (DGF.Config.info rcA1))
                      (DGF.Info.source (DGF.Config.info rcA2))) by apply HrcA.
    assert (Graph.Veq (DGF.Info.target (DGF.Config.info rcA1))
                      (DGF.Info.target (DGF.Config.info rcA2))) by apply HrcA.
    assert (Hedge_co := Graph.find_edge_compat
                          (DGF.Info.source (DGF.Config.info rcA1)) 
                          (DGF.Info.source (DGF.Config.info rcA2)) H 
                          (DGF.Info.target (DGF.Config.info rcA1))
                          (DGF.Info.target (DGF.Config.info rcA2)) H0).
    assert (HrcD : CGF.Config.eq_RobotConf (cD id1) (cD id2)) by now rewrite Hid.
    assert (HrcD' := HrcD).
    destruct HrcD' as (HDl, (HDs, HDt)). unfold CGF.loc_eq in *.
    destruct (CGF.step daD id1 (cD id1))
             eqn : Hstep1,
                   (CGF.step daD id2 (cD id2))
                     eqn : Hstep2,
                           (CGF.Config.loc (cD id1))
                             eqn : HlD1,
                                   (CGF.Config.loc (cD id2))
                                     eqn : HlD2;
      destruct
        (DGF.Config.eq_RobotConf_dec rcA1 (rcC2D (cD id1)))
        eqn : Heq1,
              (DGF.Config.eq_RobotConf_dec rcA2 (rcC2D (cD id2)))
                eqn : Heq2,
                      (Graph.find_edge
                         (DGF.Info.source (DGF.Config.info rcA1))
                         (DGF.Info.target (DGF.Config.info rcA1)))
                        eqn : Hedge1,
                              (Graph.find_edge
                                 (DGF.Info.source (DGF.Config.info rcA2))
                                 (DGF.Info.target (DGF.Config.info rcA2)))
                                eqn : Hedge2;
      simpl in *;
      try rewrite Hstep1; simpl in *;
        try (assert (Hst := CGF.step_compat);
             specialize (Hst daD id1 id2 Hid rcD rcD (reflexivity rcD));
             rewrite Hstep1, Hstep2 in Hst; now unfold CGF.Aom_eq in Hst);
        try (now exfalso);
        assert (Hst := CGF.step_compat);
        specialize (Hst daD id1 id2 Hid (cD id1) (cD id2) HrcD);
        rewrite Hstep1, Hstep2 in Hst; unfold CGF.Aom_eq in Hst;
          assert (Hfind := Graph.find_edge_compat
                             (DGF.Info.source (DGF.Config.info rcA1))
                             (DGF.Info.source (DGF.Config.info rcA2)) H
                             (DGF.Info.target (DGF.Config.info rcA1))
                             (DGF.Info.target (DGF.Config.info rcA2)) H0);
          rewrite Hedge1, Hedge2 in Hfind; try discriminate;
            try assert (HEeq : Graph.Eeq e1 e2) by (apply Hfind);
            try (assert (Graph.threshold e1 = Graph.threshold e2)
                  by now apply Graph.threshold_compat, HEeq);
            try (rewrite HrcD; intuition);
            try (rewrite <- HrcD; intuition); intuition.
    rewrite H1, Hst.
    destruct (Rle_dec dist0 (Graph.threshold e2)) eqn : Hdist; auto.
    assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
    assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
    rewrite Hst.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)).
    destruct (Rle_dec (dist0 + CGF.project_p p)); auto.
    rewrite <- H2.
    assert (Graph.threshold e = Graph.threshold e0)
      by (now apply Graph.threshold_compat).
    rewrite <- H3.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)).
    destruct (Rle_dec (dist0 + CGF.project_p p)); auto.
    auto.
    rewrite <- H2.
    assert (Graph.threshold e = Graph.threshold e0)
      by (now apply Graph.threshold_compat).
    rewrite <- H3.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)).
    destruct (Rle_dec (dist0 + CGF.project_p p)); auto. contradiction. contradiction.
    rewrite <- H2.
    assert (Graph.threshold e = Graph.threshold e0)
      by (now apply Graph.threshold_compat).
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0)).
    rewrite <- H3, Hst in *. 
    destruct (Rle_dec (dist0 + CGF.project_p p) (Graph.threshold e)); auto. auto.
    rewrite <- H2. assert (Graph.threshold e = Graph.threshold e0)
      by (now apply Graph.threshold_compat).
    rewrite <- H3, Hst in *.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)). 
    destruct (Rle_dec (dist0 + CGF.project_p p) (Graph.threshold e)); auto. auto.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)); 
      try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
      assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)); 
      try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
      assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)); 
      try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
      assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
    destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)); 
      try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
      assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
    assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
    assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
    assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
    assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
    assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
    assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
    assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
    assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
Qed.

Definition daC2D (daD : CGF.demonic_action) (cD : CGF.Config.t): DGF.demonic_action.
refine {| DGF.relocate_byz := fun b => RobotConfC2D (CGF.relocate_byz daD b);
          DGF.step := daC2D_step daD cD |}.
Proof.
+ apply daC2D_step_delta.
+ apply daC2D_step_compat.
Defined.

Instance daC2D_compat : Proper (CGF.da_eq ==> CGF.Config.eq ==> DGF.da_eq) daC2D.
Proof.
intros dad1 dad2 HdaD cD1 cD2 HrcD'.
unfold daC2D, daC2D_step, DGF.da_eq in *;
simpl.
split.
intros id confA.  assert (HrcD := HrcD' id).
assert (HrcC2D_eq : DGF.Config.eq_RobotConf (rcC2D (cD1 id)) (rcC2D (cD2 id))).
apply rcC2D_compat, HrcD.
assert (Hda_cD := CGF.step_da_compat HdaD (reflexivity id) HrcD).
unfold CGF.Aom_eq in Hda_cD.
destruct HdaD as (HdaD_G, _).
specialize (HdaD_G id (rcD2C confA)).
destruct (DGF.Config.eq_RobotConf_dec confA (rcC2D (cD1 id))) eqn : HrcD1,
         (DGF.Config.eq_RobotConf_dec confA (rcC2D (cD2 id))) eqn : HrcD2;
destruct (CGF.step dad1 id (cD1 id)),
         (CGF.step dad2 id (cD2 id));
destruct (CGF.Config.loc (cD1 id)) eqn : Hc1, (CGF.Config.loc (cD2 id)) eqn : Hc2;
destruct (Graph.find_edge (DGF.Info.source (DGF.Config.info confA))
      (DGF.Info.target (DGF.Config.info confA))); try rewrite Hda_cD;
unfold CGF.loc_eq in *;
try (destruct HrcD as (Hl,_); now rewrite Hc1, Hc2 in Hl).
destruct (Rle_dec dist0 (Graph.threshold e1)); now unfold DGF.Aom_eq.
destruct HrcD as (Hl,_); rewrite Hc1, Hc2 in Hl;
destruct Hl as (He, Hp).
assert (Hth : (Graph.threshold e1) = (Graph.threshold e2)) by apply Graph.threshold_compat, He.
rewrite Hth, Hp.
destruct (Rle_dec (CGF.project_p p0) (Graph.threshold e2)); try (
destruct (Rle_dec (dist0 + CGF.project_p p0) (Graph.threshold e2)); now unfold DGF.Aom_eq).
destruct HrcD as (Hl,_); rewrite Hc1, Hc2 in Hl;
destruct Hl as (He, Hp).
assert (Hth : (Graph.threshold e1) = (Graph.threshold e2)) by apply Graph.threshold_compat, He.
rewrite Hth, Hp.
destruct (Rle_dec (CGF.project_p p0) (Graph.threshold e2)); try (
destruct (Rle_dec (dist0 + CGF.project_p p0) (Graph.threshold e2)); now unfold DGF.Aom_eq).
assert (e' := e); rewrite HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcC2D_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcC2D_eq in e'; contradiction.
destruct HdaD as (_,Hb). intros b. apply RobotConfC2D_compat, Hb.
Qed.


Definition daD2C_step daA cA id rcD :=
  if CGF.Config.eq_RobotConf_dec rcD (rcD2C (cA id))
  then match ((DGF.step daA) id (cA id)) with
         | DGF.Active sim =>  (* if CGF.Location.eq_dec (CGF.Config.loc rcD)
                                 (CGF.Info.target (CGF.Config.info rcD))
                                then *) CGF.Active sim
                                (* else CGF.Moving 1%R *)
         | DGF.Moving b => if b then CGF.Moving 1%R else CGF.Moving 0%R
       end
  else CGF.Moving 0%R.

Lemma daD2C_step_delta : forall daA cA g Rconfig sim,
  CGF.Aom_eq (daD2C_step daA cA (Good g) Rconfig) (CGF.Active sim) ->
  (∃ l : Graph.V, CGF.Location.eq Rconfig (CGF.Loc l))
  ∧ CGF.Location.eq Rconfig (CGF.Info.target (CGF.Config.info Rconfig)).
Proof.
intros daA cA g rcD sim HrcA. unfold daD2C_step in *.
destruct (DGF.step daA (Good g) (cA (Good g))) eqn : HstepA,
(CGF.Config.eq_RobotConf_dec rcD (rcD2C (cA (Good g)))) eqn : HrcD; unfold rcC2D, LocC2D in *; simpl in *.
 - assert (e' := e); destruct e' as (Hl, (Hs, Ht)); unfold CGF.loc_eq in *; simpl in *.
   destruct (CGF.Config.loc rcD), ( CGF.Info.source (CGF.Config.info rcD)),
            (CGF.Info.target (CGF.Config.info rcD)); try (now exfalso).
   destruct dist; now exfalso.
 - now exfalso.
 - assert (e' := e); destruct e' as (Hl, (Hs, Ht)); unfold CGF.loc_eq in *; simpl in *.
   destruct (CGF.Config.loc rcD), ( CGF.Info.source (CGF.Config.info rcD)),
            ( CGF.Info.target (CGF.Config.info rcD)); try (now exfalso).
   assert (HstepA' : DGF.Aom_eq
                       (DGF.step daA (Good g) (cA (Good g))) (DGF.Active sim0))
          by now rewrite HstepA.
   apply (DGF.step_delta daA) in HstepA'.
   unfold CGF.Location.eq, CGF.loc_eq, DGF.Location.eq, rcC2D in *; simpl in *.
   split ; try (exists l1); now rewrite Ht, Hl.
 - now exfalso.
Qed.

Lemma daD2C_step_compat daA cA : Proper (eq ==> CGF.Config.eq_RobotConf ==> CGF.Aom_eq) (daD2C_step daA cA).
Proof.
intros id1 id2 Hid rcD1 rcD2 HrcD. unfold daD2C_step, CGF.Aom_eq.
assert (HcA : DGF.Config.eq_RobotConf (cA id1) (cA id2)) by now rewrite Hid.
assert(Hs1_eq := DGF.step_compat daA id1 id2 Hid (cA id1) (cA id2) (HcA)).
destruct (DGF.step daA id1 (cA id1)) eqn:Hstep1,
         (DGF.step daA id2 (cA id2)) eqn:Hstep2,
         (CGF.Config.eq_RobotConf_dec rcD1 (rcD2C (cA id1))),
         (CGF.Config.eq_RobotConf_dec rcD2 (rcD2C (cA id2))); auto.
  destruct dist, dist0; auto. unfold DGF.Aom_eq in *. discriminate.
  unfold DGF.Aom_eq in *. discriminate.
  rewrite e in HrcD. rewrite HcA in HrcD. symmetry in HrcD. contradiction.
  rewrite e in HrcD. rewrite <- HcA in HrcD. contradiction.
  destruct dist; now unfold DGF.Aom_eq in *.
  destruct dist; now unfold DGF.Aom_eq.
  destruct dist; now unfold DGF.Aom_eq.
  destruct dist; now unfold DGF.Aom_eq.
  rewrite e in HrcD. rewrite HcA in HrcD. symmetry in HrcD. contradiction.
  rewrite e in HrcD. rewrite <- HcA in HrcD. contradiction.
Qed.

Lemma daD2C_step_flexibility : forall daA cA id config r,
  CGF.Aom_eq (daD2C_step daA cA id config) (CGF.Moving r) -> (0 <= r <= 1)%R.
Proof.
+ intros daA cA id confD r. unfold daD2C_step.
  destruct (DGF.step daA id (cA id));
  destruct (CGF.Config.eq_RobotConf_dec confD (rcD2C (cA id))).
  destruct dist; intros Hm. assert (Heqm : CGF.Aom_eq (CGF.Moving 1) (CGF.Moving r)).
  now rewrite Hm. unfold CGF.Aom_eq in *. rewrite <- Heqm. lra.
  assert (Heqm : CGF.Aom_eq (CGF.Moving 0) (CGF.Moving r)).
  now rewrite Hm. unfold CGF.Aom_eq in *. rewrite <- Heqm. lra.
  destruct dist; intros Hm. assert (Heqm : CGF.Aom_eq (CGF.Moving 0) (CGF.Moving r)).
  now rewrite Hm. unfold CGF.Aom_eq in *. rewrite <- Heqm. lra.
  assert (Heqm : CGF.Aom_eq (CGF.Moving 0) (CGF.Moving r)).
  now rewrite Hm. unfold CGF.Aom_eq in *. rewrite <- Heqm. lra.
  destruct (CGF.Location.eq_dec (CGF.Config.loc confD)
                                (CGF.Info.target (CGF.Config.info confD)));
  intros Hm; now simpl in *. 
  intros Hm; assert (Heqm : CGF.Aom_eq (CGF.Moving 0) (CGF.Moving r)).
  now rewrite Hm. unfold CGF.Aom_eq in *. rewrite <- Heqm. lra.
Qed.

(* TODO : trouver une définition vrai, ou rajouter des axioms car la sinon c'est pas vrai.*)
Definition daD2C (daA : DGF.demonic_action) (cA : DGF.Config.t) : CGF.demonic_action.
refine {| CGF.relocate_byz := fun b => RobotConfD2C (DGF.relocate_byz daA b);
          CGF.step := daD2C_step daA cA |}.
Proof.
+ apply daD2C_step_delta.
+ apply daD2C_step_compat.
+ apply daD2C_step_flexibility.
Defined.

Instance daD2C_compat : Proper (DGF.da_eq ==> DGF.Config.eq ==> CGF.da_eq) daD2C.
Proof.
intros daA1 daA2 HdaA cA1 cA2 HrcA.
unfold daD2C, daD2C_step; split; simpl.
+ intros id rc. destruct HdaA as (HdaA_G,_).
  specialize (HdaA_G id (cA1 id)).
  assert (Hda' : DGF.Aom_eq (DGF.step daA2 id (cA1 id)) (DGF.step daA2 id (cA2 id))).
  apply (DGF.step_compat daA2 id id (reflexivity id) (cA1 id) (cA2 id) (HrcA id) ).
  rewrite Hda' in HdaA_G.
  destruct (CGF.Config.eq_RobotConf_dec rc (rcD2C (cA1 id))) eqn : HrcD1, 
           (CGF.Config.eq_RobotConf_dec rc (rcD2C (cA2 id))) eqn : HrcD2.
  * destruct (DGF.step daA1 id (cA1 id)), (DGF.step daA2 id (cA2 id)); unfold DGF.Aom_eq in *.
    - destruct dist, dist0; now unfold CGF.Aom_eq.
    - now exfalso.
    - now exfalso.
    - destruct (CGF.Location.eq_dec (CGF.Config.loc rc)
                                  (CGF.Info.target (CGF.Config.info rc))).
      now rewrite HdaA_G.
      now unfold DGF.Aom_eq.
  * assert (e' := e). rewrite (HrcA id) in e'. contradiction.
  * assert (e' := e). rewrite <- (HrcA id) in e'. contradiction.
  * now unfold DGF.Aom_eq.
+ destruct HdaA as (_, HdaA_B). intros b; specialize (HdaA_B b).
  auto.
Qed.


Lemma daD2C2D : forall (d: DGF.demonic_action) c,
    CGF.group_good_def (ConfigD2C c) ->
    DGF.da_eq d (daC2D (daD2C d c) (ConfigD2C c)).
Proof.
  intros d c Hc. unfold daC2D. unfold daD2C. simpl. unfold DGF.da_eq.
  split.
  - intros.
    simpl.
    unfold daC2D_step.
    simpl.
    destruct ( DGF.Config.eq_RobotConf_dec config (rcC2D (ConfigD2C c id))).
    + unfold rcC2D, ConfigD2C in e.
      simpl in *.
      unfold daD2C_step, ConfigC2D.
      destruct ( CGF.Config.eq_RobotConf_dec (ConfigD2C c id) (rcD2C (c id))).
      * simpl in *.
        destruct (DGF.step d id (c id)) eqn : Hstep1; try destruct  dist.
        -- unfold DGF.Aom_eq.
           assert (Hstep_compat := DGF.step_compat d _ _ (reflexivity id) _ _ e).
           destruct (c id), info.
           simpl in *.
           rewrite Hstep1 in Hstep_compat.
           destruct ( DGF.step d id config); try easy.
           destruct ( Graph.find_edge (DGF.Info.source (DGF.Config.info config))
                                      (DGF.Info.target (DGF.Config.info config)))
                    eqn : Hedge; try easy.
           unfold DGF.Aom_eq in Hstep_compat.
           destruct (Rle_dec 1 (Graph.threshold e1)).
           generalize (Graph.threshold_pos e1).
           intros.
           lra.
           assumption.
           destruct id.
           destruct (Hc g) as (Hri,(Ha, (Hb, He))). 
           specialize (He source target).
           destruct He; try unfold ConfigD2C, RobotConfD2C; simpl;
           unfold rcD2C, ConfigD2C, RobotConfD2C in e0;
           repeat destruct e0 as (?, e0);
           try easy.
           simpl in *.
           repeat destruct e as (?, e).
           simpl in *.
           assert (Hg := Graph.find_edge_compat _ _ H3 _ _ e).
           now rewrite Hedge, H in Hg.
           admit.
        -- destruct (Graph.find_edge (DGF.Info.source (DGF.Config.info config))
                                     (DGF.Info.target (DGF.Config.info config)))
                    eqn : Hedge;
             assert (Hstep_compat := DGF.step_compat d _ _ (reflexivity id) _ _ e);
             destruct (c id), info;
             simpl in *. 
           ++ destruct (Rle_dec 0 (Graph.threshold e1)).
              simpl in *.
              now rewrite Hstep1 in Hstep_compat.
              generalize (Graph.threshold_pos e1).
              lra.
           ++ now rewrite Hstep1 in *. 
        -- assert (Hstep_compat := DGF.step_compat d _ _ (reflexivity id) _ _ e);
             destruct (c id), info;
             simpl in *.
           now rewrite Hstep1 in *.
      * destruct n; unfold rcD2C, ConfigD2C, RobotConfD2C; now simpl in *. 
    + 
Abort.

CoFixpoint demonC2D (demonC : CGF.demon) (e : CGF.execution) : DGF.demon :=
  Stream.cons (daC2D (Stream.hd demonC) (Stream.hd e))
              ((demonC2D (Stream.tl demonC) (Stream.tl e))).

CoFixpoint demonD2C (demonD : DGF.demon) (e : DGF.execution) : CGF.demon :=
  Stream.cons (daD2C (Stream.hd demonD) (Stream.hd e))
              (demonD2C (Stream.tl demonD) (Stream.tl e)).

(* Instance demonC2D_compat : Proper (CGF.Deq  *)

(*Ensuite, pour montrer l'équivalence, on écrit des fonctions de
traduction entre les modèles Atomic et Discrete pour :
+ configuration (check)
+ robogram (check)
+ demonic_action ( check )
+ demon ( check )
+ round ( TODO )
*)

Theorem graph_equivD2C : forall (c c': DGF.Config.t) (rbg:DGF.robogram) (da:DGF.demonic_action),
DGF.Config.eq c' (DGF.round rbg da c) ->
exists da', CGF.Config.eq (ConfigD2C c') (CGF.round (rbgD2C rbg) da' (ConfigD2C c)).
Proof.

intros c c' rbg da HDGF.
exists (daD2C da c). intros id.
assert ( HeqDd : CGF.Config.eq_RobotConf
             {|
             CGF.Config.loc := CGF.Loc (DGF.Config.loc (c id));
             CGF.Config.info := {|
                                      CGF.Info.source := CGF.Loc
                                                             (DGF.Info.source
                                                                (DGF.Config.info
                                                                   (c id)));
                                      CGF.Info.target := CGF.Loc
                                                             (DGF.Info.target
                                                                (DGF.Config.info
                                                                   (c id))) |} |}
             {|
             CGF.Config.loc := CGF.Loc (DGF.Config.loc (c id));
             CGF.Config.info := {|
                                      CGF.Info.source := CGF.Loc
                                                             (DGF.Info.source
                                                                (DGF.Config.info
                                                                   (c id)));
                                      CGF.Info.target := CGF.Loc
                                                             (DGF.Info.target
                                                                (DGF.Config.info
                                                                   (c id))) |} |});
simpl in *. repeat try split; simpl; reflexivity.
 repeat try (split; simpl);
assert (Heq : DGF.Location.eq (DGF.Config.loc (c' id))
                              (DGF.Config.loc ((DGF.round rbg da c) id))) by apply HDGF;
  unfold DGF.Location.eq in Heq;
  unfold DGF.round, CGF.round in *;
  assert (Heq_rcA: DGF.Config.eq_RobotConf (c id) ({|
             DGF.Config.loc := DGF.Config.loc (c id);
             DGF.Config.info := {|
                                      DGF.Info.source := DGF.Info.source
                                                             (DGF.Config.info (c id));
                                      DGF.Info.target := DGF.Info.target
                                                             (DGF.Config.info (c id)) |} |})) by (
      repeat (try split; simpl) ; reflexivity);
assert (HstepA_compat := DGF.step_compat da id id (reflexivity id)
              (c id)
              ({| DGF.Config.loc := DGF.Config.loc (c id);
                  DGF.Config.info := {|
                     DGF.Info.source := DGF.Info.source (DGF.Config.info (c id));
                     DGF.Info.target := DGF.Info.target (DGF.Config.info (c id)) |} |})
              Heq_rcA);
destruct (DGF.step da id (c id)) eqn : HstepA,
         (CGF.step (daD2C da c) id (ConfigD2C c id)) eqn:HstepD; unfold ConfigD2C in HstepD;
  simpl in *; unfold daD2C_step, RobotConfD2C in HstepD; simpl in *;
         destruct (DGF.step da id
             {|
             DGF.Config.loc := DGF.Config.loc (c id);
             DGF.Config.info := {|
                                      DGF.Info.source := DGF.Info.source
                                                             (DGF.Config.info (c id));
                                      DGF.Info.target := DGF.Info.target
                                                             (DGF.Config.info (c id)) |} |})
      eqn : HstepA',
         (HDGF id) as (HlocA,(HsrcA,HtgtA)); unfold rcD2C in *;
destruct (CGF.Config.eq_RobotConf_dec
             {|
             CGF.Config.loc := CGF.Loc (DGF.Config.loc (c id));
             CGF.Config.info := {|
                                      CGF.Info.source := CGF.Loc
                                                             (DGF.Info.source
                                                                (DGF.Config.info
                                                                   (c id)));
                                      CGF.Info.target := CGF.Loc
                                                             (DGF.Info.target
                                                                (DGF.Config.info
                                                                   (c id))) |} |}
             {|
             CGF.Config.loc := CGF.Loc (DGF.Config.loc (c id));
             CGF.Config.info := {|
                                      CGF.Info.source := CGF.Loc
                                                             (DGF.Info.source
                                                                (DGF.Config.info
                                                                   (c id)));
                                      CGF.Info.target := CGF.Loc
                                                             (DGF.Info.target
                                                                (DGF.Config.info
                                                                   (c id))) |} |});
try contradiction; 
destruct id as [g|b]; try (now exfalso); simpl in *; rewrite HstepA in *; try discriminate.
- destruct ( Graph.Veq_dec (DGF.Info.target (DGF.Config.info (c (Good g))))
           (DGF.Config.loc (c (Good g)))).
   destruct dist; simpl in *; destruct dist1; try auto; try discriminate.
      now rewrite v in *.
      simpl in *.
  destruct (Rdec dist0 0).
    * destruct dist; simpl in *; destruct dist1; try auto; try discriminate.
      rewrite e0 in *.
      unfold daD2C_step in HstepD. simpl in HstepD.
      assert (Hfalse : CGF.Aom_eq (CGF.Moving 1) (CGF.Moving 0)) by now rewrite HstepD.
      unfold CGF.Aom_eq in *. lra.
    * destruct (Rdec dist0 1).
      destruct dist; simpl in *; auto.
      ++ rewrite e0, <- HstepA_compat in *.
         assert (Hfalse : CGF.Aom_eq (CGF.Moving 0) (CGF.Moving 1)).
         rewrite HstepD. reflexivity. unfold CGF.Aom_eq in *. lra.
      ++ destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
         -- assert (Hfalse : CGF.Aom_eq (CGF.Moving 1) (CGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold CGF.Aom_eq in *. lra.
          -- assert (Hfalse : CGF.Aom_eq (CGF.Moving 1) (CGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold CGF.Aom_eq in *. lra.
          -- assert (Hfalse : CGF.Aom_eq (CGF.Moving 0) (CGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold CGF.Aom_eq in *. lra.
          -- assert (Hfalse : CGF.Aom_eq (CGF.Moving 0) (CGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold CGF.Aom_eq in *. lra.
  - destruct dist; simpl in *; assumption.
 - destruct dist; simpl in *; discriminate.
 - destruct dist; simpl in *; discriminate.
 - simpl in *.
   destruct (CGF.Location.eq_dec
          (CGF.Loc
             (Isomorphism.retraction sim0
                (rbg
                   (CGF.Spect.from_config
                      (CGF.Config.map (CGF.apply_sim sim0) (ConfigD2C c)))
                   (sim0 (c (Good g)))))) (CGF.Loc (c (Good g))));
   destruct (DGF.Location.eq_dec
                      (Isomorphism.retraction sim
                         (rbg
                            (DGF.Spect.from_config
                               (DGF.Config.map (DGF.apply_sim sim) c))
                            (sim (c (Good g))))) (c (Good g)));
   simpl in *; try assumption.
 - simpl in *. assumption.
 - destruct (Graph.Veq_dec (DGF.Info.target (DGF.Config.info (c (Good g))))
                           (DGF.Config.loc (c (Good g)))); simpl in *.
   destruct dist; simpl in *; destruct dist1; try auto; try discriminate;
     rewrite v in *; easy.
   destruct (Rdec dist0 0); simpl in *.
    * destruct dist; destruct dist1; try auto.
    * destruct (Rdec dist0 1).
      destruct dist; simpl in *; try auto.
      destruct (Graph.Veq_dec (DGF.Config.loc (c (Good g)))
        (DGF.Info.target (DGF.Config.info (c (Good g))))); simpl in *;
      destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
 - destruct dist; assumption.
 - destruct dist; discriminate.
 - destruct dist; discriminate.
 - destruct (CGF.Location.eq_dec
             (CGF.Loc
                (Isomorphism.retraction sim0
                   (rbg
                      (CGF.Spect.from_config
                         (CGF.Config.map (CGF.apply_sim sim0) (ConfigD2C c)))
                      (sim0 (c (Good g)))))) (CGF.Loc (c (Good g))));
   destruct (DGF.Location.eq_dec
                      (Isomorphism.retraction sim
                         (rbg
                            (DGF.Spect.from_config
                               (DGF.Config.map (DGF.apply_sim sim) c))
                            (sim (c (Good g))))) (c (Good g)));
   simpl in *; try assumption.
   * destruct n.
     rewrite <- e0.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     apply HstepD'.
     apply DGF.pgm_compat .
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     unfold CGF.Aom_eq in *.
     assert (Hcompat := CGF.Spect.from_config_compat
                          (CGF.Config.map (CGF.apply_sim sim0) (ConfigD2C c))
                          (CGF.Config.map (CGF.apply_sim sim) (ConfigD2C c))).
     rewrite Hcompat.
     unfold DGF.Spect.from_config, CGF.Spect.from_config, ConfigD2C, CGF.projectS,
     CGF.projectS_loc, DGF.Config.map, DGF.apply_sim.
     now simpl.
     f_equiv.
     apply CGF.apply_sim_compat.
     now symmetry.
     rewrite <- e0 at 2.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     apply HstepD'.
   * destruct n.
     rewrite <- e0.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     symmetry; apply HstepD'.
     apply DGF.pgm_compat .
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     unfold CGF.Aom_eq in *.
     assert (Hcompat := CGF.Spect.from_config_compat
                          (CGF.Config.map (CGF.apply_sim sim0) (ConfigD2C c))
                          (CGF.Config.map (CGF.apply_sim sim) (ConfigD2C c))).
     rewrite Hcompat.
     unfold DGF.Spect.from_config, CGF.Spect.from_config, ConfigD2C, CGF.projectS,
     CGF.projectS_loc, DGF.Config.map, DGF.apply_sim.
     now simpl.
     f_equiv.
     apply CGF.apply_sim_compat.
     now symmetry.
     rewrite <- e0 at 2.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     symmetry; apply HstepD'.
 - assumption.
 - destruct (Graph.Veq_dec (DGF.Info.target (DGF.Config.info (c (Good g))))
              (DGF.Config.loc (c (Good g))));
     destruct (CGF.Info.target (CGF.Config.info (ConfigD2C c (Good g))))
              eqn : Htgt';
     unfold ConfigD2C in *; simpl in *; try discriminate.
   destruct dist; simpl in *; rewrite HtgtA;
     try (try (assert (CGF.loc_eq
                    (CGF.Loc (DGF.Info.target (DGF.Config.info (c (Good g)))))
                    (CGF.Loc l)) by (now rewrite Htgt')); simpl in *; try (easy)).
   destruct (Rdec dist0 0).
    * simpl in *.
      destruct dist; simpl in *; destruct dist1; auto; try discriminate;
      rewrite HtgtA;
      try (assert (CGF.loc_eq
                (CGF.Loc (DGF.Info.target (DGF.Config.info (c (Good g)))))
                (CGF.Loc l)) by (now rewrite Htgt')); simpl in *; easy.
    * destruct (Rdec dist0 1); simpl in *; simpl in *;
      destruct dist; simpl in *; auto.
 - destruct dist; simpl in *; assumption.
 - destruct dist; simpl in *; discriminate.
 - destruct dist; simpl in *; discriminate.
 -
   destruct (CGF.Location.eq_dec
             (CGF.Loc
                (Isomorphism.retraction sim0
                   (rbg
                      (CGF.Spect.from_config
                         (CGF.Config.map (CGF.apply_sim sim0) (ConfigD2C c)))
                      (sim0 (c (Good g)))))) (CGF.Loc (c (Good g))));
   destruct ( DGF.Location.eq_dec
                       (Isomorphism.retraction sim
                          (rbg
                             (DGF.Spect.from_config
                                (DGF.Config.map (DGF.apply_sim sim) c))
                             (sim (c (Good g))))) (c (Good g)));
   simpl in *; try assumption.
   * destruct n.
     rewrite <- e0.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     apply HstepD'.
     apply DGF.pgm_compat .
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     unfold CGF.Aom_eq in *.
     assert (Hcompat := CGF.Spect.from_config_compat
                          (CGF.Config.map (CGF.apply_sim sim0) (ConfigD2C c))
                          (CGF.Config.map (CGF.apply_sim sim) (ConfigD2C c))).
     rewrite Hcompat.
     unfold DGF.Spect.from_config, CGF.Spect.from_config, ConfigD2C, CGF.projectS,
     CGF.projectS_loc, DGF.Config.map, DGF.apply_sim.
     now simpl.
     f_equiv.
     apply CGF.apply_sim_compat.
     now symmetry.
     rewrite <- e0 at 2.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     apply HstepD'.
   * destruct n.
     rewrite <- e0.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     symmetry; apply HstepD'.
     apply DGF.pgm_compat .
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     unfold CGF.Aom_eq in *.
     assert (Hcompat := CGF.Spect.from_config_compat
                          (CGF.Config.map (CGF.apply_sim sim0) (ConfigD2C c))
                          (CGF.Config.map (CGF.apply_sim sim) (ConfigD2C c))).
     rewrite Hcompat.
     unfold DGF.Spect.from_config, CGF.Spect.from_config, ConfigD2C, CGF.projectS,
     CGF.projectS_loc, DGF.Config.map, DGF.apply_sim.
     now simpl.
     f_equiv.
     apply CGF.apply_sim_compat.
     now symmetry.
     rewrite <- e0 at 2.
     f_equiv.
     assert (HstepD' : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0))
       by now rewrite HstepD.
     symmetry; apply HstepD'.
   * simpl in *. rewrite HtgtA.
     unfold CGF.Spect.from_config, DGF.Spect.from_config.
     unfold CGF.projectS, CGF.projectS_loc.
     simpl.
     unfold DGF.Config.map, DGF.apply_sim.
     assert (HIso_eq : CGF.Aom_eq (CGF.Active sim) (CGF.Active sim0)) by now rewrite HstepD.
     unfold CGF.Aom_eq in HIso_eq.
     f_equiv.
     apply HIso_eq.
     apply DGF.pgm_compat.
     cut (DGF.Config.eq
            (λ id : Names.ident,
                    {|
                      DGF.Config.loc := Isomorphism.section (Iso.sim_V sim)
                                                            (DGF.Config.loc (c id));
                      DGF.Config.info :=
                        {|
                          DGF.Info.source := Isomorphism.section
                                                 (Iso.sim_V sim)
                                                 (DGF.Info.source
                                                    (DGF.Config.info (c id)));
                          DGF.Info.target := Isomorphism.section
                                                 (Iso.sim_V sim)
                                                 (DGF.Info.target
                                                    (DGF.Config.info (c id)))
                        |}
                    |})
            (λ id : Names.ident,
                    {|
                      DGF.Config.loc := Isomorphism.section (Iso.sim_V sim0)
                                                            (DGF.Config.loc (c id));
                      DGF.Config.info :=
                        {|
                          DGF.Info.source := Isomorphism.section
                                                 (Iso.sim_V sim0)
                                                 (DGF.Info.source
                                                    (DGF.Config.info (c id)));
                          DGF.Info.target := Isomorphism.section
                                                 (Iso.sim_V sim0)
                                                 (DGF.Info.target
                                                    (DGF.Config.info (c id)))
                        |}
                    |})).
     intros Hconf_eq; rewrite Hconf_eq.
     f_equiv.
     intros id.
     repeat split; simpl; try reflexivity;
       f_equiv; 
       now rewrite HIso_eq.
     f_equiv.
     apply HIso_eq.
 - simpl in *; assumption.
Qed.
Theorem graph_equivC2D : forall (c c': CGF.Config.t) (rbg:CGF.robogram) (da : CGF.demonic_action),
(CGF.group_good_def c) ->
CGF.Config.eq c' (CGF.round rbg da c) ->
exists da', DGF.Config.eq (ConfigC2D c') (DGF.round (rbgC2D rbg) da' (ConfigC2D c)).
Proof.
intros c c' rbg da Hri HCGF. exists (daC2D da c). intro id.
assert (Heq_rcD: CGF.Config.eq_RobotConf (c id) ({|
             CGF.Config.loc := CGF.Config.loc (c id);
             CGF.Config.info := {|
                                      CGF.Info.source := CGF.Info.source
                                                             (CGF.Config.info (c id));
                                      CGF.Info.target := CGF.Info.target
                                                             (CGF.Config.info (c id)) |} |})) by (
      repeat (try split; simpl) ; reflexivity);
assert (HstepD_compat := CGF.step_compat da id id (reflexivity id)
              (c id)
              ({| CGF.Config.loc := CGF.Config.loc (c id);
                  CGF.Config.info := {|
                     CGF.Info.source := CGF.Info.source (CGF.Config.info (c id));
                     CGF.Info.target := CGF.Info.target (CGF.Config.info (c id)) |} |})
              Heq_rcD);
destruct (CGF.step da id
                    {| CGF.Config.loc := CGF.Config.loc (c id);
                  CGF.Config.info := {|
                     CGF.Info.source := CGF.Info.source (CGF.Config.info (c id));
                     CGF.Info.target := CGF.Info.target (CGF.Config.info (c id)) |} |})
eqn : HstepD'; try (now exfalso);
unfold DGF.round, CGF.round in *; specialize (HCGF id);
unfold CGF.loc_eq in *;
destruct (CGF.step da id (c id)) eqn : HstepD,
(DGF.step (daC2D da c) id (ConfigC2D c id)) eqn : HstepA, id as [g|b]; try (now exfalso);
unfold daC2D in *; simpl in *;
unfold RobotConfC2D, daC2D_step(* , ConfigC2D, LocC2D *) in *;
repeat try (split; simpl);
try (destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e)));
  unfold CGF.ri_loc_def in *;
  destruct (Hrid g) as (v1, (v2, (Hv1, Hv2)));
  destruct (CGF.Config.loc (c (Good g))) as [lld| eld pld] eqn : HlocD;
  destruct (CGF.Info.target (CGF.Config.info (c (Good g)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (CGF.Info.source (CGF.Config.info (c (Good g)))) as [lsd | esd psd] eqn : HsrcD;
  try discriminate; try (now exfalso));
try destruct (CGF.Config.loc (c (Byz b))) as [lld| eld pld] eqn : HlocD;
simpl in *; try (rewrite <- HlocD in * );
try discriminate; rewrite HstepD in *;
destruct HCGF as (Hloc, (Hsrc, Htgt));
try (now (destruct (DGF.Config.eq_RobotConf_dec _); try discriminate;
  destruct (Graph.find_edge _ _) as [etmp|]; try discriminate;
  destruct (Rle_dec dist0 (Graph.threshold etmp)); discriminate));
try (now (destruct (DGF.Config.eq_RobotConf_dec _); try discriminate;
  destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld)); try discriminate;
  destruct (Rle_dec (dist0 + CGF.project_p pld) (Graph.threshold eld)); discriminate));
try (now (destruct (DGF.Config.eq_RobotConf_dec _); try discriminate;
  destruct (Graph.find_edge lsd ltd) as [etmp|]; try discriminate;
  destruct (Rle_dec dist0 (Graph.threshold etmp)); discriminate));
try ( now (destruct dist eqn : Hbool;
  destruct (CGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  try (now simpl in * );
  try (now (destruct (DGF.Config.eq_RobotConf_dec _);
  try discriminate;
  destruct n; unfold rcC2D, LocC2D; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl))));
try (now (try (now simpl in * );
  destruct dist eqn : Hbool;
  destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.eq_RobotConf_dec _);
  try discriminate;
  destruct n; unfold rcC2D, LocC2D; rewrite HlocD, HtgtD, HsrcD; repeat try split; try now simpl)).
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; simpl in *;
    rewrite HlocD, HsrcD, HtgtD in *;
  destruct (CGF.Config.loc (c (Good g))) eqn : Habsurd;
    rewrite HlocD in Habsurd; try discriminate.
  destruct dist1 eqn : Hbool.
  - destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
    destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
    destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
    try discriminate;
    try (now simpl in * );
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; 
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Rdec dist0 1); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Graph.Veq_dec lld ltd); try (now (simpl in *;
                                                try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ))));
    simpl in *;
    destruct (DGF.Config.eq_RobotConf_dec
             {|
             DGF.Config.loc := lld;
             DGF.Config.info := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
              (rcC2D (c (Good g)))); try discriminate;
    try (destruct (Graph.Veq_dec ltd lld);
        try (destruct (Rdec dist0 0));
        try (destruct (Rdec dist0 1));
        simpl in *;
        now rewrite HsrcD in * ).
    * destruct (Graph.Veq_dec ltd lld).
      rewrite Habsurd in *.
      now rewrite v.
      destruct (Rdec dist0 0) eqn : Hdist.
      try rewrite Habsurd, HsrcD, HtgtD in *.
      destruct (Graph.find_edge lsd ltd) eqn : Hedge1.
      ** destruct (Rle_dec (dist0) (Graph.threshold e1)); try discriminate; simpl in *.
         rewrite <- HstepD_compat in *.
         intuition.
         assert (Hfalse := Graph.threshold_pos e1). lra.
      ** discriminate.
      ** destruct (Rdec dist0 1); simpl in *; try assumption;
         destruct (Graph.Veq_dec lld ltd)
                  eqn : Heql,
                        (Graph.Veq_dec ltd lld);
           try (try destruct n0; try destruct n1;easy).
    * destruct (Graph.Veq_dec ltd lld).
      rewrite Habsurd in *.
      now rewrite v.
      destruct (Rdec dist0 0) eqn : Hdist.
      try now rewrite Habsurd, HsrcD, HtgtD in *.
      destruct (Rdec dist0 1); simpl in *; try now rewrite HtgtD in *.
    * destruct (Graph.Veq_dec ltd lld);
        try (destruct (Rdec dist0 0));
        try (destruct (Rdec dist0 1));
        simpl in *; try rewrite Habsurd in *; try easy.
      destruct (Rle_dec (CGF.project_p pld') (Graph.threshold eld'));
        rewrite HsrcD, HtgtD in *; simpl in *.
      specialize (Hex_e lsd ltd (reflexivity lsd) (reflexivity ltd)).
      destruct Hex_e as (e_st, He_st).
      destruct (Graph.find_edge lsd ltd) eqn : Hfe; try discriminate.
      destruct (Rle_dec dist0 (Graph.threshold e0)); try discriminate.
      destruct (Graph.find_edge lld ltd)eqn : HedgeA;
        simpl in *; try rewrite HedgeA in Hloc.
      simpl in *.
      destruct Hloc as (Heeq, Hpeq).
      symmetry in Hpeq.
      rewrite <- (CGF.subj_proj dist0 pld') in Hpeq.
      rewrite Hpeq in n2.
      assert (opt_eq Graph.Eeq (Graph.find_edge lld ltd) (Graph.find_edge lsd ltd)).
      apply Graph.find_edge_compat; try now simpl in *.
      specialize (Hli lld (reflexivity lld));
        destruct Hli as [Hsi | Hti]; try contradiction.
      now symmetry.
      rewrite Hfe, HedgeA in H.
      simpl in H.
      rewrite <- Heeq in H.
      assert (Hfalse := Graph.threshold_compat eld' e0 H).
      now rewrite Hfalse in r.
      assert (HstepD_aux : CGF.Aom_eq (CGF.step da (Good g) (c (Good g)))
                                      (CGF.Moving dist0))
             by now rewrite HstepD.
      assert (Hg := CGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD_aux);
        lra.
      simpl in *.
      specialize (Hli lld (reflexivity lld));
        destruct Hli as [Hsi | Hti]; try (now symmetry in Hti).
      assert (opt_eq Graph.Eeq (Graph.find_edge lld ltd) (Graph.find_edge lsd ltd)).
      apply Graph.find_edge_compat.
      now symmetry.
      reflexivity.
      rewrite HedgeA, Hfe in *.
      now simpl in H.
      now destruct n.
      simpl in *.
      destruct (Graph.find_edge lld ltd) eqn : HedgeA.
      destruct Hloc as (Heq_e, Heq_p).
      assert (Hsol : opt_eq Graph.Eeq (Graph.find_edge lld ltd) (Some eld'))
        by now rewrite HedgeA.
      apply Graph.find2st in Hsol.
      symmetry; now destruct Hsol.
      specialize (Hli lld (reflexivity lld)).
      destruct Hli as [Hsi | Hti]; try now symmetry in Hti.
      specialize (Hex_e lld ltd Hsi (reflexivity ltd)).
      destruct Hex_e as (ex_e, Hex_e).
      rewrite HedgeA in Hex_e.
      contradiction.
      now destruct n.
    * destruct (Graph.Veq_dec ltd lld);
        try (destruct (Rdec dist0 0));
        try (destruct (Rdec dist0 1));
        simpl in *; try rewrite HtgtD in *; try easy.
  - simpl in *. 
    destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
    destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
    destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
    try discriminate;
    try (now simpl in * );
    try ((destruct (Graph.Veq_dec ltd lld ); try (now (simpl in *; 
    try rewrite Habsurd in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ))));
    try ((destruct (Rdec dist0 0); try (now (simpl in *; 
    try rewrite Habsurd in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Rdec dist0 1); try (now (simpl in *;
    try rewrite Habsurd in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ))));
    simpl in *;
    try (destruct (DGF.Config.eq_RobotConf_dec
               {|
               DGF.Config.loc := lld;
               DGF.Config.info := {|
                                  CGF.InfoA.source := lsd;
                                  CGF.InfoA.target := ltd |} |} 
               (rcC2D (c (Good g)))) as [e_DGF | n_DGF];
    try (destruct (Graph.find_edge lsd ltd) as [e_st| ]eqn : Hedge0;
    try (destruct (Rle_dec dist0 (Graph.threshold e_st));
    try (assert (Hfalse := Graph.threshold_pos e_st); lra);
    try (discriminate));
    try (destruct (Hex_e lsd ltd (reflexivity lsd) (reflexivity ltd)) as (e_ex, He_ex);
    rewrite Hedge0 in He_ex; contradiction));
    try (destruct n_DGF;
    unfold rcC2D, LocC2D;
    repeat (split; simpl in * );
    try (now rewrite Habsurd);
    try (now rewrite HsrcD);
    try now rewrite HtgtD));
    try rewrite Habsurd in *;
    try (now (rewrite Hloc;
    assert (CGF.Location.eq (CGF.Loc l) (CGF.Loc lld)) by (now rewrite HlocD);
    unfold CGF.Location.eq,  CGF.loc_eq in *;
    now symmetry));
    try (now (assert (CGF.Location.eq (CGF.Loc l) (CGF.Loc lld)) by now rewrite HlocD;
    now unfold CGF.Location.eq, CGF.loc_eq in * )).
    destruct Hloc as (Heeq, Hpeq).
    destruct (Graph.find_edge lld ltd) eqn : Hedge.
    destruct (Rle_dec (CGF.project_p pld') (Graph.threshold eld')).
    destruct (Hli lld (reflexivity lld)) as [Hsi| Hti]; try now destruct n.
    assert (Hsol : opt_eq Graph.Eeq (Graph.find_edge lld ltd) (Some eld')) by now rewrite Hedge.
    apply Graph.find2st in Hsol;
    symmetry; destruct Hsol.
    try (assert (CGF.Location.eq (CGF.Loc l) (CGF.Loc lld)) by (now rewrite HlocD);
    unfold CGF.Location.eq, CGF.loc_eq in * ).
    now rewrite H in *.
    symmetry in Hpeq.
    rewrite <- (CGF.subj_proj dist0 pld') in Hpeq.
    rewrite Hpeq in r.
    assert (Hsol : opt_eq Graph.Eeq (Some eld') (Some e_st)).
    assert (Htriv : opt_eq Graph.Eeq (Some e) (Some eld')) by now simpl in *.
    rewrite <- Htriv, <- Hedge, <- Hedge0.
    apply Graph.find_edge_compat.
    destruct (Hli lld (reflexivity lld)) as [Hsi| Hti]; try now destruct n.
    now symmetry.
    reflexivity.
    simpl in *.
    rewrite Hsol in n2.
    lra.
    assert (HstepD_aux : CGF.Aom_eq (CGF.step da (Good g) (c (Good g)))
                                      (CGF.Moving dist0))
      by now rewrite HstepD.
    assert (Hf := CGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD_aux).
    lra.
    destruct (Hli lld (reflexivity lld)) as [Hsi| Hti]; try now destruct n.
    destruct (Hex_e lld ltd Hsi (reflexivity ltd)) as (e_ex, He_ex).
    rewrite Hedge in He_ex.
    contradiction.    
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD, HsrcD, HtgtD in *;
  destruct (Rle_dec 1 (CGF.project_p pld + dist0)) eqn : Hdp;
  simpl in *;
  assert (Hmi_aux : Graph.Eeq eld eld /\ pld = pld) by (split; reflexivity);
  assert (Hmi_0 := (Hmi lsd ltd eld pld (reflexivity lsd) (reflexivity ltd) Hmi_aux));
  apply Graph.find2st in Hmi_0;
  destruct Hmi_0 as (Hmi_s, Hmi_t);
  destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  try (now simpl in * );
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; 
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Rdec dist0 1); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Graph.Veq_dec lld ltd); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * )))); simpl in *.
  - now rewrite <- Hmi_t in Hloc.
  -  destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld)) eqn : Hpt.
    * destruct(
           DGF.Config.eq_RobotConf_dec
             {|
             DGF.Config.loc := Graph.src eld;
             DGF.Config.info := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
              (rcC2D (c (Good g)))).
      destruct (Rle_dec (dist0 + CGF.project_p pld) (Graph.threshold eld)).
      assert (Hfalse := Graph.threshold_pos eld).
      lra.
      discriminate.
      destruct n.
      unfold rcC2D, LocC2D; repeat (split; simpl in * );
        try rewrite HlocD;
        try rewrite HsrcD;
        try rewrite HtgtD;
      try now  destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld)).
  * assumption.
  - destruct(Rle_dec (CGF.project_p pld') (Graph.threshold eld')).
    * destruct(Rdec dist0 0).
      ** destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld)) eqn : Hpt.
         -- destruct(
            DGF.Config.eq_RobotConf_dec
             {|
               DGF.Config.loc := Graph.src eld;
               DGF.Config.info := {|
                                   DGF.Info.source := lsd;
                                   DGF.Info.target := ltd |} |}
             (rcC2D (c (Good g)))).
            ++ destruct (Rle_dec (dist0 + CGF.project_p pld) (Graph.threshold eld)).
               discriminate.
               lra.
            ++ discriminate.
         -- destruct (DGF.Config.eq_RobotConf_dec
             {|
             DGF.Config.loc := Graph.tgt eld;
             DGF.Config.info := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
  (rcC2D (c (Good g))));
            discriminate.
      ** destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld)).
         -- destruct(DGF.Config.eq_RobotConf_dec
             {|
             DGF.Config.loc := Graph.src eld;
             DGF.Config.info := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
               (rcC2D (c (Good g)))).
            ++ destruct(Rle_dec (dist0 + CGF.project_p pld) (Graph.threshold eld)).
               discriminate.
               destruct Hloc as (Heeq, Hpeq).
               symmetry in Hpeq.
               rewrite <- (CGF.subj_proj (CGF.project_p pld + dist0) pld') in Hpeq.
               rewrite <- Hpeq in r.
               assert (Htre : Graph.threshold eld = Graph.threshold eld').
               apply Graph.threshold_compat.
               now symmetry.
               rewrite <- Htre in r.
               lra.
               assert (Hsol := Graph.threshold_pos eld).
               lra.
            ++ discriminate.
         -- destruct (DGF.Config.eq_RobotConf_dec
             {|
             DGF.Config.loc := Graph.tgt eld;
             DGF.Config.info := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
              (rcC2D (c (Good g))));
            discriminate.
    * destruct(Rdec dist0 0);
      try destruct Hloc as (Heeq, Hpeq);
      try rewrite Heeq;
      try now symmetry.
  - destruct (Rdec dist0 0);
    assert (Htr : Graph.threshold eld = Graph.threshold eld') by (now apply Graph.threshold_compat);
    destruct Hloc as (Heeq, Hpeq);
    rewrite Htr, Hpeq in *;
    destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld')) eqn : Hpt'.
    * now apply Graph.src_compat.
    * now apply Graph.tgt_compat.
    * assert (Hfalse : (CGF.project_p pld < CGF.project_p pld + dist0)%R).
      assert (HstepD_aux : CGF.Aom_eq (CGF.step da (Good g) (c (Good g)))
                                      (CGF.Moving dist0))
        by now rewrite HstepD.
      assert (Hf_aux := CGF.step_flexibility da (Good g) (c (Good g))
                                             dist0 HstepD_aux).
      lra.
      assert (Hl := CGF.project_p_image pld).
      rewrite <- (CGF.inv_pro (CGF.project_p pld + dist0)) in *.
      destruct (Rle_dec (CGF.project_p pld + dist0) (Graph.threshold eld')).
      -- now apply Graph.src_compat.
      -- destruct(DGF.Config.eq_RobotConf_dec
                    {|
                      DGF.Config.loc := Graph.src eld;
             DGF.Config.info := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |} (rcC2D (c (Good g)))).
         ++ destruct (Rle_dec (dist0 + CGF.project_p pld) (Graph.threshold eld')); try lra.
            discriminate.
         ++ destruct n2.
            unfold rcC2D, LocC2D;
              try rewrite HlocD;
              try rewrite HsrcD;
              try rewrite HtgtD.
            try destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld)).
            reflexivity.
            rewrite Htr in n2.
            now destruct n2.
      -- lra.
    * assert (Hfalse : (CGF.project_p pld < CGF.project_p pld + dist0)%R).
      assert (HstepD_aux : CGF.Aom_eq (CGF.step da (Good g) (c (Good g)))
                                      (CGF.Moving dist0))
        by now rewrite HstepD.
      assert (Hf_aux := CGF.step_flexibility da (Good g) (c (Good g))
                                             dist0 HstepD_aux).
      lra.
      assert (Hl := CGF.project_p_image pld).
      rewrite <- (CGF.inv_pro (CGF.project_p pld + dist0)) in *.
      destruct (Rle_dec (CGF.project_p pld + dist0) (Graph.threshold eld')).
      ** lra.
      ** now apply Graph.tgt_compat.
      ** lra.
+ destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (
      destruct (Graph.Veq_dec ltd lld); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      destruct (Graph.Veq_dec lld ltd); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in * ).
+ destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (destruct (Rle_dec 1 (CGF.project_p pld + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; now simpl in * ); try now simpl in *.
+ destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (
      destruct (Graph.Veq_dec ltd lld); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      destruct (Graph.Veq_dec lld ltd); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in * );
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in * ).
+ destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (destruct (Rle_dec 1 (CGF.project_p pld + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; now simpl in * ); try now simpl in *.
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
  destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  try now simpl in *.
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
  destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  try (now simpl in * );
  destruct Hloc as (Hle, Hlp);
  assert (Htt : Graph.threshold eld = Graph.threshold eld') by (now apply Graph.threshold_compat);
  rewrite Htt, Hlp;
  destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
  destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  try (now simpl in * );
  destruct Hsrc as (Hse, Hsp);
  assert (Htt : Graph.threshold esd = Graph.threshold esd') by (now apply Graph.threshold_compat);
  rewrite Htt, Hsp;
  destruct (Rle_dec (CGF.project_p psd) (Graph.threshold esd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
  destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  try (now simpl in * );
  destruct Hsrc as (Hse, Hsp);
  assert (Htt : Graph.threshold esd = Graph.threshold esd') by (now apply Graph.threshold_compat);
  rewrite Htt, Hsp;
  destruct (Rle_dec (CGF.project_p psd) (Graph.threshold esd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
  destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  try (now simpl in * );
  destruct Htgt as (Hte, Htp);
  assert (Htt : Graph.threshold etd = Graph.threshold etd') by (now apply Graph.threshold_compat);
  rewrite Htt, Htp;
  destruct (Rle_dec (CGF.project_p ptd) (Graph.threshold etd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
  destruct dist1 eqn : Hbool;
  destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  try (now simpl in * );
  destruct Htgt as (Hte, Htp);
  assert (Htt : Graph.threshold etd = Graph.threshold etd') by (now apply Graph.threshold_compat);
  rewrite Htt, Htp;
  destruct (Rle_dec (CGF.project_p ptd) (Graph.threshold etd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, RobotConfC2D, rcC2D, LocC2D in *; rewrite HlocD, HsrcD, HtgtD in *.
  destruct (DGF.Config.eq_RobotConf_dec
               {|
               DGF.Config.loc := lld;
               DGF.Config.info := {|
                                  CGF.InfoA.source := lsd;
                                  CGF.InfoA.target := ltd |} |}
               {|
               DGF.Config.loc := lld;
               DGF.Config.info := {|
                                  CGF.InfoA.source := lsd;
                                  CGF.InfoA.target := ltd |} |});
  try (destruct (Graph.find_edge lsd ltd));
  try destruct (Rle_dec dist0 (Graph.threshold e0));
  try easy.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try destruct (Graph.find_edge
                 (LocC2D (CGF.Info.source (CGF.Config.info (c (Good g)))))
                 (LocC2D (CGF.Info.target (CGF.Config.info (c (Good g))))));
        try destruct (Rle_dec dist0 (Graph.threshold e0));
    try easy.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try destruct (Graph.find_edge
                 (LocC2D (CGF.Info.source (CGF.Config.info (c (Good g)))))
                 (LocC2D (CGF.Info.target (CGF.Config.info (c (Good g))))));
        try destruct (Rle_dec dist0 (Graph.threshold e0));
    try easy.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Byz b)) (rcC2D (c (Byz b))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Byz b)) (rcC2D (c (Byz b))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Byz b)) (rcC2D (c (Byz b))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Byz b)) (rcC2D (c (Byz b))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Byz b)) (rcC2D (c (Byz b))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Byz b)) (rcC2D (c (Byz b))));
    try easy.
  destruct n.
  now unfold ConfigC2D, RobotConfC2D, rcC2D in *.
+ simpl in *.
  destruct (CGF.Config.loc (c' (Good g))) eqn : HlocD'; try now rewrite HlocD in Hloc.
  destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g)))).
  assert (HstepA' : DGF.Aom_eq (DGF.Active sim0) (DGF.Active sim1))
    by now rewrite HstepA.
  unfold DGF.Aom_eq in HstepA'.
  destruct (CGF.pgm rbg
                    (DGF.Spect.from_config
                      (DGF.Config.map (DGF.apply_sim sim1) (ConfigC2D c)))
                   (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
           )eqn : Hr.
  simpl.
  assert (Hr' :=
            CGF.pgm_compat
              rbg
              (DGF.Spect.from_config (DGF.Config.map (DGF.apply_sim sim1)
                                                     (ConfigC2D c)))
              (CGF.Spect.from_config (CGF.Config.map (CGF.apply_sim sim0)
                                                     c))).
  assert (CGF.Spect.eq (DGF.Spect.from_config (DGF.Config.map (DGF.apply_sim sim1)
                                                     (ConfigC2D c)))
              (CGF.Spect.from_config (CGF.Config.map (CGF.apply_sim sim0)
                                                     c))).
  unfold DGF.Spect.from_config, CGF.Spect.from_config.
  assert (ConfigA.eq (DGF.Config.map (DGF.apply_sim sim1) (ConfigC2D c))
                     (CGF.projectS (CGF.Config.map (CGF.apply_sim sim0) c))).
  unfold DGF.Config.map, DGF.apply_sim, CGF.Config.app, CGF.Config.map, CGF.projectS,
  CGF.projectS_loc, ConfigC2D, LocC2D. 
  simpl in *.
  intros id; repeat split; simpl.
  destruct(CGF.Config.loc (c id)).
  f_equiv.
  apply (symmetry HstepA').
  rewrite <- CGF.inv_pro.
  unfold LocC2D in *.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (symmetry HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H.
  rewrite (Iso.sim_threshold sim0) in H.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (symmetry HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  destruct (CGF.Info.source (CGF.Config.info (c id))).
  f_equiv.
  apply (symmetry HstepA').
  rewrite <- CGF.inv_pro.
  unfold LocC2D in *.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (symmetry HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H.
  rewrite (Iso.sim_threshold sim0) in H.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (symmetry HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  destruct (CGF.Info.target (CGF.Config.info (c id))).
  f_equiv.
  apply (symmetry HstepA').
  rewrite <- CGF.inv_pro.
  unfold LocC2D in *.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (symmetry HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H.
  rewrite (Iso.sim_threshold sim0) in H.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (symmetry HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  rewrite H.
  reflexivity.
  specialize (Hr' H (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
                  (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld))).
  rewrite Hr in Hr'.
  unfold CGF.Location.eq, CGF.loc_eq in Hr'.
  assert (Graph.Veq (Isomorphism.section (Iso.sim_V sim1) lld)
                    (Isomorphism.section (Iso.sim_V sim0) lld)).
  f_equiv; apply (symmetry HstepA'). 
  specialize (Hr' H0).
  destruct (CGF.pgm rbg
            (CGF.Spect.from_config (CGF.Config.map (CGF.apply_sim sim0) c))
            (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld)));
    try (now exfalso).
  destruct (DGF.Location.eq_dec (Isomorphism.retraction (Iso.sim_V sim1) l0) lld).
  destruct (CGF.Location.eq_dec
                  (CGF.Loc (Isomorphism.retraction (Iso.sim_V sim0) l1))
                  (CGF.Loc lld)); simpl in *; try rewrite HlocD in Hloc.
  unfold LocC2D;
  now rewrite HlocD.
  simpl.
  unfold LocC2D.
  destruct (CGF.Location.eq_dec
                  (CGF.Loc (Isomorphism.retraction (Iso.sim_V sim0) l1))
                  (CGF.Loc lld));
    try (now rewrite HlocD in *); try rewrite HlocD in Hloc.
  assert (Hrange :=
            CGF.pgm_range
              rbg
              (DGF.Spect.from_config (DGF.Config.map (DGF.apply_sim sim1)
                                                     (ConfigC2D c)))
              (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
              (Isomorphism.section (Iso.sim_V sim1) lld) (reflexivity _)).
  destruct Hrange as (lrange, (_, (Hlrange, _))). 
  simpl. 
  destruct (CGF.Location.eq_dec
                  (CGF.Loc (Isomorphism.retraction (Iso.sim_V sim0) l1))
                  (CGF.Loc lld)).
  try (now simpl in *); try rewrite HlocD in Hloc.
  now simpl in *.
  now simpl in *.
  assert (Hrange :=
            CGF.pgm_range
              rbg
              (DGF.Spect.from_config (DGF.Config.map (DGF.apply_sim sim1)
                                                     (ConfigC2D c)))
              (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
              (Isomorphism.section (Iso.sim_V sim1) lld) (reflexivity _)).
  destruct Hrange as (lrange, (_, (Hlrange, _))). 
  now rewrite Hr in Hlrange.
  destruct n.
  unfold ConfigC2D, rcC2D, RobotConfC2D, LocC2D in *.
  reflexivity.
  destruct ( CGF.Location.eq_dec
                  (CGF.Loc
                     match
                       CGF.pgm rbg
                         (CGF.Spect.from_config
                            (CGF.Config.map (CGF.apply_sim sim0) c))
                         (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld))
                     with
                     | CGF.Loc l => Isomorphism.retraction (Iso.sim_V sim0) l
                     | CGF.Mvt e _ => Graph.src e
                     end) (CGF.Loc lld)); try (now simpl in *).
  simpl in *. now rewrite HlocD in *.
+ simpl in *.
  unfold LocC2D.
  destruct (CGF.Config.loc (c' (Good g))) eqn : HlocD'; try rewrite HlocD in Hloc;
    try now simpl.
  destruct (CGF.Location.eq_dec
                  (CGF.Loc
                     match
                       CGF.pgm rbg
                         (CGF.Spect.from_config
                            (CGF.Config.map (CGF.apply_sim sim0) c))
                         (CGF.Mvt (Isomorphism.section (Iso.sim_E sim0) eld)
                            (CGF.project_p_inv
                               (Isomorphism.section (Iso.sim_T sim0)
                                  (CGF.project_p pld))))
                     with
                     | CGF.Loc l => Isomorphism.retraction (Iso.sim_V sim0) l
                     | CGF.Mvt e _ => Graph.src e
                     end) (CGF.Mvt eld pld)).
  simpl in *. now rewrite HlocD in *.
  now simpl in *.
  destruct (CGF.Location.eq_dec
                  (CGF.Loc
                     match
                       CGF.pgm rbg
                         (CGF.Spect.from_config
                            (CGF.Config.map (CGF.apply_sim sim0) c))
                         (CGF.Mvt (Isomorphism.section (Iso.sim_E sim0) eld)
                            (CGF.project_p_inv
                               (Isomorphism.section (Iso.sim_T sim0)
                                  (CGF.project_p pld))))
                     with
                     | CGF.Loc l => Isomorphism.retraction (Iso.sim_V sim0) l
                     | CGF.Mvt e _ => Graph.src e
                     end) (CGF.Mvt eld pld)).
  now simpl in *.
  simpl in *.
  assert (HstepD_aux : CGF.Aom_eq
                         (CGF.step da (Good g) (c (Good g))) (CGF.Active sim0))
  by now rewrite HstepD.
  assert (Hdelta := CGF.step_delta da g (c (Good g)) sim0 HstepD_aux).
  destruct Hdelta as ((lf, Hf),_).
  rewrite HlocD in Hf.
  now simpl in *.
+ simpl in *; unfold LocC2D in *.
  destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try discriminate.
  (* faire sim1 => sim0;
     casser tout;
     simpl*)
  assert (HstepA' : DGF.Aom_eq (DGF.Active sim0) (DGF.Active sim1))
         by now rewrite HstepA.
  assert (CGF.Location.eq (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld))
                          (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))).
  now apply HstepA'.
  assert (CGF.Spect.eq (CGF.Spect.from_config
                          (CGF.Config.map (CGF.apply_sim sim0) c))
                       (DGF.Spect.from_config
                          (DGF.Config.map (DGF.apply_sim sim1) (ConfigC2D c)))).
  unfold DGF.Spect.from_config, CGF.Spect.from_config.
  assert (ConfigA.eq (CGF.projectS
                        (CGF.Config.map
                           (CGF.apply_sim sim0) c))
                     (DGF.Config.map
                        (DGF.apply_sim sim1)
                        (ConfigC2D c))).
  intros id; unfold DGF.Config.map, CGF.Config.map, DGF.apply_sim, CGF.Config.app, CGF.projectS, CGF.projectS_loc, ConfigC2D, LocC2D.
  repeat split; simpl.
  destruct (CGF.Config.loc (c id)).
  f_equiv.
  apply (HstepA').
  rewrite <- CGF.inv_pro.
  unfold LocC2D.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H0.
  rewrite (Iso.sim_threshold sim0) in H0.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  destruct (CGF.Info.source (CGF.Config.info (c id))).
  apply (HstepA').
  reflexivity.
  rewrite <- CGF.inv_pro.
  unfold LocC2D.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H0.
  rewrite (Iso.sim_threshold sim0) in H0.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  destruct (CGF.Info.target (CGF.Config.info (c id))).
  f_equiv.
  apply (HstepA').
  rewrite <- CGF.inv_pro.
  unfold LocC2D.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H0.
  rewrite (Iso.sim_threshold sim0) in H0.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  rewrite H0.
  reflexivity.
  assert (Hpgm_compat := CGF.pgm_compat rbg _ _ H0 _ _ H).
  destruct (CGF.pgm rbg
                      (DGF.Spect.from_config
                         (DGF.Config.map (DGF.apply_sim sim1) (ConfigC2D c)))
                      (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld)))
  eqn : Hloc_rbg1,
        (CGF.pgm rbg
                 (CGF.Spect.from_config
                    (CGF.Config.map (CGF.apply_sim sim0) c))
                 (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld)))
          eqn : Hloc_rbg0; try now simpl in *.
  destruct (CGF.Info.source (CGF.Config.info (c' (Good g))))eqn : Hs';
    simpl in *.
  destruct (DGF.Location.eq_dec (Isomorphism.retraction (Iso.sim_V sim1) l) lld);
    unfold ConfigC2D, LocC2D;
    simpl;
    destruct (CGF.Location.eq_dec
                (CGF.Loc (Isomorphism.retraction (Iso.sim_V sim0) l0))
                (CGF.Loc lld));
    try rewrite HsrcD in *;
    try easy.
  simpl in *.
  destruct n; unfold CGF.Location.eq, CGF.loc_eq.
  rewrite <- e0; f_equiv. apply HstepA'.
  apply Hpgm_compat.
  destruct n.
  unfold CGF.Location.eq, CGF.loc_eq in *.
  rewrite <- e0; f_equiv. apply (symmetry HstepA').
  apply (symmetry Hpgm_compat).
  unfold ConfigC2D, LocC2D.
  destruct ( CGF.Location.eq_dec
                    (CGF.Loc (Isomorphism.retraction (Iso.sim_V sim0) l0))
                    (CGF.Loc lld)); try rewrite HsrcD in *; now simpl in *.
  assert (Hrange := CGF.pgm_range rbg
                                  (DGF.Spect.from_config
                                     (DGF.Config.map (DGF.apply_sim sim1)
                                                     (ConfigC2D c)))
                                  (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
                                  (Isomorphism.section (Iso.sim_V sim1) lld)
         (reflexivity _)).
  destruct Hrange as (lrange, (erange, (Hlrange, _))). 
  now rewrite Hlrange in *.
+ simpl in *; unfold LocC2D.
  assert (HstepD_aux : CGF.Aom_eq (CGF.step da (Good g) (c (Good g)))
                                  (CGF.Active sim0))
    by now rewrite HstepD.
  assert (Hdelta := CGF.step_delta da g (c (Good g)) sim0 HstepD_aux).
  destruct Hdelta as ((lfalse, Hfalse),_).
  now rewrite HlocD in Hfalse.
+ unfold LocC2D; simpl in *.
  destruct (DGF.Config.eq_RobotConf_dec 
              (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
    try discriminate.
  assert (HstepA' : DGF.Aom_eq (DGF.Active sim0) (DGF.Active sim1))
    by now rewrite HstepA.
  destruct (CGF.pgm rbg
            (DGF.Spect.from_config
               (DGF.Config.map (DGF.apply_sim sim1) (ConfigC2D c))))
           eqn : Hlocpgm,
                 (CGF.pgm rbg
                          (CGF.Spect.from_config
                             (CGF.Config.map (CGF.apply_sim sim0) c))
                          (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld)))
                   eqn : Hlocpgm';
    destruct (CGF.Info.target (CGF.Config.info
                                   (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  try (now simpl in * ).
  - clear Hmi.
        assert (CGF.Location.eq (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld))
                          (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))).
  now apply HstepA'.
  
  assert (CGF.Spect.eq (CGF.Spect.from_config
                          (CGF.Config.map (CGF.apply_sim sim0) c))
                       (DGF.Spect.from_config
                          (DGF.Config.map (DGF.apply_sim sim1) (ConfigC2D c)))).
  unfold DGF.Spect.from_config, CGF.Spect.from_config.
  assert (ConfigA.eq (CGF.projectS
                        (CGF.Config.map
                           (CGF.apply_sim sim0) c))
                     (DGF.Config.map
                        (DGF.apply_sim sim1)
                        (ConfigC2D c))).
  intros id; unfold DGF.Config.map, CGF.Config.map, DGF.apply_sim, CGF.Config.app, CGF.projectS, CGF.projectS_loc, ConfigC2D, LocC2D.
  repeat split; simpl.
  destruct (CGF.Config.loc (c id)).
  f_equiv.
  apply (HstepA').
  rewrite <- CGF.inv_pro.
  unfold LocC2D.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H0.
  rewrite (Iso.sim_threshold sim0) in H0.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  destruct (CGF.Info.source (CGF.Config.info (c id))).
  apply (HstepA').
  reflexivity.
  rewrite <- CGF.inv_pro.
  unfold LocC2D.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H0.
  rewrite (Iso.sim_threshold sim0) in H0.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  destruct (CGF.Info.target (CGF.Config.info (c id))).
  f_equiv.
  apply (HstepA').
  rewrite <- CGF.inv_pro.
  unfold LocC2D.
  assert (Hcroiss := Iso.sim_croiss sim0).
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
    destruct (Rle_dec (Isomorphism.section (Iso.sim_T sim0) (CGF.project_p p))
                      (Graph.threshold (Isomorphism.section (Iso.sim_E sim0) e0))).
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Hs_sim;
    now apply (HstepA').
  destruct n;
    destruct (Rle_lt_or_eq_dec (CGF.project_p p) (Graph.threshold e0)). 
  assumption.
  apply Hcroiss in r0.
  rewrite (Iso.sim_threshold sim0) in r0.
  now left.
  rewrite <- (Iso.sim_threshold sim0).
  now rewrite e1.
  assert (Graph.threshold e0 < CGF.project_p p)%R by lra.
  apply Hcroiss in H0.
  rewrite (Iso.sim_threshold sim0) in H0.
  lra.
  f_equiv.
  destruct (Iso.sim_morphism sim0 e0) as (Hs_sim, Ht_sim).
  rewrite <- Ht_sim;
    now apply (HstepA').
  apply (Iso.sim_bound_T).
  apply CGF.project_p_image.
  now rewrite H0.
  assert (Hcompat := CGF.pgm_compat rbg _ _ H0 _ _ H).
  rewrite Hlocpgm, Hlocpgm' in Hcompat.
    destruct (DGF.Location.eq_dec (Isomorphism.retraction (Iso.sim_V sim1) l) lld);
    destruct (CGF.Location.eq_dec
                (CGF.Loc (Isomorphism.retraction (Iso.sim_V sim0) l0))
                (CGF.Loc lld));
    simpl in *;
    unfold LocC2D.
    now rewrite HtgtD in *.
    destruct n.
    rewrite <- e0.
    f_equiv.
    apply HstepA'.
    assumption.
    destruct n.
    rewrite <- e0.
    f_equiv.
    apply (symmetry HstepA').
    easy.
    rewrite Htgt.
    f_equiv.
    apply HstepA'.
    apply Hcompat.
  - destruct ( CGF.Location.eq_dec
                     (CGF.Loc (Isomorphism.retraction (Iso.sim_V sim0) l0))
                     (CGF.Loc lld)); try rewrite HtgtD in Htgt; now simpl in *.
  - destruct (CGF.pgm_range rbg
                            (CGF.Spect.from_config
                               (CGF.Config.map
                                  (CGF.apply_sim sim0) c))
                            (CGF.Loc (Isomorphism.section (Iso.sim_V sim0) lld))
                            (Isomorphism.section (Iso.sim_V sim0) lld)
                            (reflexivity _))
      as (lrange ,(_, (Hfalse, _))).
    now rewrite Hfalse in Hlocpgm'.
  - destruct ( CGF.Location.eq_dec
                     (CGF.Loc (Graph.src e0))
                     (CGF.Loc lld)); try rewrite HtgtD in Htgt; now simpl in *.
  - destruct (CGF.pgm_range rbg
                            (DGF.Spect.from_config
                               (DGF.Config.map
                                  (DGF.apply_sim sim1) (ConfigC2D c)))
                            (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
                            (Isomorphism.section (Iso.sim_V sim1) lld)
                            (reflexivity _))
      as (lrange ,(_, (Hfalse, _))).
    now rewrite Hfalse in Hlocpgm. 
  - destruct (CGF.pgm_range rbg
                            (DGF.Spect.from_config
                               (DGF.Config.map
                                  (DGF.apply_sim sim1) (ConfigC2D c)))
                            (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
                            (Isomorphism.section (Iso.sim_V sim1) lld)
                            (reflexivity _))
      as (lrange ,(_, (Hfalse, _))).
    now rewrite Hfalse in Hlocpgm. 
  - destruct (CGF.pgm_range rbg
                            (DGF.Spect.from_config
                               (DGF.Config.map
                                  (DGF.apply_sim sim1) (ConfigC2D c)))
                            (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
                            (Isomorphism.section (Iso.sim_V sim1) lld)
                            (reflexivity _))
      as (lrange ,(_, (Hfalse, _))).
    now rewrite Hfalse in Hlocpgm. 
  - destruct (CGF.pgm_range rbg
                            (DGF.Spect.from_config
                               (DGF.Config.map
                                  (DGF.apply_sim sim1) (ConfigC2D c)))
                            (CGF.Loc (Isomorphism.section (Iso.sim_V sim1) lld))
                            (Isomorphism.section (Iso.sim_V sim1) lld)
                            (reflexivity _))
      as (lrange ,(_, (Hfalse, _))).
    now rewrite Hfalse in Hlocpgm.
+ assert (HstepD_aux : CGF.Aom_eq (CGF.step da (Good g) (c (Good g)))
                                  (CGF.Active sim0))
  by (now rewrite HstepD);
    assert (Hdelta := CGF.step_delta da g (c (Good g)) sim0 HstepD_aux).
  destruct Hdelta as ((ldelta, Hldelta),Heq_delta).
  rewrite HlocD in Hldelta.
  now unfold CGF.Location.eq in Hldelta.
+ unfold ConfigC2D, RobotConfC2D, rcC2D, LocC2D in *;
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  simpl in *;
  destruct (CGF.Config.loc (c' (Byz b))) as [lbl' | ebl' pbl'] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (CGF.Config.loc (CGF.relocate_byz da b)) as [lrb | erb prb] eqn : Hrb;
  try assumption; try (now exfalso); try (now simpl in * );
  try destruct Hloc as (Hel, Hpl);
  try assert (Hth : (Graph.threshold ebl')= (Graph.threshold erb)) by (now apply Graph.threshold_compat);
  try rewrite <- Hpl, Hth; try destruct ( Rle_dec (CGF.project_p pbl') (Graph.threshold erb));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, rcC2D, LocC2D in *;
    destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  simpl in *;
  destruct (CGF.Config.loc (c' (Byz b))) as [lbl' | ebl' pbl'] eqn : HlocD';
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (CGF.Config.loc (CGF.relocate_byz da b)) as [lrb | erb prb] eqn : Hrb;
  try assumption; try (now exfalso); try (now simpl in * );
  destruct Hloc as (Hel, Hpl);
  assert (Hth : (Graph.threshold ebl')= (Graph.threshold erb)) by (now apply Graph.threshold_compat);
  rewrite <- Hpl, Hth; destruct ( Rle_dec (CGF.project_p pbl') (Graph.threshold erb));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, rcC2D, LocC2D in *;
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (CGF.Info.source (CGF.Config.info (CGF.relocate_byz da b)))
    as [lrbs | erbs prbs] eqn : Hrbs;
  simpl in *;
  try rewrite Hrbs in *;
  try assumption; try (now exfalso); try (now simpl in * );
  destruct Hsrc as (Hes, Hps);
  assert (Hth : (Graph.threshold ebs')= (Graph.threshold erbs)) by (now apply Graph.threshold_compat);
  rewrite <- Hps, Hth; destruct ( Rle_dec (CGF.project_p pbs') (Graph.threshold erbs));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, rcC2D, LocC2D in *;
  destruct (CGF.Info.source (CGF.Config.info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (CGF.Info.source (CGF.Config.info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (CGF.Info.source (CGF.Config.info (CGF.relocate_byz da b)))
    as [lrbs | erbs prbs] eqn : Hrbs;
  simpl in *;
  try rewrite Hrbs in *;
  try assumption; try (now exfalso); try (now simpl in * );
  destruct Hsrc as (Hes, Hps);
  assert (Hth : (Graph.threshold ebs')= (Graph.threshold erbs)) by (now apply Graph.threshold_compat);
  rewrite <- Hps, Hth; destruct ( Rle_dec (CGF.project_p pbs') (Graph.threshold erbs));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, rcC2D, LocC2D in *;
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  destruct (CGF.Info.target (CGF.Config.info (CGF.relocate_byz da b)))
    as [lrbt | erbt prbt] eqn : Hrbt;
  simpl in *;
  try rewrite Hrbt in *;
  simpl in *;try rewrite HtgtD in *;
  try assumption; try (now exfalso); try (now simpl in * );
  destruct Htgt as (Het, Hpt);
  assert (Hth : (Graph.threshold ebt')= (Graph.threshold erbt)) by (now apply Graph.threshold_compat);
  rewrite <- Hpt, Hth; destruct ( Rle_dec (CGF.project_p pbt') (Graph.threshold erbt));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ unfold ConfigC2D, rcC2D, LocC2D in *;
  destruct (CGF.Info.target (CGF.Config.info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (CGF.Info.target (CGF.Config.info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  destruct (CGF.Info.target (CGF.Config.info (CGF.relocate_byz da b)))
    as [lrbt | erbt prbt] eqn : Hrbt;
  simpl in *;
  try rewrite Hrbt in *;
  simpl in *;try rewrite HtgtD in *;
  try assumption; try (now exfalso); try (now simpl in * );
  destruct Htgt as (Het, Hpt);
  assert (Hth : (Graph.threshold ebt')= (Graph.threshold erbt)) by (now apply Graph.threshold_compat);
  rewrite <- Hpt, Hth; destruct ( Rle_dec (CGF.project_p pbt') (Graph.threshold erbt));
    try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
Qed.

End GraphEquivalence.
