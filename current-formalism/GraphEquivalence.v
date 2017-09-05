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
                        (MkInfoA : SourceTargetSig(LocationA))
                        (ConfigA : Configuration (LocationA)(N)(Names)(MkInfoA))
                        (SpectA : Spectrum(LocationA)(N)(Names)(MkInfoA)(ConfigA))
                        (Import Iso : Iso(Graph)(LocationA)).

Module DGF := DGF (Graph)(N)(Names)(LocationA)(MkInfoA)(ConfigA)(SpectA)(Iso).
Module CGF := CGF (Graph)(N)(Names)(LocationA)(MkInfoA)(ConfigA)(SpectA)(Iso).



(** Conversion from Discrete to Continuous settings. *)
Definition RobotConfD2C (robotconfD : DGF.Config.RobotConf) : CGF.Config.RobotConf :=
    {| CGF.Config.loc := CGF.Loc (DGF.Config.loc robotconfD);
       CGF.Config.state := 
      {| CGF.Info.source := CGF.Loc (DGF.Info.source (DGF.Config.state robotconfD));
         CGF.Info.target := CGF.Loc (DGF.Info.target (DGF.Config.state robotconfD)) |} |}.

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
     DGF.Config.state := 
       {| DGF.Info.source := LocC2D (CGF.Info.source (CGF.Config.state robotconfC));
          DGF.Info.target := LocC2D (CGF.Info.target (CGF.Config.state robotconfC)) |} |}.

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

Lemma DGF_CGF_DGF_Config : forall confA: DGF.Config.t,
  DGF.Config.eq confA (ConfigC2D (ConfigD2C confA)).
Proof.
intros confA id. unfold ConfigC2D, ConfigD2C. now repeat try (split; simpl).
Qed.

Lemma Mraw_equiv : DGF.Spect.t = CGF.Spect.t.
Proof. reflexivity. Qed.

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
     DGF.Config.state := {| DGF.Info.source := LocC2D (CGF.Info.source (CGF.Config.state rcD));
                           DGF.Info.target := LocC2D (CGF.Info.target (CGF.Config.state rcD)) |} |}.

Instance rcC2D_compat : Proper (CGF.Config.eq_RobotConf ==> DGF.Config.eq_RobotConf) rcC2D.
Proof.
intros rcD1 rcD2 HrcD. unfold rcC2D. repeat try (split;simpl); f_equiv; apply HrcD.
Qed.

Definition rcD2C (rcA : DGF.Config.RobotConf) : CGF.Config.RobotConf :=
{| CGF.Config.loc := CGF.Loc (DGF.Config.loc rcA);
        CGF.Config.state := 
          {| CGF.Info.source := CGF.Loc (DGF.Info.source (DGF.Config.state rcA));
             CGF.Info.target := CGF.Loc (DGF.Info.target (DGF.Config.state rcA)) |} |}.

Instance rcD2C_compat : Proper (DGF.Config.eq_RobotConf ==> CGF.Config.eq_RobotConf) rcD2C.
Proof.
intros rcA1 rcA2 HrcA. unfold rcD2C. repeat try (split;simpl); apply HrcA.
Qed.

Definition daC2D_step daD (cD: CGF.Config.t ) (g:Names.G) rcA :=
  if DGF.Config.eq_RobotConf_dec rcA (rcC2D (cD (Good g)))
  then match (CGF.step daD) g (cD (Good g)) with
         | CGF.Active sim => DGF.Active sim
         | CGF.Moving dist => 
             match (CGF.Config.loc (cD (Good g))) with
               | CGF.Loc _ =>
                   match (Graph.find_edge (DGF.Info.source (DGF.Config.state rcA))
                                          (DGF.Info.target (DGF.Config.state rcA))) with
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
  DGF.Aom_eq (daC2D_step daD cD (g) Rconfig) (DGF.Active sim) ->
  DGF.Location.eq Rconfig (DGF.Info.target (DGF.Config.state Rconfig)).
Proof.
intros daD cD g rcA sim HrcD. unfold DGF.Aom_eq, daC2D_step in *.
    destruct (DGF.Config.eq_RobotConf_dec rcA (rcC2D (cD (Good g))));
      try easy.
    destruct e as (Hl, (Hs, Ht)).
    (*   assert (Hax1 := CGF.ri_Loc (cD (Good g))).
  destruct Hax1 as (lax1, (lax2, ((Hax_src, Hax_tgt), (eD, HeD)))). *)
    destruct (CGF.step daD (g) (cD (Good g)))
             eqn : HstepD, 
                   (Graph.find_edge (DGF.Info.source (DGF.Config.state rcA))
                                    (DGF.Info.target (DGF.Config.state rcA)))
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
                        (CGF.step daD (g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    apply CGF.step_delta in HstepD'.
    assert (Heq : exists l, Graph.Veq (DGF.Config.loc rcA) l).
    now (exists (DGF.Config.loc rcA)).
    unfold CGF.Location.eq, DGF.Location.eq, CGF.loc_eq in *.
    unfold LocC2D in *.
    destruct HstepD' as (Hstl, Hstst).
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.state (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.state (cD (Good g))))
                             eqn : HtgtD;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption;
      try (now destruct HstepD').
    unfold rcC2D, LocC2D. simpl in *. 
    unfold LocC2D in *.
    assert (HstepD' : CGF.Aom_eq
                        (CGF.step daD (g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    assert (Hdelta := CGF.step_delta daD g (cD (Good g)) sim0 HstepD').
    destruct Hdelta as (Hld, Htd).
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.state (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.state (cD (Good g))))
                             eqn : HtgtD;
      simpl in *;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption; try now destruct Hld.
    assert (HstepD' : CGF.Aom_eq
                        (CGF.step daD (g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    apply (CGF.step_delta daD) in HstepD'.
    destruct HstepD'.
    unfold rcC2D, LocC2D in *; simpl in *.
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.state (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.state (cD (Good g))))
                             eqn : HtgtD;
      simpl in *;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption.
    assert (HstepD' : CGF.Aom_eq
                        (CGF.step daD (g) (cD (Good g))) (CGF.Active sim0))
      by now rewrite HstepD.
    apply (CGF.step_delta daD) in HstepD'.
    destruct HstepD'.
    unfold rcC2D, LocC2D in *; simpl in *.
    destruct (CGF.Config.loc (cD (Good g)))
             eqn : HlocD,
                   (CGF.Info.source (CGF.Config.state (cD (Good g))))
                     eqn : HsrcD,
                           (CGF.Info.target (CGF.Config.state (cD (Good g))))
                             eqn : HtgtD;
      simpl in *;
      try (now exfalso);
      rewrite Hl, Ht;
      try assumption;
      now destruct H.
Qed.

Lemma daC2D_step_compat daD cD : Proper (eq ==> DGF.Config.eq_RobotConf ==> DGF.Aom_eq) (daC2D_step daD cD).
Proof.
intros g1 g2 Hid rcA1 rcA2 HrcA. unfold DGF.Aom_eq, daC2D_step.
assert (Graph.Veq (DGF.Info.source (DGF.Config.state rcA1))
                  (DGF.Info.source (DGF.Config.state rcA2))) by apply HrcA.
assert (Graph.Veq (DGF.Info.target (DGF.Config.state rcA1))
                  (DGF.Info.target (DGF.Config.state rcA2))) by apply HrcA.
assert (Hedge_co := Graph.find_edge_compat
                      (DGF.Info.source (DGF.Config.state rcA1))
                      (DGF.Info.source (DGF.Config.state rcA2)) H
                      (DGF.Info.target (DGF.Config.state rcA1))
                      (DGF.Info.target (DGF.Config.state rcA2)) H0).
assert (HrcD : CGF.Config.eq_RobotConf (cD (Good g1)) (cD (Good g2)))
  by now rewrite Hid.
assert (HrcD' := HrcD).
destruct HrcD' as (HDl, (HDs, HDt)). unfold CGF.loc_eq in *.
destruct (CGF.step daD g1 (cD (Good g1))) eqn:Hstep1,
         (CGF.step daD g2 (cD (Good g2))) eqn:Hstep2,
         (CGF.Config.loc (cD (Good g1))) eqn:HlD1,
         (CGF.Config.loc (cD (Good g2))) eqn:HlD2,
         (DGF.Config.eq_RobotConf_dec rcA1 (rcC2D (cD (Good g1)))) eqn:Heq1,
         (DGF.Config.eq_RobotConf_dec rcA2 (rcC2D (cD (Good g2)))) eqn:Heq2,
         (Graph.find_edge (DGF.Info.source (DGF.Config.state rcA1))
                          (DGF.Info.target (DGF.Config.state rcA1))) eqn:Hedge1,
         (Graph.find_edge (DGF.Info.source (DGF.Config.state rcA2))
                          (DGF.Info.target (DGF.Config.state rcA2))) eqn:Hedge2;
simpl in *;
try rewrite Hstep1; simpl in *;
try (assert (Hst := CGF.step_compat);
     specialize (Hst daD id1 id2 Hid rcD rcD (reflexivity rcD));
     rewrite Hstep1, Hstep2 in Hst; now unfold CGF.Aom_eq in Hst);
try (now exfalso);
assert (Hst := CGF.step_compat);
specialize (Hst daD g1 g2 Hid (cD (Good g1)) (cD (Good g2)) HrcD);
rewrite Hstep1, Hstep2 in Hst; unfold CGF.Aom_eq in Hst;
assert (Hfind := Graph.find_edge_compat
                   (DGF.Info.source (DGF.Config.state rcA1))
                   (DGF.Info.source (DGF.Config.state rcA2)) H
                   (DGF.Info.target (DGF.Config.state rcA1))
                   (DGF.Info.target (DGF.Config.state rcA2)) H0);
rewrite Hedge1, Hedge2 in Hfind; try discriminate;
try assert (HEeq : Graph.Eeq e1 e2) by (apply Hfind);
try (assert (Graph.threshold e1 = Graph.threshold e2)
      by now apply Graph.threshold_compat, HEeq);
try (rewrite HrcD; intuition);
try (rewrite <- HrcD; intuition); intuition.
+ rewrite H1, Hst.
  destruct (Rle_dec dist0 (Graph.threshold e2)) eqn : Hdist; auto.
+ assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
+ assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
+ rewrite Hst.
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
+ rewrite <- H2. assert (Graph.threshold e = Graph.threshold e0)
  by (now apply Graph.threshold_compat).
  rewrite <- H3, Hst in *.
  destruct (Rle_dec (CGF.project_p p) (Graph.threshold e)).
  destruct (Rle_dec (dist0 + CGF.project_p p) (Graph.threshold e)); auto. auto.
+ destruct (Rle_dec (CGF.project_p p) (Graph.threshold e));
  try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
+ destruct (Rle_dec (CGF.project_p p) (Graph.threshold e));
  try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
+ destruct (Rle_dec (CGF.project_p p) (Graph.threshold e));
  try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
+ destruct (Rle_dec (CGF.project_p p) (Graph.threshold e));
  try (destruct (Rle_dec (dist + CGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
+ assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
+ assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
+ assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
+ assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
+ assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
+ assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
+ assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
+ assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
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
simpl. split.
* intros g confA.  assert (HrcD := HrcD' (Good g)).
  assert (HrcC2D_eq : DGF.Config.eq_RobotConf (rcC2D (cD1 (Good g)))
                                              (rcC2D (cD2 (Good g)))).
  { apply rcC2D_compat, HrcD. }
  assert (Hda_cD := CGF.step_da_compat HdaD (reflexivity g) HrcD).
  unfold CGF.Aom_eq in Hda_cD. revert Hda_cD.
  destruct HdaD as (HdaD_G, _).
  specialize (HdaD_G g (rcD2C confA)).
  destruct_match_eq Heq1; destruct_match_eq Heq2; try tauto; intro; subst.
+ destruct (DGF.Config.eq_RobotConf_dec confA (rcC2D (cD1 (Good g))))
    as [HrcD1 | HrcD1],
       (DGF.Config.eq_RobotConf_dec confA (rcC2D (cD2 (Good g))))
      as [HrcD2 | HrcD2],
         (CGF.step dad1 g (cD1 (Good g))) as [dist1 | iso1],
             (CGF.step dad2 g (cD2 (Good g))) as [dist2 | iso2],
             (CGF.Config.loc (cD1 (Good g))) as [v1 | e1 p1] eqn:Hc1,
             (CGF.Config.loc (cD2 (Good g))) as [v2 | e2 p2] eqn:Hc2,
             (Graph.find_edge (DGF.Info.source (DGF.Config.state confA))
                              (DGF.Info.target (DGF.Config.state confA)));
    try rewrite Hda_cD;
    unfold CGF.loc_eq in *;
    try (destruct HrcD as (Hl,_); now rewrite Hc1, Hc2 in Hl).
    - destruct (Rle_dec dist1 (Graph.threshold e1)); unfold DGF.Aom_eq.
      ++ destruct HrcD as (Hl,_). rewrite Hc1, Hc2 in Hl. destruct Hl as (He, Hp). subst p1.
         assert (Hth : (Graph.threshold e1) = (Graph.threshold e2)) by apply Graph.threshold_compat, He.
         rewrite Hth.
         destruct (Rle_dec (CGF.project_p p2) (Graph.threshold e2)); trivial; [].
         destruct HrcC2D_eq as (Hl, _). simpl in Hl.
         rewrite Hc1, Hc2 in Hl. simpl in Hl.
         now destruct_match.
      ++ destruct (Rle_dec (CGF.project_p p1) (Graph.threshold e1)) eqn : Hp1;
         destruct ( Rle_dec (dist0 + CGF.project_p p1) (Graph.threshold e1));
         destruct (Rle_dec (CGF.project_p p2) (Graph.threshold e2)) eqn : Hp2;
         destruct (Rle_dec (dist0 + CGF.project_p p2) (Graph.threshold e2));
         try easy;
         destruct HrcD as (HlrcD, _);
         rewrite Hc1, Hc2 in HlrcD;
         simpl in *;
         destruct HlrcD as (He, Hp).
         destruct n0.
         now rewrite <- Hp, (Graph.threshold_compat e2 e1 (symmetry He)) .
         destruct n0.
         now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
         destruct n0.
         now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
         destruct n1.
         now rewrite <- Hp, (Graph.threshold_compat e2 e1 (symmetry He)) .
         destruct n0.
         now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
         destruct n0.
         now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
    - destruct (Rle_dec (CGF.project_p p1) (Graph.threshold e1)) eqn : Hp1;
        destruct ( Rle_dec (dist0 + CGF.project_p p1) (Graph.threshold e1));
        destruct (Rle_dec (CGF.project_p p2) (Graph.threshold e2)) eqn : Hp2;
        destruct (Rle_dec (dist0 + CGF.project_p p2) (Graph.threshold e2));
        try easy;
        destruct HrcD as (HlrcD, _);
        rewrite Hc1, Hc2 in HlrcD;
        simpl in *;
        destruct HlrcD as (He, Hp).
      destruct n.
      now rewrite <- Hp, (Graph.threshold_compat e2 e1 (symmetry He)) .
      destruct n.
      now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
      destruct n.
      now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
      destruct n0.
      now rewrite <- Hp, (Graph.threshold_compat e2 e1 (symmetry He)) .
      destruct n.
      now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
      destruct n.
      now rewrite Hp, (Graph.threshold_compat e1 e2 He) .
    - destruct HrcD2.
      now rewrite <- HrcC2D_eq.
    - destruct HrcD2.
      now rewrite <- HrcC2D_eq.
    - destruct HrcD2.
      now rewrite <- HrcC2D_eq.
    - destruct HrcD1.
      now rewrite HrcC2D_eq.
    - destruct HrcD1.
      now rewrite HrcC2D_eq.
    - destruct HrcD1.
      now rewrite HrcC2D_eq.
  + destruct (DGF.Config.eq_RobotConf_dec confA (rcC2D (cD1 (Good g)))) eqn : Hca1,
             (DGF.Config.eq_RobotConf_dec confA (rcC2D (cD2 (Good g)))) eqn : Hca2.
    now rewrite Hda_cD.
    now destruct n; rewrite <- HrcC2D_eq.
    now destruct n; rewrite HrcC2D_eq.
    easy.
    * intros b.
      rewrite (CGF.relocate_byz_compat HdaD (reflexivity b) ).
      reflexivity.
Qed.

Definition daD2C_step daA (cA : ConfigA.t) g rc :=
  if CGF.Config.eq_RobotConf_dec (rc) (rcD2C (cA (Good g)))
  then
    match DGF.step daA g (cA (Good g)) with
    | DGF.Active sim => CGF.Active sim
    | DGF.Moving b => if b then CGF.Moving 1%R else CGF.Moving 0%R
    end
  else
    CGF.Moving 0%R.
    
Lemma daD2C_step_delta : forall daA cA g Rconfig sim,
  CGF.Aom_eq (daD2C_step daA cA (g) Rconfig) (CGF.Active sim) ->
  (∃ l : Graph.V, CGF.Location.eq (Rconfig) (CGF.Loc l))
  ∧ CGF.Location.eq (Rconfig) (CGF.Info.target (CGF.Config.state (Rconfig))).
Proof.
  intros daA cA g rcD sim Hstep. unfold daD2C_step in *.
  destruct (DGF.step daA (g) (cA (Good g))) eqn : HstepA;
  destruct ( CGF.Config.eq_RobotConf_dec (rcD) (rcD2C (cA (Good g)))); try easy.
  - destruct dist; easy.
  - assert (HstepA' : DGF.Aom_eq
                       (DGF.step daA (g) (cA (Good g))) (DGF.Active sim0))
          by now rewrite HstepA.
    unfold rcD2C in *; simpl in *.
    apply (DGF.step_delta daA) in HstepA'.
    split.
    destruct e; simpl in *.
    exists (cA (Good g)); assumption.
    destruct e, H0; simpl in *.
    rewrite H1, H. cbn in *. now rewrite HstepA'.
Qed.

Lemma daD2C_step_compat daA cA : Proper (eq ==> CGF.Config.eq_RobotConf ==> CGF.Aom_eq)
                                        (daD2C_step daA cA).
Proof. repeat intro. subst. unfold daD2C_step. destruct (CGF.Config.eq_RobotConf_dec x0 (rcD2C (cA (Good y)))), (CGF.Config.eq_RobotConf_dec y0 (rcD2C (cA (Good y)))); try (rewrite H0 in *); try easy.
Qed.

Lemma daD2C_step_flexibility : forall daA cA g rconf r,
  CGF.Aom_eq (daD2C_step daA cA g rconf) (CGF.Moving r) -> (0 <= r <= 1)%R.
Proof.
  intros daA cA g rconf r.
  unfold daD2C_step.
  destruct (CGF.Config.eq_RobotConf_dec rconf (rcD2C (cA (Good g)))).
  destruct (DGF.step daA g (cA (Good g))); simpl.
+ destruct dist; intros Hm; unfold CGF.Aom_eq in *; subst; lra.
+ intuition.
+ intros; simpl in *; lra.
Qed.

(* TODO : trouver une définition vrai, ou rajouter des axioms car la sinon c'est pas vrai.*)
Definition daD2C (daA : DGF.demonic_action) (cA : DGF.Config.t) : CGF.demonic_action.
refine {| CGF.relocate_byz := fun b => RobotConfD2C (DGF.relocate_byz daA b);
          CGF.step := fun g rc => daD2C_step daA cA g rc |}.
Proof.
  + apply daD2C_step_delta.
  + apply daD2C_step_compat.
  + apply daD2C_step_flexibility.
Defined.

Instance daD2C_compat : Proper (DGF.da_eq ==> DGF.Config.eq ==> CGF.da_eq) daD2C.
Proof.
intros daA1 daA2 HdaA cA1 cA2 HrcA.
unfold daD2C, daD2C_step; split; simpl.
+ intros g rc. destruct HdaA as (HdaA_G,_).
  specialize (HdaA_G g (cA1 (Good g))).
  assert (Hda' : DGF.Aom_eq (DGF.step daA2 g (cA1 (Good g)))
                            (DGF.step daA2 g (cA2 (Good g)))).
  apply (DGF.step_compat daA2 _ _ (reflexivity g) _ _ (HrcA (Good g)) ).
  rewrite Hda' in HdaA_G.
  destruct (CGF.Config.eq_RobotConf_dec rc (rcD2C (cA1 (Good g)))) eqn : HrcD1, 
           (CGF.Config.eq_RobotConf_dec rc (rcD2C (cA2 (Good g)))) eqn : HrcD2.
  * destruct (DGF.step daA1 g (cA1 (Good g))), (DGF.step daA2 g (cA2 (Good g))); unfold DGF.Aom_eq in *.
    - destruct dist, dist0; now unfold CGF.Aom_eq.
    - now exfalso.
    - now exfalso.
    - destruct (CGF.Location.eq_dec (CGF.Config.loc rc)
                                  (CGF.Info.target (CGF.Config.state rc))).
      now rewrite HdaA_G.
      now unfold DGF.Aom_eq.
  * assert (e' := e). rewrite (HrcA (Good g)) in e'. contradiction.
  * assert (e' := e). rewrite <- (HrcA (Good g)) in e'. contradiction.
  * now unfold DGF.Aom_eq.
+ destruct HdaA as (_, HdaA_B). intros b; specialize (HdaA_B b).
  auto.
Qed.


Lemma daD2C2D : forall (d: DGF.demonic_action) c,
    CGF.group_good_def (ConfigD2C c) ->
    forall g, DGF.Aom_eq (DGF.step d g (c (Good g))) (DGF.step (daC2D (daD2C d c) (ConfigD2C c)) g (c (Good g))).
Proof.
  intros d c Hc. unfold daC2D. unfold daD2C. simpl. unfold DGF.da_eq.
  simpl in *.
  unfold daD2C_step, daC2D_step.
  simpl.
  intros g.
  destruct (DGF.Config.eq_RobotConf_dec (c (Good g)) (rcC2D (ConfigD2C c (Good g)))).
  - destruct (CGF.Config.eq_RobotConf_dec (ConfigD2C c (Good g)) (rcD2C (c (Good g)))).
    destruct (DGF.step d g (c (Good g))) eqn : Hstep.
    + destruct dist;
      destruct (Graph.find_edge (DGF.Info.source (DGF.Config.state (c (Good g))))
                                (DGF.Info.target (DGF.Config.state (c (Good g)))))
               eqn : Hedge; try easy.
      destruct (Rle_dec 1 (Graph.threshold e1)).
      generalize (Graph.threshold_pos e1).
      intros.
      lra.
      reflexivity.
      destruct (Hc g) as (Hri,(Ha, (Hb, He))).
      destruct (Hri g) as  (source, (target, (Hs, Ht))).
      specialize (He source target).
      destruct He; try unfold ConfigD2C, RobotConfD2C; simpl;
        unfold rcD2C, ConfigD2C, RobotConfD2C in e0;
        repeat destruct e0 as (?, e0);
        try easy.
      unfold ConfigD2C in *; simpl in *.
      assert (Hedge' := Graph.find_edge_compat _ _ Hs _ _ Ht). 
      now rewrite H, Hedge in Hedge'.
      destruct (Rle_dec 0 (Graph.threshold e1)); try easy.
      generalize (Graph.threshold_pos e1).
      intros.
      lra.
    + reflexivity.
    + destruct n.
      now unfold ConfigD2C, rcD2C, RobotConfD2C.
  - destruct n.     
    unfold rcC2D, LocC2D, ConfigD2C, RobotConfD2C; simpl.
    now repeat split; simpl.
Qed.


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
  exists (daD2C da c).
  intros id.
  assert ( HeqDd : CGF.Config.eq_RobotConf
                     {|
                       CGF.Config.loc := CGF.Loc (DGF.Config.loc (c id));
                       CGF.Config.state := {|
                                            CGF.Info.source := CGF.Loc
                                                                 (DGF.Info.source
                                                                    (DGF.Config.state
                                                                       (c id)));
                                            CGF.Info.target := CGF.Loc
                                                                 (DGF.Info.target
                                                                    (DGF.Config.state
                                                                       (c id))) |} |}
                     {|
                       CGF.Config.loc := CGF.Loc (DGF.Config.loc (c id));
                       CGF.Config.state := {|
                                            CGF.Info.source := CGF.Loc
                                                                 (DGF.Info.source
                                                                    (DGF.Config.state
                                                                       (c id)));
                                            CGF.Info.target := CGF.Loc
                                                                 (DGF.Info.target
                                                                    (DGF.Config.state
                                                                       (c id))) |} |});
    simpl in *.
  repeat try split; simpl; reflexivity.
  destruct id as [g|b].
  rewrite HDGF. unfold DGF.round, CGF.round.
  simpl in *.
  unfold ConfigD2C, RobotConfD2C, daD2C_step.
  simpl in *.
  destruct (DGF.step da g (c (Good g))) eqn : Hstep;
  destruct (CGF.Config.eq_RobotConf_dec
          {|
          CGF.Config.loc := CGF.Loc (c (Good g));
          CGF.Config.state := {|
                              CGF.Info.source := CGF.Loc
                                                   (DGF.Info.source
                                                      (DGF.Config.state (c (Good g))));
                              CGF.Info.target := CGF.Loc
                                                   (DGF.Info.target
                                                      (DGF.Config.state (c (Good g)))) |} |}
          (rcD2C (c (Good g))));
  try destruct dist; simpl in *;
  try (destruct (Rdec 1 0), (Rdec 1 1); try lra;
  now destruct (Graph.Veq_dec (DGF.Info.target (DGF.Config.state (c (Good g)))) (c (Good g))));
  try (destruct (Rdec 0 0); try lra;
       try (now destruct (Graph.Veq_dec (DGF.Info.target (DGF.Config.state (c (Good g)))) (c (Good g))))).
  rewrite HDGF.
  unfold DGF.round, CGF.round; simpl;
    unfold ConfigD2C, RobotConfD2C, daD2C, daD2C_step; reflexivity.
Qed.



Theorem graph_equivC2D : forall (c c': CGF.Config.t) (rbg:CGF.robogram) (da : CGF.demonic_action),
    (CGF.group_good_def c) ->
    CGF.Config.eq c' (CGF.round rbg da c) ->
    exists da', DGF.Config.eq (ConfigC2D c') (DGF.round (rbgC2D rbg) da' (ConfigC2D c)).
Proof.
  intros c c' rbg da Hri HCGF. exists (daC2D da c).
  intro id.
  assert (Heq_rcD: CGF.Config.eq_RobotConf (c id) ({|
                                                      CGF.Config.loc := CGF.Config.loc (c id);
                                                      CGF.Config.state := {|
                                                                           CGF.Info.source := CGF.Info.source
                                                                                                (CGF.Config.state (c id));
                                                                           CGF.Info.target := CGF.Info.target
                                                                                                (CGF.Config.state (c id)) |} |})) by (
                                                                                                                                      repeat (try split; simpl) ; reflexivity); destruct id as [g|b].
    assert (HstepD_compat := CGF.step_compat da _ _ (reflexivity g)
                                             (c (Good g))
                                             ({| CGF.Config.loc := CGF.Config.loc (c (Good g));
                                                 CGF.Config.state := {|
                                                                      CGF.Info.source := CGF.Info.source (CGF.Config.state (c (Good g)));
                                                                      CGF.Info.target := CGF.Info.target (CGF.Config.state (c (Good g))) |} |})
                                             Heq_rcD);
    destruct (CGF.step da g
                       {| CGF.Config.loc := CGF.Config.loc (c (Good g));
                          CGF.Config.state := {|
                                               CGF.Info.source := CGF.Info.source (CGF.Config.state (c (Good g)));
                                               CGF.Info.target := CGF.Info.target (CGF.Config.state (c (Good g))) |} |})
             eqn : HstepD'; try (now exfalso);
      unfold DGF.round, CGF.round in *; specialize (HCGF (Good g));
        unfold CGF.loc_eq in *;
        destruct (CGF.step da g (c (Good g))) eqn : HstepD,
                                               (DGF.step (daC2D da c) g (ConfigC2D c (Good g))) eqn : HstepA; try (now exfalso);
          unfold daC2D in *; simpl in *;
            unfold RobotConfC2D, daC2D_step(* , ConfigC2D, LocC2D *) in *;
            repeat try (split; simpl);
            try (destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e)));
                 unfold CGF.ri_loc_def in *;
                 destruct (Hrid g) as (v1, (v2, (Hv1, Hv2)));
                 destruct (CGF.Config.loc (c (Good g))) as [lld| eld pld] eqn : HlocD;
                 destruct (CGF.Info.target (CGF.Config.state (c (Good g)))) as [ltd | etd ptd] eqn : HtgtD;
                 destruct (CGF.Info.source (CGF.Config.state (c (Good g)))) as [lsd | esd psd] eqn : HsrcD;
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
                           destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
                           destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
                           try (now simpl in * );
                           try (now (destruct (DGF.Config.eq_RobotConf_dec _);
                                     try discriminate;
                                     destruct n; unfold rcC2D, LocC2D; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl))));
                try (now (try (now simpl in * );
                          destruct dist eqn : Hbool;
                          destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
                          destruct (CGF.Info.source (CGF.Config.state (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
                          destruct (CGF.Info.target (CGF.Config.state (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
                          destruct (DGF.Config.eq_RobotConf_dec _);
                          try discriminate;
                          destruct n; unfold rcC2D, LocC2D; rewrite HlocD, HtgtD, HsrcD; repeat try split; try now simpl)).
  + unfold ConfigC2D, RobotConfC2D, LocC2D in *; simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *;
      destruct (CGF.Config.loc (c (Good g))) eqn : Habsurd;
      rewrite HlocD in Habsurd; try discriminate.
    destruct dist1 eqn : Hbool.
  - destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
      destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
      destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
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
                    DGF.Config.state := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
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
      assert (HstepD_aux : CGF.Aom_eq (CGF.step da (g) (c (Good g)))
                                      (CGF.Moving dist0))
        by now rewrite HstepD.
      assert (Hg := CGF.step_flexibility da (g) (c (Good g)) dist0 HstepD_aux);
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
      rewrite Graph.find_edge_Some in Hsol.
      destruct Hsol as (Hsol, Htol).
      easy.
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
      destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
      destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
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
                         DGF.Config.state := {|
                                              DGF.Info.source := lsd;
                                              DGF.Info.target := ltd |} |} 
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
    rewrite Graph.find_edge_Some in Hsol;
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
    assert (HstepD_aux : CGF.Aom_eq (CGF.step da (g) (c (Good g)))
                                    (CGF.Moving dist0))
      by now rewrite HstepD.
    assert (Hf := CGF.step_flexibility da (g) (c (Good g)) dist0 HstepD_aux).
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
        rewrite Graph.find_edge_Some in Hmi_0;
        destruct Hmi_0 as (Hmi_s, Hmi_t);
        destruct dist1 eqn : Hbool;
        destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
        destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
        destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
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
               DGF.Config.state := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
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
                 DGF.Config.state := {|
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
                       DGF.Config.state := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
                     (rcC2D (c (Good g))));
           discriminate.
         ** destruct (Rle_dec (CGF.project_p pld) (Graph.threshold eld)).
      -- destruct(DGF.Config.eq_RobotConf_dec
                    {|
                      DGF.Config.loc := Graph.src eld;
                      DGF.Config.state := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
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
                       DGF.Config.state := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |}
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
      assert (HstepD_aux : CGF.Aom_eq (CGF.step da (g) (c (Good g)))
                                      (CGF.Moving dist0))
        by now rewrite HstepD.
      assert (Hf_aux := CGF.step_flexibility da (g) (c (Good g))
                                             dist0 HstepD_aux).
      lra.
      assert (Hl := CGF.project_p_image pld).
      rewrite <- (CGF.inv_pro (CGF.project_p pld + dist0)) in *.
      destruct (Rle_dec (CGF.project_p pld + dist0) (Graph.threshold eld')).
      -- now apply Graph.src_compat.
      -- destruct(DGF.Config.eq_RobotConf_dec
                    {|
                      DGF.Config.loc := Graph.src eld;
                      DGF.Config.state := {| DGF.Info.source := lsd; DGF.Info.target := ltd |} |} (rcC2D (c (Good g)))).
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
      assert (HstepD_aux : CGF.Aom_eq (CGF.step da (g) (c (Good g)))
                                      (CGF.Moving dist0))
        by now rewrite HstepD.
      assert (Hf_aux := CGF.step_flexibility da (g) (c (Good g))
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
        destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
        destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
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
        destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
        destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
        try discriminate;
        simpl in *;
        try (destruct (Rle_dec 1 (CGF.project_p pld + dist0)); simpl in *;
             rewrite HlocD, HsrcD, HtgtD in *; now simpl in * ); try now simpl in *.
    + destruct dist1 eqn : Hbool;
        destruct (CGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
        destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
        destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
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
        destruct (CGF.Info.target (CGF.Config.state (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
        destruct (CGF.Info.source (CGF.Config.state (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
        try discriminate;
        simpl in *;
        try (destruct (Rle_dec 1 (CGF.project_p pld + dist0)); simpl in *;
             rewrite HlocD, HsrcD, HtgtD in *; now simpl in * ); try now simpl in *.
    + unfold ConfigC2D, RobotConfC2D, rcC2D, LocC2D in *; rewrite HlocD, HsrcD, HtgtD in *.
      destruct (DGF.Config.eq_RobotConf_dec
                  {|
                    DGF.Config.loc := lld;
                    DGF.Config.state := {|
                                         DGF.Info.source := lsd;
                                         DGF.Info.target := ltd |} |}
                  {|
                    DGF.Config.loc := lld;
                    DGF.Config.state := {|
                                         DGF.Info.source := lsd;
                                         DGF.Info.target := ltd |} |});
        try (destruct (Graph.find_edge lsd ltd));
        try destruct (Rle_dec dist0 (Graph.threshold e0));
        try easy.
    + destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
        try destruct (Graph.find_edge
                        (LocC2D (CGF.Info.source (CGF.Config.state (c (Good g)))))
                        (LocC2D (CGF.Info.target (CGF.Config.state (c (Good g))))));
        try destruct (Rle_dec dist0 (Graph.threshold e0));
        try easy.
    + destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g))));
        try destruct (Graph.find_edge
                        (LocC2D (CGF.Info.source (CGF.Config.state (c (Good g)))))
                        (LocC2D (CGF.Info.target (CGF.Config.state (c (Good g))))));
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
    + simpl in *.
      destruct (CGF.Config.loc (c' (Good g))) eqn : HlocD'; try now rewrite HlocD in Hloc.
    + simpl in *.
      rewrite Hloc , HlocD in *.
      easy.
    + simpl in *.
      now rewrite Hsrc, HlocD in *.
    + simpl in *.
      now rewrite Hsrc, HlocD in *.
    + simpl in *.
      rewrite Htgt.
      simpl.
      unfold LocC2D.
      destruct (CGF.Config.loc (c' (Good g))) eqn : HlocD'; try now rewrite HlocD in Hloc.    
      destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Good g)) (rcC2D (c (Good g)))).
      assert (HstepA' : DGF.Aom_eq (DGF.Active sim0) (DGF.Active sim1))
        by now rewrite HstepA.
      unfold DGF.Aom_eq in HstepA'.
      destruct (CGF.pgm rbg
                        (DGF.Spect.from_config
                           (DGF.Config.map (DGF.Config.app sim1) (ConfigC2D c)))
                        (CGF.Loc (Bijection.section (Iso.sim_V sim1) lld))
               )eqn : Hr.
      simpl.
      assert (Hr' :=
                CGF.pgm_compat
                  rbg
                  (DGF.Spect.from_config (DGF.Config.map (DGF.Config.app sim1)
                                                         (ConfigC2D c)))
                  (CGF.Spect.from_config (CGF.Config.map (CGF.apply_sim sim0)
                                                         c))).
      assert (CGF.Spect.eq (DGF.Spect.from_config (DGF.Config.map (DGF.Config.app sim1)
                                                                  (ConfigC2D c)))
                           (CGF.Spect.from_config (CGF.Config.map (CGF.apply_sim sim0)
                                                                  c))).
      unfold DGF.Spect.from_config, CGF.Spect.from_config.
      assert (ConfigA.eq (DGF.Config.map (DGF.Config.app sim1) (ConfigC2D c))
                         (CGF.projectS (CGF.Config.map (CGF.apply_sim sim0) c))).
      unfold DGF.Config.map, DGF.Config.app, CGF.Config.app, CGF.Config.map, CGF.projectS,
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
        destruct (Rle_dec (Bijection.section (Iso.sim_T sim0) (CGF.project_p p))
                          (Graph.threshold (Bijection.section (Iso.sim_E sim0) e0))).
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
      destruct (CGF.Info.source (CGF.Config.state (c id))).
      f_equiv.
      apply (symmetry HstepA').
      rewrite <- CGF.inv_pro.
      unfold LocC2D in *.
      assert (Hcroiss := Iso.sim_croiss sim0).
      destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
        destruct (Rle_dec (Bijection.section (Iso.sim_T sim0) (CGF.project_p p))
                          (Graph.threshold (Bijection.section (Iso.sim_E sim0) e0))).
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
      destruct (CGF.Info.target (CGF.Config.state (c id))).
      f_equiv.
      apply (symmetry HstepA').
      rewrite <- CGF.inv_pro.
      unfold LocC2D in *.
      assert (Hcroiss := Iso.sim_croiss sim0).
      destruct (Rle_dec (CGF.project_p p) (Graph.threshold e0));
        destruct (Rle_dec (Bijection.section (Iso.sim_T sim0) (CGF.project_p p))
                          (Graph.threshold (Bijection.section (Iso.sim_E sim0) e0))).
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
      specialize (Hr' H (CGF.Loc (Bijection.section (Iso.sim_V sim1) lld))
                      (CGF.Loc (Bijection.section (Iso.sim_V sim0) lld))).
      rewrite Hr in Hr'.
      unfold CGF.Location.eq, CGF.loc_eq in Hr'.
      assert (Graph.Veq (Bijection.section (Iso.sim_V sim1) lld)
                        (Bijection.section (Iso.sim_V sim0) lld)).
      f_equiv; apply (symmetry HstepA'). 
      specialize (Hr' H0).
      destruct (CGF.pgm rbg
                        (CGF.Spect.from_config (CGF.Config.map (CGF.apply_sim sim0) c))
                        (CGF.Loc (Bijection.section (Iso.sim_V sim0) lld)));
        try (now exfalso).
      now rewrite HstepA', Hr'.
      assert (Hrange :=
                CGF.pgm_range
                  rbg
                  (DGF.Spect.from_config (DGF.Config.map (DGF.Config.app sim1)
                                                         (ConfigC2D c)))
                  (CGF.Loc (Bijection.section (Iso.sim_V sim1) lld))
                  (Bijection.section (Iso.sim_V sim1) lld) (reflexivity _)).
      destruct Hrange as (lrange, (_, (Hlrange, _))). 
      simpl.
      now rewrite Hlrange in Hr.
      easy.
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
                               (CGF.Mvt (Bijection.section (Iso.sim_E sim0) eld)
                                        (CGF.project_p_inv
                                           (Bijection.section (Iso.sim_T sim0)
                                                                (CGF.project_p pld))))
                     with
                     | CGF.Loc l => Bijection.retraction (Iso.sim_V sim0) l
                     | CGF.Mvt e _ => Graph.src e
                     end) (CGF.Mvt eld pld)).
      simpl in *. now rewrite HlocD in *.
      destruct (CGF.Location.eq_dec
                  (CGF.Loc
                     match
                       CGF.pgm rbg
                               (CGF.Spect.from_config
                                  (CGF.Config.map (CGF.apply_sim sim0) c))
                               (CGF.Mvt (Bijection.section (Iso.sim_E sim0) eld)
                                        (CGF.project_p_inv
                                           (Bijection.section (Iso.sim_T sim0)
                                                                (CGF.project_p pld))))
                     with
                     | CGF.Loc l => Bijection.retraction (Iso.sim_V sim0) l
                     | CGF.Mvt e _ => Graph.src e
                     end) (CGF.Mvt eld pld)).
      now simpl in *.
      simpl in *.
      assert (HstepD_aux : CGF.Aom_eq
                             (CGF.step da (g) (c (Good g))) (CGF.Active sim0))
        by now rewrite HstepD.
      assert (Hdelta := CGF.step_delta da g (c (Good g)) sim0 HstepD_aux).
      destruct Hdelta as ((lf, Hf),_).
      rewrite HlocD in Hf.
      now simpl in *.
    + specialize (HCGF (Byz b)).
      unfold CGF.round, DGF.round in *.
      simpl in *.
      unfold ConfigC2D.      
      now rewrite HCGF.
Qed.

End GraphEquivalence.


                                                            (*  unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
        destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
        destruct (CGF.Info.source (CGF.Config.state (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
        destruct (CGF.Info.source (CGF.Config.state (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
        destruct (CGF.Info.target (CGF.Config.state (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
        destruct (CGF.Info.target (CGF.Config.state (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
        try (now exfalso);
        try now simpl in *.
    + unfold ConfigC2D, RobotConfC2D, LocC2D in *; rewrite HlocD in *.
      destruct dist1 eqn : Hbool;
        destruct (CGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
        destruct (CGF.Info.source (CGF.Config.state (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
        destruct (CGF.Info.source (CGF.Config.state (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
        destruct (CGF.Info.target (CGF.Config.state (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
        destruct (CGF.Info.target (CGF.Config.state (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
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
        destruct (CGF.Info.source (CGF.Config.state (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
        destruct (CGF.Info.source (CGF.Config.state (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
        destruct (CGF.Info.target (CGF.Config.state (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
        destruct (CGF.Info.target (CGF.Config.state (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
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
        destruct (CGF.Info.source (CGF.Config.state (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
        destruct (CGF.Info.source (CGF.Config.state (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
        destruct (CGF.Info.target (CGF.Config.state (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
        destruct (CGF.Info.target (CGF.Config.state (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
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
        destruct (CGF.Info.source (CGF.Config.state (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
        destruct (CGF.Info.source (CGF.Config.state (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
        destruct (CGF.Info.target (CGF.Config.state (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
        destruct (CGF.Info.target (CGF.Config.state (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
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
        destruct (CGF.Info.source (CGF.Config.state (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
        destruct (CGF.Info.source (CGF.Config.state (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
        destruct (CGF.Info.target (CGF.Config.state (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
        destruct (CGF.Info.target (CGF.Config.state (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
        try (now exfalso);
        try (now simpl in * );
        destruct Htgt as (Hte, Htp);
        assert (Htt : Graph.threshold etd = Graph.threshold etd') by (now apply Graph.threshold_compat);
        rewrite Htt, Htp;
        destruct (Rle_dec (CGF.project_p ptd) (Graph.threshold etd'));
        try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
    + 


destruct (DGF.Config.eq_RobotConf_dec (ConfigC2D c (Byz b)) (rcC2D (c (Byz b))));
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
    + 
*)