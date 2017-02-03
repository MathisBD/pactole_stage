(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

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
Require Import Pactole.AtomicGraphFormalism.
Require Import Pactole.DiscreteGraphFormalism.



Definition ConfigA2D (confA : AGF.Config.t) : DGF.Config.t :=
  fun id =>
    {| DGF.Config.loc := DGF.Loc (AGF.Config.loc (confA id));
       DGF.Config.robot_info := 
      {| DGF.Config.source := DGF.Loc (AGF.Config.source (AGF.Config.robot_info (confA id)));
         DGF.Config.target := DGF.Loc (AGF.Config.target (AGF.Config.robot_info (confA id))) |} |}.

Instance configA2D_compat : Proper (AGF.Config.eq ==> DGF.Config.eq) ConfigA2D.
Proof.
intros ca1 ca2 Hca id. unfold ConfigA2D. repeat try (split;simpl); apply Hca.
Qed.

Definition LocD2A (locD : DGF.Location.t) : AGF.Location.t :=
      match locD with
        | DGF.Loc l => l
        | DGF.Mvt e p => if Rle_dec (DGF.project_p p) (Graph.threshold e) then Graph.src e else Graph.tgt e
      end.

Definition ConfigD2A (ConfD : DGF.Config.t) : AGF.Config.t := 
  fun id =>
    {| AGF.Config.loc := LocD2A (DGF.Config.loc (ConfD id));
       AGF.Config.robot_info := 
       {| AGF.Config.source := LocD2A (DGF.Config.source (DGF.Config.robot_info (ConfD id)));
          AGF.Config.target := LocD2A (DGF.Config.target (DGF.Config.robot_info (ConfD id))) |} |}.

Instance LocD2A_compat : Proper (DGF.Location.eq ==> AGF.Location.eq) LocD2A.
Proof.
intros ld1 ld2 Hld. unfold LocD2A, AGF.Location.eq, DGF.Location.eq, DGF.loc_eq in *.
destruct ld1, ld2; auto; try (now exfalso).
destruct Hld, (Rle_dec (DGF.project_p p) (Graph.threshold e)),
              (Rle_dec (DGF.project_p p0) (Graph.threshold e0)).
apply Graph.src_compat; assumption. rewrite H0, H in r; contradiction.
rewrite <- H0, <- H in r; contradiction. apply Graph.tgt_compat; assumption.
Qed.

Instance ConfigD2A_compat : Proper (DGF.Config.eq ==> AGF.Config.eq) ConfigD2A.
Proof.
intros cd1 cd2 Hcd id. unfold ConfigD2A. repeat try(split;simpl); apply LocD2A_compat, Hcd.
Qed.

Lemma AGF_DGF_AGF_Config : forall confA: AGF.Config.t,  AGF.Config.eq confA
                                                                     (ConfigD2A (ConfigA2D confA)).
Proof.
intros confA id. unfold ConfigD2A, ConfigA2D. now repeat try (split; simpl).
Qed.


(*
Lemma DGFS_AGF_DGFS_Config : forall SconfD : DGF.Config.t, 
      DGF.Spect.eq (DGF.Spect.from_config SconfD) 
      (DGF.Spect.from_config (ConfigA2D (ConfigD2A SconfD))).
Proof.
intros SconfD. unfold ConfigA2D, ConfigD2A. 
assert DGF.Config.eq (Sconf *)

Lemma spect_equiv : AGF.Spect.t = DGF.Spect.t.
Proof. unfold AGF.Spect.t, DGF.Spect.t. reflexivity. Qed.


Definition rbgA2D (rbgA : AGF.robogram) : DGF.robogram.
  refine {| DGF.pgm := fun s => DGF.Loc ((AGF.pgm rbgA) s) |}.
Proof.
+ intros SD1 SD2 HSD. unfold DGF.Location.eq, DGF.loc_eq, DGF.Spect.eq in *.
  apply (AGF.pgm_compat rbgA). now unfold AGF.Spect.eq.
+ intros s. now exists (AGF.pgm rbgA s).
+ intros s g l Hl. assert (Hpgm := AGF.pgm_range rbgA s l g Hl).
  destruct Hpgm as (l', (e,(Heq, Hedge))).
  exists l', e. split. now rewrite Heq. assumption.
Defined.

Instance rbgA2D_compat : Proper (AGF.req ==> DGF.req) rbgA2D.
Proof.
intros ra1 ra2 Hra. unfold rbgA2D, DGF.req. intros sd1 sd2 Hsd. simpl.
fold AGF.Location.eq.  apply Hra. now unfold DGF.Spect.eq, AGF.Spect.eq in *.
Qed.

Definition rbgD2A (rbgD : DGF.robogram) : AGF.robogram.
refine {| AGF.pgm := fun s => LocD2A ((DGF.pgm rbgD) s) |}.
Proof.
+ intros SA1 SA2 HSA. unfold AGF.Location.eq, AGF.Spect.eq in *.
  apply LocD2A_compat. apply (DGF.pgm_compat rbgD). now unfold DGF.Spect.eq.
+ intros s l g Hl. assert (Hrange := DGF.pgm_range rbgD s g l Hl).
  unfold LocD2A.
  destruct Hrange as (l', (e, (Heq,Hedge))).
  rewrite Heq.
  exists l', e. now split.
Defined.

Instance rbgD2A_compat : Proper (DGF.req ==> AGF.req) rbgD2A.
Proof.
intros rd1 rd2 Hrd. unfold rbgD2A, AGF.req. intros sa1 sa2 Hsa. simpl.
apply LocD2A_compat. apply Hrd. now unfold DGF.Spect.eq, AGF.Spect.eq in *.
Qed.

Lemma RA_RD_RA_equiv : forall ra, AGF.req ra (rbgD2A (rbgA2D ra)).
Proof.
intros ra. unfold rbgA2D, rbgD2A, AGF.req. simpl.
apply (AGF.pgm_compat ra).
Qed.


Definition rcD2A  (rcD : DGF.Config.RobotConf) : AGF.Config.RobotConf :=
{| AGF.Config.loc := LocD2A (DGF.Config.loc rcD);
        AGF.Config.robot_info := 
          {| AGF.Config.source := LocD2A (DGF.Config.source (DGF.Config.robot_info rcD));
             AGF.Config.target := LocD2A (DGF.Config.target (DGF.Config.robot_info rcD)) |} |}.

Instance rcD2A_compat : Proper (DGF.Config.eq_RobotConf ==> AGF.Config.eq_RobotConf) rcD2A.
Proof.
intros rcD1 rcD2 HrcD. unfold rcD2A. repeat try (split;simpl); f_equiv; apply HrcD.
Qed.

Definition rcA2D (rcA : AGF.Config.RobotConf) : DGF.Config.RobotConf :=
{| DGF.Config.loc := DGF.Loc (AGF.Config.loc rcA);
        DGF.Config.robot_info := 
          {| DGF.Config.source := DGF.Loc (AGF.Config.source (AGF.Config.robot_info rcA));
             DGF.Config.target := DGF.Loc (AGF.Config.target (AGF.Config.robot_info rcA)) |} |}.

Instance rcA2D_compat : Proper (AGF.Config.eq_RobotConf ==> DGF.Config.eq_RobotConf) rcA2D.
Proof.
intros rcA1 rcA2 HrcA. unfold rcA2D. repeat try (split;simpl); apply HrcA.
Qed.


Definition daD2A (daD : DGF.demonic_action) (cD : DGF.Config.t): AGF.demonic_action.
refine {|
  AGF.relocate_byz := fun b => LocD2A ((DGF.relocate_byz daD) b);
  AGF.step := fun id rcA => if AGF.Config.eq_Robotconf_dec rcA (rcD2A (cD id)) then
     match (DGF.step daD) id (cD id) with
      | DGF.Active sim => AGF.Active sim
      | DGF.Moving dist => 
        match (DGF.Config.loc (cD id)) with
          | DGF.Loc _ =>
            match (Graph.find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
                             (AGF.Config.target (AGF.Config.robot_info rcA))) with
             | Some e =>
                if Rle_dec (dist) (Graph.threshold e) then AGF.Moving false else AGF.Moving true
             | None => AGF.Moving false
            end
          | DGF.Mvt e p => if Rle_dec (DGF.project_p p) (Graph.threshold e) then 
                              if Rle_dec (dist + (DGF.project_p p)) (Graph.threshold e) 
                              then AGF.Moving false else AGF.Moving true
                           else AGF.Moving false
        end
      end
      else AGF.Moving false |}.
Proof.
+ intros g rcA sim HrcD. unfold AGF.Aom_eq in *.
  destruct (AGF.Config.eq_Robotconf_dec rcA (rcD2A (cD (Good g)))); try discriminate.
  destruct e as (Hl, (Hs, Ht)).
(*   assert (Hax1 := DGF.ri_Loc (cD (Good g))).
  destruct Hax1 as (lax1, (lax2, ((Hax_src, Hax_tgt), (eD, HeD)))). *)
  destruct (DGF.step daD (Good g) (cD (Good g))) eqn : HstepD, 
  (Graph.find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
             (AGF.Config.target (AGF.Config.robot_info rcA))) eqn : Hedge,
  (DGF.Config.loc (cD (Good g))) eqn : HlD.
  destruct (Rle_dec (dist) (Graph.threshold e)) eqn : Hthresh; now exfalso.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e0)).
  destruct (Rle_dec (dist + DGF.project_p p) (Graph.threshold e0)); now exfalso.
  now exfalso. now exfalso.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)).
  destruct (Rle_dec (dist + DGF.project_p p) (Graph.threshold e)); now exfalso.
  now exfalso.
  unfold rcA2D in *; simpl in *. apply DGF.step_delta in HstepD.
  assert (Heq : exists l, Graph.Veq (AGF.Config.loc rcA) l).
  now exists (AGF.Config.loc rcA).
  unfold DGF.Location.eq, AGF.Location.eq, DGF.loc_eq in *.
  unfold LocD2A in *.
  destruct HstepD as (Hstl, Hstst).
  destruct (DGF.Config.loc (cD (Good g))) eqn : HlocD,
  (DGF.Config.source (DGF.Config.robot_info (cD (Good g)))) eqn : HsrcD,
  (DGF.Config.target (DGF.Config.robot_info (cD (Good g)))) eqn : HtgtD;
  try (now exfalso);
  rewrite Hl, Ht;
  try assumption.
  unfold rcD2A, LocD2A. simpl in *. 
  unfold LocD2A in *.
  assert (Hdelta := DGF.step_delta daD g (cD (Good g)) sim0 HstepD).
  destruct Hdelta as (Hld, Htd).
  destruct (DGF.Config.loc (cD (Good g))) eqn : HlocD,
  (DGF.Config.source (DGF.Config.robot_info (cD (Good g)))) eqn : HsrcD,
  (DGF.Config.target (DGF.Config.robot_info (cD (Good g)))) eqn : HtgtD;
  simpl in *;
  try (now exfalso);
  rewrite Hl, Ht;
  try assumption; try now destruct Hld.
  apply (DGF.step_delta daD) in HstepD.
  destruct HstepD.
  unfold rcD2A, LocD2A in *; simpl in *.
  destruct (DGF.Config.loc (cD (Good g))) eqn : HlocD,
  (DGF.Config.source (DGF.Config.robot_info (cD (Good g)))) eqn : HsrcD,
  (DGF.Config.target (DGF.Config.robot_info (cD (Good g)))) eqn : HtgtD;
  simpl in *;
  try (now exfalso);
  rewrite Hl, Ht;
  try assumption.
  apply (DGF.step_delta daD) in HstepD.
  destruct HstepD.
  unfold rcD2A, LocD2A in *; simpl in *.
  destruct (DGF.Config.loc (cD (Good g))) eqn : HlocD,
  (DGF.Config.source (DGF.Config.robot_info (cD (Good g)))) eqn : HsrcD,
  (DGF.Config.target (DGF.Config.robot_info (cD (Good g)))) eqn : HtgtD;
  simpl in *;
  try (now exfalso);
  rewrite Hl, Ht;
  try assumption;
  now destruct H.
+ intros id1 id2 Hid rcA1 rcA2 HrcA. unfold AGF.Aom_eq. 
  assert (Graph.Veq (AGF.Config.source (AGF.Config.robot_info rcA1))
              (AGF.Config.source (AGF.Config.robot_info rcA2))) by apply HrcA.
  assert (Graph.Veq (AGF.Config.target (AGF.Config.robot_info rcA1))
              (AGF.Config.target (AGF.Config.robot_info rcA2))) by apply HrcA.
  assert (Hedge_co := Graph.find_edge_compat (AGF.Config.source (AGF.Config.robot_info rcA1)) 
                          (AGF.Config.source (AGF.Config.robot_info rcA2)) H 
                          (AGF.Config.target (AGF.Config.robot_info rcA1))
                          (AGF.Config.target (AGF.Config.robot_info rcA2)) H0).
  assert (HrcD : DGF.Config.eq_RobotConf (cD id1) (cD id2)) by now rewrite Hid.
  assert (HrcD' := HrcD).
  destruct HrcD' as (HDl, (HDs, HDt)). unfold DGF.loc_eq in *.
  destruct (DGF.step daD id1 (cD id1)) eqn : Hstep1,
  (DGF.step daD id2 (cD id2)) eqn : Hstep2,
  (DGF.Config.loc (cD id1)) eqn : HlD1,
  (DGF.Config.loc (cD id2)) eqn : HlD2,
  (AGF.Config.eq_Robotconf_dec rcA1 (rcD2A (cD id1))) eqn : Heq1,
  (AGF.Config.eq_Robotconf_dec rcA2 (rcD2A (cD id2))) eqn : Heq2,
  (Graph.find_edge (AGF.Config.source (AGF.Config.robot_info rcA1))
          (AGF.Config.target (AGF.Config.robot_info rcA1))) eqn : Hedge1,
  (Graph.find_edge (AGF.Config.source (AGF.Config.robot_info rcA2))
          (AGF.Config.target (AGF.Config.robot_info rcA2))) eqn : Hedge2; simpl in *;
  try rewrite Hstep1; simpl in *;
    try (assert (Hst := DGF.step_compat);
  specialize (Hst daD id1 id2 Hid rcD rcD (reflexivity rcD));
  rewrite Hstep1, Hstep2 in Hst; now unfold DGF.Aom_eq in Hst);
  try (now exfalso);
  assert (Hst := DGF.step_compat);
  specialize (Hst daD id1 id2 Hid (cD id1) (cD id2) HrcD);
  rewrite Hstep1, Hstep2 in Hst; unfold DGF.Aom_eq in Hst;
  assert (Hfind := Graph.find_edge_compat (AGF.Config.source (AGF.Config.robot_info rcA1))
                                    (AGF.Config.source (AGF.Config.robot_info rcA2)) H
                                    (AGF.Config.target (AGF.Config.robot_info rcA1))
                                    (AGF.Config.target (AGF.Config.robot_info rcA2)) H0);
  rewrite Hedge1, Hedge2 in Hfind; try discriminate;
  try assert (HEeq : Graph.Eeq e1 e2) by (apply Hfind);
  try (assert (Graph.threshold e1 = Graph.threshold e2) by now apply Graph.threshold_compat, HEeq);
  try (rewrite HrcD; intuition); try (rewrite <- HrcD; intuition); intuition.
  rewrite H1, Hst.
  destruct (Rle_dec dist0 (Graph.threshold e2)) eqn : Hdist; auto.
  assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  rewrite Hst.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)).
  destruct (Rle_dec (dist0 + DGF.project_p p)); auto.
  rewrite <- H2. assert (Graph.threshold e = Graph.threshold e0) by (now apply Graph.threshold_compat).
  rewrite <- H3.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)).
  destruct (Rle_dec (dist0 + DGF.project_p p)); auto.
  auto.
  rewrite <- H2. assert (Graph.threshold e = Graph.threshold e0) by (now apply Graph.threshold_compat).
  rewrite <- H3.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)).
  destruct (Rle_dec (dist0 + DGF.project_p p)); auto. contradiction. contradiction.
  rewrite <- H2. assert (Graph.threshold e = Graph.threshold e0) by (now apply Graph.threshold_compat).
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e0)).
  rewrite <- H3, Hst in *. 
  destruct (Rle_dec (dist0 + DGF.project_p p) (Graph.threshold e)); auto. auto.
  rewrite <- H2. assert (Graph.threshold e = Graph.threshold e0) by (now apply Graph.threshold_compat).
  rewrite <- H3, Hst in *.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)). 
  destruct (Rle_dec (dist0 + DGF.project_p p) (Graph.threshold e)); auto. auto.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  destruct (Rle_dec (DGF.project_p p) (Graph.threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (Graph.threshold e)); auto);
  assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
Defined.

Instance daD2A_compat : Proper (DGF.da_eq ==> DGF.Config.eq ==> AGF.da_eq) daD2A.
Proof.
intros dad1 dad2 HdaD cD1 cD2 HrcD'.
unfold daD2A, AGF.da_eq in *;
simpl.
split.
intros id confA.  assert (HrcD := HrcD' id).
assert (HrcD2A_eq : AGF.Config.eq_RobotConf (rcD2A (cD1 id)) (rcD2A (cD2 id))).
apply rcD2A_compat, HrcD.
assert (Hda_cD := DGF.step_da_compat HdaD (reflexivity id) HrcD).
unfold DGF.Aom_eq in Hda_cD.
destruct HdaD as (HdaD_G, _).
specialize (HdaD_G id (rcA2D confA)).
destruct (AGF.Config.eq_Robotconf_dec confA (rcD2A (cD1 id))) eqn : HrcD1,
         (AGF.Config.eq_Robotconf_dec confA (rcD2A (cD2 id))) eqn : HrcD2;
destruct (DGF.step dad1 id (cD1 id)),
         (DGF.step dad2 id (cD2 id));
destruct (DGF.Config.loc (cD1 id)) eqn : Hc1, (DGF.Config.loc (cD2 id)) eqn : Hc2;
destruct (Graph.find_edge (AGF.Config.source (AGF.Config.robot_info confA))
      (AGF.Config.target (AGF.Config.robot_info confA))); try rewrite Hda_cD;
unfold DGF.loc_eq in *;
try (destruct HrcD as (Hl,_); now rewrite Hc1, Hc2 in Hl).
destruct (Rle_dec dist0 (Graph.threshold e1)); now unfold AGF.Aom_eq.
destruct HrcD as (Hl,_); rewrite Hc1, Hc2 in Hl;
destruct Hl as (He, Hp).
assert (Hth : (Graph.threshold e1) = (Graph.threshold e2)) by apply Graph.threshold_compat, He.
rewrite Hth, Hp.
destruct (Rle_dec (DGF.project_p p0) (Graph.threshold e2)); try (
destruct (Rle_dec (dist0 + DGF.project_p p0) (Graph.threshold e2)); now unfold AGF.Aom_eq).
destruct HrcD as (Hl,_); rewrite Hc1, Hc2 in Hl;
destruct Hl as (He, Hp).
assert (Hth : (Graph.threshold e1) = (Graph.threshold e2)) by apply Graph.threshold_compat, He.
rewrite Hth, Hp.
destruct (Rle_dec (DGF.project_p p0) (Graph.threshold e2)); try (
destruct (Rle_dec (dist0 + DGF.project_p p0) (Graph.threshold e2)); now unfold AGF.Aom_eq).
assert (e' := e); rewrite HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcD2A_eq in e'; contradiction.
assert (e' := e); rewrite <- HrcD2A_eq in e'; contradiction.
destruct HdaD as (_,Hb). intros b. apply LocD2A_compat, Hb.
Qed.


(* TODO : trouver une définition vrai, ou rajouter des axioms car la sinon c'est pas vrai.*)
Definition daA2D (daA : AGF.demonic_action) (cA : AGF.Config.t) : DGF.demonic_action.
refine {| 
  DGF.relocate_byz := fun b => DGF.Loc ((AGF.relocate_byz daA) b);
  DGF.step := fun id rcD => if DGF.Config.eq_Robotconf_dec rcD (rcA2D (cA id)) then
              match ((AGF.step daA) id (cA id)) with
                | AGF.Active sim =>  (* if DGF.Location.eq_dec (DGF.Config.loc rcD)
                                                    (DGF.Config.target (DGF.Config.robot_info rcD))
                                     then *) DGF.Active sim
                                     (* else DGF.Moving 1%R *)
                | AGF.Moving b => if b then DGF.Moving 1%R else DGF.Moving 0%R
              end
              else DGF.Moving 0%R
  (* DGF.step_delta := forall id rcD sim, *) |}.
Proof.
+ intros g rcD sim HrcA .
destruct (AGF.step daA (Good g) (cA (Good g))) eqn : HstepA, 
(DGF.Config.eq_Robotconf_dec rcD (rcA2D (cA (Good g)))) eqn : HrcD; unfold rcD2A, LocD2A in *; simpl in *.
 - assert (e' := e); destruct e' as (Hl, (Hs, Ht)); unfold DGF.loc_eq in *; simpl in *.
   destruct (DGF.Config.loc rcD), ( DGF.Config.source (DGF.Config.robot_info rcD)),
            ( DGF.Config.target (DGF.Config.robot_info rcD)); try (now exfalso).
   destruct dist; now exfalso.
 - now exfalso.
 - assert (e' := e); destruct e' as (Hl, (Hs, Ht)); unfold DGF.loc_eq in *; simpl in *.
   destruct (DGF.Config.loc rcD), ( DGF.Config.source (DGF.Config.robot_info rcD)),
            ( DGF.Config.target (DGF.Config.robot_info rcD)); try (now exfalso).
   apply (AGF.step_delta daA) in HstepA.
   unfold DGF.Location.eq, DGF.loc_eq, AGF.Location.eq, rcD2A in *; simpl in *.
   split ; try (exists l1); now rewrite Ht, Hl.
 - now exfalso.
+ intros id1 id2 Hid rcD1 rcD2 HrcD. unfold DGF.Aom_eq.
  assert (HcA : AGF.Config.eq_RobotConf (cA id1) (cA id2)) by now rewrite Hid.
  assert(Hs1_eq := AGF.step_compat daA id1 id2 Hid (cA id1) (cA id2) (HcA)).
  destruct (AGF.step daA id1 (cA id1)) eqn : Hstep1,
  (AGF.step daA id2 (cA id2)) eqn:Hstep2;
  destruct (DGF.Config.eq_Robotconf_dec rcD1 (rcA2D (cA id1))),
           (DGF.Config.eq_Robotconf_dec rcD2 (rcA2D (cA id2))); auto.
  destruct dist, dist0; auto. unfold AGF.Aom_eq in *. discriminate.
  unfold AGF.Aom_eq in *. discriminate.
  rewrite e in HrcD. rewrite HcA in HrcD. symmetry in HrcD. contradiction.
  rewrite e in HrcD. rewrite <- HcA in HrcD. contradiction.
  destruct dist; now unfold AGF.Aom_eq in *.
  destruct dist; now unfold AGF.Aom_eq.
  destruct dist; now unfold AGF.Aom_eq.
  destruct dist; now unfold AGF.Aom_eq.
  rewrite e in HrcD. rewrite HcA in HrcD. symmetry in HrcD. contradiction.
  rewrite e in HrcD. rewrite <- HcA in HrcD. contradiction.
+ intros id confD r. destruct (AGF.step daA id (cA id));
  destruct (DGF.Config.eq_Robotconf_dec confD (rcA2D (cA id))).
  destruct dist; intros Hm. assert (Heqm : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving r)).
  now rewrite Hm. unfold DGF.Aom_eq in *. rewrite <- Heqm. lra.
  assert (Heqm : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving r)).
  now rewrite Hm. unfold DGF.Aom_eq in *. rewrite <- Heqm. lra.
  destruct dist; intros Hm. assert (Heqm : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving r)).
  now rewrite Hm. unfold DGF.Aom_eq in *. rewrite <- Heqm. lra.
  assert (Heqm : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving r)).
  now rewrite Hm. unfold DGF.Aom_eq in *. rewrite <- Heqm. lra.
  destruct (DGF.Location.eq_dec (DGF.Config.loc confD)
                                (DGF.Config.target (DGF.Config.robot_info confD)));
  intros Hm. discriminate. discriminate.
  intros Hm; assert (Heqm : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving r)).
  now rewrite Hm. unfold DGF.Aom_eq in *. rewrite <- Heqm. lra.
Defined.

Instance daA2D_compat : Proper (AGF.da_eq ==> AGF.Config.eq ==> DGF.da_eq) daA2D.
Proof.
intros daA1 daA2 HdaA cA1 cA2 HrcA.
unfold daA2D; split; simpl.
+ intros id rc. destruct HdaA as (HdaA_G,_).
  specialize (HdaA_G id (cA1 id)).
  assert (Hda' : AGF.Aom_eq (AGF.step daA2 id (cA1 id)) (AGF.step daA2 id (cA2 id))).
  apply (AGF.step_compat daA2 id id (reflexivity id) (cA1 id) (cA2 id) (HrcA id) ).
  rewrite Hda' in HdaA_G.
  destruct (DGF.Config.eq_Robotconf_dec rc (rcA2D (cA1 id))) eqn : HrcD1, 
           (DGF.Config.eq_Robotconf_dec rc (rcA2D (cA2 id))) eqn : HrcD2.
  * destruct (AGF.step daA1 id (cA1 id)), (AGF.step daA2 id (cA2 id)); unfold AGF.Aom_eq in *.
    - destruct dist, dist0; now unfold DGF.Aom_eq.
    - now exfalso.
    - now exfalso.
    - destruct (DGF.Location.eq_dec (DGF.Config.loc rc)
                                  (DGF.Config.target (DGF.Config.robot_info rc))).
      now rewrite HdaA_G.
      now unfold AGF.Aom_eq.
  * assert (e' := e). rewrite (HrcA id) in e'. contradiction.
  * assert (e' := e). rewrite <- (HrcA id) in e'. contradiction.
  * now unfold AGF.Aom_eq.
+ destruct HdaA as (_, HdaA_B). intros b; specialize (HdaA_B b).
  auto.
Qed.

(* 
CoFixpoint demonD2A (demonD : DGF.demon) : AGF.demon :=
  AGF.NextDemon (daD2A (DGF.demon_head demonD)) (demonD2A demonD).

CoFixpoint demonA2D (demonA : AGF.demon) : DGF.demon :=
  DGF.NextDemon (daA2D (AGF.demon_head demonA)) (demonA2D demonA).
 *)
(* Instance demonD2A_compat : Proper (DGF.Deq  *)

(*Ensuite, pour montrer l'équivalence, on écrit des fonctions de
traduction entre les modèles Atomic et Discrete pour :
+ configuration (check)
+ robogram (check)
+ demonic_action ( check )
+ demon ( check )
+ round ( TODO )
*)

Theorem graph_equivA2D : forall (c c': AGF.Config.t) (rbg:AGF.robogram) (da:AGF.demonic_action),
AGF.Config.eq c' (AGF.round rbg da c) ->
exists da', DGF.Config.eq (ConfigA2D c') (DGF.round (rbgA2D rbg) da' (ConfigA2D c)).
Proof.
intros c c' rbg da HAGF.
exists (daA2D da c). intros id.
assert ( HeqDd : DGF.Config.eq_RobotConf
             {|
             DGF.Config.loc := DGF.Loc (AGF.Config.loc (c id));
             DGF.Config.robot_info := {|
                                      DGF.Config.source := DGF.Loc
                                                             (AGF.Config.source
                                                                (AGF.Config.robot_info
                                                                   (c id)));
                                      DGF.Config.target := DGF.Loc
                                                             (AGF.Config.target
                                                                (AGF.Config.robot_info
                                                                   (c id))) |} |}
             {|
             DGF.Config.loc := DGF.Loc (AGF.Config.loc (c id));
             DGF.Config.robot_info := {|
                                      DGF.Config.source := DGF.Loc
                                                             (AGF.Config.source
                                                                (AGF.Config.robot_info
                                                                   (c id)));
                                      DGF.Config.target := DGF.Loc
                                                             (AGF.Config.target
                                                                (AGF.Config.robot_info
                                                                   (c id))) |} |});
simpl in *. repeat try split; simpl; reflexivity.
 repeat try (split; simpl);
assert (Heq : AGF.Location.eq (AGF.Config.loc (c' id))
                              (AGF.Config.loc ((AGF.round rbg da c) id))) by apply HAGF;
  unfold AGF.Location.eq in Heq;
  unfold AGF.round, DGF.round in *;
  assert (Heq_rcA: AGF.Config.eq_RobotConf (c id) ({|
             AGF.Config.loc := AGF.Config.loc (c id);
             AGF.Config.robot_info := {|
                                      AGF.Config.source := AGF.Config.source
                                                             (AGF.Config.robot_info (c id));
                                      AGF.Config.target := AGF.Config.target
                                                             (AGF.Config.robot_info (c id)) |} |})) by (
      repeat (try split; simpl) ; reflexivity);
assert (HstepA_compat := AGF.step_compat da id id (reflexivity id)
              (c id)
              ({| AGF.Config.loc := AGF.Config.loc (c id);
                  AGF.Config.robot_info := {|
                     AGF.Config.source := AGF.Config.source (AGF.Config.robot_info (c id));
                     AGF.Config.target := AGF.Config.target (AGF.Config.robot_info (c id)) |} |})
              Heq_rcA);
destruct (AGF.step da id (c id)) eqn : HstepA,
         (DGF.step (daA2D da c) id (ConfigA2D c id)) eqn:HstepD; unfold ConfigA2D in HstepD;
  simpl in *; unfold rcD2A in HstepD; simpl in *;
         destruct (AGF.step da id
             {|
             AGF.Config.loc := AGF.Config.loc (c id);
             AGF.Config.robot_info := {|
                                      AGF.Config.source := AGF.Config.source
                                                             (AGF.Config.robot_info (c id));
                                      AGF.Config.target := AGF.Config.target
                                                             (AGF.Config.robot_info (c id)) |} |})
      eqn : HstepA',
         (HAGF id) as (HlocA,(HsrcA,HtgtA)); unfold rcA2D in *;
destruct (DGF.Config.eq_Robotconf_dec
             {|
             DGF.Config.loc := DGF.Loc (AGF.Config.loc (c id));
             DGF.Config.robot_info := {|
                                      DGF.Config.source := DGF.Loc
                                                             (AGF.Config.source
                                                                (AGF.Config.robot_info
                                                                   (c id)));
                                      DGF.Config.target := DGF.Loc
                                                             (AGF.Config.target
                                                                (AGF.Config.robot_info
                                                                   (c id))) |} |}
             {|
             DGF.Config.loc := DGF.Loc (AGF.Config.loc (c id));
             DGF.Config.robot_info := {|
                                      DGF.Config.source := DGF.Loc
                                                             (AGF.Config.source
                                                                (AGF.Config.robot_info
                                                                   (c id)));
                                      DGF.Config.target := DGF.Loc
                                                             (AGF.Config.target
                                                                (AGF.Config.robot_info
                                                                   (c id))) |} |});
try contradiction; 
destruct id as [g|b]; try (now exfalso); simpl in *; rewrite HstepA in *; try discriminate.
  - destruct (Rdec dist0 0).
    * destruct dist; simpl in *; destruct dist1; try auto; try discriminate.
      rewrite e0 in *.
      assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving 0)) by now rewrite HstepD.
      unfold DGF.Aom_eq in *. lra.
    * destruct (Rdec dist0 1).
      destruct dist; simpl in *; auto.
      ++ rewrite e0, <- HstepA_compat in *.
         assert (Hfalse : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving 1)).
         rewrite HstepD. reflexivity. unfold DGF.Aom_eq in *. lra.
      ++ destruct (Graph.Veq_dec (AGF.Config.loc (c (Good g)))
        (AGF.Config.target (AGF.Config.robot_info (c (Good g))))); simpl in *.
        ** destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
        ** destruct dist; simpl in *; destruct dist1; simpl in *; try discriminate.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
 - destruct dist; simpl in *; assumption.
 - destruct dist; simpl in *; discriminate.
 - destruct dist; simpl in *; discriminate.
 - simpl in *. assumption.
 - simpl in *. assumption.
 - destruct (Rdec dist0 0); simpl in *.
    * destruct dist; destruct dist1; try auto.
    * destruct (Rdec dist0 1).
      destruct dist; simpl in *; try auto.
      destruct (Graph.Veq_dec (AGF.Config.loc (c (Good g)))
        (AGF.Config.target (AGF.Config.robot_info (c (Good g))))); simpl in *;
      destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
 - destruct dist; assumption.
 - destruct dist; discriminate.
 - destruct dist; discriminate.
 - assumption.
 - assumption.
 - destruct (Rdec dist0 0).
    * simpl in *.
      destruct dist; simpl in *; destruct dist1; auto; try discriminate.
    * destruct (Rdec dist0 1); simpl in *; simpl in *.
      destruct dist; simpl in *; auto.
      destruct (Graph.Veq_dec (AGF.Config.loc (c (Good g)))
        (AGF.Config.target (AGF.Config.robot_info (c (Good g))))); simpl in *;
      destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
 - destruct dist; simpl in *; assumption.
 - destruct dist; simpl in *; discriminate.
 - destruct dist; simpl in *; discriminate.
 - simpl in *. rewrite HtgtA.
    assert (Htest : forall confA, DGF.Config.eq (ConfigA2D (confA)) (DGF.project (ConfigA2D confA))).
    intros confA id.
    unfold DGF.project, ConfigA2D; simpl in *. reflexivity.
    specialize (Htest c). rewrite <- Htest.
    assert (AGF.Spect.eq (AGF.Spect.from_config c) (DGF.Spect.from_config (ConfigA2D c))).
    unfold AGF.Spect.eq, View.eq.
    unfold ConfigA2D; simpl in *.
    repeat try (split; simpl); now unfold AGF.Spect.from_config.
    now rewrite H.
 - simpl in *; assumption.
Save.

Theorem graph_equivD2A : forall (c c': DGF.Config.t) (rbg:DGF.robogram) (da : DGF.demonic_action),
DGF.group_good_def c ->
DGF.Config.eq c' (DGF.round rbg da c) ->
exists da', AGF.Config.eq (ConfigD2A c') (AGF.round (rbgD2A rbg) da' (ConfigD2A c)).
Proof.
intros c c' rbg da Hri HDGF. exists (daD2A da c). intro id.
assert (Heq_rcD: DGF.Config.eq_RobotConf (c id) ({|
             DGF.Config.loc := DGF.Config.loc (c id);
             DGF.Config.robot_info := {|
                                      DGF.Config.source := DGF.Config.source
                                                             (DGF.Config.robot_info (c id));
                                      DGF.Config.target := DGF.Config.target
                                                             (DGF.Config.robot_info (c id)) |} |})) by (
      repeat (try split; simpl) ; reflexivity);
assert (HstepD_compat := DGF.step_compat da id id (reflexivity id)
              (c id)
              ({| DGF.Config.loc := DGF.Config.loc (c id);
                  DGF.Config.robot_info := {|
                     DGF.Config.source := DGF.Config.source (DGF.Config.robot_info (c id));
                     DGF.Config.target := DGF.Config.target (DGF.Config.robot_info (c id)) |} |})
              Heq_rcD);
destruct (DGF.step da id
                    {| DGF.Config.loc := DGF.Config.loc (c id);
                  DGF.Config.robot_info := {|
                     DGF.Config.source := DGF.Config.source (DGF.Config.robot_info (c id));
                     DGF.Config.target := DGF.Config.target (DGF.Config.robot_info (c id)) |} |})
eqn : HstepD'; try (now exfalso);
unfold AGF.round, DGF.round in *; specialize (HDGF id);
unfold DGF.loc_eq in *;
destruct (DGF.step da id (c id)) eqn : HstepD,
(AGF.step (daD2A da c) id (ConfigD2A c id)) eqn : HstepA, id as [g|b]; try (now exfalso);
unfold daD2A in *; simpl in *;
unfold rcA2D, ConfigD2A, LocD2A in *;
repeat try (split; simpl);
try (destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e)));
  unfold DGF.ri_loc_def in *;
  specialize (Hrid g);
  destruct Hrid as (v1, (v2, (Hv1, Hv2)));
  destruct (DGF.Config.loc (c (Good g))) as [lld| eld pld] eqn : HlocD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lsd | esd psd] eqn : HsrcD;
  try discriminate; try (now exfalso));
try destruct (DGF.Config.loc (c (Byz b))) as [lld| eld pld] eqn : HlocD;
simpl in *; try (rewrite <- HlocD in *);
try discriminate; rewrite HstepD in *;
destruct HDGF as (Hloc, (Hsrc, Htgt));
try (now (destruct (AGF.Config.eq_Robotconf_dec _); try discriminate;
  destruct (Graph.find_edge _ _) as [etmp|]; try discriminate;
  destruct (Rle_dec dist0 (Graph.threshold etmp)); discriminate));
try (now (destruct (AGF.Config.eq_Robotconf_dec _); try discriminate;
  destruct (Rle_dec (DGF.project_p pld) (Graph.threshold eld)); try discriminate;
  destruct (Rle_dec (dist0 + DGF.project_p pld) (Graph.threshold eld)); discriminate));
try (now (destruct (AGF.Config.eq_Robotconf_dec _); try discriminate;
  destruct (Graph.find_edge lsd ltd) as [etmp|]; try discriminate;
  destruct (Rle_dec dist0 (Graph.threshold etmp)); discriminate));
try ( now (destruct dist eqn : Hbool;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  try (now simpl in *);
  try (now (destruct (AGF.Config.eq_Robotconf_dec _);
  try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl))));
try (now (try (now simpl in *);
  destruct dist eqn : Hbool;
  destruct (DGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (AGF.Config.eq_Robotconf_dec _);
  try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; try now simpl)).
+ destruct dist1 eqn : Hbool.
  - destruct (DGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
    destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
    destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
    try discriminate;
    try (now simpl in *);
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; 
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Rdec dist0 1); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in *));
    destruct (Graph.Veq_dec lld ltd); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in *))));
    destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g)))); try discriminate.
    * simpl in *.
      destruct (Rdec dist0 0) eqn : Hdist.
      try rewrite HlocD, HsrcD, HtgtD in *.
      destruct (Graph.find_edge lsd ltd) eqn : Hedge1.
      ** destruct (Rle_dec (dist0) (Graph.threshold e1)); try discriminate; simpl in *.
         rewrite <- HstepD_compat in *.
         intuition.
         assert (Hfalse := Graph.threshold_pos e1); lra.
      ** discriminate.
      ** destruct (Rdec dist0 1); simpl in *; try assumption.
         destruct (Graph.Veq_dec lld ltd) eqn : Heql.
          ++ rewrite HlocD in *. now rewrite Hloc.
          ++ simpl in *; now exfalso.
   * simpl in *; try ((destruct (Rdec dist0 0); try (now (simpl in *; rewrite HlocD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HlocD in *));
     destruct (Graph.Veq_dec lld ltd); try (now (simpl in *; rewrite HlocD in *)))).
     destruct (Graph.find_edge lsd ltd) eqn : Hedge0; try discriminate.
     destruct (Rle_dec dist0 (Graph.threshold e0)); try discriminate.
     destruct (Graph.find_edge lld ltd)eqn : HedgeA;
     simpl in *.
     ** destruct (Rle_dec (DGF.project_p pld') (Graph.threshold eld')).
        destruct Hloc as (Heeq, Hpeq).
        symmetry in Hpeq.
        rewrite <- (DGF.subj_proj dist0 pld') in Hpeq.
        rewrite Hpeq in n2.
        assert (opt_eq Graph.Eeq (Graph.find_edge lld ltd) (Graph.find_edge lsd ltd)).
        apply Graph.find_edge_compat; try now simpl in *.
        specialize (Hli lld (reflexivity lld));
        destruct Hli as [Hsi | Hti]; try contradiction.
        now symmetry.
        now symmetry in Hti.
        rewrite Hedge0, HedgeA in H.
        simpl in H.
        rewrite <- Heeq in H.
        rewrite <- H in n2.
        lra.
        assert (Hg := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD); lra.
        specialize (Hli lld (reflexivity lld));
        destruct Hli as [Hsi | Hti]; try (now symmetry in Hti).
        rewrite HtgtD in *.
        destruct Hloc as (Heq_e, Heq_p).
        assert (Hsol : opt_eq Graph.Eeq (Graph.find_edge lld ltd) (Some eld')) by now rewrite HedgeA.
        apply Graph.find2st in Hsol.
        symmetry; now destruct Hsol.
     ** specialize (Hli lld (reflexivity lld)).
        destruct Hli as [Hsi | Hti]; try now symmetry in Hti.
        specialize (Hex_e lld ltd Hsi (reflexivity ltd)).
        destruct Hex_e as (ex_e, Hex_e).
        rewrite HedgeA in Hex_e.
        contradiction.
  - simpl in *.
    destruct (DGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
    destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
    destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
    try discriminate;
    try (now simpl in *); rewrite HlocD in *;
    try ((destruct (Rdec dist0 0); try (now (simpl in *; 
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Rdec dist0 1); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in *));
    destruct (Graph.Veq_dec lld ltd); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in *))));
    simpl in *;
    try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g)))) as [e_AGF | n_AGF];
    try (destruct (Graph.find_edge lsd ltd) as [e_st| ]eqn : Hedge0;
    try (destruct (Rle_dec dist0 (Graph.threshold e_st));
    try (assert (Hfalse := Graph.threshold_pos e_st); lra);
    try (discriminate));
    try (destruct (Hex_e lsd ltd (reflexivity lsd) (reflexivity ltd)) as (e_ex, He_ex);
    rewrite Hedge0 in He_ex; contradiction));
    try (destruct n_AGF;
    unfold rcD2A, LocD2A;
    repeat (split; simpl in * );
    try (now rewrite HlocD);
    try (now rewrite HsrcD);
    try now rewrite HtgtD)).
    destruct (Graph.Veq_dec lld ltd);
    simpl in *. contradiction.
    destruct Hloc as (Heeq, Hpeq).
    destruct (Graph.find_edge lld ltd) eqn : Hedge. 
    destruct (Rle_dec (DGF.project_p pld') (Graph.threshold eld')).
    destruct (Hli lld (reflexivity lld)) as [Hsi| Hti]; try now symmetry in Hti.
    assert (Hsol : opt_eq Graph.Eeq (Graph.find_edge lld ltd) (Some eld')) by now rewrite Hedge.
    apply Graph.find2st in Hsol.
    symmetry; now destruct Hsol.
    symmetry in Hpeq.
    rewrite <- (DGF.subj_proj dist0 pld') in Hpeq.
    rewrite Hpeq in r.
    assert (Hsol : opt_eq Graph.Eeq (Some eld') (Some e_st)).
    assert (Htriv : opt_eq Graph.Eeq (Some e) (Some eld')) by now simpl in *.
    rewrite <- Htriv, <- Hedge, <- Hedge0.
    apply Graph.find_edge_compat.
    destruct (Hli lld (reflexivity lld)) as [Hsi| Hti]; try now symmetry in Hti.
    now symmetry.
    reflexivity.
    simpl in *.
    rewrite Hsol in n3.
    lra.
    assert (Hf := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD).
    lra.
    destruct (Hli lld (reflexivity lld)) as [Hsi| Hti]; try now symmetry in Hti.
    destruct (Hex_e lld ltd Hsi (reflexivity ltd)) as (e_ex, He_ex).
    rewrite Hedge in He_ex. contradiction.
+ destruct (Rle_dec 1 (DGF.project_p pld + dist0)) eqn : Hdp;
  simpl in *;
  assert (Hmi_aux : Graph.Eeq eld eld /\ pld = pld) by (split; reflexivity);
  assert (Hmi_0 := (Hmi lsd ltd eld pld (reflexivity lsd) (reflexivity ltd) Hmi_aux));
  apply Graph.find2st in Hmi_0;
  destruct Hmi_0 as (Hmi_s, Hmi_t);
  destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  try (now simpl in *);
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; 
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in * ));
    destruct (Rdec dist0 1); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in *));
    destruct (Graph.Veq_dec lld ltd); try (now (simpl in *;
    try rewrite HlocD in * ; try rewrite HsrcD in *; try rewrite HtgtD in *)))); simpl in *.
  - now rewrite <- Hmi_t in Hloc.
  -  destruct (Rle_dec (DGF.project_p pld) (Graph.threshold eld)) eqn : Hpt.
    * destruct(
           AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := Graph.src eld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g)))).
      destruct (Rle_dec (dist0 + DGF.project_p pld) (Graph.threshold eld)).
      assert (Hfalse := Graph.threshold_pos eld).
      lra.
      discriminate.
      destruct n.
      unfold rcD2A, LocD2A; repeat (split; simpl in * ).
      now rewrite HlocD, Hpt.
      now rewrite HsrcD.
      now rewrite HtgtD.
    * assumption.
  - destruct(Rle_dec (DGF.project_p pld') (Graph.threshold eld')).
    * destruct(Rdec dist0 0); rewrite HlocD in *.
      ** destruct (Rle_dec (DGF.project_p pld) (Graph.threshold eld)) eqn : Hpt.
         -- destruct(
            AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := Graph.src eld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g)))).
            ++ destruct (Rle_dec (dist0 + DGF.project_p pld) (Graph.threshold eld)).
               discriminate.
               lra.
            ++ discriminate.
         -- destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := Graph.tgt eld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g))));
            discriminate.
      ** destruct (Rle_dec (DGF.project_p pld) (Graph.threshold eld)).
         -- destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := Graph.src eld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g)))).
            ++ destruct(Rle_dec (dist0 + DGF.project_p pld) (Graph.threshold eld)).
               discriminate.
               destruct Hloc as (Heeq, Hpeq).
               symmetry in Hpeq.
               rewrite <- (DGF.subj_proj (DGF.project_p pld + dist0) pld') in Hpeq.
               rewrite <- Hpeq in r.
               assert (Htre : Graph.threshold eld = Graph.threshold eld').
               apply Graph.threshold_compat.
               now symmetry.
               rewrite <- Htre in r.
               lra.
               assert (Hsol := Graph.threshold_pos eld).
               lra.
            ++ discriminate.
         -- destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := Graph.tgt eld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g))));
            discriminate.
    * destruct(Rdec dist0 0);
      rewrite HlocD in *;
      destruct Hloc as (Heeq, Hpeq);
      rewrite Heeq;
      now symmetry.
  - destruct (Rdec dist0 0);
    rewrite HlocD in *;
    assert (Htr : Graph.threshold eld = Graph.threshold eld') by (now apply Graph.threshold_compat);
    destruct Hloc as (Heeq, Hpeq);
    rewrite Htr, Hpeq in *;
    destruct (Rle_dec (DGF.project_p pld) (Graph.threshold eld')) eqn : Hpt'.
    * now apply Graph.src_compat.
    * now apply Graph.tgt_compat.
    * assert (Hfalse : (DGF.project_p pld < DGF.project_p pld + dist0)%R).
      assert (Hf_aux := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD).
      lra.
      assert (Hl := DGF.project_p_image pld).
      rewrite <- (DGF.inv_pro (DGF.project_p pld + dist0)) in *.
      destruct (Rle_dec (DGF.project_p pld + dist0) (Graph.threshold eld')).
      ** now apply Graph.src_compat.
      ** destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := Graph.src eld;
             AGF.Config.robot_info := {| AGF.Config.source := lsd; AGF.Config.target := ltd |} |}
             (rcD2A (c (Good g)))).
         -- destruct (Rle_dec (dist0 + DGF.project_p pld) (Graph.threshold eld')); try lra.
            discriminate.
         -- destruct n2.
            unfold rcD2A, LocD2A; repeat (split;simpl in *).
            ++ now rewrite HlocD, Htr, Hpt'.
            ++ now rewrite HsrcD.
            ++ now rewrite HtgtD.
      ** lra.
    * assert (Hfalse : (DGF.project_p pld < DGF.project_p pld + dist0)%R).
      assert (Hf_aux := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD).
      lra.
      assert (Hl := DGF.project_p_image pld).
      rewrite <- (DGF.inv_pro (DGF.project_p pld + dist0)) in *.
      destruct (Rle_dec (DGF.project_p pld + dist0) (Graph.threshold eld')).
      ** lra.
      ** now apply Graph.tgt_compat.
      ** lra.
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Graph.Veq_dec lld ltd); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (destruct (Rle_dec 1 (DGF.project_p pld + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; now simpl in *); try now simpl in *.
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Graph.Veq_dec lld ltd); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Good g))) as [lld' | eld' pld' ] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [ltd' | etd' pdt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lsd' | esd' psd'] eqn : HsrcD';
  try discriminate;
  simpl in *;
  try (destruct (Rle_dec 1 (DGF.project_p pld + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; now simpl in *); try now simpl in *.
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  rewrite HlocD in *;
  try now simpl in *.
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  rewrite HlocD in *;
  try (now simpl in *);
  destruct Hloc as (Hle, Hlp);
  assert (Htt : Graph.threshold eld = Graph.threshold eld') by (now apply Graph.threshold_compat);
  rewrite Htt, Hlp;
  destruct (Rle_dec (DGF.project_p pld) (Graph.threshold eld'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  rewrite HlocD in *;
  try (now simpl in *);
  destruct Hsrc as (Hse, Hsp);
  assert (Htt : Graph.threshold esd = Graph.threshold esd') by (now apply Graph.threshold_compat);
  rewrite Htt, Hsp;
  destruct (Rle_dec (DGF.project_p psd) (Graph.threshold esd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  rewrite HlocD in *;
  try (now simpl in *);
  destruct Hsrc as (Hse, Hsp);
  assert (Htt : Graph.threshold esd = Graph.threshold esd') by (now apply Graph.threshold_compat);
  rewrite Htt, Hsp;
  destruct (Rle_dec (DGF.project_p psd) (Graph.threshold esd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  rewrite HlocD in *;
  try (now simpl in *);
  destruct Htgt as (Hte, Htp);
  assert (Htt : Graph.threshold etd = Graph.threshold etd') by (now apply Graph.threshold_compat);
  rewrite Htt, Htp;
  destruct (Rle_dec (DGF.project_p ptd) (Graph.threshold etd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c' (Byz b))) as [lld' | eld' pld'] eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lsd | esd psd] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lsd' | esd' psd'] eqn : HsrcD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [ltd | etd ptd] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [ltd' | etd' ptd'] eqn : HtgtD';
  try (now exfalso);
  rewrite HlocD in *;
  try (now simpl in *);
  destruct Htgt as (Hte, Htp);
  assert (Htt : Graph.threshold etd = Graph.threshold etd') by (now apply Graph.threshold_compat);
  rewrite Htt, Htp;
  destruct (Rle_dec (DGF.project_p ptd) (Graph.threshold etd'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ rewrite HlocD in *.
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  try now simpl in *.
+ rewrite HlocD in *.
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  try (now simpl in * ); simpl in *;
  destruct Hloc as (Hel, Hpl);
  assert (Htl : Graph.threshold eld = Graph.threshold egl') by (now apply Graph.threshold_compat);
  rewrite Hpl, Htl; destruct (Rle_dec (DGF.project_p pld) (Graph.threshold egl'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ rewrite HlocD in *.
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  try (now simpl in * ); simpl in *;
  destruct Hloc as (Hel, Hpl);
  assert (Htl : Graph.threshold eld = Graph.threshold egl') by (now apply Graph.threshold_compat);
  rewrite Hpl, Htl; destruct (Rle_dec (DGF.project_p pld) (Graph.threshold egl'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ rewrite HlocD in *.
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  try (now simpl in * ); simpl in *;
  destruct Hsrc as (Hes, Hps);
  assert (Htl : Graph.threshold eld = Graph.threshold egs') by (now apply Graph.threshold_compat);
  rewrite Hps, Htl; destruct (Rle_dec (DGF.project_p pld) (Graph.threshold egs'));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  try (now simpl in *).
  - cut (Graph.Veq lgt' match DGF.pgm rbg (ConfigD2A c)
              with
                | DGF.Loc l => l
                | DGF.Mvt e p =>
                    if Rle_dec (DGF.project_p p) (Graph.threshold e) then Graph.src e else Graph.tgt e
              end); trivial; [].
    cut (Graph.Veq lgt' match DGF.pgm rbg ((DGF.Spect.from_config (DGF.project c)))
                with
    | DGF.Loc l => l
    | DGF.Mvt e p => if Rle_dec (DGF.project_p p) (Graph.threshold e) then Graph.src e else Graph.tgt e
    end).
    assert (AGF.Config.eq (DGF.Spect.from_config (DGF.project c)) (ConfigD2A c)).
    unfold ConfigD2A, DGF.Spect.from_config, DGF.project, DGF.projectS, DGF.projectS_loc, LocD2A.
    intros id. destruct (DGF.Config.loc (c id)) eqn : Hlid. rewrite Hlid; simpl in *. reflexivity.
    simpl in *. reflexivity.
    assert (Hpgm := DGF.pgm_compat rbg (DGF.Spect.from_config (DGF.project c)) (ConfigD2A c) H).
    destruct (DGF.pgm rbg (DGF.Spect.from_config (DGF.project c))) eqn : Hpgm1,
    (DGF.pgm rbg (ConfigD2A c)) eqn : Hpgm2; unfold DGF.Location.eq, DGF.loc_eq in Hpgm.
    intros Hv; now rewrite Hv. now exfalso. now exfalso. destruct Hpgm as (Hepgm, Hppgm).
    rewrite Hppgm.
    assert (Hthpgm : Graph.threshold e = Graph.threshold e0) by now apply Graph.threshold_compat.
    rewrite Hthpgm.
    intros Hv.
    destruct (Rle_dec (DGF.project_p p0) (Graph.threshold e0)).
    rewrite Hv; now apply Graph.src_compat.
    rewrite Hv; now apply Graph.tgt_compat.
    now destruct (DGF.pgm rbg (DGF.Spect.from_config (DGF.project c))).
  - assert (Hpgm := DGF.pgm_loc rbg (DGF.Spect.from_config (DGF.project c))).
    destruct Hpgm as (vf, Hfalse). now rewrite Hfalse in Htgt.
+ simpl in *.
  assert (Hfalse := DGF.step_delta da g (c (Good g)) sim0 HstepD).
  destruct Hfalse as ((lf, Hfalse),_).
  now rewrite HlocD in Hfalse.
+ destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  simpl in *;
  destruct (DGF.Config.loc (c' (Byz b))) as [lbl' | ebl' pbl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (DGF.relocate_byz da b) as [lrb | erb prb] eqn : Hrb;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Hloc as (Hel, Hpl);
  assert (Hth : (Graph.threshold ebl')= (Graph.threshold erb)) by (now apply Graph.threshold_compat);
  rewrite <- Hpl, Hth; destruct ( Rle_dec (DGF.project_p pbl') (Graph.threshold erb));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  simpl in *;
  destruct (DGF.Config.loc (c' (Byz b))) as [lbl' | ebl' pbl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (DGF.relocate_byz da b) as [lrb | erb prb] eqn : Hrb;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Hloc as (Hel, Hpl);
  assert (Hth : (Graph.threshold ebl')= (Graph.threshold erb)) by (now apply Graph.threshold_compat);
  rewrite <- Hpl, Hth; destruct ( Rle_dec (DGF.project_p pbl') (Graph.threshold erb));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (DGF.relocate_byz da b) as [lrb | erb prb] eqn : Hrb;
  simpl in *;
  rewrite HsrcD in *;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Hsrc as (Hes, Hps);
  assert (Hth : (Graph.threshold ebs')= (Graph.threshold ebs)) by (now apply Graph.threshold_compat);
  rewrite <- Hps, Hth; destruct ( Rle_dec (DGF.project_p pbs') (Graph.threshold ebs));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (DGF.relocate_byz da b) as [lrb | erb prb] eqn : Hrb;
  simpl in *;
  rewrite HsrcD in *;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Hsrc as (Hes, Hps);
  assert (Hth : (Graph.threshold ebs')= (Graph.threshold ebs)) by (now apply Graph.threshold_compat);
  rewrite <- Hps, Hth; destruct ( Rle_dec (DGF.project_p pbs') (Graph.threshold ebs));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  simpl in *;try rewrite HtgtD in *;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Htgt as (Het, Hpt);
  assert (Hth : (Graph.threshold ebt')= (Graph.threshold ebt)) by (now apply Graph.threshold_compat);
  rewrite <- Hpt, Hth; destruct ( Rle_dec (DGF.project_p pbt') (Graph.threshold ebt));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
+ destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  simpl in *;try rewrite HtgtD in *;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Htgt as (Het, Hpt);
  assert (Hth : (Graph.threshold ebt')= (Graph.threshold ebt)) by (now apply Graph.threshold_compat);
  rewrite <- Hpt, Hth; destruct ( Rle_dec (DGF.project_p pbt') (Graph.threshold ebt));
  try (now apply Graph.src_compat); try (now apply Graph.tgt_compat).
Qed.
