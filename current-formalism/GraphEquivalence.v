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


About AGF.Config.t.
About DGF.Spect.t.


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
        | DGF.Mvt e p => if Rle_dec (DGF.project_p p) (threshold e) then src e else tgt e
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
destruct Hld, (Rle_dec (DGF.project_p p) (threshold e)),
              (Rle_dec (DGF.project_p p0) (threshold e0)).
apply src_compat; assumption. rewrite H0, H in r; contradiction.
rewrite <- H0, <- H in r; contradiction. apply tgt_compat; assumption.
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
            match (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
                             (AGF.Config.target (AGF.Config.robot_info rcA))) with
             | Some e =>
                if Rle_dec (dist) (threshold e) then AGF.Moving false else AGF.Moving true
             | None => AGF.Moving false
            end
          | DGF.Mvt e p => if Rle_dec (DGF.project_p p) (threshold e) then 
                              if Rle_dec (dist + (DGF.project_p p)) (threshold e) 
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
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
             (AGF.Config.target (AGF.Config.robot_info rcA))) eqn : Hedge,
  (DGF.Config.loc (cD (Good g))) eqn : HlD.
  destruct (Rle_dec (dist) (threshold e)) eqn : Hthresh; now exfalso.
  destruct (Rle_dec (DGF.project_p p) (threshold e0)).
  destruct (Rle_dec (dist + DGF.project_p p) (threshold e0)); now exfalso.
  now exfalso. now exfalso.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (Rle_dec (dist + DGF.project_p p) (threshold e)); now exfalso.
  now exfalso.
  unfold rcA2D in *; simpl in *. apply DGF.step_delta in HstepD.
  assert (Heq : exists l, Veq (AGF.Config.loc rcA) l).
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
  assert (Veq (AGF.Config.source (AGF.Config.robot_info rcA1))
              (AGF.Config.source (AGF.Config.robot_info rcA2))) by apply HrcA.
  assert (Veq (AGF.Config.target (AGF.Config.robot_info rcA1))
              (AGF.Config.target (AGF.Config.robot_info rcA2))) by apply HrcA.
  assert (Hedge_co := find_edge_compat (AGF.Config.source (AGF.Config.robot_info rcA1)) 
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
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA1))
          (AGF.Config.target (AGF.Config.robot_info rcA1))) eqn : Hedge1,
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA2))
          (AGF.Config.target (AGF.Config.robot_info rcA2))) eqn : Hedge2; simpl in *;
  try rewrite Hstep1; simpl in *;
    try (assert (Hst := DGF.step_compat);
  specialize (Hst daD id1 id2 Hid rcD rcD (reflexivity rcD));
  rewrite Hstep1, Hstep2 in Hst; now unfold DGF.Aom_eq in Hst);
  try (now exfalso);
  assert (Hst := DGF.step_compat);
  specialize (Hst daD id1 id2 Hid (cD id1) (cD id2) HrcD);
  rewrite Hstep1, Hstep2 in Hst; unfold DGF.Aom_eq in Hst;
  assert (Hfind := find_edge_compat (AGF.Config.source (AGF.Config.robot_info rcA1))
                                    (AGF.Config.source (AGF.Config.robot_info rcA2)) H
                                    (AGF.Config.target (AGF.Config.robot_info rcA1))
                                    (AGF.Config.target (AGF.Config.robot_info rcA2)) H0);
  rewrite Hedge1, Hedge2 in Hfind; try discriminate;
  try assert (HEeq : Eeq e1 e2) by (apply Hfind);
  try (assert (threshold e1 = threshold e2) by now apply threshold_compat, HEeq);
  try (rewrite HrcD; intuition); try (rewrite <- HrcD; intuition); intuition.
  rewrite H1, Hst.
  destruct (Rle_dec dist0 (threshold e2)) eqn : Hdist; auto.
  assert (e' := e); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  assert (e' := e); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  rewrite Hst.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (Rle_dec (dist0 + DGF.project_p p)); auto.
  rewrite <- H2. assert (threshold e = threshold e0) by (now apply threshold_compat).
  rewrite <- H3.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (Rle_dec (dist0 + DGF.project_p p)); auto.
  auto.
  rewrite <- H2. assert (threshold e = threshold e0) by (now apply threshold_compat).
  rewrite <- H3.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (Rle_dec (dist0 + DGF.project_p p)); auto. contradiction. contradiction.
  rewrite <- H2. assert (threshold e = threshold e0) by (now apply threshold_compat).
  destruct (Rle_dec (DGF.project_p p) (threshold e0)).
  rewrite <- H3, Hst in *. 
  destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)); auto. auto.
  rewrite <- H2. assert (threshold e = threshold e0) by (now apply threshold_compat).
  rewrite <- H3, Hst in *.
  destruct (Rle_dec (DGF.project_p p) (threshold e)). 
  destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)); auto. auto.
  destruct (Rle_dec (DGF.project_p p) (threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (threshold e)); auto);
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  destruct (Rle_dec (DGF.project_p p) (threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (threshold e)); auto);
  assert (e' := e1); rewrite HrcD in *; rewrite HrcA in e'; contradiction.
  destruct (Rle_dec (DGF.project_p p) (threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (threshold e)); auto);
  assert (e' := e1); rewrite <- HrcD in *; rewrite <- HrcA in e'; contradiction.
  destruct (Rle_dec (DGF.project_p p) (threshold e)); 
  try (destruct (Rle_dec (dist + DGF.project_p p) (threshold e)); auto);
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
destruct (find_edge (AGF.Config.source (AGF.Config.robot_info confA))
      (AGF.Config.target (AGF.Config.robot_info confA))); try rewrite Hda_cD;
unfold DGF.loc_eq in *;
try (destruct HrcD as (Hl,_); now rewrite Hc1, Hc2 in Hl).
destruct (Rle_dec dist0 (threshold e1)); now unfold AGF.Aom_eq.
destruct HrcD as (Hl,_); rewrite Hc1, Hc2 in Hl;
destruct Hl as (He, Hp).
assert (Hth : (threshold e1) = (threshold e2)) by apply threshold_compat, He.
rewrite Hth, Hp.
destruct (Rle_dec (DGF.project_p p0) (threshold e2)); try (
destruct (Rle_dec (dist0 + DGF.project_p p0) (threshold e2)); now unfold AGF.Aom_eq).
destruct HrcD as (Hl,_); rewrite Hc1, Hc2 in Hl;
destruct Hl as (He, Hp).
assert (Hth : (threshold e1) = (threshold e2)) by apply threshold_compat, He.
rewrite Hth, Hp.
destruct (Rle_dec (DGF.project_p p0) (threshold e2)); try (
destruct (Rle_dec (dist0 + DGF.project_p p0) (threshold e2)); now unfold AGF.Aom_eq).
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
      ++ destruct (Veq_dec (AGF.Config.loc (c (Good g)))
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
      destruct (Veq_dec (AGF.Config.loc (c (Good g)))
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
      destruct (Veq_dec (AGF.Config.loc (c (Good g)))
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
    repeat try (split; simpl); now unfold AGF.Spect.from_config. now rewrite H.
 - simpl in *; assumption.
Save.

Theorem graph_equivD2A : forall (c c': DGF.Config.t) (rbg:DGF.robogram) (da : DGF.demonic_action),
DGF.group_good_def c ->
DGF.Config.eq c' (DGF.round rbg da c) ->
exists da', AGF.Config.eq (ConfigD2A c') (AGF.round (rbgD2A rbg) da' (ConfigD2A c)).
Proof.
intros c c' rbg da Hri HDGF. exists (daD2A da c). intro id.
(* assert (Hax1 := DGF.ri_Loc (c id)).
destruct Hax1 as (lax1, (lax2, ((Hax_src, Hax_tgt), (eD, HeD)))).
assert (Hax2 := DGF.ri_Loc (c' id)).
destruct Hax2 as (lax1', (lax2', ((Hax_src', Hax_tgt'), (eD',HeD')))). *)
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
unfold AGF.round, DGF.round in *; specialize (HDGF id); destruct (HDGF) as (Hloc, (Hsrc, Htgt));
unfold DGF.loc_eq in *;
destruct (DGF.step da id (c id)) eqn : HstepD,
(AGF.step (daD2A da c) id (ConfigD2A c id)) eqn : HstepA, id as [g|b]; try (now exfalso);
unfold daD2A in *; simpl in *;
unfold rcA2D, ConfigD2A, LocD2A in *;
repeat try (split; simpl).
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct dist1 eqn : Hbool.
  - destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
    rewrite <- HlocD in *;
    destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
    destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
    destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
    try (now simpl in *);
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
    destruct (Veq_dec l l1); try (now (simpl in *; rewrite HtgtD in *))));
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
    destruct (Veq_dec l l1); try (now (simpl in *; rewrite HsrcD in *))));
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HlocD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HlocD in *));
    destruct (Veq_dec l l1); try (now (simpl in *; rewrite HlocD in *)))).
    destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))). Focus 2. unfold AGF.Config.eq_RobotConf, LocD2A in *; simpl in n.
             destruct n. unfold LocD2A. rewrite HlocD, HtgtD, HsrcD. now repeat (split).
    rewrite HstepD in HstepA.
    * destruct (Rdec dist0 0) eqn : Hdist. try rewrite HlocD, HsrcD, HtgtD in *;
      destruct (find_edge l3 l1) eqn : Hedge1.
      ** destruct (Rle_dec (dist0) (threshold e1)); try discriminate; simpl in *.
         rewrite <- HstepD_compat in *.
         intuition.
         assert (Hfalse := threshold_pos e1); lra.
      ** assert (Hfalse : AGF.Aom_eq (AGF.Moving false) (AGF.Moving true)).
         now rewrite HstepA. now unfold AGF.Aom_eq in *.
      ** destruct (Rdec dist0 1); simpl in *; try assumption.
         destruct (Veq_dec l l1) eqn : Heql.
          ++ rewrite HlocD in *; now rewrite Hloc.
          ++ simpl in *; now exfalso.
   * try ((destruct (Rdec dist0 0); try (now (simpl in *; rewrite HlocD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HlocD in *));
    destruct (Veq_dec l l0); try (now (simpl in *; rewrite HlocD in *)))).
    simpl in *.
    destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate.
     rewrite HstepD in HstepA.
     destruct (find_edge l2 l0) eqn : Hedge0; try discriminate.
     destruct (Rle_dec dist0 (threshold e1)); try discriminate.
     destruct (find_edge l l0)eqn : HedgeA.
     destruct Hloc as (Heeq, Hpeq).
     symmetry in Hpeq.
     rewrite <- (DGF.subj_proj dist0 p) in Hpeq.
     assert (opt_eq Eeq (find_edge l2 l0) (find_edge l l0)).
     apply find_edge_compat; try now simpl in *.
     specialize (Hli l (reflexivity l));
     destruct Hli as [Hsi | Hti]; try contradiction.
     assumption. now symmetry in Hti.
     rewrite Hedge0, HedgeA in H. simpl in H. rewrite <- Heeq in H. rewrite H in n2.
     rewrite <-Hpeq. destruct (Rle_dec dist0 (threshold e)); try lra.
     rewrite Heeq.
     assert (Hedge : opt_eq Eeq (find_edge l l0) (Some e2)) by now rewrite HedgeA.
     apply find2st in Hedge.
     symmetry; now destruct Hedge.
     assert (Hg := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD); lra.
     specialize (Hli l (reflexivity l));
     destruct Hli as [Hsi | Hti]; try (now symmetry in Hti).
     assert (Hfalse : opt_eq Eeq (find_edge l2 l0) (find_edge l l0)) by now apply find_edge_compat.
     now rewrite HedgeA, Hedge0 in Hfalse.
   * try ((destruct (Rdec dist0 0); try (now (simpl in *; rewrite HlocD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HlocD in *));
    destruct (Veq_dec l l0); try (now (simpl in *; rewrite HlocD in *)))).
    simpl in *.
    destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate.
     rewrite HstepD in HstepA.
     destruct (find_edge l2 l0) eqn : Hedge0; try discriminate.
     destruct (Rle_dec dist0 (threshold e2)); try discriminate.
     destruct (find_edge l l0)eqn : HedgeA.
     destruct Hloc as (Heeq, Hpeq).
     symmetry in Hpeq.
     rewrite <- (DGF.subj_proj dist0 p) in Hpeq.
     assert (opt_eq Eeq (find_edge l2 l0) (find_edge l l0)).
     apply find_edge_compat; try now simpl in *.
     specialize (Hli l (reflexivity l));
     destruct Hli as [Hsi | Hti]; try contradiction.
     assumption. now symmetry in Hti.
     rewrite Hedge0, HedgeA in H. simpl in H. rewrite <- Heeq in H. rewrite H in n2.
     rewrite <-Hpeq. destruct (Rle_dec dist0 (threshold e)); try lra.
     rewrite Heeq.
     assert (Hedge : opt_eq Eeq (find_edge l l0) (Some e3)) by now rewrite HedgeA.
     apply find2st in Hedge.
     symmetry; now destruct Hedge.
     assert (Hg := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD); lra.
     specialize (Hli l (reflexivity l));
     destruct Hli as [Hsi | Hti]; try (now symmetry in Hti).
     assert (Hfalse : opt_eq Eeq (find_edge l2 l0) (find_edge l l0)) by now apply find_edge_compat.
     now rewrite HedgeA, Hedge0 in Hfalse.
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HtgtD in *)).
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HsrcD in *)).
   * destruct(Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
     assert (Hmi_aux : Eeq e e /\ p=p) by (split; reflexivity);
     specialize (Hmi v1 v2 e p Hv1 Hv2 Hmi_aux);
     apply find2st in Hmi. rewrite Hv2, Hloc; now destruct Hmi.
     destruct (Rdec dist0 0); try (now simpl in *). 
     now rewrite HlocD in Hloc.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
     now rewrite HsrcD in *.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
     now rewrite HtgtD in *.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
     now rewrite HsrcD in *.
   * destruct (Rle_dec (DGF.project_p p) (threshold e)); rewrite HstepD in HstepA.
     destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate.
     destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)); try discriminate.
     destruct (Rle_dec 1 (DGF.project_p p + dist0)); try now simpl in *.
     simpl in *.
     destruct (Rdec dist0 0); rewrite HlocD in *;
     destruct (Rle_dec (DGF.project_p p0) (threshold e0));
     try lra.
     destruct Hloc.
     rewrite H0, H in r0.
     rewrite <- (DGF.inv_pro) in r0.
     lra.
     assert (Hpro := DGF.project_p_image p);
     assert (Hdi := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD). lra.
     assert (Hmi_aux : Eeq e e ∧ p = p) by now split. 
     specialize (Hmi v1 v2 e p Hv1 Hv2 Hmi_aux).
     destruct Hloc.
     symmetry in H.
     assert (Hf : opt_eq Eeq (Some e) (Some e0)) by now apply H.
     rewrite Hf in Hmi.
     apply find2st in Hmi; symmetry; now rewrite Hv2.
     destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate.
   * destruct (Rle_dec (DGF.project_p p) (threshold e)); rewrite HstepD in HstepA.
     destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate.
     destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)); try discriminate.
     destruct (Rle_dec 1 (DGF.project_p p + dist0)); try now simpl in *.
     simpl in *.
     destruct (Rdec dist0 0); rewrite HlocD in *;
     destruct (Rle_dec (DGF.project_p p0) (threshold e0));
     try lra.
     destruct Hloc.
     rewrite H0, H in r0.
     rewrite <- (DGF.inv_pro) in r0.
     lra.
     assert (Hpro := DGF.project_p_image p);
     assert (Hdi := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD). lra.
     assert (Hmi_aux : Eeq e e ∧ p = p) by now split. 
     specialize (Hmi v1 v2 e p Hv1 Hv2 Hmi_aux).
     destruct Hloc.
     symmetry in H.
     assert (Hf : opt_eq Eeq (Some e) (Some e0)) by now apply H.
     rewrite Hf in Hmi.
     apply find2st in Hmi; symmetry; now rewrite Hv2.
     destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate.
  * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
     now rewrite HtgtD in *.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
     now rewrite HtgtD in *.
 - simpl in *. destruct (DGF.Config.loc (c (Good g))) eqn : HlocD;
    destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD'; simpl in *;
    rewrite <- HlocD in *;
    destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
    destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
    rewrite <- HtgtD, <- HsrcD in *; try rewrite HsrcD, HtgtD in *; try now simpl in *;
    rewrite HstepD in *.
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
    destruct (Veq_dec l l1); try (now (simpl in *; rewrite HtgtD in *))));
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
    destruct (Veq_dec l l1); try (now (simpl in *; rewrite HsrcD in *))));
    try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HlocD in *));
    destruct (Rdec dist0 1); try (now (simpl in *; rewrite HlocD in *));
    destruct (Veq_dec l l1); try (now (simpl in *; rewrite HlocD in *)))).
    destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))). Focus 2. unfold AGF.Config.eq_RobotConf, LocD2A in *; simpl in n.
             destruct n. unfold LocD2A. rewrite HlocD, HtgtD, HsrcD. now repeat (split).
    rewrite HstepD in HstepA.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))). Focus 2. unfold AGF.Config.eq_RobotConf, LocD2A in *; simpl in n.
             destruct n. unfold LocD2A. rewrite HlocD, HtgtD, HsrcD. now repeat (split).
      destruct (Rdec dist0 0).
      ** now rewrite HlocD in *.
      ** destruct (Rdec dist0 1).
         ++ simpl in *. rewrite HtgtD, HlocD, HsrcD in *.
            destruct (find_edge l3 l1) eqn : Hf.
            rewrite HstepD_compat in HstepA.
            destruct (Rle_dec dist (threshold e2)).
            assert (Hfalse := threshold_pos e2).
            lra.
            discriminate.
            specialize (Hex_e l3 l1 (reflexivity l3) (reflexivity l1)).
            destruct Hex_e as (efalse, Hfalse).
            now rewrite Hf in Hfalse.
         ++ destruct (Veq_dec l l1). now rewrite HlocD in Hloc.
            simpl in *. now exfalso.
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Veq_dec l l1); try (now (simpl in *; rewrite HsrcD in *)).
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l1); try (now (simpl in *; rewrite HtgtD in *)).
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l1); try (now (simpl in *; rewrite HtgtD in *)).
   *  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))).
     rewrite HstepD in *.
     destruct (Rdec dist0 0).
      ** now rewrite HlocD in *.
      ** destruct (Rdec dist0 1).
         ++ simpl in *. now rewrite HtgtD, HlocD, HsrcD in *.
         ++ destruct (Veq_dec l l0). now rewrite HlocD in *.
            simpl in *. destruct Hloc as (Heq_e, Heq_p).
            rewrite HlocD, HtgtD, HsrcD in *;
            symmetry in Heq_p;
            rewrite <- DGF.subj_proj in Heq_p;
            rewrite HstepD_compat, Heq_p in *.
            assert (opt_eq Eeq (find_edge l2 l0) (find_edge l3 l1)).
            now apply find_edge_compat.
            unfold DGF.Location.eq ,DGF.loc_eq in *.
            specialize (Hex_e l2 l0 (reflexivity l2) (reflexivity l0)).
            destruct (find_edge l2 l0) eqn : He'; try discriminate.
            destruct (Hli l (reflexivity l)) as [Hsi | Hti]; try (now symmetry in Hti).
            destruct (find_edge l l0) eqn : He3.
            assert (Hhelp : opt_eq Eeq (find_edge l l0) (Some e2)) by (now rewrite He3);
            rewrite <- Hsi in Hhelp. rewrite He' in Hhelp.
            simpl in *.
            assert (threshold e = threshold e1).
            apply threshold_compat.
            now rewrite Hhelp.
            rewrite H0.
            destruct (Rle_dec (DGF.project_p p) (threshold e1)); try discriminate.
            assert (Hhelp' : opt_eq Eeq (find_edge l l0) (Some e2)) by now rewrite He3.
            apply find2st in Hhelp'. destruct Hhelp' as (Hfs, Hft).
            now rewrite Heq_e.
            assert (Hhelp : opt_eq Eeq (find_edge l2 l0) (Some e1)) by now rewrite He'.
            now rewrite Hsi, He3 in Hhelp.
            now destruct Hex_e.
            assert (Hfl := DGF.step_flexibility da (Good g) (c (Good g)) dist HstepD);
            lra.
         ** destruct n. unfold rcD2A, LocD2A; now rewrite HlocD, HsrcD, HtgtD.
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HsrcD in *)).
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HtgtD in *)).
   * try destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HtgtD in *)).
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)) eqn : Hpd; simpl in *;
     rewrite HlocD, HtgtD, HsrcD, HstepD in *; try (now exfalso).
     destruct (Rle_dec (DGF.project_p p) (threshold e)).
     simpl in *.
     destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g))))
             .
     destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)).
     assert (Hfalse := threshold_pos e). lra. discriminate.
     destruct n.
     unfold rcD2A, LocD2A. simpl in *. repeat split.
     rewrite HlocD; simpl in *.
     destruct (Rle_dec(DGF.project_p p) (threshold e)); try lra.
     reflexivity.
     simpl in *. rewrite HsrcD. reflexivity.
     simpl in *. rewrite HtgtD. reflexivity.
     assumption.
     now destruct (Rdec dist0 0).
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *; now rewrite HsrcD in Hsrc.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *; now rewrite HtgtD in Htgt.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *; now rewrite HtgtD in Htgt.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *. now exfalso.
     destruct (Rdec dist0 0).
     rewrite HlocD in *. destruct Hloc as (He_eq, Hp_eq).
     assert (Hte : threshold e = threshold e0) by (now apply threshold_compat).
     rewrite <- Hte, Hp_eq.
     destruct (Rle_dec (DGF.project_p p) (threshold e)).
     now apply src_compat. now apply tgt_compat.
     rewrite HstepD in *.
     destruct Hloc as (He_eq,Hp_eq). rewrite HsrcD, HtgtD in *. rewrite Hp_eq;
    assert (Hte : threshold e = threshold e0) by (now apply threshold_compat);
    rewrite <- Hte;
     destruct (Rle_dec (DGF.project_p p) (threshold e));
    destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e));
    destruct (AGF.Config.eq_Robotconf_dec
            {|
            AGF.Config.loc := src e;
            AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
            (rcD2A (c (Good g))));
    destruct (AGF.Config.eq_Robotconf_dec
            {|
            AGF.Config.loc := tgt e;
            AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
            (rcD2A (c (Good g))));
    try (now exfalso); try (
    assert (Hfalse := threshold_pos e); lra); try assumption;
    try (now apply src_compat); try (now apply tgt_compat);
    rewrite <- DGF.inv_pro; try (assert (0 < DGF.project_p p + dist0 < 1)%R;
    assert (Hde := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hpp := DGF.project_p_image p); lra);
    destruct (Rle_dec (DGF.project_p p + dist0)); try lra;
    try (now apply src_compat); try (now apply tgt_compat).
    rewrite <- e1 in e2. destruct e2 as (Hle, _); simpl in *.
    assert (Hfalse := NoAutoLoop e); now symmetry in Hle.
    destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate.
    destruct n4; rewrite <- e1; try (split; now simpl).
    unfold rcD2A, LocD2A in e1. 
    rewrite HtgtD, HsrcD, HlocD in *. destruct e1 as (Hle,_). simpl in *.
    destruct (Rle_dec (DGF.project_p p) (threshold e)) ; try lra.
    assert (Hfalse := NoAutoLoop e); now symmetry in Hle.
    destruct n2. unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try (split; simpl);
    try assumption. now destruct (Rle_dec (DGF.project_p p) (threshold e)).
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *; now rewrite HsrcD in Hsrc.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *; now rewrite HtgtD in Htgt.
   * destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *; now rewrite HtgtD in Htgt.
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Veq_dec l l1); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      simpl in *;  now simpl in *);
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Veq_dec l l0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
  try (destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; now simpl in *); try now simpl in *.
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Veq_dec l l1); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      simpl in *;  now simpl in *);
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      destruct (Veq_dec l l0); try (rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; now simpl in *);
  try (destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; now simpl in *); try now simpl in *. 
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  try rewrite HlocD in *;
  try (assumption); try (now exfalso);
  destruct Hloc as (He, Hp); rewrite Hp;
  assert (Hth : threshold e = threshold e0) by (now apply threshold_compat);
  rewrite Hth; destruct (Rle_dec (DGF.project_p p) (threshold e0));
  try (now apply src_compat); try (now apply tgt_compat).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  try (now simpl in *); try (now exfalso); destruct Hsrc as (Hse, Hsp);
  assert (Hts : threshold ebs = threshold ebs') by (now apply threshold_compat); rewrite Hts, Hsp;
  destruct (Rle_dec (DGF.project_p pbs) (threshold ebs'));
  try (now apply src_compat); try (now apply tgt_compat).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  try (now simpl in *); try (now exfalso); destruct Htgt as (Hte, Htp);
  assert (Htt : threshold ebt = threshold ebt') by (now apply threshold_compat); rewrite Htt, Htp;
  destruct (Rle_dec (DGF.project_p pbt) (threshold ebt'));
  try (now apply src_compat); try (now apply tgt_compat).
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HsrcD in *))));
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HtgtD in *))));
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lgl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge lgs lgt) as [ef| ]; try discriminate;
  destruct (Rle_dec dist0 (threshold ef)); discriminate);
  destruct (Rle_dec (DGF.project_p pgl) (threshold egl));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p pgl) (threshold egl)) ; discriminate).
+  destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HsrcD in *))));
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HtgtD in *))));
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lgl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge lgs lgt) as [ef| ]; try discriminate;
  destruct (Rle_dec dist0 (threshold ef)); discriminate);
  destruct (Rle_dec (DGF.project_p pgl) (threshold egl));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p pgl) (threshold egl)) ; discriminate).
+  destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HsrcD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HsrcD in *))));
  try (now (destruct (Rdec dist0 0); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Rdec dist0 1); try (now (simpl in *; rewrite HtgtD in *));
     destruct (Veq_dec l l0); try (now (simpl in *; rewrite HtgtD in *))));
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lgl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge lgs lgt) as [ef| ]; try discriminate;
  destruct (Rle_dec dist0 (threshold ef)); discriminate);
  destruct (Rle_dec (DGF.project_p pgl) (threshold egl));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p pgl) (threshold egl)) ; discriminate).
+ rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.loc (c (Byz b))) as [lbl | ebl pbl] eqn : HlocD; simpl in *;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge lbs lbt) as [ef | ]; try discriminate;
  destruct (Rle_dec dist0 (threshold ef)); discriminate).
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); discriminate.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) lbt) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) lbt) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge lbs (src ebt)) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge lbs (tgt ebt)) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) (src ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) (tgt ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) (src ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) (tgt ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
+ rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.loc (c (Byz b))) as [lbl | ebl pbl] eqn : HlocD; simpl in *;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge lbs lbt) as [ef | ]; try discriminate;
  destruct (Rle_dec dist0 (threshold ef)); discriminate).
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); discriminate.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) lbt) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) lbt) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge lbs (src ebt)) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge lbs (tgt ebt)) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) (src ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) (tgt ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) (src ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) (tgt ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
      + rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.loc (c (Byz b))) as [lbl | ebl pbl] eqn : HlocD; simpl in *;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge lbs lbt) as [ef | ]; try discriminate;
  destruct (Rle_dec dist0 (threshold ef)); discriminate).
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); discriminate.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) lbt) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) lbt) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge lbs (src ebt)) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge lbs (tgt ebt)) as [ef | ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) (src ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (src ebs) (tgt ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) (src ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (find_edge (tgt ebs) (tgt ebt)) as [ef| ]; try discriminate;
      destruct (Rle_dec dist0 (threshold ef)); discriminate.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl));
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs));
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)).
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct (Rle_dec (dist0 + DGF.project_p pbl) (threshold ebl)); discriminate.
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct dist eqn : Hbool;
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lgl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  destruct (Rle_dec (DGF.project_p pgl) (threshold egl));
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n0; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (apply DGF.step_delta in HstepD;
  destruct HstepD as ((ll, Hll), Hlt); rewrite HlocD in Hll; now simpl in *).
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct dist eqn : Hbool;
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lgl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  destruct (Rle_dec (DGF.project_p pgl) (threshold egl));
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n0; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (apply DGF.step_delta in HstepD;
  destruct HstepD as ((ll, Hll), Hlt); rewrite HlocD in Hll; now simpl in *).
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct dist eqn : Hbool;
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lgl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  destruct (Rle_dec (DGF.project_p pgl) (threshold egl));
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt egl;
             AGF.Config.robot_info := {| AGF.Config.source := lgs; AGF.Config.target := lgt |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n0; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (apply DGF.step_delta in HstepD;
  destruct HstepD as ((ll, Hll), Hlt); rewrite HlocD in Hll; now simpl in *).
+ rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.loc (c (Byz b))) as [lbl | ebl pbl] eqn : HlocD; simpl in *.
  - destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
    destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hn.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hn.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt, Hnl; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n2. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
+ rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.loc (c (Byz b))) as [lbl | ebl pbl] eqn : HlocD; simpl in *.
  - destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
    destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hn.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hn.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt, Hnl; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n2. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
+ rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.loc (c (Byz b))) as [lbl | ebl pbl] eqn : HlocD; simpl in *.
  - destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
    destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hn.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {| AGF.Config.source := lbs; AGF.Config.target := lbt |} |}
             (rcD2A (c (Byz b)))); try discriminate.
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hn.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hn; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := lbt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnt, Hnl; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := lbs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
     destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := lbl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hns, Hnt; now simpl in *.
  - destruct (Rle_dec (DGF.project_p pbl) (threshold ebl)) eqn : Hnl;
    destruct (Rle_dec (DGF.project_p pbs) (threshold ebs)) eqn : Hns;
    destruct (Rle_dec (DGF.project_p pbt) (threshold ebt)) eqn : Hnt.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := src ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := src ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n1. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt ebl;
             AGF.Config.robot_info := {|
                                      AGF.Config.source := tgt ebs;
                                      AGF.Config.target := tgt ebt |} |} 
             (rcD2A (c (Byz b)))); try discriminate;
      destruct n2. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD, Hnl, Hns, Hnt; now simpl in *.
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  destruct Hloc as (Hel, Hpl);
  assert (Htl : threshold egl = threshold egl') by (now apply threshold_compat);
  rewrite Hpl, Htl; destruct (Rle_dec (DGF.project_p pgl) (threshold egl'));
  try (now apply src_compat); try (now apply tgt_compat).
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
  destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) as [lgs | egs pgs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) as [lgs' | egs' pgs'] eqn : HsrcD';
  rewrite HstepD in HstepA; try (now simpl in *);
  destruct Hsrc as (Hel, Hpl);
  assert (Htl : threshold egl = threshold egs') by (now apply threshold_compat);
  rewrite Hpl, Htl; destruct (Rle_dec (DGF.project_p pgl) (threshold egs'));
  try (now apply src_compat); try (now apply tgt_compat).
+ destruct (Hri g) as (Hrid, (Hli, (Hmi, Hex_e))).
  unfold DGF.ri_loc_def in *.
  specialize (Hrid g).
  destruct Hrid as (v1, (v2, (Hv1, Hv2))).
(*   destruct (DGF.Config.loc (c (Good g))) as [lgl | egl pgl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) as [lgl' | egl' pgl'] eqn : HlocD'; *)
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) as [lgt | egt pgt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) as [lgt' | egt' pgt'] eqn : HtgtD';
  rewrite HstepD in HstepA; try (now simpl in *).
  - cut (Veq lgt' match DGF.pgm rbg (ConfigD2A c)
              with
                | DGF.Loc l => l
                | DGF.Mvt e p =>
                    if Rle_dec (DGF.project_p p) (threshold e) then src e else tgt e
              end); trivial; [].
    cut (Veq lgt' match DGF.pgm rbg ((DGF.Spect.from_config (DGF.project c)))
                with
    | DGF.Loc l => l
    | DGF.Mvt e p => if Rle_dec (DGF.project_p p) (threshold e) then src e else tgt e
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
    assert (Hthpgm : threshold e = threshold e0) by now apply threshold_compat.
    rewrite Hthpgm.
    intros Hv.
    destruct (Rle_dec (DGF.project_p p0) (threshold e0)).
    rewrite Hv; now apply src_compat.
    rewrite Hv; now apply tgt_compat.
    now destruct (DGF.pgm rbg (DGF.Spect.from_config (DGF.project c))).
  - assert (Hpgm := DGF.pgm_loc rbg (DGF.Spect.from_config (DGF.project c))).
    destruct Hpgm as (vf, Hfalse). now rewrite Hfalse in Htgt.
+ rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.loc (c (Byz b))) as [lbl | ebl pbl] eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) as [lbl' | ebl' pbl'] eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (DGF.relocate_byz da b) as [lrb | erb prb] eqn : Hrb;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Hloc as (Hel, Hpl);
  assert (Hth : (threshold ebl')= (threshold erb)) by (now apply threshold_compat);
  rewrite <- Hpl, Hth; destruct ( Rle_dec (DGF.project_p pbl') (threshold erb));
  try (now apply src_compat); try (now apply tgt_compat).
+ destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) as [lbs | ebs pbs] eqn : HsrcD;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) as [lbs' | ebs' pbs'] eqn : HsrcD';
  destruct (DGF.relocate_byz da b) as [lrb | erb prb] eqn : Hrb;
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Hsrc as (Hes, Hps);
  assert (Hth : (threshold ebs')= (threshold ebs)) by (now apply threshold_compat);
  rewrite <- Hps, Hth; destruct ( Rle_dec (DGF.project_p pbs') (threshold ebs));
  try (now apply src_compat); try (now apply tgt_compat).
+ rewrite HstepD in HstepA.
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) as [lbt | ebt pbt] eqn : HtgtD;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) as [lbt' | ebt' pbt'] eqn : HtgtD';
  try assumption; try (now exfalso); try (now simpl in *);
  destruct Htgt as (Het, Hpt);
  assert (Hth : (threshold ebt')= (threshold ebt)) by (now apply threshold_compat);
  rewrite <- Hpt, Hth; destruct ( Rle_dec (DGF.project_p pbt') (threshold ebt));
  try (now apply src_compat); try (now apply tgt_compat).
Qed.

