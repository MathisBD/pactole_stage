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
intros SD1 SD2 HSD. unfold DGF.Location.eq, DGF.loc_eq, DGF.Spect.eq in *.
apply (AGF.pgm_compat rbgA). now unfold AGF.Spect.eq.
Defined.

Instance rbgA2D_compat : Proper (AGF.req ==> DGF.req) rbgA2D.
Proof.
intros ra1 ra2 Hra. unfold rbgA2D, DGF.req. intros sd1 sd2 Hsd. simpl.
fold AGF.Location.eq.  apply Hra. now unfold DGF.Spect.eq, AGF.Spect.eq in *.
Qed.

Definition rbgD2A (rbgD : DGF.robogram) : AGF.robogram.
refine {| AGF.pgm := fun s => LocD2A ((DGF.pgm rbgD) s) |}.
Proof.
intros SA1 SA2 HSA. unfold AGF.Location.eq, AGF.Spect.eq in *.
apply LocD2A_compat. apply (DGF.pgm_compat rbgD). now unfold DGF.Spect.eq.
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
+ intros id rcA sim HrcD. unfold AGF.Aom_eq in *.
  destruct (AGF.Config.eq_Robotconf_dec rcA (rcD2A (cD id))); try discriminate.
  destruct e as (Hl, (Hs, Ht)).
  assert (Hax1 := DGF.ri_Loc (cD id)).
  destruct Hax1 as (lax1, (lax2, ((Hax_src, Hax_tgt), (eD, HeD)))).
  destruct (DGF.step daD id (cD id)) eqn : HstepD, 
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
             (AGF.Config.target (AGF.Config.robot_info rcA))) eqn : Hedge,
  (DGF.Config.loc (cD id)) eqn : HlD.
  destruct (Rle_dec (dist) (threshold e)) eqn : Hthresh; now exfalso.
  destruct (Rle_dec (DGF.project_p p) (threshold e0)).
  destruct (Rle_dec (dist + DGF.project_p p) (threshold e0)); now exfalso.
  now exfalso. now exfalso.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (Rle_dec (dist + DGF.project_p p) (threshold e)); now exfalso.
  now exfalso.
  unfold rcA2D in *; simpl in *. apply (DGF.step_delta daD) in HstepD.
  assert (Heq : exists l, Veq (AGF.Config.loc rcA) l).
  now exists (AGF.Config.loc rcA).
  unfold DGF.Location.eq, AGF.Location.eq, DGF.loc_eq in *.
  rewrite Hax_tgt in HstepD. rewrite HlD in *. try (now exfalso).
  simpl in *. rewrite Hl, Ht.
  unfold rcD2A, LocD2A. simpl in *. now rewrite Hax_tgt.
  apply (DGF.step_delta daD) in HstepD.
  destruct HstepD.
  destruct H. rewrite HlD in H. now unfold DGF.Location.eq, DGF.loc_eq.
  apply (DGF.step_delta daD) in HstepD.
  destruct HstepD.
  unfold rcD2A, LocD2A in *; simpl in *. rewrite Hax_tgt, Hax_src in *.
  assert (opt_eq Eeq (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
          (AGF.Config.target (AGF.Config.robot_info rcA)))
          (find_edge lax1 lax2)).
  apply find_edge_compat; assumption. now rewrite HeD, Hedge in H1.
  unfold rcD2A, LocD2A in *; simpl in *. rewrite Hax_tgt, Hax_src in *.
  assert (opt_eq Eeq (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
          (AGF.Config.target (AGF.Config.robot_info rcA)))
          (find_edge lax1 lax2)).
  apply find_edge_compat; assumption. now rewrite HeD, Hedge in H.
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
+ intros id rcD sim HrcA .
destruct (AGF.step daA id (cA id)) eqn : HstepA, 
(DGF.Config.eq_Robotconf_dec rcD (rcA2D (cA id))) eqn : HrcD; unfold rcD2A, LocD2A in *; simpl in *.
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

Theorem graph_equivD2A : forall (c c': DGF.Config.t) (rbg:DGF.robogram) (da:DGF.demonic_action),
DGF.Config.eq c' (DGF.round rbg da c) ->
exists da', AGF.Config.eq (ConfigD2A c') (AGF.round (rbgD2A rbg) da' (ConfigD2A c)).
Proof.
intros c c' rbg da HDGF. exists (daD2A da c). intro id.
assert (Hax1 := DGF.ri_Loc (c id)).
destruct Hax1 as (lax1, (lax2, ((Hax_src, Hax_tgt), (eD, HeD)))).
assert (Hax2 := DGF.ri_Loc (c' id)).
destruct Hax2 as (lax1', (lax2', ((Hax_src', Hax_tgt'), (eD',HeD')))).
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
+ destruct dist1 eqn : Hbool.
  - destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
    rewrite <- HlocD in *;
    destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
    destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
    destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate.
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
    * destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))).
      rewrite HstepD in *.
      destruct (find_edge l2 l0) eqn : Hedge2; try discriminate;
      destruct(Rle_dec dist0 (threshold e1)); try discriminate;
      destruct (Rle_dec (DGF.project_p p) (threshold e)); simpl in *;
      destruct (Rdec dist0 0) eqn : Hdist; try rewrite HlocD, HsrcD, HtgtD in *;
      try (now exfalso); destruct (Rdec dist0 1) eqn : Hdist1; simpl in *; try (now exfalso);
      destruct (Veq_dec l l0); rewrite HlocD in *; try (now exfalso);
      simpl in *; rewrite HstepD_compat in Hloc;
      rewrite HsrcD, HtgtD in *. (* assert (Hax : Veq l l2) by admit. *)
      ** assert ( Hax := DGF.ax_cont (c' (Good g)) e p HlocD').
         destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
(*          assert (opt_eq Eeq (find_edge l2 l0) (find_edge l l0)).
         apply find_edge_compat. now symmetry. reflexivity. *)
         destruct (find_edge l l0) eqn : Hedge;
         destruct Hloc as (Heq_edge, Heq_p);
         assert (Hproj_eq : DGF.project_p p = dist) by (
         symmetry; rewrite DGF.subj_proj; symmetry; assumption).
         ++ assert (opt_eq Eeq (find_edge ld1 ld2) (find_edge l2 l0)).
            apply find_edge_compat; rewrite HsrcD' in *;
            assert (Htemp : DGF.loc_eq (DGF.Loc l3) (DGF.Loc ld1)) by now (rewrite Hax1). 
            unfold DGF.loc_eq in *; now rewrite <- Htemp.
            rewrite HtgtD' in *;
            assert (Htemp2 : DGF.loc_eq (DGF.Loc l1) (DGF.Loc ld2)) by now (rewrite Hax2).
            unfold DGF.loc_eq in *; now rewrite <- Htemp2.
            rewrite Hedge2, He in H.
            assert (Heq_e2 : Eeq e e1) by apply H.
            assert (Ht : threshold e1 = threshold e).
            now apply threshold_compat.
            rewrite Ht in n. lra.
         ++ assert (opt_eq Eeq (find_edge ld1 ld2) (find_edge l2 l0)).
            apply find_edge_compat. rewrite HsrcD' in *.
            assert (Htemp : DGF.loc_eq (DGF.Loc l3) (DGF.Loc ld1)) by now rewrite Hax1.
            unfold DGF.loc_eq in *. now rewrite <- Htemp.
            rewrite HtgtD' in *.
            assert (Htemp : DGF.loc_eq (DGF.Loc l1) (DGF.Loc ld2)) by now rewrite Hax2.
            unfold DGF.loc_eq in *. now rewrite <- Htemp.
            rewrite Hedge2, He in H.
            assert (Heq_e2 : Eeq e e1) by apply H.
            assert (Ht : threshold e1 = threshold e).
            now apply threshold_compat.
            rewrite Ht in n. lra.
      ** assert ( Hax := DGF.ax_cont (c' (Good g)) e p HlocD').
         destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
         assert (opt_eq Eeq (find_edge l3 l1) (find_edge l l0)).
            apply find_edge_compat.
            admit.
            assert (opt_eq Eeq (find_edge l1 l3) (find_edge l2 l0)).
            admit.
            rewrite H0 in H.
         destruct (find_edge l l0) eqn : Hedge; simpl in *.
         ++ destruct Hloc. rewrite H1.
            assert (Hf := find_edge_Some e2).
            rewrite <- Hedge in Hf.
            admit. (* on a (opt_eq Eeq (find_edge (src e1) (tgt e1)) (find_edge l l0)) *)
         ++ rewrite Hedge2 in H. contradiction.
      ** destruct n. now repeat split.
   * assert ( Hax := DGF.ax_cont (c (Good g)) e p HlocD).
     destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
     destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := if Rle_dec (DGF.project_p p) (threshold e) then src e else tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))).
     destruct (Rle_dec 1 (DGF.project_p p + dist0)) eqn : Heq1; simpl in *;
     try rewrite HlocD, HsrcD, HtgtD in *.
     ** assert (Eeq e eD').
        assert (Eeq e eD). admit.
        assert (Eeq eD eD').
        assert (opt_eq Eeq (Some eD) (Some eD')).
        rewrite <- HeD, <- HeD'.
        apply find_edge_compat.
        admit. (* faire a partir de Hax_src et Hax_src' *)
        admit. (* faire a partir de Hax_tgt et Hax_tgt' *)
        auto.
        now rewrite H.
        assert (DGF.Location.eq (DGF.Loc (tgt e)) (DGF.Loc l0)).
        rewrite Hax2. unfold DGF.Location.eq, DGF.loc_eq.
        admit (* voir He *).
        unfold DGF.Location.eq, DGF.loc_eq in *.
        now rewrite <- H0.
     ** destruct (Rdec dist0 0); now exfalso.
     ** destruct n. repeat split; simpl;
        unfold LocD2A. now rewrite HlocD. now rewrite HsrcD. now rewrite HtgtD.
   * assert ( Hax := DGF.ax_cont (c (Good g)) e p HlocD).
     destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
     rewrite HstepD in HstepA.
     destruct (Rle_dec 1 (DGF.project_p p + dist0)) eqn : Heq1; simpl in *;
     try rewrite HlocD, HsrcD, HtgtD in *; try (now exfalso). 
     destruct (Rle_dec (DGF.project_p p0) (threshold e0)) eqn : Hp_t2;
     destruct (Rdec dist0 0), Hloc as (Heq_e, Heq_p).
     ** rewrite Heq_e.
        destruct (Rle_dec (DGF.project_p p) (threshold e)) eqn : Hp_t1.
        ++ destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))).
           destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; try discriminate. lra.
           discriminate.
        ++ destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try (now unfold AGF.Aom_eq).
     ** rewrite Heq_e.
        destruct (Rle_dec (DGF.project_p p) (threshold e)) eqn : Hp_t1.
        ++ destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))).
           destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; try discriminate.
           assert (r' := r); rewrite Heq_p in r'.
           rewrite DGF.proj_comm, <- DGF.inv_pro in r'.
           assert (threshold e = threshold e0) by now apply threshold_compat.
           rewrite H in n1. lra.
           assert (H' := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD).
           assert (Hht := threshold_pos e); assert (Hpt := DGF.project_p_image p). lra.
           assert (AGF.Aom_eq (AGF.Moving false) (AGF.Moving true)) by now rewrite HstepA.
           now unfold AGF.Aom_eq.
        ++ destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try (now unfold AGF.Aom_eq).
     ** rewrite Heq_e.
        assert (Heq : opt_eq Eeq (find_edge l1 l) (Some e)).
        assert (Hveq1 : DGF.Location.eq (DGF.Loc l1) (DGF.Loc ld1)) by now rewrite Hax1.
        assert (Hveq2 : DGF.Location.eq (DGF.Loc l) (DGF.Loc ld2)) by now rewrite Hax2.
        assert (Hcompat := find_edge_compat l1 ld1 Hveq1 l ld2 Hveq2).
        now rewrite <- He.
        rewrite <- find_edge_Some in Heq.
        admit (* voir He *).
     ** rewrite Heq_e.
        assert (Heq : opt_eq Eeq (find_edge l1 l) (Some e)).
        assert (Hveq1 : DGF.Location.eq (DGF.Loc l1) (DGF.Loc ld1)) by now rewrite Hax1.
        assert (Hveq2 : DGF.Location.eq (DGF.Loc l) (DGF.Loc ld2)) by now rewrite Hax2.
        assert (Hcompat := find_edge_compat l1 ld1 Hveq1 l ld2 Hveq2).
        now rewrite <- He.
        rewrite <- find_edge_Some in Heq.
        admit (* voir He *).
  - simpl in *. destruct (DGF.Config.loc (c (Good g))) eqn : HlocD;
    destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD'; simpl in *;
    rewrite <- HlocD in *;
    destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
    destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
    rewrite <- HtgtD, <- HsrcD in *.
    *  destruct (AGF.Config.eq_Robotconf_dec
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
            rewrite HstepD, HstepD_compat in HstepA.
            destruct (Rle_dec dist (threshold e1)).
            assert (Hfalse := threshold_pos e1).
            lra.
            discriminate.
            rewrite find_edge_None in Hf.
            specialize (Hf eD).
            assert (Hv1 : DGF.Location.eq (DGF.Loc lax1) (DGF.Loc l3)).
            now rewrite Hax_src.
            assert (Hv2 : DGF.Location.eq (DGF.Loc lax2) (DGF.Loc l1)).
            now rewrite Hax_tgt.
            unfold DGF.Location.eq ,DGF.loc_eq in *.
            assert (Hsr : Veq (src eD) l3) by admit (* voir Hv1 et HeD *).
            assert (Htg : Veq (tgt eD) l1) by admit (* voir Hv2 et HeD *).
            exfalso; apply Hf; now split.
         ++ destruct (Veq_dec l l1). now rewrite HlocD in Hloc.
            simpl in *. now exfalso.
   * destruct (AGF.Config.eq_Robotconf_dec
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
            symmetry in Heq_p;
            rewrite <- DGF.subj_proj in Heq_p.
            rewrite HstepD_compat, Heq_p in *.
            rewrite HsrcD, HtgtD in *.
            assert (opt_eq Eeq (find_edge l2 l0) (find_edge l3 l1)).
            now apply find_edge_compat.
            assert (opt_eq Eeq (find_edge lax1' lax2') (find_edge l3 l1)).
            assert (Hv1 : DGF.Location.eq (DGF.Loc lax1') (DGF.Loc l3)).
            now rewrite Hax_src'.
            assert (Hv2 : DGF.Location.eq (DGF.Loc lax2') (DGF.Loc l1)).
            now rewrite Hax_tgt'.
            unfold DGF.Location.eq ,DGF.loc_eq in *.
            now apply find_edge_compat.
            rewrite <- H0, HeD' in H.
            destruct (find_edge l2 l0) eqn : He'; try discriminate.
            assert (Hax := DGF.ax_cont (c' (Good g)) e p HlocD').
            destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
            assert (opt_eq Eeq (find_edge ld1 ld2) (find_edge l3 l1)).
            apply find_edge_compat.
            rewrite HsrcD' in Hax1.
            assert (DGF.Location.eq (DGF.Loc l3) (DGF.Loc ld1)) by (now rewrite Hax1).
            now unfold DGF.Location.eq, DGF.loc_eq.
            rewrite HtgtD' in Hax2.
            assert (DGF.Location.eq (DGF.Loc l1) (DGF.Loc ld2)) by (now rewrite Hax2).
            now unfold DGF.Location.eq, DGF.loc_eq. rewrite He, <- H0, HeD' in H1.
            assert (threshold e = threshold e1).
            apply threshold_compat.
            rewrite <- H in H1.
            apply H1.
            rewrite H2 in *.
            destruct (Rle_dec (DGF.project_p p) (threshold e1)); try discriminate.
            destruct (find_edge l l0) eqn : He3.
            assert (Veq (src e2) l) by admit (* voir He3 *).
            now rewrite Heq_e.
            assert (Veq l l2).
            admit (* si on est sur un nœud, soit on est au départ, soit a l'arrivé, et on a n1 *).
            assert (Eeq e eD') by apply H1.
            assert (Eeq e1 eD') by apply H.
            rewrite H3, H4, <- H5. admit (* apply He' *).
            now simpl in H.
         ** destruct n. unfold rcD2A, LocD2A; now rewrite HlocD, HsrcD, HtgtD.
   * assert ( Hax := DGF.ax_cont (c (Good g)) e p HlocD).
     destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
     rewrite HstepD in HstepA.
     destruct (Rdec dist0 0);
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
     
     destruct (Rle_dec 1 (DGF.project_p p + dist0)) eqn : Hpd; simpl in *;
     rewrite HlocD, HtgtD, HsrcD in *;try (now exfalso); try (
     assert (Hfalse := threshold_pos e); lra); try assumption.
     destruct n1. unfold rcD2A, LocD2A. repeat try (split; simpl in *); 
     try rewrite HlocD; try rewrite HsrcD; try rewrite HtgtD;
     now destruct (Rle_dec (DGF.project_p p) (threshold e)).
     destruct n1. unfold rcD2A, LocD2A. repeat try (split; simpl in *); 
     try rewrite HlocD; try rewrite HsrcD; try rewrite HtgtD;
     now destruct (Rle_dec (DGF.project_p p) (threshold e)).
  * assert ( Hax := DGF.ax_cont (c (Good g)) e p HlocD).
    destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
    assert ( Hax := DGF.ax_cont (c' (Good g)) e0 p0 HlocD').
    destruct Hax as (ld1', (ld2', ((Hax1', Hax2'), He'))).
    rewrite HstepD in HstepA. simpl in *.
    destruct (Rle_dec 1 (DGF.project_p p + dist0)) eqn : Hpd; simpl in *;
    rewrite HlocD, HtgtD, HsrcD in *; try (now exfalso);
    destruct (Rdec dist0 0);
    destruct Hloc as (He_eq,Hp_eq); rewrite Hp_eq;
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
    destruct (Rle_dec (DGF.project_p (p + DGF.project_p_inv dist0)));
    try (now apply src_compat); try (now apply tgt_compat).
    rewrite <- e1 in e2. destruct e2 as (Hle, _); simpl in *.
    assert (Hfalse := NoAutoLoop e); now symmetry in Hle.
    destruct n2. rewrite DGF.proj_comm, <- DGF.inv_pro. lra.
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD).
    assert (Hte_p := threshold_pos e). assert (Hpos_p := DGF.project_p_image p). lra.
    destruct n2. rewrite DGF.proj_comm, <- DGF.inv_pro. lra.
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD).
    assert (Hte_p := threshold_pos e). assert (Hpos_p := DGF.project_p_image p). lra.
    destruct n3. rewrite DGF.proj_comm, <- DGF.inv_pro. lra.
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD).
    assert (Hte_p := threshold_pos e). assert (Hpos_p := DGF.project_p_image p). lra.
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
    rewrite <- e1 in e2. destruct e2 as (Hle, _); simpl in *.
    assert (Hfalse := NoAutoLoop e); now symmetry in Hle.
    destruct n1. rewrite DGF.proj_comm, <- DGF.inv_pro in r0;
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hte_p := threshold_pos e); assert (Hpos_p := DGF.project_p_image p); lra.
    destruct n1. rewrite DGF.proj_comm, <- DGF.inv_pro in r0;
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hte_p := threshold_pos e); assert (Hpos_p := DGF.project_p_image p); lra.
    destruct n1. rewrite DGF.proj_comm, <- DGF.inv_pro in r0;
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hte_p := threshold_pos e); assert (Hpos_p := DGF.project_p_image p); lra.
    destruct n1. rewrite DGF.proj_comm, <- DGF.inv_pro in r;
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hte_p := threshold_pos e); assert (Hpos_p := DGF.project_p_image p); lra.
    destruct n1. rewrite DGF.proj_comm, <- DGF.inv_pro in r;
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hte_p := threshold_pos e); assert (Hpos_p := DGF.project_p_image p); lra.
    destruct n1. rewrite DGF.proj_comm, <- DGF.inv_pro in r;
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hte_p := threshold_pos e); assert (Hpos_p := DGF.project_p_image p); lra.
    destruct n1. rewrite DGF.proj_comm, <- DGF.inv_pro in r;
    assert (Hd := DGF.step_flexibility da (Good g) (c (Good g)) dist0 HstepD);
    assert (Hte_p := threshold_pos e); assert (Hpos_p := DGF.project_p_image p); lra.
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Veq_dec l l1); try (rewrite HlocD, HsrcD, HtgtD in *; assumption);
      simpl in *; now exfalso);
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Veq_dec l l0); try (rewrite HlocD, HsrcD, HtgtD in *; now exfalso);
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; assumption);
  try (destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; assumption).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Veq_dec l l1); try (rewrite HlocD, HsrcD, HtgtD in *; assumption);
      simpl in *; now exfalso);
  try (destruct (Rdec dist0 0); try (rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Rdec dist0 1); try (simpl in *; rewrite HlocD, HsrcD, HtgtD in *; assumption);
      destruct (Veq_dec l l0); try (rewrite HlocD, HsrcD, HtgtD in *; now exfalso);
      simpl in *; rewrite HlocD, HsrcD, HtgtD in *; assumption);
  try (destruct (Rle_dec 1 (DGF.project_p p + dist0)); simpl in *;
      rewrite HlocD, HsrcD, HtgtD in *; assumption).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  try (assumption); try (now exfalso);
  destruct Hloc as (He, Hp); rewrite Hp;
  assert (Hth : threshold e = threshold e0) by (now apply threshold_compat);
  rewrite Hth; destruct (Rle_dec (DGF.project_p p) (threshold e0));
  try (now apply src_compat); try (now apply tgt_compat).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  try (assumption); try (now exfalso).
+ destruct dist1 eqn : Hbool;
  destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  try (assumption); try (now exfalso).
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge l3 l1); try discriminate;
  destruct (Rle_dec dist0 (threshold e0)); discriminate);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge l2 l0); try discriminate;
  destruct (Rle_dec dist0 (threshold e1)); discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge l3 l1); try discriminate;
  destruct (Rle_dec dist0 (threshold e0)); discriminate);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge l2 l0); try discriminate;
  destruct (Rle_dec dist0 (threshold e1)); discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge l3 l1); try discriminate;
  destruct (Rle_dec dist0 (threshold e0)); discriminate);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct (find_edge l2 l0); try discriminate;
  destruct (Rle_dec dist0 (threshold e1)); discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge l3 l1); try discriminate;
  destruct (Rle_dec dist0 (threshold e0)); discriminate);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge l2 l0); try discriminate;
  destruct (Rle_dec dist0 (threshold e1)); discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge l3 l1); try discriminate;
  destruct (Rle_dec dist0 (threshold e0)); discriminate);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge l2 l0); try discriminate;
  destruct (Rle_dec dist0 (threshold e1)); discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge l3 l1); try discriminate;
  destruct (Rle_dec dist0 (threshold e0)); discriminate);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate;
  destruct (find_edge l2 l0); try discriminate;
  destruct (Rle_dec dist0 (threshold e1)); discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct(AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))); try discriminate);
  try (destruct (Rle_dec (dist0 + DGF.project_p p) (threshold e)) ; discriminate).
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA; destruct dist; simpl in *;
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))); try discriminate;
  destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  destruct (Rle_dec (DGF.project_p p) (threshold e));
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl);
  try (destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g))))); try discriminate;
  try (destruct n0; unfold rcD2A, LocD2A; rewrite HlocD, HtgtD, HsrcD; repeat try split; now simpl).
  rewrite <- e2 in e1; destruct e1 as (Hl,_); simpl in *; symmetry in Hl;
  now assert (Hfalse := NoAutoLoop e).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); discriminate.
  rewrite <- e2 in e1; destruct e1 as (Hl,_); simpl in *; symmetry in Hl;
  now assert (Hfalse := NoAutoLoop e).
  rewrite <- e2 in e1; destruct e1 as (Hl,_); simpl in *; symmetry in Hl;
  now assert (Hfalse := NoAutoLoop e).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))); try discriminate.
  destruct n0. rewrite <- e1. repeat try split; now simpl.
  rewrite <- e2 in e1; destruct e1 as (Hl,_); simpl in *; symmetry in Hl;
  now assert (Hfalse := NoAutoLoop e).
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA.
    destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Good g)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD;try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD;try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD;try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD;try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l3; AGF.Config.target := l1 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := l;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; now simpl.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l2; AGF.Config.target := l0 |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD; try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (Rle_dec (DGF.project_p p) (threshold e)).
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := src e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD;try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
  destruct (AGF.Config.eq_Robotconf_dec
             {|
             AGF.Config.loc := tgt e;
             AGF.Config.robot_info := {| AGF.Config.source := l1; AGF.Config.target := l |} |}
             (rcD2A (c (Byz b)))). discriminate. destruct dist; simpl in *. discriminate.
  destruct n0. unfold rcD2A, LocD2A; rewrite HlocD, HsrcD, HtgtD;try repeat split; simpl;
  destruct (Rle_dec (DGF.project_p p) (threshold e)); try lra; reflexivity.
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  try assumption; try (now exfalso).
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  try assumption; try (now exfalso).
+ destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate;
  try assumption; try (now exfalso). rewrite HstepD in HstepA. 
  unfold AGF.Spect.from_config, DGF.Spect.from_config, DGF.projectS, DGF.projectS_loc, DGF.project in *. 
  rewrite HlocD in *. simpl in *.
  assert ( (ConfigD2A c) = (λ id : Names.ident,
       {|
       AGF.Config.loc := match DGF.Config.loc (c id) with
                         | DGF.Loc l5 => l5
                         | DGF.Mvt e p =>
                             if Rle_dec (DGF.project_p p) (threshold e) then src e else tgt e
                         end;
       AGF.Config.robot_info := {|
                                AGF.Config.source := match
                                                       DGF.Config.source
                                                         (DGF.Config.robot_info (c id))
                                                     with
                                                     | DGF.Loc l5 => l5
                                                     | DGF.Mvt e p =>
                                                         if
                                                          Rle_dec (DGF.project_p p)
                                                            (threshold e)
                                                         then src e
                                                         else tgt e
                                                     end;
                                AGF.Config.target := match
                                                       DGF.Config.target
                                                         (DGF.Config.robot_info (c id))
                                                     with
                                                     | DGF.Loc l5 => l5
                                                     | DGF.Mvt e p =>
                                                         if
                                                          Rle_dec (DGF.project_p p)
                                                            (threshold e)
                                                         then src e
                                                         else tgt e
                                                     end |} |})).
  unfold ConfigD2A, LocD2A. reflexivity. admit (* rewrite <- H.*).
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA; destruct (DGF.relocate_byz da b); try assumption; try now exfalso.
  destruct Hloc as (He, Hp); assert (Hth : (threshold e)= (threshold e0)) by now apply threshold_compat.
  rewrite Hp, Hth. destruct ( Rle_dec (DGF.project_p p0) (threshold e0)). now apply src_compat.
  now apply tgt_compat.
  destruct Hloc as (He, Hp); assert (Hth : (threshold e0)= (threshold e1)) by now apply threshold_compat.
  rewrite Hp, Hth. destruct ( Rle_dec (DGF.project_p p1) (threshold e1)). now apply src_compat.
  now apply tgt_compat.
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA; try assumption.
+ destruct (DGF.Config.loc (c (Byz b))) eqn : HlocD; simpl in *;
  rewrite <- HlocD in *;
  destruct (DGF.Config.loc (c' (Byz b))) eqn : HlocD';
  destruct (DGF.Config.target (DGF.Config.robot_info (c (Byz b)))) eqn : HtgtD; try discriminate;
  destruct (DGF.Config.target (DGF.Config.robot_info (c' (Byz b)))) eqn : HtgtD'; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c (Byz b)))) eqn : HsrcD; try discriminate;
  destruct (DGF.Config.source (DGF.Config.robot_info (c' (Byz b)))) eqn : HsrcD'; try discriminate;
  rewrite HstepD in HstepA; try assumption.
Qed.

