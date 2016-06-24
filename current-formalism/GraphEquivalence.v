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
        | DGF.Mvt e p Hp => if Rle_dec p (threshold e) then src e else tgt e
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
destruct ld1, ld2; auto. exfalso; assumption. exfalso; assumption.
destruct Hld, (Rle_dec p (threshold e)), (Rle_dec p0 (threshold e0)).
apply src_compat; assumption. rewrite H0, H in r; contradiction.
rewrite <- H0, <- H in r; contradiction. apply tgt_compat; assumption.
Qed.

Instance ConfigD2A_compat : Proper (DGF.Config.eq ==> AGF.Config.eq) ConfigD2A.
Proof.
intros cd1 cd2 Hcd id. unfold ConfigD2A. repeat try(split;simpl); apply LocD2A_compat, Hcd.
Qed.

Lemma AGF_DGF_AGF_Config : forall confA: AGF.Config.t,  AGF.Config.eq confA (ConfigD2A (ConfigA2D confA)).
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

(*Ensuite, pour montrer l'équivalence, on écrit des fonctions de
traduction entre les modèles Atomic et Discrete pour :
+ configuration (check)
+ robogram (check)
+ demonic_action ( TODO )
+ demon
+ round
*)

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


Definition daD2A (daD : DGF.demonic_action) : AGF.demonic_action.
refine {|
  AGF.relocate_byz := fun b => LocD2A ((DGF.relocate_byz daD) b);
  AGF.step := fun id rcA => match (DGF.step daD) id (rcA2D rcA) with
      | DGF.Active sim => AGF.Active sim
      | DGF.Moving dist => 
        match (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
                                     (AGF.Config.target (AGF.Config.robot_info rcA))) with
           | Some e =>
        if Rle_dec dist (threshold e) then AGF.Moving false else AGF.Moving true
           | None => AGF.Moving false
        end
      end |}.
Proof.
+ intros id rcA sim HrcD. unfold AGF.Aom_eq in *.
  destruct (DGF.step daD id (rcA2D rcA)) eqn : HstepD, 
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
             (AGF.Config.target (AGF.Config.robot_info rcA))) eqn : Hedge.
  destruct (Rle_dec dist (threshold e)) eqn : Hthresh; now exfalso.
  now exfalso.
  unfold rcA2D in *; simpl in *.
  apply (DGF.step_delta daD) in HstepD. (* 
  unfold DGF.Location.eq, AGF.Location.eq, DGF.loc_eq in *. *)
  destruct (DGF.Config.loc (rcA2D rcA)) eqn : Heq_loc,
  (DGF.Config.target (DGF.Config.robot_info (rcA2D rcA))) eqn : Heq_tgt; simpl in *;
  now unfold AGF.Location.eq. admit.
+ intros id1 id2 Hid rcA1 rcA2 HrcA. unfold AGF.Aom_eq. 
  assert (Veq (AGF.Config.source (AGF.Config.robot_info rcA1))
              (AGF.Config.source (AGF.Config.robot_info rcA2))) by apply HrcA.
  assert (Veq (AGF.Config.target (AGF.Config.robot_info rcA1))
              (AGF.Config.target (AGF.Config.robot_info rcA2))) by apply HrcA.
  assert (Hedge_co := find_edge_compat (AGF.Config.source (AGF.Config.robot_info rcA1)) 
                          (AGF.Config.source (AGF.Config.robot_info rcA2)) H 
                          (AGF.Config.target (AGF.Config.robot_info rcA1))
                          (AGF.Config.target (AGF.Config.robot_info rcA2)) H0).
  destruct (DGF.step daD id1 (rcA2D rcA1)) eqn : Hstep1,
  (DGF.step daD id2 (rcA2D rcA2)) eqn:Hstep2,
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA1))
          (AGF.Config.target (AGF.Config.robot_info rcA1))) eqn : Hedge1,
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA2))
          (AGF.Config.target (AGF.Config.robot_info rcA2))) eqn : Hedge2; simpl in *;
  try (assert (Hst := DGF.step_compat);
  specialize (Hst daD id1 id2 Hid (rcA2D rcA1) (rcA2D rcA2) (rcA2D_compat HrcA));
  rewrite Hstep1, Hstep2 in Hst; now unfold DGF.Aom_eq in Hst).
  - destruct (Rle_dec dist (threshold e)),(Rle_dec dist0 (threshold e0)); auto.
  assert (Hth := threshold_compat e e0 Hedge_co).
  rewrite Hth in r. exfalso. apply n.
  assert (Hst := DGF.step_compat).
  specialize (Hst daD id1 id2 Hid (rcA2D rcA1) (rcA2D rcA2) (rcA2D_compat HrcA)).
  rewrite Hstep1, Hstep2 in Hst. unfold DGF.Aom_eq in Hst. rewrite Hst in r.
  assumption.
  assert (Hth := threshold_compat e e0 Hedge_co).
  rewrite Hth in n. exfalso. apply n.
  assert (Hst := DGF.step_compat).
  specialize (Hst daD id1 id2 Hid (rcA2D rcA1) (rcA2D rcA2) (rcA2D_compat HrcA)).
  rewrite Hstep1, Hstep2 in Hst. unfold DGF.Aom_eq in Hst. rewrite <- Hst in r.
  assumption.
Qed. 


Definition daA2D (daA : AGF.demonic_action) : DGF.demonic_action.
refine {| 
  DGF.relocate_byz := fun b => DGF.Loc ((AGF.relocate_byz daA) b);
  DGF.step := fun id rcD => 
              match ((AGF.step daA) id (rcD2A rcD)) with
                | AGF.Active sim => DGF.Active sim
                | AGF.Moving b => if b then DGF.Moving 1%R else DGF.Moving 0%R
              end 
  (* DGF.step_delta := forall id rcD sim, *) |}.
Proof.
+ intros id rcD sim HrcA. unfold rcD2A in HrcA.
destruct (DGF.Config.loc rcD). now exists l.
unfold DGF.Aom_eq in HrcA. unfold DGF.Location.eq, DGF.loc_eq.
destruct (AGF.step daA id (rcD2A rcD)).
unfold DGF.Location.eq, DGF.loc_eq.
 assert (Hstep_DeltaA := AGF.step_delta daA).
specialize (Hstep_DeltaA id (rcD2A rcD) sim).
destruct (AGF.step daA id (rcD2A rcD)) eqn : Heq. destruct dist; unfold DGF.Aom_eq in *; now exfalso.
unfold DGF.Aom_eq, AGF.Aom_eq in *. specialize (Hstep_DeltaA HrcA).
unfold DGF.Location.eq, DGF.loc_eq, AGF.Location.eq, rcD2A in *; simpl in *.
unfold LocD2A in *.
destruct (DGF.Config.loc rcD). now exists l. 
destruct (DGF.Config.target (DGF.Config.robot_info rcD)).
destruct rcD as (loc, r_i). destruct loc; simpl.
now exists l. unfold rcD2A, LocD2A in *; simpl in *.
destruct (DGF.Config.target r_i). 
destruct (Rle_dec p (threshold e)).

destruct ( AGF.step daA id rcA).  exists loc. apply HrcA'.
exists (LocD2A (DGF.Config.loc rcD)).
unfold LocD2A in *. admit.
+ intros id1 id2 Hid rcD1 rcD2 HrcD. unfold DGF.Aom_eq.
  assert(Hs1_eq := AGF.step_compat daA id1 id2 Hid (rcD2A rcD1) (rcD2A rcD2) (rcD2A_compat HrcD)).
  destruct (AGF.step daA id1 (rcD2A rcD1)) eqn : Hstep1,
  (AGF.step daA id2 (rcD2A rcD2)) eqn:Hstep2.
  destruct dist, dist0; auto. unfold AGF.Aom_eq in *. discriminate.
  unfold AGF.Aom_eq in *. discriminate.
  destruct dist; now unfold AGF.Aom_eq in *.
  destruct dist; now unfold AGF.Aom_eq.
  auto.
+ intros id confD r. destruct (AGF.step daA id (rcD2A confD)).
  destruct dist; auto.


Theorem graph_equiv : forall (c c': AGF.Config.t) (rbg:AGF.robogram) (da:AGF.demonic_action),
c' = AGF.round rbg da c -> exists da', ConfigA2D c' = DGF.round (rbgA2D rbg) da' (ConfigA2D c).
Proof.
intros c c' rbg da HAGF.

Save.


