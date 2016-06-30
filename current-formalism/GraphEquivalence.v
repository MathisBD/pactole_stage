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


Definition daD2A (daD : DGF.demonic_action) : AGF.demonic_action.
refine {|
  AGF.relocate_byz := fun b => LocD2A ((DGF.relocate_byz daD) b);
  AGF.step := fun id rcA => match (DGF.step daD) id (rcA2D rcA) with
      | DGF.Active sim => AGF.Active sim
      | DGF.Moving dist => 
        match (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
                                     (AGF.Config.target (AGF.Config.robot_info rcA))) with
           | Some e =>
        if Rle_dec (DGF.project_p dist) (threshold e) then AGF.Moving false else AGF.Moving true
           | None => AGF.Moving false
        end
      end |}.
Proof.
+ intros id rcA sim HrcD. unfold AGF.Aom_eq in *. 
  destruct (DGF.step daD id (rcA2D rcA)) eqn : HstepD, 
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
             (AGF.Config.target (AGF.Config.robot_info rcA))) eqn : Hedge.
  destruct (Rle_dec (DGF.project_p dist) (threshold e)) eqn : Hthresh; now exfalso.
  now exfalso.
  unfold rcA2D in *; simpl in *;
  apply (DGF.step_delta daD) in HstepD.
  assert (Heq : exists l, Veq (AGF.Config.loc rcA) l).
  now exists (AGF.Config.loc rcA).
  unfold DGF.Location.eq, AGF.Location.eq, DGF.loc_eq in *.
  now simpl in *. now exists (AGF.Config.loc rcA).
    unfold rcA2D in *; simpl in *;
  apply (DGF.step_delta daD) in HstepD.
  destruct (DGF.Config.loc (rcA2D rcA)) eqn : Heq_loc,
  (DGF.Config.target (DGF.Config.robot_info (rcA2D rcA))) eqn : Heq_tgt; simpl in *;
  now unfold AGF.Location.eq. now exists (AGF.Config.loc rcA).
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
  - destruct (Rle_dec (DGF.project_p dist) (threshold e)),
             (Rle_dec (DGF.project_p dist0) (threshold e0)); auto.
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
Defined. 

Instance daD2A_compat : Proper (DGF.da_eq ==> AGF.da_eq) daD2A.
Proof.
intros dad1 dad2 HdaD.
unfold daD2A, AGF.da_eq in *.
simpl.
split.
intros id confA.
assert (Hda_cD := DGF.step_da_compat HdaD (reflexivity id) (reflexivity (rcA2D confA))).
unfold DGF.Aom_eq in Hda_cD.
destruct HdaD as (HdaD_G, _).
specialize (HdaD_G id (rcA2D confA)).
destruct (DGF.step dad1 id (rcA2D confA)).
destruct (DGF.step dad2 id (rcA2D confA)).
unfold AGF.Aom_eq.
rewrite HdaD_G.
destruct (match
    find_edge (AGF.Config.source (AGF.Config.robot_info confA))
      (AGF.Config.target (AGF.Config.robot_info confA))
  with
  | Some e => if Rle_dec (DGF.project_p dist0) (threshold e) then AGF.Moving false else AGF.Moving true
  | None => AGF.Moving false
  end); reflexivity.
exfalso; assumption.
destruct (DGF.step dad2 id (rcA2D confA)). now exfalso.
auto.
destruct HdaD as (_,Hb). intros b. apply LocD2A_compat, Hb.
Qed.


(* TODO : trouver une définition vrai, ou rajouter des axioms car la sinon c'est pas vrai.*)
Definition daA2D (daA : AGF.demonic_action) : DGF.demonic_action.
refine {| 
  DGF.relocate_byz := fun b => DGF.Loc ((AGF.relocate_byz daA) b);
  DGF.step := fun id rcD => 
              match ((AGF.step daA) id (rcD2A rcD)) with
                | AGF.Active sim =>  (* if DGF.Location.eq_dec (DGF.Config.loc rcD)
                                                    (DGF.Config.target (DGF.Config.robot_info rcD))
                                     then *) DGF.Active sim
                                     (* else DGF.Moving 1%R *)
                | AGF.Moving b => if b then DGF.Moving 1%R else DGF.Moving 0%R
              end 
  (* DGF.step_delta := forall id rcD sim, *) |}.
Proof.
+ intros id rcD sim HrcA Heq_locD.
destruct (AGF.step daA id (rcD2A rcD)) eqn : HstepA.
 - destruct dist; now exfalso.
 - apply (AGF.step_delta daA) in HstepA.
   unfold DGF.Location.eq, DGF.loc_eq, AGF.Location.eq, rcD2A in *; simpl in *.
   unfold LocD2A in *.
destruct (DGF.Config.loc rcD) eqn : Hh.
destruct (DGF.Location.eq_dec (DGF.Loc l) (DGF.Config.target (DGF.Config.robot_info rcD)));
destruct (DGF.Config.target (DGF.Config.robot_info rcD)) eqn : HH; try assumption;
assert (Htl := DGF.ri_Loc rcD); destruct Htl as (l1, (l2, (Ht, Hs))).
rewrite HH in Ht. discriminate. destruct Heq_locD.  now exfalso.
+ intros id1 id2 Hid rcD1 rcD2 HrcD. unfold DGF.Aom_eq.
  assert(Hs1_eq := AGF.step_compat daA id1 id2 Hid (rcD2A rcD1) (rcD2A rcD2) (rcD2A_compat HrcD)).
  destruct (AGF.step daA id1 (rcD2A rcD1)) eqn : Hstep1,
  (AGF.step daA id2 (rcD2A rcD2)) eqn:Hstep2.
  destruct dist, dist0; auto. unfold AGF.Aom_eq in *. discriminate.
  unfold AGF.Aom_eq in *. discriminate.
  destruct dist; now unfold AGF.Aom_eq in *.
  destruct dist; now unfold AGF.Aom_eq.
  destruct (if DGF.Location.eq_dec (DGF.Config.loc rcD1)
                                   (DGF.Config.target (DGF.Config.robot_info rcD1))
   then DGF.Active sim
   else DGF.Moving 1) eqn : HifD1, 
   (if DGF.Location.eq_dec (DGF.Config.loc rcD2) (DGF.Config.target (DGF.Config.robot_info rcD2))
   then DGF.Active sim0
   else DGF.Moving 1) eqn : HifD2;
     destruct (DGF.Location.eq_dec (DGF.Config.loc rcD1)
            (DGF.Config.target (DGF.Config.robot_info rcD1))),
           (DGF.Location.eq_dec (DGF.Config.loc rcD2)
            (DGF.Config.target (DGF.Config.robot_info rcD2))); try discriminate;
  destruct HrcD as (HlocD, (HsrcD, HtgtD)); fold DGF.Location.eq in HlocD.
  assert (Heqm : DGF.Aom_eq (DGF.Moving dist) (DGF.Moving dist0)).
  rewrite <- HifD1, <- HifD2. reflexivity.
  now unfold DGF.Aom_eq in Heqm.
  rewrite HlocD, HtgtD in n. contradiction.
  rewrite HlocD, HtgtD in e. contradiction.
  unfold AGF.Aom_eq in *. rewrite Hs1_eq in HifD1; rewrite HifD1 in HifD2.
  assert (Heqm : DGF.Aom_eq (DGF.Active sim1) (DGF.Active sim2)).
  rewrite HifD2. reflexivity. now unfold DGF.Aom_eq in Heqm.
+ intros id confD r. destruct (AGF.step daA id (rcD2A confD)).
  destruct dist; intros Hm. assert (Heqm : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving r)).
  now rewrite Hm. unfold DGF.Aom_eq in *. rewrite <- Heqm. lra.
  assert (Heqm : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving r)).
  now rewrite Hm. unfold DGF.Aom_eq in *. rewrite <- Heqm. lra.
  destruct (DGF.Location.eq_dec (DGF.Config.loc confD)
                                (DGF.Config.target (DGF.Config.robot_info confD)));
  intros Hm. discriminate. discriminate.
Defined.

(* Instance daA2D_compat : Proper (AGF.da_eq ==> DGF.da_eq) daA2D.
Proof.
intros daA1 daA2 HdaA.
unfold daA2D. split; simpl.
+ intros id rc. destruct HdaA as (HdaA_G,_).
  specialize (HdaA_G id (rcD2A rc)).
  destruct (AGF.step daA1 id (rcD2A rc)), (AGF.step daA2 id (rcD2A rc)); unfold AGF.Aom_eq in *.
  - destruct dist, dist0; now unfold DGF.Aom_eq.
  - now exfalso.
  - now exfalso.
  - destruct (DGF.Location.eq_dec (DGF.Config.loc rc)
                                  (DGF.Config.target (DGF.Config.robot_info rc))).
    now rewrite HdaA_G.
    reflexivity.
+ destruct HdaA as (_, HdaA_B). intros b; specialize (HdaA_B b).
  auto.
Qed. *)

CoFixpoint demonD2A (demonD : DGF.demon) : AGF.demon :=
  AGF.NextDemon (daD2A (DGF.demon_head demonD)) (demonD2A demonD).

CoFixpoint demonA2D (demonA : AGF.demon) : DGF.demon :=
  DGF.NextDemon (daA2D (AGF.demon_head demonA)) (demonA2D demonA).

(* Instance demonD2A_compat : Proper (DGF.Deq  *)

(*Ensuite, pour montrer l'équivalence, on écrit des fonctions de
traduction entre les modèles Atomic et Discrete pour :
+ configuration (check)
+ robogram (check)
+ demonic_action ( check )
+ demon ( check )
+ round ( TODO )
*)

Theorem graph_equiv : forall (c c': AGF.Config.t) (rbg:AGF.robogram) (da:AGF.demonic_action),
AGF.Config.eq c' (AGF.round rbg da c) ->
exists da', DGF.Config.eq (ConfigA2D c') (DGF.round (rbgA2D rbg) da' (ConfigA2D c)).
Proof.
intros c c' rbg da HAGF.
exists (daA2D da). repeat try (split; simpl);
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
         (DGF.step (daA2D da) id (ConfigA2D c id)) eqn:HstepD; unfold ConfigA2D in HstepD;
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
         (HAGF id) as (HlocA,(HsrcA,HtgtA)),
         id as [g|b]; try now exfalso; simpl in *; rewrite HstepA in *.
  - destruct (Rdec dist0 0).
    * destruct dist; simpl in *; destruct dist1; try auto; try discriminate.
      rewrite e in *.
      assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving 0)). unfold daA2D in *.
      rewrite HstepD; reflexivity. unfold DGF.Aom_eq in *. lra.
    * destruct (Rdec dist0 1).
      destruct dist; simpl in *; auto.
      ++ rewrite e, <- HstepA_compat in *.
         assert (Hfalse : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving 1)).
         rewrite HstepD. reflexivity. unfold DGF.Aom_eq in *. lra.
      ++ destruct (Veq_dec (AGF.Config.loc (c (Good g)))
        (AGF.Config.target (AGF.Config.robot_info (c (Good g))))); simpl in *.
        ** destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving dist0)).
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
 - destruct dist0; simpl in *; discriminate.
 - destruct dist0; simpl in *; discriminate.
 - simpl in *. assumption.
 - simpl in *. assumption.
 - destruct (Rdec dist0 0); rewrite HstepA in *; simpl in *.
    * destruct dist; destruct dist1; try auto.
    * destruct (Rdec dist0 1).
      destruct dist; simpl in *; try auto.
      destruct (Veq_dec (AGF.Config.loc (c (Good g)))
        (AGF.Config.target (AGF.Config.robot_info (c (Good g))))); simpl in *;
      destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
 - rewrite HstepA in *. destruct dist; assumption.
 - rewrite HstepA in *. destruct dist0; discriminate.
 - rewrite HstepA in *. destruct dist0; discriminate.
 - rewrite HstepA in *. assumption.
 - rewrite HstepA in *; assumption.
 - destruct (Rdec dist0 0).
    * rewrite HstepA in *. simpl in *.
      destruct dist; simpl in *; destruct dist1; auto; try discriminate.
    * destruct (Rdec dist0 1); simpl in *. rewrite HstepA in *; simpl in *.
      destruct dist; simpl in *; auto.
      ++ destruct (Veq_dec (AGF.Config.loc (c (Good g)))
        (AGF.Config.target (AGF.Config.robot_info (c (Good g))))); simpl in *.
        ** rewrite HstepA in *.
          destruct dist; simpl in *; destruct dist1; simpl in *; try discriminate.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
        ** rewrite HstepA in *.
          destruct dist; simpl in *; destruct dist1; simpl in *; try discriminate.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 1) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
          -- assert (Hfalse : DGF.Aom_eq (DGF.Moving 0) (DGF.Moving dist0)).
             { rewrite HstepD. reflexivity. }
             unfold DGF.Aom_eq in *. lra.
 - rewrite HstepA in *; destruct dist; simpl in *; assumption.
 - rewrite HstepA in *; destruct dist0; simpl in *; discriminate.
 - rewrite HstepA in *; destruct dist0; simpl in *; discriminate.
 - rewrite HstepA in *. simpl in *. rewrite HtgtA.
    assert (Htest : forall confA, DGF.Config.eq (ConfigA2D (confA)) (DGF.project (ConfigA2D confA))).
    intros confA id.
    unfold DGF.project, ConfigA2D; simpl in *. reflexivity.
    specialize (Htest c). rewrite <- Htest.
    assert (AGF.Spect.eq (AGF.Spect.from_config c) (DGF.Spect.from_config (ConfigA2D c))).
    unfold AGF.Spect.eq, View.eq.
    unfold ConfigA2D; simpl in *.
    repeat try (split; simpl); now unfold AGF.Spect.from_config. now rewrite H.
 - rewrite HstepA in *; simpl in *; assumption.
Save.

(*assert (Htest : forall confD, AGF.Config.eq (ConfigD2A confD) (ConfigD2A (DGF.project confD))).
    intros confD id.
    unfold DGF.project, ConfigD2A; simpl in *. unfold LocD2A.
    destruct (DGF.Config.loc (confD id)) eqn : HconfD.
    rewrite HconfD; simpl in *. reflexivity.
    reflexivity.*)

Lemma test : n : ]0;1[
