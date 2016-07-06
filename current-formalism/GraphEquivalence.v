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
        if Rle_dec (dist) (threshold e) then AGF.Moving false else AGF.Moving true
           | None => AGF.Moving false
        end
      end |}.
Proof.
+ intros id rcA sim HrcD. unfold AGF.Aom_eq in *. 
  destruct (DGF.step daD id (rcA2D rcA)) eqn : HstepD, 
  (find_edge (AGF.Config.source (AGF.Config.robot_info rcA))
             (AGF.Config.target (AGF.Config.robot_info rcA))) eqn : Hedge.
  destruct (Rle_dec (dist) (threshold e)) eqn : Hthresh; now exfalso.
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
  - destruct (Rle_dec (dist) (threshold e)),
             (Rle_dec (dist0) (threshold e0)); auto.
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
  | Some e => if Rle_dec (dist0) (threshold e) then AGF.Moving false else AGF.Moving true
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
assert (Htl := DGF.ri_Loc rcD); destruct Htl as (l1, (l2, ((Hs, Ht), _))).
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

Theorem graph_equivA2D : forall (c c': AGF.Config.t) (rbg:AGF.robogram) (da:AGF.demonic_action),
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
    * destruct (Rdec dist0 1); simpl in *; rewrite HstepA in *; simpl in *.
      destruct dist; simpl in *; auto.
      destruct (Veq_dec (AGF.Config.loc (c (Good g)))
        (AGF.Config.target (AGF.Config.robot_info (c (Good g))))); simpl in *;
      destruct dist; simpl in *; destruct dist1; simpl in *; try auto.
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

Theorem graph_equivD2A : forall (c c': DGF.Config.t) (rbg:DGF.robogram) (da:DGF.demonic_action),
DGF.Config.eq c' (DGF.round rbg da c) ->
exists da', AGF.Config.eq (ConfigD2A c') (AGF.round (rbgD2A rbg) da' (ConfigD2A c)).
Proof.
intros c c' rbg da HDGF. exists (daD2A da). intro id.
assert (Hax1 := DGF.ri_Loc (c id)).
destruct Hax1 as (lax1, (lax2, ((Hax_src, Hax_tgt), (eD, HeD)))).
assert (Hax2 := DGF.ri_Loc (c' id)).
destruct Hax2 as (lax1', (lax2', ((Hax_src', Hax_tgt'), (eD',HeD')))).
assert (Ha := DGF.a).
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
(AGF.step (daD2A da) id (ConfigD2A c id)) eqn : HstepA, id as [g|b]; try (now exfalso);
unfold daD2A in *; simpl in *;
unfold rcA2D, ConfigD2A, LocD2A in *.
+ repeat try (split; simpl);
  destruct dist1 eqn : Hbool.
  - destruct (DGF.Config.loc (c (Good g))) eqn : HlocD; simpl in *;
    rewrite <- HlocD in *;
    destruct (DGF.Config.loc (c' (Good g))) eqn : HlocD';
    destruct (DGF.Config.target (DGF.Config.robot_info (c (Good g)))) eqn : HtgtD; try discriminate;
    destruct (DGF.Config.target (DGF.Config.robot_info (c' (Good g)))) eqn : HtgtD'; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c (Good g)))) eqn : HsrcD; try discriminate;
    destruct (DGF.Config.source (DGF.Config.robot_info (c' (Good g)))) eqn : HsrcD'; try discriminate.
    * rewrite HstepD' in *.
      destruct (Rdec dist0 0) eqn : Hdist; try rewrite HlocD, HsrcD, HtgtD in *;
      destruct (find_edge l3 l1) eqn : Hedge1.
      ** destruct (Rle_dec (dist) (threshold e0)); try discriminate; rewrite e in *.
         rewrite <- HstepD_compat in *.
         intuition.
         assert (Hfalse := threshold_pos e0); lra.
      ** assert (Hfalse : AGF.Aom_eq (AGF.Moving false) (AGF.Moving true)).
         now rewrite HstepA. now unfold AGF.Aom_eq in *.
      ** destruct (Rle_dec (dist) (threshold e)); try discriminate.
         destruct (Rdec dist0 1); simpl in *; try assumption.
         destruct (Veq_dec l l1) eqn : Heql.
          ++ rewrite HlocD in *; now rewrite Hloc.
          ++ simpl in *; now exfalso.
      ** assert (Hfalse : AGF.Aom_eq (AGF.Moving false) (AGF.Moving true)).
         now rewrite HstepA. now unfold AGF.Aom_eq in *.
    * rewrite HstepD' in *.
      destruct (find_edge l2 l0) eqn : Hedge2; try discriminate;
      destruct(Rle_dec dist (threshold e0)); try discriminate;
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
         ++ assert (opt_eq Eeq (find_edge l1 l3) (find_edge l l0)).
            admit.
            assert (opt_eq Eeq (find_edge l1 l3) (find_edge l2 l0)).
            admit.
            rewrite H0 in H.
            assert (Veq l l2).
            admit (* voir H *).
            rewrite Hproj_eq in r.
            assert (Heq_some : opt_eq Eeq (Some e) (Some e0)).
            rewrite <- Hedge2.
            assert (Heq_some' : opt_eq Eeq (Some e)(Some e1)). now simpl.
            rewrite Heq_some', <- Hedge.
            now symmetry.
            assert (Ht : threshold e0 = threshold e).
            now apply CommonGraphFormalism.threshold_compat.
            rewrite Ht in n. lra.
         ++ assert (opt_eq Eeq (find_edge l1 l3) (find_edge l l0)).
            admit.
            assert (opt_eq Eeq (find_edge l1 l3) (find_edge l2 l0)).
            admit.
            rewrite H0 in H.
            rewrite Hedge2, Hedge in H. contradiction.
      ** assert ( Hax := DGF.ax_cont (c' (Good g)) e p HlocD').
         destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
         assert (opt_eq Eeq (find_edge l1 l3) (find_edge l l0)).
            admit.
            assert (opt_eq Eeq (find_edge l1 l3) (find_edge l2 l0)).
            admit.
            rewrite H0 in H.
         destruct (find_edge l l0) eqn : Hedge; simpl in *.
         ++ destruct Hloc. rewrite H1.
            assert (Hf := find_edge_Some e1).
            rewrite <- Hedge in Hf.
            admit. (* on a (opt_eq Eeq (find_edge (src e1) (tgt e1)) (find_edge l l0)) *)
         ++ rewrite Hedge2 in H. contradiction.
   * assert ( Hax := DGF.ax_cont (c (Good g)) e p HlocD).
     destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
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
     ** now exfalso.
   * assert ( Hax := DGF.ax_cont (c (Good g)) e p HlocD).
     destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
     destruct (Rle_dec 1 (DGF.project_p p + dist0)) eqn : Heq1; simpl in *;
     try rewrite HlocD, HsrcD, HtgtD in *; try (now exfalso).
     destruct (Rle_dec (DGF.project_p p0) (threshold e0)) eqn : Hp_t2;
     destruct Hloc as (Heq_e, Heq_p).
     ** rewrite Heq_e. 
        specialize (Ha e p c da (Good g) HlocD).
        destruct (Rle_dec (DGF.project_p p) (threshold e)) eqn : Hp_t1.
        destruct (DGF.step da (Good g)
             {|
             DGF.Config.loc := DGF.Loc (src e);
             DGF.Config.robot_info := {|
                                      DGF.Config.source := DGF.Loc l1;
                                      DGF.Config.target := DGF.Loc l |} |}
        ) eqn : HstepA'; try discriminate.
        rewrite <- HsrcD, <- HtgtD in *.
        rewrite <- Ha in HstepA'.
        assert (Hdist02 : dist0 = dist2).
        rewrite HstepD in HstepA'.
        assert (DGF.Aom_eq (DGF.Moving dist0) (DGF.Moving dist2)) by now rewrite HstepA'.
        now unfold DGF.Aom_eq.
        assert (opt_eq Eeq (find_edge l1 l) (find_edge ld1 ld2)) by admit.
        rewrite He in H.
        destruct (find_edge l1 l) eqn : He2; try discriminate.
        destruct (Rle_dec dist2 (threshold e1)); try discriminate.
        assert (Eeq e1 e). apply H.
        assert (r' := r).
        rewrite Heq_p in r'. rewrite Hdist02, Heq_e, <- H0 in r'.
        rewrite DGF.proj_comm, <- DGF.inv_pro in r'.
        assert (z:=DGF.project_p_image p).
        lra. split. assert (zz := threshold_pos e1); try lra.
        assert (n' := n). rewrite Hdist02 in n'.
        assert (z:=DGF.project_p_image p). lra.
        destruct (DGF.step da (Good g)
             {|
             DGF.Config.loc := DGF.Loc (tgt e);
             DGF.Config.robot_info := {|
                                      DGF.Config.source := DGF.Loc l1;
                                      DGF.Config.target := DGF.Loc l |} |}
        ) eqn : HstepA'; try discriminate.
        rewrite <- HsrcD, <- HtgtD in *.
        rewrite <- Ha in HstepA'.
        assert (Hdist02 : dist0 = dist2).
        rewrite HstepD in HstepA'.
        assert (DGF.Aom_eq (DGF.Moving dist0) (DGF.Moving dist2)) by now rewrite HstepA'.
        now unfold DGF.Aom_eq.
        assert (opt_eq Eeq (find_edge l1 l) (find_edge ld1 ld2)) by admit.
        rewrite He in H.
        destruct (find_edge l1 l) eqn : He2; try discriminate.
        destruct (Rle_dec dist2 (threshold e1)); try discriminate.
        assert (Eeq e1 e). apply H.
        assert (r' := r).
        rewrite Heq_p in r'. rewrite Hdist02, Heq_e, <- H0 in r'.
        rewrite DGF.proj_comm, <- DGF.inv_pro in r'.
        assert (z:=DGF.project_p_image p).
        lra. split. assert (zz := threshold_pos e1); try lra.
        assert (n' := n). rewrite Hdist02 in n'.
        assert (z:=DGF.project_p_image p). lra.
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
    * rewrite HstepD' in *.
      destruct (Rdec dist0 0).
      ** now rewrite HlocD in *.
      ** destruct (Rdec dist0 1).
         ++ simpl in *. rewrite HtgtD, HlocD, HsrcD in *.
            destruct (find_edge l3 l1) eqn : Hf.
            destruct (Rle_dec dist (threshold e0)).
            assert (Hfalse := threshold_pos e0). 
            rewrite HstepD_compat in *; lra.
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
   * rewrite HstepD' in *.
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
            assert (threshold e = threshold e0).
            apply threshold_compat.
            rewrite <- H in H1.
            apply H1.
            rewrite H2 in *.
            destruct (Rle_dec (DGF.project_p p) (threshold e0)); try discriminate.
            destruct (find_edge l l0) eqn : He3.
            assert (Veq (src e1) l) by admit (* voir He3 *).
            now rewrite Heq_e.
            assert (Veq l l2).
            admit (* si on est sur un nœud, soit on est au départ, soit a l'arrivé, et on a n1 *).
            assert (Eeq e eD') by apply H1.
            assert (Eeq e0 eD') by apply H.
            rewrite H3, H4, <- H5. admit (* apply He' *).
            now simpl in H.
   * assert ( Hax := DGF.ax_cont (c (Good g)) e p HlocD).
     destruct Hax as (ld1, (ld2, ((Hax1, Hax2), He))).
     destruct (Rle_dec 1 (DGF.project_p p + dist0)) eqn : Hpd; try (now exfalso).
     simpl in *. rewrite HtgtD, HsrcD in *.
     specialize (Ha e p c da (Good g) HlocD).
     destruct (Rle_dec (DGF.project_p p) (threshold e)); try assumption.
     rewrite <-HsrcD, <- HtgtD, <- Ha, HstepD in HstepA.
     assert (Hf : find_edge l2 l0 = find_edge ld1 ld2) by admit.
     rewrite Hf, He, HstepD_compat in HstepA.
     destruct (Rle_dec dist (threshold e)) ; try discriminate.

     
           
            
            rewrite 
            rewrite <- H.
            destruct (find_edge l2 l0)
            destruct (Rle_dec (DGF.project_p p) (threshold e)).
         
    rewrite HlocD, HsrcD, HtgtD in *.
    destruct (find_edge l3 l1) eqn : Hf. now exfalso.
         
         
         
         