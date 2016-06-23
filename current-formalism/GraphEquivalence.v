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

Definition daA2D (daA : AGF.demonic_action) : DGF.demonic_action.
refine {| 
  DGF.relocate_byz := fun b => DGF.Loc (AGF.relocate_byz daA);
  DGF.step := fun id rcD => (* TODO *) Names.ident -> Config.RobotConf -> Active_or_Moving |}.
Theorem graph_equiv : forall (c c': AGF.Config.t) (rbg:AGF.robogram) (da:AGF.demonic_action),
c' = AGF.round rbg da c -> exists da', ConfigA2D c' = DGF.round (rbgA2D rbg) da' (ConfigA2D c).
Proof.
intros c c' rbg da HAGF.

Save.


