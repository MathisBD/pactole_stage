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
Require Import Pactole.AtomicGraphFormalism.
Require Import Pactole.DiscreteGraphFormalism.
Require Import Pactole.CommonGraphFormalism.


Print Module Location.


Module View : DecidableType with Definition t := V with Definition eq:= Veq.
    Definition t := V.
    Definition eq:= Veq.
    Definition eq_equiv := Veq_equiv.
    Definition eq_dec := Veq_dec.
End View.

Module GraphEquivalence (N : Size)(Names : Robots(N)).

Module Atom := AtomicGraphFormalism.Make(N)(Names)(View).
Module Disc := DiscreteGraphFormalism.Make(N)(Names)(View).


Import Atom.Common.
Import Disc.Common.

Check Atom.Config.t.

Definition ConfigA2D (confA : Atom.Config.t) : Disc.Config.t :=
    fun id =>
        {| Disc.Config.loc := DiscreteGraphFormalism.Loc (Atom.Config.loc (confA id));
           Disc.Config.robot_info := 
           {| Disc.Config.source := DiscreteGraphFormalism.Loc (Atom.Config.source (Atom.Config.robot_info (confA id)));
              Disc.Config.target := DiscreteGraphFormalism.Loc (Atom.Config.target (Atom.Config.robot_info (confA id))) |} |}.

Instance configA2D_compat : Proper (Atom.Config.eq ==> Disc.Config.eq) ConfigA2D.
Proof.
intros ca1 ca2 Hca id. unfold ConfigA2D. repeat try (split;simpl); apply Hca.
Qed.

Definition LocD2A (locD : DiscreteGraphFormalism.Location.t) : AtomicGraphFormalism.Location.t :=
      match locD with
        | Loc l => l
        | Mvt e p Hp => if Rle_dec p (threshold e) then src e else tgt e
      end.

Definition ConfigD2A (ConfD : Disc.Config.t) : Atom.Config.t := 
    fun id =>
        {| Atom.Config.loc := LocD2A (Disc.Config.loc (ConfD id));
           Atom.Config.robot_info := 
           {| Atom.Config.source := LocD2A (Disc.Config.source (Disc.Config.robot_info (ConfD id)));
              Atom.Config.target := LocD2A (Disc.Config.target (Disc.Config.robot_info (ConfD id))) |} |}.

Instance LocD2A_compat : Proper (DiscreteGraphFormalism.Location.eq ==> AtomicGraphFormalism.Location.eq) LocD2A.
Proof.
intros ld1 ld2 Hld. unfold LocD2A, AtomicGraphFormalism.Location.eq, Location.eq, loc_eq in *.
destruct ld1, ld2; auto. exfalso; assumption. exfalso; assumption.
destruct Hld, (Rle_dec p (threshold e)), (Rle_dec p0 (threshold e0)).
apply src_compat; assumption. rewrite H0, H in r; contradiction.
rewrite <- H0, <- H in r; contradiction. apply tgt_compat; assumption.
Qed.

Instance ConfigD2A_compat : Proper (Disc.Config.eq ==> Atom.Config.eq) ConfigD2A.
Proof.
intros cd1 cd2 Hcd id. unfold ConfigD2A. repeat try(split;simpl); apply LocD2A_compat, Hcd.
Qed.

Lemma Atom_Disc_Atom_Config : forall confA: Atom.Config.t,  Atom.Config.eq confA (ConfigD2A (ConfigA2D confA)).
Proof.
intros confA id. unfold ConfigD2A, ConfigA2D. now repeat try (split; simpl).
Qed.





Lemma DiscS_Atom_DiscS_Config : forall SconfD : Disc.Config.t, 
      Disc.SpectD.eq (Disc.SpectD.from_config SconfD) 
      (Disc.SpectD.from_config (ConfigA2D (ConfigD2A SconfD))).

(*Ensuite, pour montrer l'équivalence, on écrit des fonctions de
traduction entre les modèles Atomic et Discrete pour :
+ configuration
+ robogram
+ demonic_action
+ demon
+ round
*)



Theorem graph_equiv : forall (c c': Atom.Config.t) (rbg:robogram) (da:Atom.demonic_action),
c' = Atom.round rbg da c -> exists da', config_A2D c' = Disc.round rbg da' (config_A2D c).
Proof.

Save.*)


