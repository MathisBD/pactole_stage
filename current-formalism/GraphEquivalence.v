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

Module GraphEquivalence (N : Size)(Names : Robots(N))
                        (SpectA : Spectrum(AtomicGraphFormalism.Location)(N))
                        (CommonA: CommonFormalism.Sig(AtomicGraphFormalism.Location)(N)(SpectA)).

Module Atom := AtomicGraphFormalism.Make(N)(Names)(SpectA)(CommonA).

Import CommonA.

Module SpectD : Spectrum(DiscreteGraphFormalism.Location)(N).
  Module Names := Names.
  Module Config := Configurations.Make(DiscreteGraphFormalism.Location)(N)(Names).

Definition config_A2D (confA : SpectA.Config.t): Config.t :=
  fun id => 
    let rcA := confA id in
      {| Config.loc := Loc (SpectA.Config.loc rcA);
         Config.robot_info := 
         {| Config.source := Loc (SpectA.Config.source (SpectA.Config.robot_info rcA));
            Config.target := Loc (SpectA.Config.target (SpectA.Config.robot_info rcA)) |}
            |}.


Instance config_A2D_compat : Proper (SpectA.Config.eq ==> Config.eq) config_A2D.
Proof.
intros x y Hxy id. unfold config_A2D, Config.eq_RobotConf. destruct (Hxy id) as (Hl, Hi),
(x id) as (locx, infox), (y id) as (locy, infoy). split; simpl in *.
+ assumption.
+ unfold Config.Info_eq, SpectA.Config.Info_eq in *; destruct Hi; split;simpl;
  destruct infox, infoy; simpl in *; assumption.
Qed.
  
Definition project_loc (loc : Location.t) : AtomicGraphFormalism.Location.t :=
  match loc  with
      | Loc l =>  l
      | Mvt e p Hp => 
          (if Rle_dec p (CommonGraphFormalism.threshold e) then CommonGraphFormalism.src e 
                                                           else CommonGraphFormalism.tgt e)
  end.
  

Instance project_loc_compat : Proper ( Location.eq ==> AtomicGraphFormalism.Location.eq) project_loc.
Proof.
intros x y Hxy. simpl in *. unfold Location.eq, loc_eq, AtomicGraphFormalism.Location.eq in *.
unfold project_loc. destruct x,y.
 - assumption.
 - exfalso; assumption.
 - exfalso; assumption.
 - destruct Hxy as (Hexy, Hpxy), (Rle_dec p (threshold e)) eqn : Hx,
   (Rle_dec p0 (threshold e0)) eqn:Hy.
   + now apply src_compat.
   + assert (Ht := threshold_compat e e0 Hexy).
     assert (Hr : (p <= threshold e)%R) by assumption.
     now rewrite Ht, Hpxy in Hr.
   + assert (Hr : (p0 <= threshold e0)%R) by assumption.
     assert (Ht := threshold_compat e e0 Hexy).
     now rewrite <- Ht, <- Hpxy in Hr.
   + now apply tgt_compat.
Qed.


Definition project (config : Config.t) : SpectA.Config.t :=
  fun id =>
    {| SpectA.Config.loc := (project_loc (Config.loc (config id)));
       SpectA.Config.robot_info := 
       {| SpectA.Config.source := (project_loc (Config.source (Config.robot_info (config id))));
          SpectA.Config.target := (project_loc (Config.target (Config.robot_info (config id)))) |} |}.


Instance project_compat : Proper (Config.eq ==> SpectA.Config.eq) project.
Proof.
intros c1 c2 Hc id. destruct (Hc id) as (Hl, (Hs, Ht)). unfold project.
split; simpl. now apply project_loc_compat. split; simpl; now apply project_loc_compat.
Qed.

Definition t := SpectA.t.
Definition eq := SpectA.eq.
Definition eq_equiv : Equivalence eq := SpectA.eq_equiv.
Definition eq_dec : forall x y : t, {eq x y} + {~eq x y} := SpectA.eq_dec.

Definition from_config := fun x => SpectA.from_config (project x).
Definition from_config_compat : Proper (Config.eq ==> eq) from_config.
Proof.
intros x y Hxy. unfold from_config. f_equiv. now apply project_compat.
Defined.
Definition is_ok : t -> Config.t -> Prop := fun t c => SpectA.is_ok t (project c) .
Definition from_config_spec : forall config, is_ok (from_config config) config.
Proof.
intro.
unfold is_ok, from_config. apply SpectA.from_config_spec.
Defined.

End SpectD.

(* Module CommonD : (CommonFormalism.Sig(AtomicGraphFormalism.Location)(N)(SpectA)).
End CommonD. *)
Module Disc := DiscreteGraphFormalism.Make(N)(Names)(SpectD)(CommonA).
               (CommonFormalism.Sig(AtomicGraphFormalism.Location)(N)(SpectA)).

Print Module AtomicGraphFormalism.Location.


Theorem graph_equiv : forall (c c': Atom.Config.t) (rbg:robogram) (da:Atom.demonic_action),
c' = Atom.round rbg da c -> exists da', config_A2D c' = Disc.round rbg da' (config_A2D c).
Proof.

Save.


