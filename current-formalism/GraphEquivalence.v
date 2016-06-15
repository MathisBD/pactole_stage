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


Print Module Location.

Module GraphEquivalence (N : Size)(Names : Robots(N))
                        (SpectA : Spectrum(AtomicGraphFormalism.Location)(N))
                        (CommonA: CommonFormalism.Sig(AtomicGraphFormalism.Location)(N)(SpectA)).

Module Atom := AtomicGraphFormalism.Make(N)(Names)(SpectA)(CommonA).

Import CommonA.

Module SpectD : Spectrum(DiscreteGraphFormalism.Location)(N).
  Module Names := Robots.Make(N).
  Module Config := Configurations.Make(DiscreteGraphFormalism.Location)(N)(Names).

Definition config_A2D (confA : SpectA.Config.t): Config.t :=
  fun id => 
    let rcA := confA id in
      {| Config.loc := Loc (SpectA.Config.loc rcA);
         Config.robot_info := 
         {| Config.source := Loc (SpectA.Config.source (SpectA.Config.robot_info rcA));
            Config.target := Loc (SpectA.Config.target (SpectA.Config.robot_info rcA)) |}
            |}.

Definition t := SpectA.t.
Definition eq := SpectA.eq.
Definition eq_equiv : Equivalence eq := SpectA.eq_equiv.
Definition eq_dec : forall x y : t, {eq x y} + {~eq x y} := SpectA.eq_dec.

Definition from_config := fun x => (SpectA.from_config (config_A2D x)).
Definition from_config_compat : Proper (Config.eq ==> eq) from_config.
Proof.
Admitted.
Definition is_ok : t -> Config.t -> Prop := eq.
Definition from_config_spec : forall config, is_ok (from_config config) config.
Proof. intro. reflexivity. Qed.



Module SpectD : Spectrum (DiscreteGraphFormalism.Location)(N) := 
    

Module Disc := DiscreteGraphFormalism.Make(N)(Names)(Spect)(Common).

Print Module AtomicGraphFormalism.Location.

