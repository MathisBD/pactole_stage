(* This file specialises the common formalism to real metric spaces and contains a common notion of similarity. *)

Require Import Reals.
Require Import Morphisms.
Require Import Equalities.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Export Similarity.
Require Import Pactole.Preliminary.
Require Export Pactole.RealMetricSpace.
Require Pactole.CommonFormalism.


Module Type Sig (Loc : RealMetricSpace)
                (N : Size)
                (Names : Robots(N))
                (Info : DecidableTypeWithApplication(Loc))
                (Config : Configuration(Loc)(N)(Names)(Info))
                (Spect : Spectrum(Loc)(N)(Names)(Info)(Config)).
  
  Include CommonFormalism.Sig(Loc)(N)(Names)(Info)(Config)(Spect).
  Module Sim := Similarity.Make(Loc).
End Sig.

Module Make (Loc : RealMetricSpace)
            (N : Size)
            (Names : Robots(N))
            (Info : DecidableTypeWithApplication(Loc))
            (Config : Configuration(Loc)(N)(Names)(Info))
            (Spect : Spectrum(Loc)(N)(Names)(Info)(Config)) : Sig(Loc)(N)(Names)(Info)(Config)(Spect).
  
  Module Common := CommonFormalism.Make(Loc)(N)(Names)(Info)(Config)(Spect).
  Include Common.
  Module Sim := Similarity.Make(Loc).
End Make.
