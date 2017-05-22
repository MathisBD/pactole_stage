(* This file extends the common formalism for real metric spaces and contains a common notion of similarity. *)

Require Import Equalities.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Export Similarity.
Require Pactole.CommonFormalism.


Module Type Sig (Loc : RealMetricSpace)
                (N : Size)
                (Names : Robots(N))
                (Info : DecidableType)
                (Config : Configuration(Loc)(N)(Names)(Info))
                (Spect : Spectrum(Loc)(N)(Names)(Info)(Config)).
  
  Include CommonFormalism.Sig(Loc)(N)(Names)(Info)(Config)(Spect).
  Module Sim := Similarity.Make(Loc).
End Sig.

Module Make (Loc : RealMetricSpace)
            (N : Size)
            (Names : Robots(N))
            (Info : DecidableType)
            (Config : Configuration(Loc)(N)(Names)(Info))
            (Spect : Spectrum(Loc)(N)(Names)(Info)(Config)) : Sig(Loc)(N)(Names)(Info)(Config)(Spect).
  
  Module Common := CommonFormalism.Make(Loc)(N)(Names)(Info)(Config)(Spect).
  Include Common.
  Module Sim := Similarity.Make(Loc).
End Make.
