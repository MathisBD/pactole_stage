(* This file extends the common formalism for real metric spaces and contains a common notion of similarity. *)

Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Export Similarity.
Require Pactole.CommonFormalism.


Module Type Sig (Loc : RealMetricSpace)(N : Size)(Names : Robots(N))
                (Config : Configuration(Loc)(N)(Names))(Spect : Spectrum(Loc)(N)(Names)(Config)).
  Include CommonFormalism.Sig(Loc)(N)(Names)(Config)(Spect).
  Module Sim := Similarity.Make(Loc).
End Sig.

Module Make (Loc : RealMetricSpace)(N : Size)(Names : Robots(N))
            (Config : Configuration(Loc)(N)(Names))
            (Spect : Spectrum(Loc)(N)(Names)(Config)) : Sig(Loc)(N)(Names)(Config)(Spect).
  Module Common := CommonFormalism.Make(Loc)(N)(Names)(Config)(Spect).
  Include Common.
  Module Sim := Similarity.Make(Loc).
End Make.
