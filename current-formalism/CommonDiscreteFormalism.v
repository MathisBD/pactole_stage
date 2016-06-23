(* This file extends the common formalism for real metric spaces and contains a common notion of similarity. *)

Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Export DiscreteSimilarity.
Require Pactole.CommonFormalism.


Module Type Sig (Loc : DiscreteSpace)(N : Size)(Names : Robots(N))
                (Config : Configuration(Loc)(N)(Names))(Spect : Spectrum(Loc)(N)(Names)(Config)).
  Include CommonFormalism.Sig(Loc)(N)(Names)(Config)(Spect).
  Module Sim := DiscreteSimilarity.Make(Loc).
End Sig.

Module Make (Loc : DiscreteSpace)(N : Size)(Names : Robots(N))
            (Config : Configuration(Loc)(N)(Names))(Spect : Spectrum(Loc)(N)(Names)(Config))
            : Sig(Loc)(N)(Names)(Config)(Spect).
  Module Common := CommonFormalism.Make(Loc)(N)(Names)(Config)(Spect).
  Include Common.
  Module Sim := DiscreteSimilarity.Make(Loc).
End Make.
