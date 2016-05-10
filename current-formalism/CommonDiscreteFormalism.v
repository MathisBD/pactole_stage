(* This file extends the common formalism for real metric spaces and contains a common notion of similarity. *)

Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Export DiscreteSimilarity.
Require Pactole.CommonFormalism.


Module Type Sig (Loc : DiscreteSpace)(N : Size)(Spect : Spectrum(Loc)(N)).
  Include CommonFormalism.Sig(Loc)(N)(Spect).
  Module Sim := DiscreteSimilarity.Make(Loc).
End Sig.

Module Make (Loc : DiscreteSpace)(N : Size)(Spect : Spectrum(Loc)(N)) : Sig(Loc)(N)(Spect).
  Module Common := CommonFormalism.Make(Loc)(N)(Spect).
  Include Common.
  Module Sim := DiscreteSimilarity.Make(Loc).
End Make.
