(* This file extends the common formalism for real metric spaces and contains a common notion of similarity. *)

Require Import Pactole.Robots.
Require Import Pactole.Positions.
Require Export Similarity.
Require Pactole.CommonFormalism.


Module Type Sig (Loc : RealMetricSpace)(N : Size)(Spect : Spectrum(Loc)(N)).
  Include CommonFormalism.Sig(Loc)(N)(Spect).
  Module Sim := Similarity.Make(Loc).
End Sig.

Module Make (Loc : RealMetricSpace)(N : Size)(Spect : Spectrum(Loc)(N)) : Sig(Loc)(N)(Spect).
  Module Common := CommonFormalism.Make(Loc)(N)(Spect).
  Include Common.
  Module Sim := Similarity.Make(Loc).
End Make.
