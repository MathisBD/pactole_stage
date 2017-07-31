(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             

      PACTOLE project                                                      
                                                                        
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
(**************************************************************************)
(* This file extends the common formalism for real metric spaces and contains a common notion of similarity. *)

Require Import ZArith.
Require Import Morphisms.
Require Import Equalities.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Export Pactole.DiscreteSpace.
Require Export DiscreteSimilarity.
Require Pactole.CommonFormalism.



Module Type Sig (Loc : DiscreteSpace)
                (N : Size)
                (Names : Robots(N))
                (Info : DecidableTypeWithApplication(Loc))
                (Config : Configuration(Loc)(N)(Names)(Info))
                (Spect : Spectrum(Loc)(N)(Names)(Info)(Config)).
  
  Include CommonFormalism.Sig(Loc)(N)(Names)(Info)(Config)(Spect).
  Module Sim := DiscreteSimilarity.Make(Loc).
End Sig.

Module Make (Loc : DiscreteSpace)
            (N : Size)
            (Names : Robots(N))
            (Info : DecidableTypeWithApplication(Loc))
            (Config : Configuration(Loc)(N)(Names)(Info))
            (Spect : Spectrum(Loc)(N)(Names)(Info)(Config))
            : Sig(Loc)(N)(Names)(Info)(Config)(Spect).
  
  Module Common := CommonFormalism.Make(Loc)(N)(Names)(Info)(Config)(Spect).
  Include Common.
  Module Sim := DiscreteSimilarity.Make(Loc).
End Make.
