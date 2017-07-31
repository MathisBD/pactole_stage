(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             

      PACTOLE project                                                      
                                                                        
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
(**************************************************************************)

Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.Isomorphism.

Module Type Iso (Graph: GraphDef) (Loc : LocationADef(Graph)).
  Module Iso := Isomorphism.Make(Graph)(Loc).
End Iso.

Module Make (Graph: GraphDef) (Loc : LocationADef(Graph)).
  Module Iso := Isomorphism.Make(Graph)(Loc).
End Make.