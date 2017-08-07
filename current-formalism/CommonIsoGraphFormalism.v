Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.Isomorphism.

Module Type Iso (Graph: GraphDef) (Loc : LocationADef(Graph)).
  Module Iso := Isomorphism.Make(Graph)(Loc).
End Iso.

Module Make (Graph: GraphDef) (Loc : LocationADef(Graph)).
  Module Iso := Isomorphism.Make(Graph)(Loc).
End Make.