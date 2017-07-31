(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             

      PACTOLE project                                                      
                                                                        
      This file is distributed under the terms of the CeCILL-C licence     
                                                                          *)
(**************************************************************************)

Require Import Rbase.
Require Import Equalities.
Require Import Morphisms.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.CommonGraphFormalism.

Module Type FiniteGraphDef <: GraphDef.  

  Parameter n : nat.
  Definition V : Set := Fin.t n.
  Parameter E : Set. (* possibility to pass it to a finite set later *)
  Parameter tgt src : E -> V. (* fst et snd du couple *)
  Parameter threshold : E -> R. (* ça reste un parametre *)
  Parameter Veq : V -> V -> Prop. 
  Parameter Eeq : E -> E -> Prop.
  Axiom Veq_equiv : Equivalence Veq.
  Axiom Eeq_equiv : Equivalence Eeq.
  Axiom Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'}.
  Axiom Eeq_dec : forall e e' : E, {Eeq e e'} + {~Eeq e e'}.
  Axiom threshold_pos : forall e, (0 < threshold e < 1)%R.
  Parameter tgt_compat : Proper (Eeq ==> Veq) tgt.
  Parameter src_compat : Proper (Eeq ==> Veq) src.
  Parameter threshold_compat : Proper (Eeq ==> eq) threshold.

  Parameter find_edge : V -> V -> option E.
  Axiom find_edge_Some : forall e : E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e).
  Axiom find_edge_None : forall a b : V,
      find_edge a b = None <-> forall e : E, ~(Veq (src e) a /\ Veq (tgt e) b).
  Parameter find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Axiom find2st : forall v1 v2 e, opt_eq Eeq (find_edge v1 v2) (Some e) ->
                                  Veq v1 (src e) /\ Veq v2 (tgt e).

End FiniteGraphDef.

Module Type LocationAFiniteDef (Graph : FiniteGraphDef) <: DecidableType.
  Definition t := Graph.V.
  Definition eq := Graph.Veq. (*Graph.V -> Graph.V -> Prop. *)
  Parameter eq_equiv : Equivalence eq.
  Parameter eq_dec : forall l l', {eq l l'} + {~eq l l'}.
End LocationAFiniteDef.

