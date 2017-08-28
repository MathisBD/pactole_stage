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


Module Type GraphDef.
  Parameter V : Set.
  Parameter E : Set.
  Parameter src tgt : E -> V. (* source and target of an edge *)
  Parameter threshold : E -> R.
  Parameter Veq : V -> V -> Prop. 
  Parameter Eeq : E -> E -> Prop.
  Declare Instance Veq_equiv : Equivalence Veq.
  Declare Instance Eeq_equiv : Equivalence Eeq.
  Axiom Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'}.
  Axiom Eeq_dec : forall e e' : E, {Eeq e e'} + {~Eeq e e'}.
  Axiom threshold_pos : forall e, (0 < threshold e < 1)%R.
  Declare Instance tgt_compat : Proper (Eeq ==> Veq) tgt.
  Declare Instance src_compat : Proper (Eeq ==> Veq) src.
  Declare Instance threshold_compat : Proper (Eeq ==> eq) threshold.

  Parameter find_edge : V -> V -> option E.
  Declare Instance find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Axiom find_edge_None : forall a b : V,
    find_edge a b = None <-> forall e : E, ~(Veq (src e) a /\ Veq (tgt e) b).
  Axiom find_edge_Some : forall v1 v2 e,
    opt_eq Eeq (find_edge v1 v2) (Some e) <-> Veq v1 (src e) /\ Veq v2 (tgt e).
(*   Axiom find_some_edge : forall e : E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e). *)
End GraphDef.

Module Type LocationADef (Graph : GraphDef) <: DecidableType.
  Definition t := Graph.V.
  Definition eq := Graph.Veq. (*Graph.V -> Graph.V -> Prop. *)
  Parameter eq_equiv : Equivalence eq.
  Parameter eq_dec : forall l l', {eq l l'} + {~eq l l'}.
End LocationADef.


(** Specialized version of the Info type with Unit. *)
Module Type UnitSig (Loc : DecidableType) <: DecidableTypeWithApplication(Loc).
  Definition t := unit.
  Definition eq := @Logic.eq unit.
  Declare Instance eq_equiv : Equivalence eq.
  Parameter eq_dec : forall x y : t, {x = y} + {x <> y}.
  
  Definition app (f : Loc.t -> Loc.t) (x : t) := tt : t.
  
  Declare Instance app_compat : Proper ((Loc.eq ==> Loc.eq) ==> eq ==> eq) app.
  Parameter app_id : (eq ==> eq)%signature (app Datatypes.id) Datatypes.id.
  Parameter app_compose : forall f g, Proper (Loc.eq ==> Loc.eq) f -> Proper (Loc.eq ==> Loc.eq) g ->
    (eq ==> eq)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
End UnitSig.
