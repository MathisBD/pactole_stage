(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain              
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)


Require Import Rbase SetoidDec.
Require Import Pactole.Util.Coqlib.
Require Pactole.Core.Robots.
Set Implicit Arguments.


Class Graph (V E : Type) := {
  V_Setoid :> Setoid V;
  E_Setoid :> Setoid E;
  V_EqDec :> EqDec V_Setoid;
  E_EqDec :> EqDec E_Setoid;

  src : E -> V; (* source and target of an edge *)
  tgt : E -> V;
  threshold : E -> R;
  threshold_pos : forall e, (0 < threshold e < 1)%R;
  src_compat :> Proper (equiv ==> equiv) src;
  tgt_compat :> Proper (equiv ==> equiv) tgt;
  threshold_compat :> Proper (equiv ==> Logic.eq) threshold;

  find_edge : V -> V -> option E;
  find_edge_compat :> Proper (equiv ==> equiv ==> opt_eq equiv) find_edge;
  find_edge_None : forall a b : V, find_edge a b == None <-> forall e : E, ~(src e == a /\ tgt e == b);
  find_edge_Some : forall v1 v2 e, find_edge v1 v2 == Some e <-> v1 == src e /\ v2 == tgt e }.

Global Opaque threshold_pos src_compat tgt_compat threshold_compat find_edge_compat find_edge_None find_edge_Some.

(** A finite graph ia a graph where the set [V] of vertices is a prefix of N. *)
(* FIXME: nothing prevents E from being infinite! *)
(* TODO: Maybe we should reuse the type used for robot names *)
Definition finite_node n := {m : nat | m < n}.

(* We explictely define the setoid here to avoid using proj1_Setoid instead. *)
Instance finite_node_Setoid n : Setoid (finite_node n) := eq_setoid _.
Instance finite_node_EqDec n : EqDec (finite_node_Setoid n) := @Robots.subset_dec n.

Definition FiniteGraph (n : nat) E := Graph (finite_node n) E.
Existing Class FiniteGraph.
Global Identity Coercion proj_graph : FiniteGraph >-> Graph.
