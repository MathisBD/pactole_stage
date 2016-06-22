(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)


Require Import Rbase.
Require Import Equalities.
Require Import Morphisms.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.


Parameter V : Type.
Parameter E : Type.
Parameter tgt src : E -> V.
Parameter threshold : E -> R.
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



Declare Module N : Size.
Declare Module Names : Robots(N).

Module LocationA : DecidableType with Definition t := V with Definition eq := Veq.
  Definition t := V.
  Definition eq := Veq.
  Definition eq_equiv : Equivalence eq := Veq_equiv.
  Definition eq_dec : forall l l', {eq l l'} + {~eq l l'} := Veq_dec.
End LocationA.

Module ConfigA := Configurations.Make (LocationA)(N)(Names).

(** For spectra *)
Module View : DecidableType with Definition t := ConfigA.t with Definition eq := ConfigA.eq.
  Definition t := ConfigA.t.
  Definition eq := ConfigA.eq.
  Definition eq_equiv := ConfigA.eq_equiv.
  Definition eq_dec := ConfigA.eq_dec.
End View.
