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
Require Import Pactole.Preliminary.
Require Import Morphisms.


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