(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Reals.
Require Import Omega.
Require Import Arith.Div2.
Require Import Psatz.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Stream.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.DiscreteGraphFormalismSSync.
Require Import Pactole.DiscreteSimilarity.
Require Import Pactole.CommonDiscreteFormalism.
Require Import Pactole.DiscreteRigidFormalism.
Require Import Pactole.MultisetSpectrum.
Require Import Pactole.CommonIsoGraphFormalism.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.


Close Scope Z_scope.
Set Implicit Arguments.


(** Definition of the ring. *)
Parameter n : nat.
Axiom n_sup_1 : 1 < n.

Module Def : RingDef with Definition n := n.
 Definition n:= n.
 Lemma n_pos : n <> 0. Proof. unfold n. generalize n_sup_1. omega. Qed.
 Lemma n_sup_1 : n > 1. Proof. unfold n; apply n_sup_1. Qed.
End Def.


Module ExplorationDefs (N : Size).

Import Def.
Module Names := Robots.Make(N).
Module Ring := MakeRing(Def).


Module Loc <: DecidableType.
  Definition t := Ring.V.
  Definition eq := Ring.Veq.
  Definition eq_dec : forall x y, {eq x y} + {~eq x y} := Ring.Veq_dec.
  Instance eq_equiv : Equivalence eq := Ring.Veq_equiv.
  Definition origin := Ring.of_Z 0.
  
  Definition add (x y : t) := Ring.of_Z (Ring.to_Z x + Ring.to_Z y).
  Definition mul (x y : t) := Ring.of_Z (Ring.to_Z x * Ring.to_Z y).
  Definition unit := Ring.of_Z 1.
  Definition opp (x : t) := Ring.of_Z (- Ring.to_Z x)%Z.
  
  Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Proof. intros ? ? Hx ? ? Hy. hnf in Hx, Hy. unfold add. now rewrite Hx, Hy. Qed.
  
  Instance mul_compat : Proper (eq ==> eq ==> eq) mul.
  Proof. intros ? ? Hx ? ? Hy. hnf in Hx, Hy. unfold mul. now rewrite Hx, Hy. Qed.
  
  Instance opp_compat : Proper (eq ==> eq) opp.
  Proof. intros ? ? Heq. hnf in Heq. unfold opp. now rewrite Heq. Qed.
  
  Lemma add_origin : forall u, eq (add u origin) u.
  Proof.
  generalize (Def.n_sup_1).
  intros Hn u. hnf. unfold add, origin.
  rewrite Ring.Z2Z, Z.mod_0_l, Z.add_0_r, Ring.V2V; trivial; unfold Ring.n; omega.
  Qed.
  
  Lemma add_opp : forall u, eq (add u (opp u)) origin.
  Proof.
  intro u. unfold add, opp, origin. hnf. rewrite Ring.Z2Z.
  apply eq_proj1. unfold Ring.of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_r.
  ring_simplify (Ring.to_Z u + - Ring.to_Z u)%Z.
  rewrite Z.mod_0_l; trivial; [].
  generalize (Def.n_sup_1). unfold Ring.n. omega.
  Qed.
  
  Lemma add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Proof.
  intros u v w. hnf. unfold eq, add.
  rewrite 2 Ring.Z2Z. apply eq_proj1. unfold Ring.of_Z. simpl.
  rewrite Zdiv.Zplus_mod_idemp_r, Zdiv.Zplus_mod_idemp_l.
  do 2 f_equal. ring.
  Qed.
  
  Lemma add_comm : forall u v, eq (add u v) (add v u).
  Proof.
  unfold eq, add. intros u v. hnf.
  now rewrite Z.add_comm.
  Qed.
  
  Lemma add_reg_r : forall w u v, eq (add u w) (add v w) -> eq u v.
  Proof. (* proof taken from DiscreteSpace.v *)
  intros w u v Heq. setoid_rewrite <- add_origin.
  now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
  Qed.
  
  Lemma add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Proof. (* proof taken from DiscreteSpace.v *)
  setoid_rewrite add_comm. apply add_reg_r.
  Qed.
  
  Lemma opp_opp : forall u, eq (opp (opp u)) u.
  Proof.
  generalize (Def.n_sup_1).
  intros Hn [u Hu]. unfold opp. hnf. rewrite Ring.Z2Z.
  apply eq_proj1. unfold Ring.of_Z. simpl.
  destruct (Nat.eq_dec u 0); try (now subst); []. (* required for the proofs about Z.opp and mod *)
  unfold Ring.to_Z. simpl proj1_sig.
  rewrite (Z.mod_opp_l_nz (Z.of_nat u)), (Z.mod_small (Z.of_nat u)), Z.mod_opp_l_nz, Z.mod_small;
  try lia || (rewrite Z.mod_small; lia); [].
  ring_simplify (Z.of_nat Ring.n - (Z.of_nat Ring.n - Z.of_nat u))%Z. apply Nat2Z.id.
  Qed.
  
  Lemma opp_origin : eq (opp origin) origin.
  Proof. apply add_reg_l with origin. now rewrite add_opp, add_origin. Qed.
  
  Lemma opp_distr_add : forall u v, eq (opp (add u v)) (add (opp u) (opp v)).
  Proof. (* proof taken from DiscreteSpace.v *)
  intros u v. apply (@add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
  setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
  Qed.
End Loc.


Module Iso := CommonIsoGraphFormalism.Make(Ring)(Loc). (* Careful! It also contains a module called Iso *)
Module MkInfo := CommonGraphFormalism.Make(Ring)(Loc).
Module Info := MkInfo.Info.
Module Config := Configurations.Make(Loc)(N)(Names)(Info).
Module Spect := MultisetSpectrum.Make(Loc)(N)(Names)(Info)(Config).
Module DGF := DiscreteGraphFormalism.DGF(Ring)(N)(Names)(Loc)(MkInfo)(Config)(Spect)(Iso).
Export Iso DGF.

Notation "s [ pt ]" := (Spect.multiplicity pt s) (at level 5, format "s [ pt ]").
Notation "!!" := Spect.from_config (at level 1).
Add Search Blacklist "Spect.M" "Ring".


Definition bij_trans_V (c : Loc.t) : Bijection.t Loc.eq.
refine {|
  Bijection.section := fun x => (Loc.add x (Loc.opp c));
  Bijection.retraction := fun x => Loc.add x c |}.
Proof.
abstract (intros x y; split; intro Heq;
          now rewrite <- Heq, <- Loc.add_assoc, ?(Loc.add_comm _ c), Loc.add_opp, Loc.add_origin).
Defined.

Definition bij_trans_E (c : Loc.t) : Bijection.t Ring.Eeq.
  refine {|
      Bijection.section := fun x =>  (Loc.add (fst x) (Loc.opp c), snd x);
      Bijection.retraction := fun x => (Loc.add (fst x) c, snd x) |}.
Proof.
+ abstract (intros ? ? Heq; hnf in *; simpl; destruct Heq as [Heq ?]; now rewrite Heq).
+ abstract (intros x y; split; intro Heq; hnf in *; simpl in *;
            now rewrite <- (proj1 Heq), <- Loc.add_assoc, ?(Loc.add_comm _ c), Loc.add_opp, Loc.add_origin).
Defined.

(* Definition bij_trans_T := Isomorphism.bij_id Iso.Req_equiv. *)
Parameter bij_trans_T : Loc.t -> Bijection.t Iso.Req.
Axiom bT_morph : forall c (e : Ring.E),
    (Bijection.section (bij_trans_T c)) (Ring.threshold e) =
    Ring.threshold ((Bijection.section (bij_trans_E c)) e).
Axiom bT_bound : forall c r, (0 < r < 1)%R <->
                             (0 < (Bijection.section (bij_trans_T c) r) < 1)%R.
Axiom bT_crois : forall c a b, (a < b)%R ->
                               ((Bijection.section (bij_trans_T c) a) <
                                (Bijection.section (bij_trans_T c) b))%R.
Axiom bT_compat : forall c1 c2, Bijection.eq (bij_trans_T c1) (bij_trans_T c2).

Definition id_s := Iso.id.

Definition trans (c : Loc.t) : Iso.t.
refine {|
    Iso.sim_V := bij_trans_V c;
    Iso.sim_E := bij_trans_E c;
    Iso.sim_T := bij_trans_T c |}.
Proof.
* intro e. split.
  + unfold Ring.src. simpl. reflexivity.
  + apply eq_proj1.
    unfold Ring.tgt. simpl. unfold Loc.t, Loc.add. rewrite 2 Ring.Z2Z.
    destruct (snd e) eqn:Hsnd.
    - rewrite 2 Zdiv.Zplus_mod_idemp_l. do 2 f_equal. ring.
    - rewrite Zdiv.Zplus_mod_idemp_l, Zdiv.Zminus_mod_idemp_l. do 2 f_equal. ring.
    - rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod; trivial; [].
      unfold Ring.n. generalize Def.n_sup_1. omega.
* apply bT_morph.
* apply bT_crois.
* apply bT_bound.
Defined. (* TODO: abstract the proofs *)


Instance trans_compat : Proper (Loc.eq ==> Iso.eq) trans.
Proof.
intros c1 c2 Hc. unfold Iso.eq, trans. simpl in *.
split; [| split].
+ intros x y Heq. simpl. now rewrite Heq, Hc.
+ intros x y [Heq ?]. simpl. split; simpl; trivial; []. now rewrite Heq, Hc.
+ now apply bT_compat.
Qed.

Lemma trans_origin : Iso.eq (trans Loc.origin) Iso.id.
Proof.
split; [| split].
+ hnf. intros. simpl. now rewrite Loc.opp_origin, Loc.add_origin.
+ intros [] [] []. hnf. simpl. now rewrite Loc.opp_origin, Loc.add_origin.
+ intros x y Heq. rewrite Heq. hnf. cbn. (* bij_trans_T is a still parameter... *) admit.
Admitted.

(* Module Export Common := CommonFormalism.Make(Loc)(N)(Names)(Config)(Spect). *)
Definition is_visited (loc : Loc.t) (config : Config.t) :=
  exists g, Loc.eq (config (Good g)) loc.

Instance is_visited_compat : Proper (Loc.eq ==> Config.eq ==> iff) is_visited.
Proof.
intros l1 l2 Hl c1 c2 Hc. unfold is_visited.
split; intros [g Hv]; exists g.
- rewrite <- Hl, <- Hv. symmetry. apply Hc.
- rewrite Hl, <- Hv. apply Hc.
Qed.

Definition Will_be_visited (loc : Loc.t) (e : execution) : Prop :=
  Stream.eventually (Stream.instant (is_visited loc)) e.

Definition stop_now (e : execution) :=
  Config.eq (Stream.hd e) (Stream.hd (Stream.tl e)).

Instance stop_now_compat : Proper (eeq ==> iff) stop_now.
Proof.
intros e1 e2 He. split; intros Hs;
unfold stop_now in *.
now rewrite <- He.
now rewrite He.
Qed.

Definition Stopped (e : execution) : Prop :=
  Stream.forever (stop_now) e.

Instance Stopped_compat : Proper (eeq ==> iff) Stopped.
Proof.
intros e1 e2 He. split; revert e1 e2 He ; coinduction rec.
- destruct H. now rewrite <- He.
- destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
- destruct H. now rewrite He.
- destruct H as [_ H], He as [_ He]. apply (rec _ _ He H).
Qed.


Definition Will_stop (e : execution) : Prop :=
  Stream.eventually Stopped e.
 
Instance Will_be_visited_compat : Proper (Loc.eq ==> eeq ==> iff) Will_be_visited.
Proof.
intros l1 l2 Hl. now apply Stream.eventually_compat, Stream.instant_compat, is_visited_compat.
Qed.

Instance Will_stop_compat : Proper (eeq ==> iff) Will_stop.
Proof. apply Stream.eventually_compat, Stopped_compat. Qed.

(* [Exploration_with_stop e] mean that after a finite time, every node of the space has been
  visited, and after that time, all robots will stay at the same place forever*)
Definition FullSolExplorationStop  (r : robogram) (d : demon) := 
forall config, (forall l, Will_be_visited l (execute r d config)) /\ Will_stop (execute r d config).

Definition ValidStartingConf conf :=
  (exists l : Loc.t,
    let m := Spect.from_config(conf) in
    m[l] > 1) -> False.

Instance ValidStartingConf_compat : Proper (Config.eq ==> iff) ValidStartingConf.
Proof.
intros c1 c2 Hc.
split; intros Hv Hf; unfold ValidStartingConf in *;
destruct Hv, Hf as (l ,Hf); exists l; try now rewrite <- Hc.
now rewrite Hc.
Qed.

Definition ValidStartingConfSolExplorationStop (r : robogram) (d : demon) :=
  forall config,
    ValidStartingConf config -> 
    (forall l, Will_be_visited l (execute r d config)) /\
    Will_stop (execute r d config).

Definition HasBeenVisited loc e :=
  forall (conf : Config.t) r d,
    e = execute r d conf -> 
  exists conf_start,
    let e_start := execute r d conf_start in
    Stream.eventually (fun e1 => Config.eq (Stream.hd e1) conf) e_start
    -> ((Spect.from_config(conf_start))[loc])>0.

End ExplorationDefs.
