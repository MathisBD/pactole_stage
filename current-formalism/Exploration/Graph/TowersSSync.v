(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain, R. Pelle                  *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
(* Require Import List SetoidList. *)
Require Import Decidable.
Require Import Equalities.
Require Import List Setoid Compare_dec Morphisms FinFun.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteSpace.
Require Import Pactole.Exploration.Graph.DefinitionsSSync.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.
(* Require Import Pactole.Exploration.ZnZ.ImpossibilityKDividesN. *)
Require Import SetoidList.
Require Import Arith_base.
Open Scope list_scope.
Require Import Utf8.

Parameter k : nat.


(** The setting is a ring. *)
Module Gra := MakeRing.

(** There are k good robots and no byzantine ones. *)

Module def : RingDef with Definition n := MakeRing.n.
 Definition n:= MakeRing.n.
 Lemma n_sup_1 : n > 1. Proof. unfold n; apply MakeRing.n_sup_1. Qed.
 Lemma n_pos : n <> 0. Proof. generalize n_sup_1. omega. Qed.
End def.


Axiom k_inf_n : k < MakeRing.n.


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module K : Size with Definition nG := k with Definition nB := 0%nat.
  Definition nG := k.
  Definition nB := 0%nat.
End K.

Module DefsE := DefinitionsSSync.ExplorationDefs(K).
Export DefsE.
Export Gra.
Export MakeRing.

Ltac ImpByz b :=
  assert (Hfalse := Names.Bnames_length);
  assert (Hfalse' := Names.In_Bnames b);
  unfold Names.Bnames, K.nB in *;
  apply length_0 in Hfalse;
  rewrite Hfalse in Hfalse';
  apply in_nil in Hfalse';
  now exfalso.

Import DGF.

(** ** First part: Proof that the starting configuration of a protocole that satify the [Explores_and_stop] property cannot be stall  *)

(** Some definitions and lemmas on Fin.t objects. *)
Fixpoint fin_map n A (f : Fin.t n -> A) {struct n} : list A :=
  match n as n' return n = n' -> list A with
    | 0%nat => fun _ => nil
    | S m => fun Heq => cons (f (eq_rec_r _ Fin.F1 Heq)) (fin_map m A (fun x => f (eq_rec_r _ (Fin.FS x) Heq)))
  end (eq_refl n).

 Definition Vlist : list Graph.V := fin_map n Graph.V (fun x : Graph.V => x).

 Lemma fin_map_length : forall n A (f : Fin.t n -> A), length (fin_map n A f) = n.
 Proof.
   intros n A f. induction n.
   reflexivity.
   simpl. now rewrite IHn.
 Qed.

 
 Lemma Vlist_length : length Vlist = n.
 Proof.
   unfold Vlist, Graph.V.
   apply fin_map_length.
 Qed.

 Theorem InA_fin_map : forall n0 A eqA `(Equivalence A eqA) g (f : Fin.t n0 -> A), InA eqA (f g) (fin_map n0 A f).
Proof.
intros n0 A eqA HeqA g f. destruct n0.
+ now apply Fin.case0.
+ revert n0 g f. apply (Fin.rectS (fun n' g => forall f : Fin.t (S n') -> A, InA eqA (f g) (fin_map (S n') A f))).
  - intros n0 f. now left.
  - intros n0 g IHn f. right. apply (IHn (fun x => f (Fin.FS x))).
Qed.

 Lemma fin_map_eq n0 A eqA : forall f g, eqlistA eqA (@fin_map n0 A f) (@fin_map n0 A g) -> forall x, eqA (f x) (g x).
 Proof.
   induction n0; intros f g Heq x.
   * now apply Fin.case0.
   * remember (S n0) as m. destruct x as [m | m x].
   + simpl in Heq. unfold eq_rec_r, eq_sym, eq_rec, eq_rect in Heq. now inv Heq.
   + assert (m = n0) by omega. subst m. clear Heqm.
     simpl in Heq. unfold eq_rec_r, eq_sym, eq_rec, eq_rect in Heq. inv Heq.
     now apply (IHn0 (fun x => f (Fin.FS x)) (fun x => g (Fin.FS x))).
 Qed.

 Set Implicit Arguments.
 Corollary In_fin_map : forall n0 A g (f : Fin.t n0 -> A), In (f g) (fin_map n0 A f).
 Proof. intros. rewrite <- InA_Leibniz. apply (InA_fin_map _). intuition. Qed.
 
 
 Lemma Vlist_In : forall l: V, In l Vlist.
 Proof.
   intros; unfold Vlist.
   change l with (Datatypes.id l). apply In_fin_map. Qed.   

 Theorem fin_map_InA : forall A eqA `(Equivalence A eqA) (eq_dec : forall x y : A, {eqA x y} + {~eqA x y}),
     forall n0 (f : Fin.t n0 -> A) x, InA eqA x (fin_map n0 A f) <-> exists id : Fin.t n0, eqA x (f id).
 Proof.
   intros A eqA HeqA eq_dec n0. induction n0; intros f x.
   * simpl. rewrite InA_nil. split; intro Habs; try elim Habs. destruct Habs. now apply Fin.case0.
   * destruct (eq_dec x (f Fin.F1)) as [Heq | Heq].
   + subst. split; intro Hin. 
   - firstorder.
   - rewrite Heq. now apply (InA_fin_map _).
     + simpl. unfold eq_rec_r. simpl. split; intro Hin.
   - inversion_clear Hin; try contradiction. rewrite (IHn0 (fun id => f (Fin.FS id)) x) in H.
     destruct H as [id Hin]; subst; try now elim Heq. now exists (Fin.FS id).
                                                                 - right. destruct Hin as [id Hin]. rewrite Hin in *. clear Hin.
                                                                   rewrite (IHn0 (fun id => f (Fin.FS id)) (f id)). revert f Heq.
                                                                   apply (Fin.caseS  (λ n0 (t : Fin.t (S n0)), forall f : Fin.t (S n0) -> A,
                                                                                         ~eqA (f t) (f Fin.F1) -> exists id0 : Fin.t n0, eqA (f t) (f (Fin.FS id0)))).
                                                                   clear -HeqA. intros n f Hn. elim Hn. reflexivity.
                                                                   clear -HeqA. intros n id f Hn. exists id. reflexivity.
 Qed.
 
 Lemma fin_map_NoDupA : forall n0 A (f : Fin.t n0 -> A) (eqA : relation A), 
     Equivalence eqA ->
     (forall x y : A, {eqA x y} + {~ eqA x y}) ->
     injective (fun x y =>
                  (Z.of_nat (proj1_sig (Fin.to_nat x)) mod Z.of_nat n0) =
                  (Z.of_nat (proj1_sig (Fin.to_nat y)) mod Z.of_nat n0))%Z
                  eqA f
     -> NoDupA eqA (fin_map n0 A f).
 Proof.
   intros n0 A f eqA HeqAe HeqAd Hinj. induction n0.
   * assert (Heq : fin_map 0 A f = nil).
     { rewrite <- length_zero_iff_nil. apply fin_map_length. }
     rewrite Heq. constructor.
   * simpl. constructor.
   + rewrite (fin_map_InA _).
   - intros [id Heq].
     unfold injective in Hinj.
     apply Hinj in Heq.
     rewrite 2 Z.mod_small in Heq; try (simpl ;lia).
     apply Nat2Z.inj_iff in Heq.
     apply Fin.to_nat_inj in Heq.
     simpl in *.
     inversion Heq.
     split.
     lia.
     apply inj_lt.
     unfold eq_rec_r, eq_rec, eq_rect.
     destruct (eq_sym eq_refl).
     apply Fin2Restrict.f2n_ok.
   - apply HeqAd.
     + apply IHn0. intros x y Heq.
       apply Hinj in Heq.
       rewrite 2 Z.mod_small in Heq; try (split;
       try lia;
       apply inj_lt;
       unfold eq_rec_r, eq_rec, eq_rect;
       destruct (eq_sym eq_refl);
       apply Fin2Restrict.f2n_ok).
       apply Nat2Z.inj_iff in Heq.
       apply Fin.to_nat_inj in Heq.
       unfold eq_rec_r, eq_rec, eq_rect in *.
       destruct (eq_sym eq_refl).
       apply Fin.FS_inj in Heq.
       now rewrite Heq.
 Qed.


  Lemma Vlist_NoDup : NoDupA Graph.Veq Vlist.
  Proof.
  unfold Vlist. apply fin_map_NoDupA.
  - apply Graph.Veq_equiv.
  - apply Graph.Veq_dec.
  - intros x y Hxy.
    unfold Graph.Veq, V2Z in Hxy.
    unfold Loc.eq in *.
    rewrite 2 Z.mod_mod in *.
    assumption.
    generalize n_sup_1. lia.
    generalize n_sup_1. lia.
  Qed.

(** All location cannot be filled, as we have the axiom [k_inf_n] *)
  
 Lemma ConfExistsEmpty :
  forall (conf:Config.t),
    (∀ l : Spect.M.elt, Spect.M.In l (snd (!! conf Loc.origin))) -> False.
 Proof.
  intro.
  generalize k_inf_n; intros Hkin.
  assert (Hcard : Spect.M.cardinal (snd (!! conf Loc.origin)) = k).
  { unfold Spect.from_config.
    simpl.
    rewrite Spect.cardinal_multiset,
    Config.list_spec, map_map, map_length.
    generalize Names.names_length.
    intros.
    unfold Names.ident.
    rewrite H.
    now unfold K.nG, K.nB. }
  assert (Hsize : (Spect.M.size (snd (!! conf Loc.origin)) < n)%nat).
  { generalize (Spect.M.size_cardinal (snd (!! conf Loc.origin))).
    omega.
  }
  assert ((forall l, Spect.M.In l (snd (!! conf Loc.origin))) ->
           (length (Vlist) <= Spect.M.size (snd (!! conf Loc.origin)))%nat).
  { intros Hin_fa.
    generalize Vlist_In.
    intros Hin.
    rewrite Spect.M.size_spec.
    assert (forall l : Spect.M.elt, InA Graph.Veq l (Spect.M.support (snd (!! conf Loc.origin)))).
    intros.
    specialize (Hin_fa l).
    now rewrite Spect.M.support_spec.
    apply (Preliminary.inclA_length Graph.Veq_equiv).
    apply Vlist_NoDup.
    unfold inclA.
    intros.
    apply H.
  }
  rewrite Vlist_length in H.
  intros.
  specialize (H H0).
  omega.
Qed.

Lemma stop_tl : forall e, Stopped e -> Stopped (Stream.tl e).
Proof.
  intros.
  apply H.
Qed.

Lemma stop_eeq : forall e, Stopped e -> eeq e (Stream.tl e). 
Proof.
  cofix.
  coinduction e.
  apply H.
  apply H.
Qed.

(** Any starting configuration cannot be stalled. *)  
Theorem no_stop_on_starting_conf : forall c r d e,
    Explores_and_stop r ->
    eeq e (execute r d c) -> 
    Valid_starting_conf c ->
    Fair d ->
    ~Stopped e.
Proof.  
  intros c r d e Hexp Heqe Hvalid Hfair Hsto.
  destruct (Hexp d c Hvalid) as (Hvisit, Hstop).
  apply Hfair.
  assert (Hfalse :=  ConfExistsEmpty c).
  unfold Visited_now in *.
  assert (Hfalse' : exists loc, ~ Spect.M.In loc (snd (!! c Loc.origin))).
  { now apply Logic.Classical_Pred_Type.not_all_ex_not. }
  clear Hfalse.
  destruct Hfalse' as (loc, Hfalse).
  specialize (Hvisit loc).
  rewrite <- Heqe in *.
  induction Hvisit.
  rewrite Heqe in *.
  destruct H.
  rewrite Spect.from_config_In in Hfalse;
    destruct Hfalse.
  exists (Good x).
  apply H.
  apply IHHvisit.
  rewrite Heqe.
  symmetry; 
  apply stop_eeq.
  now rewrite Heqe in *.
  destruct Hsto.
  apply Hsto.
  destruct Hsto.
  constructor.
  apply Hsto.
Qed.


(** ** Second Part : To performe the exploration with stop, a least 2 robot are needed. *)

(** A configuartion that is stalled have a towen on, that means a location with more than 1 robot *)
Lemma finalconf_towerOn : forall r,
    (Explores_and_stop r) ->
    forall c d e,
      Fair d ->
      eeq e (execute r d c) -> 
      Stopped e -> 
      exists loc, ((snd (!! c Loc.origin))[loc] > 1)%nat.
Proof.
  intros.
  generalize (no_stop_on_starting_conf (H) H1).
  intros.
  destruct (Classical_Prop.classic (Valid_starting_conf c)).
  now specialize (H3 H4 H0).
  apply Classical_Pred_Type.not_all_not_ex.
  intros Hf.
  destruct H3.
  unfold Valid_starting_conf.
  intros l' (ex, Hex).
  now specialize (Hf ex).
  apply H0.
  easy.
Qed.


Parameter c : Config.t.
Axiom Vc : Valid_starting_conf c.
Parameter d: demon.
Axiom fair_d : Fair d.

Lemma exec_stopped r : forall d c, Fair d -> Will_stop (execute r d c)
                        -> exists d' c', Fair d'/\ Stopped (execute r d' c').
Proof.
  intros.
  remember (execute r d0 c0) as s.
  revert Heqs.
  revert d0 c0 H.
  induction H0.
  intros.
  exists d0, c0; now rewrite Heqs in H.
  intros d0 c0 Hd Hs.
  apply (IHeventually (Stream.tl d0) (Stream.hd (Stream.tl s))).
  destruct Hd.
  constructor.
  apply Hd.
  apply Hd.
  rewrite Hs, execute_tail.
  now simpl.
Qed.


(** final theorem: to permform the exploration with stop, a at least 2 robots are needed *)  
Lemma no_exploration_k_inf_2 : forall r,
    Explores_and_stop r ->
    (k > 1)%nat.
Proof.
  intros.
  assert (Hexr := exec_stopped r).
  assert (Htower := finalconf_towerOn).  
  destruct (H d c Vc).
  apply fair_d.
  specialize (Hexr d c fair_d H1).
  destruct Hexr as (d', ( c', (Hfair, Hstop))).
  specialize (Htower r H c' d'(execute r d' c') Hfair (reflexivity _) Hstop).
  destruct Htower.
  assert (Hcard := Spect.M.cardinal_lower x (snd (!! c' Loc.origin))).
  rewrite Spect.cardinal_from_config in Hcard.
  unfold K.nG, K.nB in *.
  lia.
Qed.
