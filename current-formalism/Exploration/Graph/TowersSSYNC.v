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
Require Import Pactole.Exploration.ZnZ.ImpossibilityKDividesN.
Require Import SetoidList.
Require Import Arith_base.
Open Scope list_scope.
Require Import Utf8.

Parameter kG : nat.


Module Gra := MakeRing.
(** The setting is a ring. *)

  (** There are KG good robots and no byzantine ones. *)

Module def : RingDef with Definition n := n.
 Definition n:= n.
 Lemma n_sup_1 : n > 1. Proof. unfold n; apply n_sup_1. Qed.
 Lemma n_pos : n <> 0. Proof. generalize n_sup_1. omega. Qed.
End def.


Axiom k_inf_n : kG < n.


(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
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

Fixpoint fin_map n A (f : Fin.t n -> A) {struct n} : list A :=
  match n as n' return n = n' -> list A with
    | 0 => fun _ => nil
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
    unfold Graph.Veq, Loc in Hxy.
    unfold ImpossibilityKDividesN.Loc.eq, n in *.
    rewrite 2 Z.mod_mod in *.
    assumption.
    generalize n_sup_1. unfold ImpossibilityKDividesN.def.n; lia.
    generalize n_sup_1. unfold ImpossibilityKDividesN.def.n; lia.
  Qed.
 
 Lemma ConfExistsEmpty :
  forall (conf:Config.t),
    (∀ l : Spect.elt, Spect.In l (!! conf)) -> False.
 Proof.
  intro.
  generalize k_inf_n; intros Hkin.
  assert (Hcard : Spect.cardinal (!!conf) = kG).
  { unfold Spect.from_config.
    rewrite Spect.cardinal_multiset,
    Config.list_spec, map_map, map_length.
    generalize Names.names_length.
    intros.
    unfold Names.ident.
    rewrite H.
    now unfold K.nG, K.nB. }
  assert (Hsize : Spect.size (!!conf) < n).
  { generalize (Spect.size_cardinal (!! conf)).
    unfold n.
    omega.
  }
  assert ((forall l, Spect.In l (!! conf)) ->
           length (Vlist) <= Spect.size (!! conf)).
  { intros Hin_fa.
    generalize Vlist_In.
    intros Hin.
    rewrite Spect.size_spec.
    assert (forall l : Spect.elt, InA Graph.Veq l (Spect.support (!!conf))).
    intros.
    specialize (Hin_fa l).
    now rewrite Spect.support_spec.
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

Definition SequencialExection (e : execution) : Prop :=
  Stream.forever
    (fun e' => forall r d conf,
         eeq e' (execute r d conf) /\
         (exists id, forall id', id' <> id /\ step (Stream.hd d) id' (conf id')
                                              = None)) e.

Fixpoint Biggest_list_of_exe (l : list Config.t) (e : execution) : Prop :=
  match l with
  | nil => Stopped e
  | x :: nil => Config.eq x (Stream.hd e) /\ Stopped e
  | x :: y => Config.eq x (Stream.hd e) /\
                if Config.eq_dec (Stream.hd e) (Stream.hd (Stream.tl (Stream.tl e)))
                then False
                else Biggest_list_of_exe y (Stream.tl (Stream.tl e))

  end.

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

  
Theorem finalconf_towerOn_aux : forall c r d e,
    ValidStartingConfSolExplorationStop r ->
    eeq e (execute r d c) -> 
    ValidStartingConf c ->
    ~Stopped e.
Proof.  
  intros c r d e Hexp Heqe Hvalid Hsto.
  destruct (Hexp d c Hvalid) as (Hvisit, Hstop).
  assert (Hfalse :=  ConfExistsEmpty c).
  unfold is_visited in *.
  assert (Hfalse' : exists loc, ~ Spect.In loc (!! c)).
  { now apply Logic.Classical_Pred_Type.not_all_ex_not. }
  clear Hfalse.
  destruct Hfalse' as (loc, Hfalse). 
  specialize (Hvisit loc).
  rewrite <- Heqe in *.
  induction Hvisit.
  rewrite Heqe in *.
  destruct H.
  simpl in *.
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

Lemma finalconf_towerOn : forall r,
    (ValidStartingConfSolExplorationStop r) ->
    forall c d e, eeq e (execute r d c) -> 
                  Stopped e -> 
                  exists loc, (!! c)[loc] > 1.
Proof.
  intros.
  generalize (finalconf_towerOn_aux d (H) H0).
  intros.
  destruct (Classical_Prop.classic (ValidStartingConf c)).
  now specialize (H2 H3).
  apply Classical_Pred_Type.not_all_not_ex.
  intros Hf.
  destruct H3.
  unfold ValidStartingConf.
  intros (ex, Hex).
  now specialize (Hf ex).
Qed.

Corollary finalconf_towerOn_bis : forall c,
    forall r, ValidStartingConfSolExplorationStop r ->
              forall d, Stopped (execute r d c) ->
                        exists loc, (!! c)[loc] > 1.
Proof.
  intros.
  now apply (finalconf_towerOn H c d (reflexivity (execute r d c))).
Qed.


Parameter c : Config.t.
Axiom Vc : ValidStartingConf c.
Parameter d: demon.
Parameter e : execution.
Axiom Ve : ValidStartingConf (Stream.hd e).

(* CoFixpoint In_Stream {A} (s : Stream.t A) (a : A) (eqA : A -> A -> Prop) :=
  match s with
  | cons e s' => eqA a e \/ In_Stream s' a eqA
  end.
 *)

Definition exec_r_comp (e:execution) (r: robogram) :=
  exists d c, eeq e (execute r d c).

Lemma exec_stopped r : forall d c, Will_stop (execute r d c)
                        -> exists d' c', Stopped (execute r d' c').
(*exists e, exec_r_comp e r /\ Stopped e.*)
Proof.
  intros.
  remember (execute r d0 c0) as s.
  revert Heqs.
  revert d0 c0.
  induction H.
  intros.
  exists d0, c0; now rewrite Heqs in H.
  intros d0 c0 Hs.
  apply (IHeventually (Stream.tl d0) (Stream.hd (Stream.tl s))).
  rewrite Hs, execute_tail.
  now simpl.
Qed.


  
Lemma no_exploration_k_inf_2 : forall r,
    ValidStartingConfSolExplorationStop r ->
    kG > 1.
Proof.
  intros.
  assert (Hexr := exec_stopped r).
  assert (Htower := finalconf_towerOn_bis).  
  destruct (H d c Vc).
  specialize (Hexr d c H1).
  destruct Hexr as (d', ( c', Hstop)).
  specialize (Htower c' r H d' Hstop).
  destruct Htower.
  assert (Hcard := Spect.cardinal_lower x (!! c')).
  rewrite Spect.cardinal_from_config in Hcard.
  unfold K.nG, K.nB in *.
  lia.
Qed.
  
Fixpoint last_init_conf (l : list Config.t) (a : Config.t) :=
  match l with
  | nil => (False, nil)
  | conf :: l' => if Config.eq_dec a conf
                  then (((List.Forall (fun x => ~ ValidStartingConf x ) l')
                        /\ ValidStartingConf a),l')
                  else last_init_conf l' a
  end.
  
  

Theorem TowerOnFinalConf : forall l r d c e x,
    ValidStartingConf c->
    eeq e (execute r d c) ->
    Biggest_list_of_exe l e ->
    let (P,l') := last_init_conf l c in
    P ->
    ValidStartingConfSolExplorationStop r d ->
    SequencialExection e ->
    (forall conf, In conf l' ->
                  exists loc, (!! conf)[loc] = x
                              -> 1 < x -> x < kG)
      
      -> length l' >= n - kG + 1.


Proof.
  intros l r d c e x Hconf Heq_e Hlist.
  destruct (last_init_conf l c) as (P, l') eqn : Hlic.
  intros HP Hvalid Hsequ Hl_conf.
  assert (length l' < n - kG + 1
         -> False).
  { intros Hf.
    unfold last_init_conf in Hlic.
    induction l.
    simpl in *.
    rewrite surjective_pairing in Hlic.
    simpl in *.
    assert (P = fst (P, l')) by intuition.
    rewrite <- Hlic in *.
    simpl in *.
    now rewrite <- H.
    destruct (Config.eq_dec c a).
    assert (P = fst (P, l')) by intuition.
    assert (l' = snd (P, l')) by intuition.
    rewrite <- Hlic in *; simpl in *.
    destruct HP.
    apply H in HP.
    apply Hlic.
    intuition.
    assert (ValidStartingConf a).
    destruct (last_init_conf l) eqn : Hl.
    
    
  split.
  - intros.
    destruct Hsequ.
    specialize (H0 r d conf). 
    destruct H0 as (He_conf, (id,Hid)).
    
    destruct l eqn : Hl.
  - simpl in *.
    destruct (Hvalid c Hconf) as (Hvisit, Hstop).
    assert (Hfalse :=  ConfExistsEmpty c).
    unfold is_visited in *.
    rewrite Heq_e in Hlist.
    now generalize (test Hvalid Heq_e Hconf Hlist).
  - destruct l0 eqn : Hl'.
     + simpl in *.
       destruct Hlist as (Hceq, Hstp).
       generalize (test Hvalid Heq_e Hconf).
       intros Htest.
       assert (Hval_t: ValidStartingConf t).
       rewrite Hceq.
       rewrite Heq_e.
       now simpl in *.
       assert (He_eq : eeq e (execute r d t)).
       rewrite Hceq.
       now rewrite Heq_e.
       generalize (test Hvalid He_eq Hval_t). 
       intros Htest'.
       destruct Htest.
       now rewrite <- Heq_e.
     + destruct (Classical_Prop.classic (ValidStartingConf (last (t :: t0 :: l1) c)))
         as [Hv|Hnv].
       simpl in *.
       destruct ( Config.eq_dec (Stream.hd e) (Stream.hd (Stream.tl (Stream.tl e))));
         try easy.
       destruct Hlist as (Hceq, Hlist).       
       assert (Hse : ~Stopped e).
       intros Hs.
       destruct Hs as (Hse, Hs).
       now unfold stop_now in Hse.
       destruct l1.
       * destruct (Classical_Prop.classic
                     (ValidStartingConfSolExplorationStop
                     r (Stream.tl (Stream.tl d)))) as [Hvrd|Hnvrd].
         assert (Heeq_to : eeq (Stream.tl (Stream.tl e)) (execute r (Stream.tl (Stream.tl d)) t0)).  
         { rewrite Heq_e.
           destruct Hlist as (Hlist, Hstp).
           rewrite Heq_e in Hlist.
           repeat rewrite execute_tail in *.
           apply execute_compat; try easy.
         }
         destruct (test Hvrd Heeq_to Hv).
         now rewrite <- Heeq_to.
         unfold ValidStartingConfSolExplorationStop in *.
         apply Classical_Prop.NNPP.
         intro.
         apply Hnvrd.
         intros.
         destruct (Hvrd t0 Hv).  Heeq_to).
         admit.
       apply Classical_Pred_Type.not_all_not_ex.
       intros Hf.
       destruct Hnv.
       unfold ValidStartingConf.
       intros (ex, Hex).
       now specialize (Hf ex).
Qed.       