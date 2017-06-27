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
Require Import Pactole.Exploration.Graph.Definitions.
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

Module DefsE := Definitions.ExplorationDefs(K).
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

Import Equiv.DGF.

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

CoFixpoint SequencialExection (e : execution) :
  Stream.forever
    (fun e' => forall r d conf,
         e' = execute r d conf /\
         (exists id, forall id', id' <> id /\ step (Stream.hd d) id' (conf id')
                                              = Moving false)) e.


Definition list_of_conf_diff (l : list Config.t) :  list (list Config.t) :=
  fold_left
    (fun acc c =>
       match acc with
       | nil => (c :: nil) :: nil
       | a :: l' => match l' with | nil => 
         if (Config.eq_dec c)
                    then (c::nil)::acc
                    else ((a ++ (c :: nil)) :: nil)
       end) nil  .
                                   
  match l with
  | nil => nil
  | a :: nil => (a :: nil) :: nil
  | a :: b :: l' => if Config.eq_dec a b
  then (match (list_of_conf_diff l) with
                  | c :: d => (a :: c) :: d
                  | nil => (a :: nil) :: nil
                  end)
                     else (a::nil) ::(list_of_conf_diff (b :: l'))
  end.
           

Definition MRS r d conf : List Config.t :=
  fold_left 
    (fun (acc : nat) l =>
       if length

            
Theorem TowerOnFinalConf :
  forall (conf : Config.t) (r : robogram) (d : demon),
    (exists conf_start,
        ValidStartingConf conf_start /\
    let e_start := execute r d conf_start in
    Stream.eventually (fun e1 => Config.eq (Stream.hd e1) conf) e_start ) -> 
    ValidStartingConfSolExplorationStop r d ->
    let e := execute r d conf in
    Stopped e ->
    (forall loc, HasBeenVisited loc e) ->
    forall l : Loc.t, let m := Spect.from_config(conf)  in
                      m[l] <= 1 -> False.
Proof.
  intros.
  simpl in *.
  destruct H.
  destruct H.
  simpl in *.
  destruct (H0 x).
  assumption.
  destruct H4.
  simpl in *.
  destruct H6.
  unfold e in *.
  rewrite H4 in *.
  assert (exists l', (!! conf)[l'] = 0).
  { induction Names.names eqn : Hnames.
    exists Loc.origin.
    assert (Spect.cardinal (!! conf) = 0).
    rewrite Spect.cardinal_from_config.
    rewrite <- Names.names_length.
    rewrite Hnames.
    easy.
    rewrite Equiv.M.cardinal_0 in H7.
    rewrite H7.
    apply Equiv.M.empty_spec.
    generalize 
    unfold Spect.multiplicity.
    
  }
  now rewrite <- H4.
  constructor.
  intros.
  specialize (H1 l0).
  constructor.
  