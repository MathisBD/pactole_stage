(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain               
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence.      
                                                                          *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Set Implicit Arguments.
Require Import Utf8.
Require Import List SetoidList.
Require Import Decidable.
Require Import Setoid Equalities Morphisms.
Require Import Compare_dec FinFun.
Require Import Arith_base Arith.Div2.
Require Import Omega Psatz.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.DiscreteSpace.
Require Import Pactole.Exploration.Graph.DefinitionsSSync.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.
Open Scope list_scope.


(** There are kG good robots and no byzantine ones. *)
Parameter kG : nat.

Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.

(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := DefinitionsSSync.ExplorationDefs(K).
Export DefsE.

(** Assumptions on the number of robots: it is non zero, less than n and divides n (the size of the ring). *)
Axiom kdn : (n mod kG = 0)%nat.
Axiom k_inf_n : (kG < n)%nat.
Axiom k_sup_1 : (1 < kG)%nat.

(** There is no meaningful information inside state. *)
Lemma no_info : forall rc1 rc2, Loc.eq (Config.loc rc1) (Config.loc rc2) -> Config.eq_RobotConf rc1 rc2.
Proof. intros [? []] [? []] Heq; split; simpl in *; auto. Qed.

(** There is no byzantine robot so we can simplify properties about identifiers and configurations. *)
Lemma no_byz : forall (id : Names.ident) P, (forall g, P (Good g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. unfold K.nB in *. omega.
Qed.

Lemma no_byz_eq : forall config1 config2 : Config.t,
  (forall g, Loc.eq (config1 (Good g)) (config2 (Good g))) -> Config.eq config1 config2.
Proof. intros config1 config2 Heq id. apply (no_byz id). intro g. apply no_info, Heq. Qed.

(** A dummy value used for (inexistant) byzantine robots. *)
Definition dummy_val := {| Config.loc := Loc.origin; Config.state := tt |}.

(** In order to prove that at least one position is occupied, ee define the list of positions. *)
Definition Vlist := Robots.enum n.

Lemma Vlist_NoDup : NoDupA Ring.Veq Vlist.
Proof. unfold Ring.Veq. rewrite NoDupA_Leibniz. apply enum_NoDup. Qed.

Lemma Vlist_length : length Vlist = n.
Proof. apply enum_length. Qed.

Lemma ConfigExistsEmpty : forall config pt, ¬ (∀ l, Spect.M.In l (snd (!! config pt))).
Proof.
generalize k_inf_n; intros Hkin config pt Hall.
assert (Hcard : Spect.M.cardinal (snd (!! config pt)) = kG).
{ unfold Spect.from_config. simpl.
  rewrite Spect.cardinal_multiset, Config.list_spec, map_map, map_length.
  unfold Names.ident. rewrite Names.names_length. now unfold K.nG, K.nB. }
assert (Hsize : Spect.M.size (snd (!! config pt)) < n).
{ generalize (Spect.M.size_cardinal (snd (!! config pt))). omega. }
assert (Hle : n <= Spect.M.size (snd (!! config pt))).
{ rewrite Spect.M.size_spec.
  assert (Hspect : forall l : Spect.M.elt, InA Loc.eq l (Spect.M.support (snd (!! config pt)))).
  { intro l. specialize (Hall l). now rewrite Spect.M.support_spec. }
  rewrite <- Vlist_length.
  apply (Preliminary.inclA_length Ring.Veq_equiv).
  - apply Vlist_NoDup.
  - repeat intro. apply Hspect. }
omega.
Qed.

Definition SequencialExecution (e : execution) : Prop :=
  Stream.forever
    (fun e' => forall r d conf,
         eeq e' (execute r d conf) /\
         (exists id, forall id', id' <> id /\ step (Stream.hd d) id' = None)) e.

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
Proof. intros e He. apply He. Qed.

Lemma stop_eeq : forall e, Stopped e -> eeq e (Stream.tl e). 
Proof. coinduction Hrec; apply H. Qed.

Theorem no_stop_on_starting_config : forall r d config e,
  Fair d ->
  Explore_and_Stop r ->
  eeq e (execute r d config) ->
  Valid_starting_config config ->
  ~Stopped e.
Proof.
intros r d config e Hfair Hsol Heqe Hvalid Hsto.
destruct (Hsol d config Hfair Hvalid) as [Hvisit Hstop].
assert (Hfalse :=  ConfigExistsEmpty config).
assert (Hfalse' : exists loc, ~ Spect.M.In loc (snd (!! config Loc.origin))).
{ now apply Logic.Classical_Pred_Type.not_all_ex_not. }
clear Hfalse.
destruct Hfalse' as (loc, Hfalse).
specialize (Hvisit loc).
rewrite <- Heqe in *.
induction Hvisit.
+ rewrite Heqe in *. destruct H.
  rewrite Spect.from_config_In in Hfalse; destruct Hfalse.
  exists (Good x).
  apply H.
+ apply IHHvisit.
  - rewrite Heqe. symmetry; apply stop_eeq. now rewrite Heqe in *.
  - destruct Hsto. apply Hsto.
  - destruct Hsto. constructor. apply Hsto.
Qed.

Lemma finalconfig_towerOn : forall r d config e,
  Fair d ->
  Explore_and_Stop r ->
  eeq e (execute r d config) -> 
  Stopped e -> 
  exists loc, ((snd (!! config Loc.origin))[loc] > 1)%nat.
Proof.
intros r d config e Hfair Hsol He Hstop.
assert (Hequiv := @no_stop_on_starting_config r d config e Hfair Hsol He).
destruct (Classical_Prop.classic (Valid_starting_config config)) as [Hvalid | Hvalid].
+ now elim Hequiv.
+ apply Classical_Pred_Type.not_all_not_ex.
  intros Hf.
  destruct Hvalid.
  unfold Valid_starting_config.
  intros l' (ex, Hex).
  now specialize (Hf ex).
Qed.

Corollary finalconfig_towerOn_bis : forall r d config,
  Fair d ->
  Explore_and_Stop r ->
  Stopped (execute r d config) ->
  exists loc, ((snd (!! config Loc.origin))[loc] > 1)%nat.
Proof.
intros r d config Hfair Hsol Hstop.
now apply (finalconfig_towerOn config Hfair Hsol (reflexivity (execute r d config))).
Qed.

(*
Parameter config : Config.t.
Axiom Vc : Valid_starting_config config.
Parameter d : demon.
Axiom fair_d : Fair d.
Parameter e : execution.
Axiom Ve : Valid_starting_config (Stream.hd e).
*)

(* CoFixpoint In_Stream {A} (s : Stream.t A) (a : A) (eqA : A -> A -> Prop) :=
  match s with
  | cons e s' => eqA a e \/ In_Stream s' a eqA
  end.
 *)

Definition exec_r_comp (e : execution) (r : robogram) :=
  exists d c, eeq e (execute r d c).

Lemma exec_stopped r : forall d c, Fair d -> Will_stop (execute r d c) ->
  exists d' c', Fair d'/\ Stopped (execute r d' c').
(*exists e, exec_r_comp e r /\ Stopped e.*)
Proof.
intros d' config' Hfair Hstop.
remember (execute r d' config') as e'.
revert Heqe'.
revert d' config' Hfair.
induction Hstop as [e' Hstop | e' Hstop IHstop].
+ intros d' config' Hfair Heq.
  exists d', config'; now rewrite Heq in *.
+ intros d' config' Hfair Heq.
  apply (IHstop (Stream.tl d') (Stream.hd (Stream.tl e'))).
  - destruct Hfair as [_ Hfair]. constructor; apply Hfair.
  - now rewrite Heq, execute_tail.
Qed.

Lemma no_exploration_k_inf_2 : forall r d config,
  Fair d ->
  Explore_and_Stop r ->
  Valid_starting_config config ->
  (kG > 1)%nat.
Proof.
intros r d config Hfair Hsol Hvalid.
assert (Hexr := exec_stopped r).
assert (Htower := finalconfig_towerOn_bis).
destruct (Hsol d config Hfair Hvalid) as [Hvisit Hstop].
destruct (Hexr d config Hfair Hstop) as [d' [config' [Hfair' Hstop']]].
specialize (Htower r d' config' Hfair' Hsol Hstop').
destruct Htower.
assert (Hcard := Spect.M.cardinal_lower x (snd (!! config' Loc.origin))).
rewrite Spect.cardinal_from_config in Hcard.
unfold K.nG, K.nB in *.
lia.
Qed.

Fixpoint last_init_conf (l : list Config.t) (a : Config.t) :=
  match l with
  | nil => (False, nil)
  | conf :: l' => if Config.eq_dec a conf
                  then (((List.Forall (fun x => ~ Valid_starting_config x ) l')
                        /\ Valid_starting_config a),l')
                  else last_init_conf l' a
  end.

(* 
Theorem TowerOnFinalConf : forall l r d c e x,
    Valid_starting_config c ->
    eeq e (execute r d c) ->
    Biggest_list_of_exe l e ->
    let (P, l') := last_init_conf l c in
    P ->
    Explore_and_Stop r ->
    SequencialExecution e ->
    (forall conf, In conf l' ->
                  exists loc, (snd (!! conf Loc.origin))[loc] = x
                              -> (1 < x)%nat  -> (x < kG)%nat)
      -> (length l' >= n - kG + 1)%nat.
Proof.
intros l r d c e x Hconf Heq_e Hlist.
destruct (last_init_conf l c) as (P, l') eqn : Hlic.
intros HP Hvalid Hsequ Hl_conf.
assert ((length l' < n - kG + 1)%nat
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
  + assert (HeqP : P = fst (P, l')) by intuition.
    assert (l' = snd (P, l')) by intuition.
    rewrite <- Hlic in *; simpl in *.
    rewrite HeqP in HP.
    intuition.
    assert (Valid_starting_config a).
    { revert_one Config.eq. intro Heq. now rewrite <- Heq. }
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
 *)