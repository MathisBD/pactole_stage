(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain             *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
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
Require Import Pactole.Exploration.Graph.Definitions.
Require Import Pactole.Exploration.Graph.GraphFromZnZ.
Open Scope list_scope.


(** There are kG good robots and no byzantine ones. *)
Parameter kG : nat.

Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.

(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(K).
Export DefsE.

(** Assumptions on the number of robots: it is non zero, less than n and divides n (the size of the ring). *)
Axiom kdn : (n mod kG = 0)%nat.
Axiom k_inf_n : (kG < n)%nat.
Axiom k_sup_1 : (1 < kG)%nat.


(** There is no byzantine robot so we can simplify properties about identifiers and configurations. *)
Lemma no_byz : forall (id : Names.ident) P, (forall g, P (Good g)) -> P id.
Proof.
intros [g | b] P HP.
+ apply HP.
+ destruct b. unfold K.nB in *. omega.
Qed.

Lemma no_byz_eq : forall config1 config2 : Config.t,
  (forall g, Config.eq_RobotConf (config1 (Good g)) (config2 (Good g))) -> Config.eq config1 config2.
Proof. intros config1 config2 Heq id. apply (no_byz id). intro g. apply Heq. Qed.

(** A dummy value used for (inexistant) byzantine robots. *)
Definition dummy_val := {| Config.loc := Loc.origin;
                           Config.info := {| Info.source := Loc.origin; Info.target := Loc.origin |} |}.

(** In order to prove that at least one position is occupied, ee define the list of positions. *)
Definition Vlist := Robots.enum n.

Lemma Vlist_NoDup : NoDupA Ring.Veq Vlist.
Proof. unfold Ring.Veq. rewrite NoDupA_Leibniz. apply enum_NoDup. Qed.

Lemma Vlist_length : length Vlist = n.
Proof. apply enum_length. Qed.

Lemma ConfigExistsEmpty : forall config, ¬ (∀ l, Spect.In l (!! config)).
Proof.
generalize k_inf_n; intros Hkin config Hall.
assert (Hcard : Spect.cardinal (!! config) = kG).
{ unfold Spect.from_config.
  rewrite Spect.cardinal_multiset, Config.list_spec, map_map, map_length.
  unfold Names.ident. rewrite Names.names_length. now unfold K.nG, K.nB. }
assert (Hsize : Spect.size (!! config) < n).
{ generalize (Spect.size_cardinal (!! config)). omega. }
assert (Hle : n <= Spect.size (!! config)).
{ rewrite Spect.size_spec.
  assert (Hspect : forall l : Spect.elt, InA Loc.eq l (Spect.support (!! config))).
  { intro l. specialize (Hall l). now rewrite Spect.support_spec. }
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
         (exists id, forall id', id' <> id /\ step (Stream.hd d) id' (conf id')
                                              = Moving false)) e.

Fixpoint Biggest_list_of_exe (l : list Config.t) (e : execution) : Prop :=
  match l with
  | nil => Stopped e
  | x :: nil => Config.eq x (Stream.hd e) /\ Stopped e
  | x :: y => Config.eq x (Stream.hd e) /\
                if Config.eq_dec (Stream.hd e) (Stream.hd (Stream.tl (Stream.tl e)))
                then False
                else Biggest_list_of_exe y (Stream.tl (Stream.tl e))

  end.
Axiom stop_tl : forall e, Stopped e -> Stopped (Stream.tl e).


Lemma stop_tl_tl : forall e, Stopped e -> eeq e (Stream.tl (Stream.tl e)).
Proof.
  intros.
  destruct H.
Admitted.


Theorem test : forall c r d e,
    ValidStartingConfSolExplorationStop r d ->
    eeq e (execute r d c) -> 
    ValidStartingConf c ->
    ~Stopped e.
Proof.
intros c r d e Hexp Heqe Hvalid Hsto.
destruct (Hexp c Hvalid) as (Hvisit, Hstop).
assert (Hfalse :=  ConfigExistsEmpty c).
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
apply stop_tl_tl.
now rewrite Heqe in *.
destruct Hsto.
apply Hsto.
destruct Hsto.
constructor.
apply Hsto.
Qed.

Lemma finalconf_towerOn : forall r,
  (forall d, ValidStartingConfSolExplorationStop r d) ->
  forall c d e, eeq e (execute r d c) -> 
                Stopped e -> 
                exists loc, (!! c)[loc] > 1.
Proof.
intros r Hr config d e Heq Hstop.
assert (Htest := test (Hr d) Heq). Locate ValidStartingConfSolExplorationStop.
destruct (Classical_Prop.classic (ValidStartingConf config)) as [Hcase | Hcase].
+ now specialize (Htest Hcase).
+ apply Classical_Pred_Type.not_all_not_ex.
  intros Hf. apply Hcase.
  unfold ValidStartingConf.
  intros (ex, Hex).
  now specialize (Hf ex).
Qed.


Fixpoint last_init_conf (l : list Config.t) (a : Config.t) :=
  match l with
  | nil => (False, nil)
  | conf :: l' => if Config.eq_dec a conf
                  then (((List.Forall (fun x => ~ ValidStartingConf x ) l')
                        /\ ValidStartingConf a),l')
                  else last_init_conf l' a
  end.


Theorem TowerOnFinalConf : forall l r d config e x,
    ValidStartingConf config ->
    eeq e (execute r d config) ->
    Biggest_list_of_exe l e ->
    let (P,l') := last_init_conf l config in
    P ->
    ValidStartingConfSolExplorationStop r d ->
    SequencialExecution e ->
    (forall conf, In conf l' ->
                  exists loc, (!! conf)[loc] = x
                              -> 1 < x -> x < kG)
      -> length l' >= n - kG + 1.
Proof.
intros l r d config e x Hconf Heq_e Hlist.
destruct (last_init_conf l config) as (P, l') eqn : Hlic.
intros HP Hvalid Hseq Hl_config.
assert (length l' < n - kG + 1 -> False).
{ intros Hf.
  unfold last_init_conf in Hlic.
  induction l as [| config' l].
  + simpl in *.
    rewrite surjective_pairing in Hlic.
    simpl in *.
    assert (P = fst (P, l')) by intuition.
    rewrite <- Hlic in *.
    simpl in *.
    now rewrite <- H.
  + destruct (Config.eq_dec config config').
    - assert (Heq_P : P = fst (P, l')) by intuition.
      assert (Heq_l : l' = snd (P, l')) by intuition.
      rewrite <- Hlic in *; simpl in *.
      rewrite Heq_P in HP. destruct HP as [Hall Hstart].
      assert (ValidStartingConf config').
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