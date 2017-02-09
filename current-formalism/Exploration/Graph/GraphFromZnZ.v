Require Import Reals.
Require Import Omega.
Require Import Psatz.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.DiscreteGraphFormalism.
Require Import Pactole.Exploration.ZnZ.Definitions.
Require Import Pactole.Exploration.ZnZ.ImpossibilityKDividesN.
Require Import Pactole.GraphEquivalence.

(* On a un espace V/E qui représente un graphe.
   On veux transposer Z/nZ sur un graphe V/E.
   Apres on veux utiliser ConfigA2D pour avoir un graph continu.
   pourquoi V/E <=> Z/nZ?
    - Z/nZ représente un anneau donc un graphe.
    - V c'est tout les entiers entre 0 et n
    - E c'est entre les nombres qui se suivent.


   un anneau avec V et E c'est : 
   [n] noeuds V et pour tout E [(src : V) * (tgt : V)], src = tgt (+/-) 1.
 *)

Set Implicit Arguments.

Module MakeRing : GraphDef 
    with Definition V := Loc.t.

  Inductive direction := Forward | Backward. 
  Definition V := Loc.t.
  Definition E := (Loc.t * direction)%type.
  Definition Veq := Loc.eq.
  Definition tgt (e:E) := match snd e with
                          | Forward => Loc.add (fst e) 1
                          | Backward => Loc.add (fst e) (-1)
                          end.
  Definition src (e:E) := fst e.
  
  Definition Eeq e1 e2 := Veq (src e1) (src e2) /\  snd e1 = snd e2.

  Lemma Veq_equiv : Equivalence Veq. Proof. unfold Veq; apply Loc.eq_equiv. Qed.

  Lemma Eeq_equiv : Equivalence Eeq.
  Proof.
    split.
    + intros e.
      unfold Eeq.
      split; reflexivity.
    + intros e1 e2 (Hes, Het).
      unfold Eeq.
      split; now symmetry.
    + intros e1 e2 e3 (Hs12, Ht12) (Hs23, Ht23). 
      unfold Eeq.
      split. now transitivity (src e2). now transitivity (snd e2).
  Qed.

  Instance tgt_compat : Proper (Eeq ==> Veq) tgt.
  Proof.
    intros e1 e2 He.
    unfold Eeq in He.
    unfold tgt.
    destruct He as (Ht, Hd); unfold src, Loc.add in *.
    rewrite Hd; destruct (snd e2);
    now rewrite Zdiv.Zplus_mod, Ht, <- Zdiv.Zplus_mod.
  Qed.

  Instance src_compat : Proper (Eeq ==> Veq) src.
  Proof.
    intros e1 e2 He.
    now unfold Eeq in He.
  Qed.

  Parameter threshold :E -> R.
  Axiom threshold_pos : forall e, (0 < threshold e < 1)%R.
  Parameter threshold_compat : Proper (Eeq ==> eq) threshold.
  
  Lemma Veq_dec : forall l l' : V, {Veq l l'} + {~Veq l l'}.
  Proof.
    unfold V, Veq; apply Loc.eq_dec.
  Qed.

  Lemma dir_eq_dec : forall d d': direction, {d = d'} + { d <> d'}.
  Proof.
    intros.
    destruct d, d'; intuition; right; discriminate.
  Qed.
    
  Lemma Eeq_dec : forall e e' : E, {Eeq e e'} + {~Eeq e e'}.
  Proof.
    intros.
    unfold Eeq.
    destruct (Veq_dec (src e) (src e')),
    (dir_eq_dec (snd e) (snd e')); intuition.
  Qed.

  Definition find_edge v1 v2 := if Loc.eq_dec v1 (Loc.add v2 1) then
                                  Some (v1, Backward)
                                else
                                  if Loc.eq_dec (Loc.add v1 1) v2 then
                                    Some (v1, Forward)
                                  else
                                    None.

  Lemma find_edge_Some : forall e :E, opt_eq Eeq (find_edge (src e) (tgt e)) (Some e).
  Proof.
    intros.
    unfold find_edge, Eeq, src, tgt, opt_eq, Veq in *.
    destruct (snd e) eqn : Hdir.
    - destruct (Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) 1) 1)).
      + generalize k_sup_1, k_inf_n.
        intros.
        assert (H2n : 2 < n) by omega.
        clear H; clear H0.
        exfalso.
        unfold Loc.eq, Loc.add, def.n in e0.
        rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod in e0.
        set (X := (fst e)%Z) in *; set (N := Z.of_nat n) in *.
        replace (X+1+1)%Z with (X + (1 + 1))%Z in e0 by omega.
        rewrite <- Z.mod_mod in e0 at 1; try (unfold N; omega).
        rewrite <- Zdiv.Zplus_mod_idemp_l in e0.
        generalize Zdiv.Z_mod_lt; intros Hlt;
          specialize (Hlt X N); destruct Hlt as (Hl0, HlN); try (unfold N; omega).
        destruct (Z.compare (X mod N + 2) N) eqn : Heq;
        try rewrite Z.compare_lt_iff in *;
        try rewrite Z.compare_eq_iff in *;
        try rewrite Z.compare_gt_iff in *;
        simpl in *.
        * rewrite Heq in e0.
          rewrite Z.mod_same in e0; try (unfold N; omega).
          replace (X mod N)%Z with (N - 2)%Z in e0 by omega.
          rewrite <- Zdiv.Zminus_mod_idemp_l in e0; try (unfold N; omega).
          rewrite Z.mod_same in e0; try (unfold N; omega).
          simpl in *.
          apply Zdiv.Z_mod_zero_opp_full in e0.
          simpl in e0.
          rewrite Z.mod_small in e0; try (unfold N; omega).
        * rewrite Z.mod_small in e0; try omega.
          rewrite Z.mod_small with (a := (X mod N + 2)%Z) in e0; try omega.
        * assert (X mod N = N - 1)%Z.
          destruct (Z.compare (X mod N + 1)%Z N) eqn : Heq_1;
            try rewrite Z.compare_lt_iff in *;
            try rewrite Z.compare_eq_iff in *;
            try rewrite Z.compare_gt_iff in *; try omega.
          rewrite H in *.
          replace (N - 1 + 2)%Z with (N + 1) %Z in e0 by omega.
          rewrite Z.mod_small, <- Zdiv.Zplus_mod_idemp_l, Z.mod_same in e0;
            try (unfold N; omega).
          simpl in e0.
          rewrite Z.mod_1_l in e0; try (unfold N; omega).
          assert (N = 2)%Z by omega.
          unfold N in *; omega.
        * omega.
      + destruct (Loc.eq_dec (Loc.add (fst e) 1) (Loc.add (fst e) 1)).
        * simpl; now split.
        * destruct n0.
          reflexivity.
    - destruct (Loc.eq_dec (fst e) (Loc.add (Loc.add (fst e) (-1)) 1)).
      + simpl; now split.
      + destruct n.
        unfold Loc.add.
        rewrite Zdiv.Zplus_mod_idemp_l.
        unfold Loc.eq; rewrite Z.mod_mod; try omega.
        replace (fst e + -1 + 1)%Z with (fst e + 1 + -1)%Z by omega. 
        rewrite Z.add_opp_r with (m := 1%Z).
        replace (fst e + 1 - 1)%Z with (fst e + 0)%Z by omega.
        assert (fst e + 0 = fst e)%Z.
        omega.
        rewrite H.
        reflexivity.
        generalize n_sup_1.
        unfold def.n; omega.
  Qed.
  
  Lemma NoAutoLoop : forall e, ~Veq (src e) (tgt e).
  Proof.
    intros e.
    intros Hf.
    unfold src, tgt in Hf.
    destruct (snd e).
    + unfold Veq in *.
      unfold Loc.eq, Loc.add in *.
      unfold def.n in *.
      generalize n_sup_1; intro ns1.
      rewrite Z.mod_mod in *; try omega.
      rewrite <- Zdiv.Zplus_mod_idemp_l in Hf.
      destruct (Z.compare (fst e mod Z.of_nat n + 1)%Z (Z.of_nat n)) eqn : Heq;
        try rewrite Z.compare_lt_iff in *;
        try rewrite Z.compare_eq_iff in *;
        try rewrite Z.compare_gt_iff in *;
        simpl in *; try omega.
      rewrite Heq in Hf; rewrite Z.mod_same in Hf; try omega.
      rewrite Z.mod_small with (a := (fst e mod Z.of_nat n + 1)%Z) in Hf.      
      omega.
      split; try omega.
      generalize Zdiv.Z_mod_lt.
      intros Ho.
      specialize (Ho (fst e) (Z.of_nat n)).
      omega.
      generalize Zdiv.Z_mod_lt.
      intros Ho.
      specialize (Ho (fst e) (Z.of_nat n)).
      assert (Z.of_nat n > 0)%Z.
      omega.
      specialize (Ho H); clear H.
      omega.
    + unfold Veq in Hf; generalize neq_a_a1 ; intros Hn.
      specialize (Hn (fst e)).
      destruct Hn.
      unfold Loc.eq, Loc.add in *.
      rewrite Z.mod_mod in Hf.
      replace (fst e + -1)%Z with (fst e - 1)%Z in Hf by omega.
      assumption.
      unfold def.n; generalize n_sup_1; omega.
  Qed.


  Lemma find_edge_None : forall a b : V,
      find_edge a b = None <-> forall e : E, ~(Veq (src e) a /\ Veq (tgt e) b).
  Proof.
    intros a b; split; unfold find_edge; destruct (Loc.eq_dec a (Loc.add b 1)).
    - intros Hnone.
      discriminate.
    - destruct (Loc.eq_dec (Loc.add a 1) b); try discriminate.
      intros Hnone.
      clear Hnone.
      intros e (Hsrc, Htgt).
      unfold Veq, Loc.eq, Loc.add, src, tgt in *.
      destruct (snd e).
      + rewrite <- Htgt in n0.
        destruct n0.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l with (a := (fst e)).
        rewrite Hsrc.
        rewrite Zdiv.Zplus_mod_idemp_l.
        reflexivity.
      + destruct n.
        unfold Loc.add.
        rewrite <- Zdiv.Zplus_mod_idemp_l.
        rewrite <- Hsrc, <- Htgt.
        unfold Loc.add.
        try repeat rewrite Z.mod_mod, Zdiv.Zplus_mod_idemp_l.
        rewrite Zdiv.Zplus_mod_idemp_l.
        replace (fst e + -1 + 1)%Z with (fst e + 1 + -1)%Z by omega. 
        rewrite Z.add_opp_r with (m := 1%Z).
        replace (fst e + 1 - 1)%Z with (fst e + 0)%Z by omega.
        assert (fst e + 0 = fst e)%Z.
        omega.
        rewrite H.
        reflexivity.
        unfold def.n; generalize n_sup_1; omega.
    - intros He.
      specialize (He (a, Backward)).
      destruct He.
      split; unfold Veq, src, tgt; simpl.
      reflexivity.
      rewrite e.
      unfold Loc.add.
      rewrite Zdiv.Zplus_mod_idemp_l.
      replace (b + -1 + 1)%Z with (b + 1 + -1)%Z by omega. 
      rewrite Z.add_opp_r with (m := 1%Z).
      replace (b + 1 - 1)%Z with (b + 0)%Z by omega.
      assert (b + 0 = b)%Z.
      omega.
      rewrite H.
      unfold Loc.eq; rewrite Z.mod_mod.
      reflexivity.
      unfold def.n; generalize n_sup_1; omega.
    - intros Ho.
      destruct (Loc.eq_dec (Loc.add a 1) b).
      specialize (Ho (a, Forward)).
      destruct Ho.
      split; unfold src, tgt, Veq, Loc.add, Loc.eq in *; try (rewrite e); simpl.
      reflexivity.
      rewrite e.
      reflexivity.
      reflexivity.
  Qed.

  Instance find_edge_compat : Proper (Veq ==> Veq ==> opt_eq (Eeq)) find_edge.
  Proof.
    intros v1 v2 Hv12 v3 v4 Hv34. 
    unfold Eeq, find_edge; simpl.
    destruct (Loc.eq_dec v1 (Loc.add v3 1)),
             (Loc.eq_dec v2 (Loc.add v4 1)).
    simpl.
    now split.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv12, <- Zdiv.Zplus_mod_idemp_l, Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv12, <- Zdiv.Zplus_mod_idemp_l, <- Hv34, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    destruct (Loc.eq_dec (Loc.add v1 1) v3),
    ( Loc.eq_dec (Loc.add v2 1) v4).
    simpl.
    now split.
    unfold Loc.eq, Loc.add in *.
    rewrite Hv34, <- Zdiv.Zplus_mod_idemp_l, Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    unfold Loc.eq, Loc.add in *.
    rewrite <-Hv34, <- Zdiv.Zplus_mod_idemp_l, <- Hv12, Zdiv.Zplus_mod_idemp_l in e.
    contradiction.
    simpl; now split.
  Qed.

  Lemma find2st : forall v1 v2 e, opt_eq Eeq (find_edge v1 v2) (Some e) ->
                                Veq v1 (src e) /\ Veq v2 (tgt e).  
  Proof.
    intros v1 v2 e Hsome.
    unfold find_edge in *.
    destruct (Loc.eq_dec v1 (Loc.add v2 1)).
    simpl in *.
    rewrite <- Hsome.
    unfold src, tgt.
    simpl.
    split; try reflexivity.
    rewrite e0.
    unfold Loc.add, Veq, Loc.eq.
    rewrite Zdiv.Zplus_mod_idemp_l, Z.mod_mod.
    replace (v2 + 1 + -1)%Z with v2 by omega.
    reflexivity.
    unfold def.n; generalize n_sup_1; omega.
    destruct (Loc.eq_dec (Loc.add v1 1) v2).
    simpl in *.
    rewrite <- Hsome; simpl.
    split; try reflexivity.
    rewrite e0.
    reflexivity.
    contradiction.
  Qed.
    
End MakeRing.


Module LocationA := LocationAD (MakeRing).

Module N : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End N.

Module Names := Robots.Make (N).

Module ConfigA := Configurations.Make (LocationA)(N)(Names).

(** For spectra *)
Module View : DecidableType with Definition t := ConfigA.t with Definition eq := ConfigA.eq.
  Definition t := ConfigA.t.
  Definition eq := ConfigA.eq.
  Definition eq_equiv := ConfigA.eq_equiv.
  Definition eq_dec := ConfigA.eq_dec.
End View.



Module AGF.


  (* They come from the common part as they are shared by AGF and DGF. *)
  
Module Location := LocationA.
Module Config := ConfigA.

(* Identity spectrum *)
Module Spect : Spectrum(Location)(N)(Names)(Config) with Definition t := View.t with Definition from_config := (fun x : ConfigA.t => x) with Definition eq := View.eq.
  Definition t := View.t. (* too strong as we identify byzantine robots *)
  Definition eq := View.eq.
  Definition eq_equiv : Equivalence eq := View.eq_equiv.
  Definition eq_dec : forall x y : t, {eq x y} + {~eq x y} := View.eq_dec.
  
  Definition from_config := fun x : ConfigA.t => x.
  Definition from_config_compat : Proper (ConfigA.eq ==> eq) from_config.
  Proof. repeat intro. apply H. Qed.
  Definition is_ok : t -> ConfigA.t -> Prop := eq.
  Definition from_config_spec : forall config, is_ok (from_config config) config.
  Proof. intro. reflexivity. Qed.
End Spect.
  
Record robogram := {
  pgm :> Spect.t -> Location.t;
  pgm_compat : Proper (Spect.eq ==> Location.eq) pgm;
  pgm_range : forall spect l g,
    MakeRing.Veq (ConfigA.loc (spect (Good g))) l ->
    exists l0 e, pgm spect = l0 /\ MakeRing.find_edge l l0 = Some e}.

Global Existing Instance pgm_compat.

Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq)%signature r1 r2.

Instance req_equiv : Equivalence req.
Proof. split.
+ intros [robogram Hrobogram] x y Heq; simpl. rewrite Heq. reflexivity.
+ intros r1 r2 H x y Heq. rewrite <- (H _ _ (reflexivity _)). now apply (pgm_compat r1).
+ intros r1 r2 r3 H1 H2 x y Heq.
  rewrite (H1 _ _ (reflexivity _)), (H2 _ _ (reflexivity _)). now apply (pgm_compat r3).
Qed.

(** ** Executions *)

(** Now we can [execute] some robogram from a given configuration with a [demon] *)
CoInductive execution :=
  NextExecution : Config.t -> execution -> execution.


(** *** Destructors for demons *)

Definition execution_head (e : execution) : Config.t :=
  match e with NextExecution conf _ => conf end.

Definition execution_tail (e : execution) : execution :=
  match e with NextExecution _ e => e end.

CoInductive eeq (e1 e2 : execution) : Prop :=
  | Ceeq : Config.eq (execution_head e1) (execution_head e2) ->
           eeq (execution_tail e1) (execution_tail e2) -> eeq e1 e2.

Instance eeq_equiv : Equivalence eeq.
Proof. split.
+ coinduction eeq_refl. reflexivity.
+ coinduction eeq_sym. symmetry. now inversion H. now inversion H.
+ coinduction eeq_trans. 
  - inversion H. inversion H0. now transitivity (execution_head y).
  - apply (eeq_trans (execution_tail x) (execution_tail y) (execution_tail z)).
    now inversion H. now inversion H0.
Qed.

Instance eeq_bisim : Bisimulation execution.
Proof. exists eeq. apply eeq_equiv. Qed.

Instance execution_head_compat : Proper (eeq ==> Config.eq) execution_head.
Proof. intros e1 e2 He id. subst. inversion He. intuition. Qed.

Instance execution_tail_compat : Proper (eeq ==> eeq) execution_tail.
Proof. intros e1 e2 He. now inversion He. Qed.

(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
Inductive Active_or_Moving := 
  | Moving (dist : bool)                   (* moving ratio *)
  | Active (sim : unit). (* change of referential *)

Definition Aom_eq (a1 a2: Active_or_Moving) :=
  match a1, a2 with
    | Moving d1, Moving d2 => d1 = d2
    | Active sim1, Active sim2 => (Logic.eq)%signature sim1 sim2
    | _, _ => False
  end.


Instance Active_compat : Proper (Logic.eq ==> Aom_eq) Active.
Proof. intros ? ? ?. auto. Qed.

(* as Active give a function, Aom_eq is not reflexive. It's still symmetric and transitive.*)
Instance Aom_eq_Symmetric : Symmetric Aom_eq.
Proof.
intros x y H. unfold Aom_eq in *. destruct x, y; auto.
Qed.

Instance Aom_eq_Transitive : Transitive Aom_eq.
Proof.
intros [] [] [] H12 H23; unfold Aom_eq in *; congruence || easy || auto.
Qed.

Record demonic_action := {
  relocate_byz : Names.B -> Location.t;
  step : Names.ident -> Config.RobotConf -> Active_or_Moving;
  step_delta : forall g Rconfig sim, (step (Good g) Rconfig) = (Active sim) ->
       Location.eq Rconfig.(Config.loc) Rconfig.(Config.robot_info).(Config.target);
  step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step}.
Set Implicit Arguments.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id config, (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
  (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

Instance da_eq_equiv : Equivalence da_eq.
Proof. split.
+ split; intuition. now apply step_compat.
+ intros da1 da2 [Hda1 Hda2]. repeat split; repeat intro; try symmetry; auto.
+ intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
  repeat split; intros; try etransitivity; eauto.
Qed.

Instance step_da_compat : Proper (da_eq ==> eq ==> Config.eq_RobotConf ==> Aom_eq) step.
Proof.
intros da1 da2 [Hd1 Hd2] p1 p2 Hp x y Hxy. subst.
etransitivity.
- apply Hd1.
- apply (step_compat da2); auto.
Qed.

Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Location.eq) relocate_byz.
Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.

Lemma da_eq_step_Moving : forall da1 da2, da_eq da1 da2 -> 
                        forall id config r, step da1 id config = (Moving r) <-> 
                                            step da2 id config = (Moving r).
Proof.
intros da1 da2 Hda id config r.
assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step; reflexivity || elim Hopt_eq; auto.
Qed.

(** A [demon] is just a stream of [demonic_action]s. *)
CoInductive demon :=
  NextDemon : demonic_action -> demon -> demon.

(** Destructors for demons, getting the head demonic action or the
    tail of the demon. *)

Definition demon_head (d : demon) : demonic_action :=
  match d with NextDemon da _ => da end.

Definition demon_tail (d : demon) : demon :=
  match d with NextDemon _ d => d end.

CoInductive deq (d1 d2 : demon) : Prop :=
  | Cdeq : da_eq (demon_head d1) (demon_head d2) ->
           deq (demon_tail d1) (demon_tail d2) -> deq d1 d2.

Instance deq_equiv : Equivalence deq.
Proof. split.
+ coinduction deq_refl. reflexivity.
+ coinduction deq_sym. symmetry. now inversion H. now inversion H.
+ coinduction deq_trans.
  - inversion H. inversion H0. now transitivity (demon_head y).
  - apply (deq_trans (demon_tail x) (demon_tail y) (demon_tail z)).
      now inversion H.
      now inversion H0.
Qed.

Instance demon_head_compat : Proper (deq ==> da_eq) demon_head.
Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.

Instance demon_tail_compat : Proper (deq ==> deq) demon_tail.
Proof. intros [da1 d1] [da2 d2] Heq. destruct Heq. simpl in *. assumption. Qed.

(** [round r da conf] return the new configuration of robots (that is a function
    giving the configuration of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
(* TODO: Should we keep the Moving/Active disctinction?
         We could use :
         1) bool in da, 2 states for robots (Loc / MoveTo)
         2) 3 states in da (Compute, Move, Wait), 2 states for robots *)
Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let conf := config id in
    let pos := conf.(Config.loc) in
    match da.(step) id conf with (** first see whether the robot is activated *)
      | Moving false => conf
      | Moving true => match id with
           | Good g => let tgt := conf.(Config.robot_info).(Config.target) in
                       {| Config.loc := tgt ; Config.robot_info := conf.(Config.robot_info) |}
           | Byz b => conf
           end
      | Active sim => (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
        match id with
        | Byz b => (* byzantine robot are relocated by the demon *)
                   {| Config.loc := da.(relocate_byz) b;
                      Config.robot_info := Config.robot_info (config id) |}
        | Good g => 
          let local_conf := config in
          let target := r (Spect.from_config local_conf) in
           {| Config.loc := pos ; 
              Config.robot_info := {| Config.source := pos ; Config.target := target|} |}
        end
    end.

Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof.
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
unfold req in Hr.
unfold round.
assert (Hrconf : Config.eq_RobotConf (conf1 id) (conf2 id)). 
apply Hconf.
assert (Hstep := step_da_compat Hda (reflexivity id) Hrconf).
assert (Hsim: Aom_eq (step da1 id (conf1 id)) (step da1 id (conf2 id))).
apply step_da_compat; try reflexivity.
apply Hrconf.
destruct (step da1 id (conf1 id)) eqn : He1, (step da2 id (conf2 id)) eqn:He2,
(step da1 id (conf2 id)) eqn:He3, id as [ g| b]; try now elim Hstep.
+ unfold Aom_eq in *.
  rewrite Hstep.
  destruct dist0.
  f_equiv;
  apply Hrconf.
  apply Hrconf.
+ unfold Aom_eq in *.
  split;
  simpl.
  apply Hrconf.
  split; simpl.
  apply Hrconf.
  apply Hr.
  unfold Spect.from_config.
  unfold Spect.eq, View.eq.
  apply Hconf.
Qed.


(** [execute r d conf] returns an (infinite) execution from an initial global
    configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon -> Config.t -> execution :=
  cofix execute d conf :=
  NextExecution conf (execute (demon_tail d) (round r (demon_head d) conf)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (conf : Config.t),
  execution_tail (execute r d conf) = execute r (demon_tail d) (round r (demon_head d) conf).
Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.

Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
Proof.
intros r1 r2 Hr.
cofix proof. constructor. simpl. assumption.
apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
Qed.

End AGF.
