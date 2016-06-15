Require Import Reals.
Require Import Psatz.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.CommonFormalism.
Require Import Pactole.CommonGraphFormalism.


Inductive location :=
  | Loc (l : V)
  | Mvt (e : E) (p : R) (Hp : (0 < p < 1)%R).

Definition loc_eq l l' :=
  match l, l' with
    | Loc l, Loc l' => Veq l l'
    | Mvt e p _, Mvt e' p' _ => Eeq e e' /\ p = p'
    | _, _ => False
  end.

Axiom e_default : E.

Module Location : DecidableType with Definition t := location.
  Definition t := location.
  Definition eq := loc_eq.
  
  Lemma eq_equiv : Equivalence eq.
  Proof.
  split.
  + intros x. unfold eq, loc_eq. destruct x. reflexivity. split; reflexivity.
  + intros x y Hxy. unfold eq, loc_eq in *. destruct x, y;
    try auto. now symmetry. split; now symmetry.
  + intros x y z Hxy Hyz. destruct x, y, z; unfold eq, loc_eq in *; try auto.
    now transitivity l0. exfalso; auto. exfalso; auto. 
    split. now transitivity e0. now transitivity p0.
  Qed.
  
  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof.
  intros l l'.
  destruct l, l'; unfold eq, loc_eq; auto. apply Veq_dec. destruct (Eeq_dec e e0), (Rdec p p0);
  intuition.
  Qed.
End Location.

(* (* Identity spectrum *)
Module IdentitySpectrum(Location : DecidableType)(N : Size) : Spectrum(Location)(N).
  Module Names := Robots.Make(N).
  Module Config := Configurations.Make(Location)(N)(Names).
  
  Definition t := Config.t. (* too strong as we identify byzantine robots *)
  Definition eq := Config.eq.
  Definition eq_equiv : Equivalence eq := Config.eq_equiv.
  Definition eq_dec : forall x y : t, {eq x y} + {~eq x y} := Config.eq_dec.
  
  Definition from_config := fun x : Config.t => x.
  Definition from_config_compat : Proper (Config.eq ==> eq) from_config.
  Proof.
  Admitted.
  Definition is_ok : t -> Config.t -> Prop := eq.
  Definition from_config_spec : forall config, is_ok (from_config config) config.
  Proof. intro. reflexivity. Qed.
End IdentitySpectrum.
 *)

(* Record graph_iso :=  *)

Module Make (N : Size)(Names : Robots(N))(Spect : Spectrum(Location)(N))
            (Common : CommonFormalism.Sig(Location)(N)(Spect)).
(* Module Spect := IdentitySpectrum(Location)(N). *)
Import Common.

(** ** Demonic schedulers *)

(** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
Inductive Active_or_Moving := 
  | Moving (dist :R)                   (* moving ratio *)
  | Active (sim : unit). (* change of referential *)

Definition Aom_eq (a1 a2: Active_or_Moving) :=
  match a1, a2 with
    | Moving d1, Moving d2 => d1 = d2
    | Active sim1, Active sim2 => (Logic.eq)%signature sim1 sim2
    | _, _ => False
  end.


Instance Active_compat : Proper (Logic.eq ==> Aom_eq) Active.
Proof. intros ? ? ?. auto. Qed.

Instance Aom_eq_reflexive : Reflexive Aom_eq.
Proof. intros x. unfold Aom_eq. now destruct x. Qed.

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
  step_delta : forall id Rconfig sim, step id Rconfig = Active sim ->
       (exists l, Location.eq Rconfig.(Config.loc) (Loc l));
  step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step;
  step_flexibility : forall id config r, step id config = Moving r -> (0 <= r <= 1)%R}.
Set Implicit Arguments.

Definition da_eq (da1 da2 : demonic_action) :=
  (forall id config, (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
  (forall b : Names.B, Location.eq (da1.(relocate_byz) b) (da2.(relocate_byz) b)).

Instance da_eq_equiv : Equivalence da_eq.
Proof. split.
+ split; intuition. (* now apply step_compat. *)
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
Definition project (config : Config.t) : Config.t :=
  fun id =>
    match Config.loc (config id) with
      | Loc l => config id
      | Mvt e p Hp => {| Config.loc := Loc (if Rle_dec p (threshold e) then src e else tgt e);
                         Config.robot_info := Config.robot_info (config id) |}
    end.

Program Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
  (** for a given robot, we compute the new configuration *)
  fun id =>
    let conf := config id in
    let pos := conf.(Config.loc) in
    match da.(step) id conf with (** first see whether the robot is activated *)
      | Moving mv_ratio =>
        match id, pos with
          | Good g, Mvt e p Hp => if Rle_dec 1%R (p + mv_ratio)
              then {| Config.loc := Loc (tgt e); Config.robot_info := Config.robot_info conf |}
              else {| Config.loc := Mvt e (p + mv_ratio) _ ; Config.robot_info := Config.robot_info conf |}
          | Good g, Loc l =>
              if Rdec mv_ratio 0%R then conf else
              if Rdec mv_ratio 1%R then {| Config.loc := Config.target (Config.robot_info conf);
                                           Config.robot_info := Config.robot_info conf |} else
              let new_pos := match Config.target (Config.robot_info conf) with
                               | Loc l => l
                               | Mvt e _ _ => src e
                             end in
              if Veq_dec l new_pos then conf
              else 
              let e := match find_edge l new_pos with
                         | Some e => e
                         | None => e_default
                       end in
                       {| Config.loc := Mvt e mv_ratio _; Config.robot_info := Config.robot_info conf |}
          | Byz b, _ => conf
        end
      | Active sim => (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
        match id with
        | Byz b => (* byzantine robot are relocated by the demon *)
                   {| Config.loc := da.(relocate_byz) b;
                      Config.robot_info := Config.robot_info (config id) |}
        | Good g => 
          let local_conf := project config in
          let target := r (Spect.from_config local_conf) in
           {| Config.loc := pos ; 
              Config.robot_info := {| Config.source := pos ; Config.target := target|} |}
        end
    end.
Next Obligation.
assert (Hs: step da (Good g) (config (Good g)) = Moving mv_ratio). 
auto. apply step_flexibility in Hs.
lra.
Qed.
Next Obligation.
symmetry in Heq_anonymous. apply step_flexibility in Heq_anonymous.
lra.
Qed.

Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
Proof. (* Admitted. *)
intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf. intros id.
unfold req in Hr.
assert (Hrconf : Config.eq_RobotConf (conf1 id) (conf2 id)) by apply Hconf.
assert (Hstep := step_da_compat Hda (reflexivity id) Hrconf).
assert (Hsim: Aom_eq (step da1 id (conf1 id)) (step da1 id (conf2 id))).
{ apply step_da_compat; try reflexivity. apply Hrconf. }
destruct id as [g | b].
unfold round. 

+ simpl in Hstep. intuition. rewrite He1 in step.
  rewrite Hstep.
  f_equiv.
  f_equiv.
  apply Hrconf.
  do 2 f_equiv.
  apply Hrconf.
  f_equiv; apply Hrconf.
  unfold Config.Info_eq.
  split; apply Hrconf.
+ unfold Aom_eq in *. exfalso; auto.
+ unfold Aom_eq in *. exfalso; auto.
+ f_equiv; try (now apply Hconf); [].
  split; cbn; try (now apply Hconf); [].
  simpl in Hstep. f_equiv.
  - f_equiv. apply Hstep, Hrconf.
  - apply Hr. do 3 f_equiv; trivial; []. apply Hstep, Hconf.
+ rewrite Hda. destruct (Hconf (Byz b)) as [? Heq]. now rewrite Heq.
Qed. *)

(* Lemma compat_helper1 : Aom_eq (da.(step) id conf) (Moving mv_r) ->  *)

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

End Make.
