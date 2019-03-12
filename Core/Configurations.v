(**************************************************************************)
(*  Mechanised Framework for Local Interactions & Distributed Algorithms  *)
(*  T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                        *)
(*  PACTOLE project                                                       *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(**************************************************************************)

(** Mechanised Framework for Local Interactions & Distributed Algorithms    
                                                                            
    T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                          
                                                                            
    PACTOLE project                                                         
                                                                            
    This file is distributed under the terms of the CeCILL-C licence      *)


Require Import SetoidList.
Require Import SetoidDec.
Require Import Decidable.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.Bijection.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.RobotInfo.
Set Implicit Arguments.
Typeclasses eauto := (dfs).


(** * Configurations *)

(** A configuration is simply a map fron robot indentifiers to robot states (including their locations). *)
Definition configuration `{State} `{Names} := ident -> info.

Section Configuration.

Context `{State}.
Context `{Names}.

(** Equality of configurations is extensional. *)
Global Instance configuration_Setoid : Setoid configuration := fun_equiv ident _.

Global Instance configuration_compat : forall config : configuration, Proper (Logic.eq ==> equiv) config.
Proof. repeat intro. now subst. Qed.

(** The lists of positions for good, Byzantine, and all robots. *)
Definition Gpos := fun config : configuration => List.map (fun g => config (Good g)) Gnames.
Definition Bpos := fun config : configuration => List.map (fun b => config (Byz b)) Bnames.
Definition config_list := fun config => Gpos config ++ Bpos config.

Lemma Gpos_spec : forall config, Gpos config = List.map (fun g => config (Good g)) Gnames.
Proof. reflexivity. Qed.

Lemma Bpos_spec : forall config, Bpos config = List.map (fun g => config (Byz g)) Bnames.
Proof. reflexivity. Qed.

Lemma config_list_spec : forall config, config_list config = List.map config names.
Proof. intros. unfold config_list, names. rewrite map_app. now do 2 rewrite map_map. Qed.

(** Compatilities with equivalences. *)
Global Instance Gpos_compat : Proper (@equiv _ configuration_Setoid ==> eqlistA equiv) Gpos.
Proof.
intros f g Hfg. eapply map_extensionalityA_compat; reflexivity || autoclass; [].
intros x y Hxy. cbn in Hxy. subst. apply Hfg.
Qed.

Global Instance Bpos_compat : Proper (@equiv _ configuration_Setoid ==> eqlistA equiv) Bpos.
Proof.
intros f g Hfg. eapply map_extensionalityA_compat; reflexivity || autoclass; [].
intros x y Hxy. cbn in Hxy. subst. apply Hfg.
Qed.

Global Instance config_list_compat : Proper (@equiv _ configuration_Setoid ==> eqlistA equiv) config_list.
Proof.
intros f g Hfg. rewrite 2 config_list_spec. f_equiv.
intros x y Hxy. cbn in Hxy. subst. apply Hfg.
Qed.

(** Properties w.r.t. [InA] and [length]. *)
Lemma Gpos_InA : forall l config, InA equiv l (Gpos config) <-> exists g, equiv l (config (Good g)).
Proof.
intros. rewrite Gpos_spec, InA_map_iff; autoclass; [|].
+ split; intros [g Hg]; exists g.
  - now symmetry.
  - split; try (now symmetry); []. rewrite InA_Leibniz. apply In_Gnames.
+ repeat intro. cbn in *. now subst.
Qed.

Lemma Bpos_InA : forall l config, InA equiv l (Bpos config) <-> exists b, equiv l (config (Byz b)).
Proof.
intros. rewrite Bpos_spec, InA_map_iff; autoclass; [|].
+ split; intros [b Hb]; exists b.
  - now symmetry.
  - split; try (now symmetry); []. rewrite InA_Leibniz. apply In_Bnames.
+ repeat intro. cbn in *. now subst.
Qed.

Lemma config_list_InA : forall l config, InA equiv l (config_list config) <-> exists id, equiv l (config id).
Proof.
intros l config. rewrite config_list_spec. unfold names. rewrite map_app, (InA_app_iff _).
repeat rewrite InA_map_iff; autoclass || (try now cbn; repeat intro; subst); [].
split; intro Hin.
+ destruct Hin as [[g [Hin _]] | [b [Hin  _]]]; symmetry in Hin; eauto.
+ setoid_rewrite InA_Leibniz. destruct Hin as [[g | b] Hin]; symmetry in Hin.
  - left. exists (Good g). auto using in_map, In_Gnames.
  - right. exists (Byz b). auto using in_map, In_Bnames.
Qed.

Lemma Gpos_length : forall config, length (Gpos config) = nG.
Proof. intro. rewrite Gpos_spec, map_length. apply Gnames_length. Qed.

Lemma Bpos_length : forall config, length (Bpos config) = nB.
Proof. intro. rewrite Bpos_spec, map_length. apply Bnames_length. Qed.

Lemma config_list_length : forall config, length (config_list config) = nG + nB.
Proof. intro. now rewrite config_list_spec, map_length, names_length. Qed.

(** As the number of robots is finite, extensional equality of configurations is decidable. *)
Global Instance configuration_EqDec : @EqDec configuration _.
Proof.
intros config₁ config₂.
destruct (eqlistA_dec equiv_dec (config_list config₁) (config_list config₂)) as [Heq | Heq];
rewrite 2 config_list_spec in Heq.
+ left. intro x. apply (fun_names_eq _ _ Heq).
+ right. intro Habs. apply Heq. f_equiv. intros ? ? Hpt. hnf in Hpt. subst. apply Habs.
Qed.

(** If two configurations are not equal, then there exists a robot
    that is not located in the same place in both. *)
Theorem config_neq_equiv : forall config₁ config₂ : configuration,
  config₁ =/= config₂ <-> exists id, ~config₁ id == config₂ id.
Proof.
intros config₁ config₂. split; intro Hneq.
+ assert (Hlist : ~eqlistA equiv (List.map config₁ names) (List.map config₂ names)).
  { intro Habs. apply Hneq. hnf. cbn. intro id.
    assert (Hin : List.In id names) by now apply In_names.
    induction names as [| id' l].
    - inversion Hin.
    - inversion_clear Habs. inversion_clear Hin; solve [now subst | now apply IHl]. }
  induction names as [| id l].
  - now elim Hlist.
  - cbn in Hlist. destruct (equiv_dec (config₁ id) (config₂ id)) as [Hid | Hid].
    -- apply IHl. intro Heq. apply Hlist. now constructor.
    -- eauto.
+ destruct Hneq as [id Hneq]. intro Habs. apply Hneq, Habs.
Qed.

End Configuration.

(** Applying a function on all states of a configuration. *)

Section MapConfig.

Context `{Location}.
Context {info1 info2 : Type}.
Context {St1 : @State _ info1}.
Context {St2 : @State _ info2}.
Context `{Names}.

Definition map_config (f : info1 -> info2) (config : @configuration _ _ St1 _) : configuration :=
  fun id => f (config id).

Global Instance map_config_compat :
    Proper ((equiv ==> equiv) ==> @equiv _ configuration_Setoid ==> @equiv _ configuration_Setoid) map_config.
Proof. intros f g Hfg ? ? Hconfig id. unfold map. apply Hfg, Hconfig. Qed.

Lemma config_list_map : forall f, Proper (equiv ==> equiv) f ->
  forall config, config_list (map_config f config) == List.map f (config_list config).
Proof. intros. now rewrite 2 config_list_spec, map_map. Qed.

End MapConfig.

Arguments map_config {_} {info1} {info2} {_} {_} {_} f config /.

Lemma map_config_id `{State} `{Names} : forall config,
  map_config Datatypes.id config == config.
Proof. now repeat intro. Qed.

Lemma map_config_merge `{Location} {T U V : Type} `{@State _ T} `{@State _ U} `{@State _ V} `{Names} :
  forall (f : T -> U) (g : U -> V), Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) g ->
  forall config : configuration, map_config g (map_config f config) == map_config (fun x => g (f x)) config.
Proof. now repeat intro. Qed.

(** Injective configurations *)
Definition config_injective `{State} `{Names} :=
  Util.Preliminary.injective (@eq ident) (@equiv _ state_Setoid).

Lemma config_injective_equiv_NoDupA `{State} `{Names} : forall config : configuration,
  config_injective config <-> NoDupA equiv (config_list config).
Proof.
intros config. rewrite config_list_spec. split; intro Hinj.
+ eapply map_injective_NoDupA; try apply Hinj; autoclass; [].
  rewrite NoDupA_Leibniz. apply names_NoDup.
+ intros id id' Hconfig.
  eapply (map_NoDupA_eq _ _ names_eq_dec _ Hinj); auto; rewrite InA_Leibniz; apply In_names.
Qed.

Lemma config_injective_dec `{State} `{Names} : forall config : configuration,
  {config_injective config} + {~ config_injective config}.
Proof.
intros config.
destruct (NoDupA_dec equiv equiv_dec (config_list config));
rewrite <- (config_injective_equiv_NoDupA config) in *; tauto.
Qed.

Lemma config_not_injective `{State} `{Names} : forall config : configuration,
  ~ config_injective config <-> exists id id', id <> id' /\ config id == config id'.
Proof.
intros config. split; intro Hinj. 
+ rewrite config_injective_equiv_NoDupA, not_NoDupA in Hinj; autoclass; try apply state_EqDec; [].
  destruct Hinj as [state [l Hperm]].
  assert (Hid : exists id, state == config id).
  { rewrite <- config_list_InA, Hperm. now left. }
  destruct Hid as [id Hid]. exists id.
  rewrite config_list_spec in Hperm.
  assert (Hin : In id names) by apply In_names.
  rewrite <- InA_Leibniz in Hin.
  apply PermutationA_split in Hin; autoclass; [].
  destruct Hin as [l' Hnames].
  assert (Hl' := Hnames). apply (PermutationA_map _ (f := config)) in Hl'; autoclass; [].
  rewrite Hl' in Hperm. simpl in Hperm. rewrite <- Hid in Hperm.
  apply PermutationA_cons_inv in Hperm; autoclass; [].
  assert (Hid' : InA equiv state (state :: l)) by now left.
  rewrite <- Hperm in Hid'.
  destruct (PermutationA_split _ Hid') as [l'' Hl''].
  rewrite (InA_map_iff (eqA := eq)) in Hid'; autoclass; [].
  destruct Hid' as [id' [Heq Hid']].
  exists id'. rewrite Heq, <- Hid. split; try reflexivity; [].
  intro Habs.
  assert (Hnodup := names_NoDup).
  rewrite <- NoDupA_Leibniz, Hnames in Hnodup. inversion_clear Hnodup. subst. tauto.
+ destruct Hinj as [id [id' [Hid Heq]]]. intro Habs. apply Habs in Heq. contradiction.
Qed.
