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
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Util.Bijection.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.RobotInfo.
Set Implicit Arguments.


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
Proof. intros f g Hfg. rewrite 2 config_list_spec. f_equiv. intros x y Hxy. cbn in Hxy. subst. apply Hfg. Qed.

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
destruct (eqlistA_dec _ equiv_dec (config_list config₁) (config_list config₂)) as [Heq | Heq];
rewrite 2 config_list_spec in Heq.
+ left. intro x. apply (fun_names_eq _ _ Heq).
+ right. intro Habs. apply Heq. f_equiv. intros ? ? Hpt. hnf in Hpt. subst. apply Habs.
Qed.

(** If two configurations are not equal, then there exists a robot that is not located in the same place in both. *)
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

(** Applying a function on all states of a configuration. *)
Definition map_config (f : info -> info) (config : configuration) : configuration := fun id => f (config id).

Global Instance map_config_compat :
    Proper ((equiv ==> equiv) ==> @equiv _ configuration_Setoid ==> @equiv _ configuration_Setoid) map_config.
Proof. intros f g Hfg ? ? Hconfig id. unfold map. apply Hfg, Hconfig. Qed.

Lemma config_list_map : forall f, Proper (equiv ==> equiv) f ->
  forall config, config_list (map_config f config) == List.map f (config_list config).
Proof. intros. now rewrite 2 config_list_spec, map_map. Qed.

Lemma map_config_merge : forall f g, Proper (equiv ==> equiv) f ->
  Proper (equiv ==> equiv) g -> forall config : configuration,
  map_config g (map_config f config) == map_config (fun x => g (f x)) config.
Proof. now repeat intro. Qed.

Lemma map_config_id : forall config, map_config Datatypes.id config == config.
Proof. now repeat intro. Qed.

End Configuration.

Arguments map_config {info} {_} {_} {_} f config /.
