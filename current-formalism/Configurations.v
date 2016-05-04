(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Robots.


(** * Configurations *)

Class Configuration (loc : Type) {S : Setoid loc} (Loc : @EqDec loc S) `(N : Names) := {
  configuration := ident -> loc;
  configuration_Setoid : Setoid configuration := fun_equiv ident S;
  
  config_neq_equiv : forall config₁ config₂ : configuration,
    ~@equiv _ configuration_Setoid config₁ config₂ <-> exists id, ~equiv (config₁ id) (config₂ id);
  
  map_config := fun (f : loc -> loc) (config : configuration) => ((fun id => f (config id)) : configuration);
  map_config_compat :
    Proper ((equiv ==> equiv) ==> @equiv _ configuration_Setoid ==> @equiv _ configuration_Setoid) map_config;
  
  Gpos : configuration -> list loc;
  Bpos : configuration -> list loc;
  config_list := fun config => Gpos config ++ Bpos config;
  Gpos_compat : Proper (@equiv _ configuration_Setoid ==> eqlistA equiv) Gpos;
  Bpos_compat : Proper (@equiv _ configuration_Setoid ==> eqlistA equiv) Bpos;
  config_list_compat : Proper (@equiv _ configuration_Setoid ==> eqlistA equiv) config_list;
  
  Gpos_spec : forall config, Gpos config = List.map (fun g => config (Good g)) Gnames;
  Bpos_spec : forall config, Bpos config = List.map (fun g => config (Byz g)) Bnames;
  config_list_spec : forall config, config_list config = List.map config names;

  Gpos_InA : forall l config, InA equiv l (Gpos config) <-> exists g, equiv l (config (Good g));
  Bpos_InA : forall l config, InA equiv l (Bpos config) <-> exists b, equiv l (config (Byz b));
  config_list_InA : forall l config, InA equiv l (config_list config) <-> exists id, equiv l (config id);
  
  Gpos_length : forall config, length (Gpos config) = nG;
  Bpos_length : forall config, length (Bpos config) = nB;
  config_list_length : forall config, length (config_list config) = nG + nB;
  
  config_list_map : forall f, Proper (equiv ==> equiv) f ->
    forall config, config_list (map_config f config) == List.map f (config_list config);
  map_merge : forall f g, Proper (equiv ==> equiv) f ->
    Proper (equiv ==> equiv) g -> forall config : configuration,
    @equiv _ configuration_Setoid (map_config g (map_config f config)) (map_config (fun x => g (f x)) config);
  map_id : forall config : configuration, @equiv _ configuration_Setoid (map_config Datatypes.id config) config}.

Existing Instance configuration_Setoid.
Instance configuration_compat loc `(Configuration loc) :
  forall config : configuration, Proper (Logic.eq ==> equiv) config.
Proof. repeat intro. now subst. Qed.

Global Instance Make_Configuration loc `(ES : EqDec loc) `(Names) : Configuration loc ES _ := {|
  Gpos := fun config => List.map (fun g : G => config (Good g)) Gnames;
  Bpos := fun config => List.map (fun b => config (Byz b)) Bnames |}.
Proof.
* intros config₁ config₂. split; intro Hneq.
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
* intros f g Hfg ? ? Hconfig id. unfold map. apply Hfg, Hconfig.
* intros f g Hfg. eapply map_extensionalityA_compat; reflexivity || autoclass; [].
  intros x y Hxy. cbn in Hxy. subst. apply Hfg.
* intros f g Hfg. eapply map_extensionalityA_compat; reflexivity || autoclass; [].
  intros x y Hxy. cbn in Hxy. subst. apply Hfg.
* intros f g Hfg. f_equiv;
  (eapply map_extensionalityA_compat; reflexivity || autoclass; []; intros x y Hxy; cbn in Hxy; subst; apply Hfg).
* reflexivity.
* reflexivity.
* intros. unfold config_list, names. rewrite map_app. now do 2 rewrite map_map.
* intros. rewrite InA_map_iff; autoclass; [|].
  + split; intros [g Hg]; exists g.
    - now symmetry.
    - split; try (now symmetry); []. rewrite InA_Leibniz. apply In_Gnames.
  + repeat intro. cbn in *. now subst.
* intros. rewrite InA_map_iff; autoclass; [|].
  + split; intros [b Hb]; exists b.
    - now symmetry.
    - split; try (now symmetry); []. rewrite InA_Leibniz. apply In_Bnames.
  + repeat intro. cbn in *. now subst.
* intros l config. rewrite (InA_app_iff _).
  repeat rewrite InA_map_iff; autoclass || (try now cbn; repeat intro; subst); [].
  split; intro Hin.
  + destruct Hin as [[g [Hin _]] | [b [Hin  _]]]; symmetry in Hin; eauto.
  + setoid_rewrite InA_Leibniz. destruct Hin as [[g | b] Hin]; symmetry in Hin.
    - left. exists g. auto using In_Gnames.
    - right. exists b. auto using In_Bnames.
* intro. rewrite map_length. apply Gnames_length.
* intro. rewrite map_length. apply Bnames_length.
* intro. now rewrite app_length, map_length, map_length, Gnames_length, Bnames_length.
* intros f Hf conf. now rewrite map_app, map_map, map_map.
* reflexivity.
* reflexivity.
Qed.
