(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                       *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)


Require Import SetoidList.
Require Import SetoidDec.
Require Import Decidable.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Robots.
Set Implicit Arguments.


Class Information (loc info : Type) `(Setoid loc)  `(@EqDec loc _)
                                    `(Setoid info) `(@EqDec info _) := {
  app : (loc -> loc) -> info -> info;
  app_compat :> Proper ((equiv ==> equiv) ==> equiv ==> equiv) app;
  app_id : (equiv ==> equiv)%signature (app Datatypes.id) Datatypes.id;
  app_compose : forall f g,
    Proper (equiv ==> equiv) f ->
    Proper (equiv ==> equiv) g ->
    (equiv ==> equiv)%signature (app (fun x => f (g x))) (fun x => app f (app g x))
}.
Arguments Information loc info {_} {_} {_} {_}.
Arguments app_compose {_} {_} {_} {_} {_} {_} {_} f g _ _.


(** [unit] is a valid information type that does not contain any information. *)

Local Instance Unit (loc : Type) `(Setoid loc) `(@EqDec loc _) : Information loc unit := {
  app := fun _ _ => tt;
  app_compat := fun _ _ _ _ _ _ => eq_refl;
  app_compose := fun _ _ _ _ _ _ _ => eq_refl }.
Proof.
now intros _ [] _.
Defined.

Definition Ignore (loc T : Type) `{EqDec loc} `{EqDec T} : Information loc T := {|
  app := fun _ x => x;
  app_compat := fun _ _ _ _ _ x => x;
  app_id := fun _ _ x => x;
  app_compose := fun _ _ _ _ _ _ x => x |}.

(** A pair of information can be combined. *)
Require Pactole.Util.FMaps.FMapInterface.
(* Already inside FMapInterface.
Instance pair_setoid A B `(Setoid A) `(Setoid B) : Setoid (A * B). *)

Local Instance pair_Information loc A B
                                `(Setoid loc) `(@EqDec loc _)
                                `(Setoid A)   `(@EqDec A _)   `(@Information loc A _ _ _ _)
                                `(Setoid B)   `(@EqDec B _)   `(@Information loc B _ _ _ _)
 : Information loc (A * B) := {
  app := fun f x => (app f (fst x), app f (snd x)) }.
Proof.
+ intros f g Hfg x y Hxy. unfold app. split; simpl; now apply app_compat, Hxy.
+ intros x y Hxy. split; apply app_id, Hxy.
+ intros ? ? ? ? [] [] []. split; now apply app_compose.
Defined.

(** We can also keep only the target location. *)
Local Instance Location (loc : Type) `{Setoid loc} `{@EqDec loc _} : Information loc loc := {
  app := fun f x => f x }.
Proof.
+ repeat intro. auto.
+ repeat intro. auto.
+ repeat intro. auto.
Defined.

(*
(** Under some condition on the app function, if we can project the location type,
    then we can project any info type. *)
Instance project_location {A B info} `{EqDec B} `(Info : Information A info)
                          (section : A -> B) (retract : B -> A) (Hsection : forall x, section (retract x) == x)
 : Information B info := {
  app := fun f x => app (fun y => retract (f (section y))) x }.
Proof.
+ intros f g Hfg x y Hxy. apply app_compat; trivial; [].
  clear x y Hxy. intros x y Hxy. apply section_compat in Hxy. f_equiv.
Defined.
*)

(** * Configurations *)

(* FIXME: It could simply be separate definitions.  No need to bundle them into a class. *)
(** This class represents the space in which robots evolve.
    It can be anything as long as it is a non-trivial real metric space.

    The framework for robots should be more general as for instance a ring is not a metric space.
    It seems that we only need a decidable type for locations and a notion of distance.  *)

Class Configuration loc info `(Information loc info) `(Names) := {
  configuration := ident -> loc * info;
  configuration_Setoid : Setoid configuration := fun_equiv ident _;
  
  config_neq_equiv : forall config₁ config₂ : configuration,
    ~@equiv _ configuration_Setoid config₁ config₂ <-> exists id, ~equiv (config₁ id) (config₂ id);
  
  map_config := fun (f : loc -> loc) (config : configuration) => ((fun id => app f (config id)) : configuration);
  map_config_compat :
    Proper ((equiv ==> equiv) ==> @equiv _ configuration_Setoid ==> @equiv _ configuration_Setoid) map_config;
  
  Gpos : configuration -> list (loc * info);
  Bpos : configuration -> list (loc * info);
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
    forall config, config_list (map_config f config) == List.map (app f) (config_list config);
  map_config_merge : forall f g, Proper (equiv ==> equiv) f ->
    Proper (equiv ==> equiv) g -> forall config : configuration,
    map_config g (map_config f config) == map_config (fun x => g (f x)) config;
  map_config_id : forall config : configuration, map_config Datatypes.id config == config}.

Existing Instance configuration_Setoid.
Existing Instance map_config_compat.
Existing Instance Gpos_compat.
Existing Instance Bpos_compat.
Existing Instance config_list_compat.

Instance configuration_compat loc info `(Configuration loc info) :
  forall config : configuration, Proper (Logic.eq ==> @equiv (loc * info) _) config.
Proof. repeat intro. now subst. Qed.

Instance Make_Configuration loc info `(Info : Information loc info) `(N : Names) : Configuration Info N := {
  Gpos := fun config => List.map (fun g => config (Good g)) Gnames;
  Bpos := fun config => List.map (fun b => config (Byz b)) Bnames }.
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
* intros f g Hfg ? ? Hconfig id. unfold map. now apply app_compat, Hconfig.
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
* intros f g Hf Hg config id. symmetry. split; simpl; try reflexivity; []. now apply app_compose.
* intros config id. split; simpl; try reflexivity; []. now apply app_id.
Qed.
