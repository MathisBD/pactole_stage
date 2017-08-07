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


Class Information (loc : Type) `(Setoid loc) `(@EqDec loc _)
                  (info : Type) `(Setoid info) `(@EqDec info _) := {
  app : (loc -> loc) -> info -> info;
  app_compat :> Proper ((equiv ==> equiv) ==> equiv ==> equiv) app;
  app_id : (equiv ==> equiv)%signature (app Datatypes.id) Datatypes.id;
  app_compose : forall f g,
    Proper (equiv ==> equiv) f ->
    Proper (equiv ==> equiv) g ->
    (equiv ==> equiv)%signature (app (fun x => f (g x))) (fun x => app f (app g x))
}.
Arguments Information loc _ _ info _ _ : clear implicits.
Arguments app_compose {_} {_} {_} {_} {_} {_} {_} f g _ _.


(** [unit] is a valid information type that does not contain any information. *)
Local Instance Unit (loc : Type) `(Setoid loc) `(@EqDec loc _) : Information loc _ _ unit _ _ := {
  app := fun _ _ => tt;
  app_compat := fun _ _ _ _ _ _ => eq_refl;
  app_compose := fun _ _ _ _ _ _ _ => eq_refl }.
Proof.
now intros _ [] _.
Defined.

(** A pair of information can be combined. *)
Require FMapInterface.
(* Already inside FMapInterface.
Instance pair_setoid A B `(Setoid A) `(Setoid B) : Setoid (A * B) := {
  equiv := fun x y => fst x == fst y /\ snd x == snd y }.
Proof. split.
+ intros []. split; reflexivity.
+ intros ? ? []. now split; symmetry.
+ intros ? ? ? [] []. split; etransitivity; eauto.
Defined.

Instance fst_compat A B `(Setoid A) `(Setoid B) : Proper (equiv ==> equiv) (@fst A B).
Proof. now intros [] [] []. Qed.

Instance snd_compat A B `(Setoid A) `(Setoid B) : Proper (equiv ==> equiv) (@snd A B).
Proof. now intros [] [] []. Qed.

Instance pair_EqDec A B `(Setoid A) (equiv_decA : @EqDec A _) `(Setoid B) (equiv_decB : @EqDec B _)
  : @EqDec (A * B) _.
Proof.
intros [x1 x2] [y1 y2].
destruct (equiv_decA x1 y1); [destruct (equiv_decB x2 y2) |].
+ now left.
+ right. now intros [_ ?].
+ right. now intros [? _].
Qed.
*)
Local Instance pair_Information loc `(Setoid loc) `(@EqDec loc _)
                                A   `(Setoid A)   `(@EqDec A _)   `(@Information loc _ _ A _ _)
                                B   `(Setoid B)   `(@EqDec B _)   `(@Information loc _ _ B _ _)
 : Information loc _ _ (A * B) _ _ := {
  app := fun f x => (app f (fst x), app f (snd x)) }.
Proof.
+ intros f g Hfg x y Hxy. unfold app. split; simpl; now apply app_compat, Hxy.
+ intros x y Hxy. split; apply app_id, Hxy.
+ intros ? ? ? ? [] [] []. split; now apply app_compose.
Defined.

(** We can also keep only the target location. *)
Local Instance Target (loc : Type) `(Setoid loc) `(@EqDec loc _) : Information loc _ _ loc _ _  := {
  app := fun f x => f x }.
Proof.
+ repeat intro. auto.
+ repeat intro. auto.
+ repeat intro. auto.
Defined.

(** * Configurations *)

(* FIXME: It should simply be separate definitions.  No need to bundle them into a class. *)
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


(* 
Module Type Configuration (Location : DecidableType)
                          (N : Size)
                          (Names : Robots(N))
                          (Info : DecidableTypeWithApplication(Location)).

  Record RobotConf := { loc :> Location.t; info: Info.t }.

  Definition t := Names.ident -> RobotConf.

  Definition eq_RobotConf g1 g2 := Location.eq (loc g1) (loc g2)
                                /\ Info.eq (info g1) (info g2).

  Definition app f rc := {| loc := f (loc rc); info := Info.app f (info rc) |}.
  Declare Instance app_compat : Proper ((Location.eq ==> Location.eq) ==> eq_RobotConf ==> eq_RobotConf) app.
  Axiom app_id : (eq_RobotConf ==> eq_RobotConf)%signature (app Datatypes.id) Datatypes.id.
  Axiom app_compose : forall f g, Proper (Location.eq ==> Location.eq) f -> Proper (Location.eq ==> Location.eq) g ->
     (eq_RobotConf ==> eq_RobotConf)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
  Axiom loc_app : forall f, Proper (Location.eq ==> Location.eq) f ->
    (eq_RobotConf ==> Location.eq)%signature (fun x => loc (app f x)) (fun x => f (loc x)).

  Definition eq (config₁ config₂ : t) := forall id, eq_RobotConf (config₁ id) (config₂ id).

  Declare Instance eq_equiv : Equivalence eq.
  Declare Instance eq_RobotConf_equiv : Equivalence eq_RobotConf.
  Parameter eq_RobotConf_dec : forall rc1 rc2, {eq_RobotConf rc1 rc2} + {~ eq_RobotConf rc1 rc2}.
  Parameter eq_dec : forall c1 c2, {eq c1 c2} + {~eq c1 c2}.
  Declare Instance eq_info_equiv : Equivalence Info.eq.
  Declare Instance eq_subrelation : subrelation eq (Logic.eq ==> eq_RobotConf)%signature.
  Declare Instance Build_RobotConf_compat : Proper (Location.eq ==> Info.eq ==> eq_RobotConf) Build_RobotConf.
  Declare Instance loc_compat : Proper (eq_RobotConf ==> Location.eq) loc.
  Declare Instance info_compat : Proper (eq_RobotConf ==> Info.eq) info.

  Parameter neq_equiv : forall config₁ config₂,
    ~eq config₁ config₂ <-> exists id, ~eq_RobotConf (config₁ id) (config₂ id).


  Definition map (f : RobotConf -> RobotConf) (config : t) : t := fun id => f (config id).
  Declare Instance map_compat : Proper ((eq_RobotConf ==> eq_RobotConf) ==> eq ==> eq) map.

  Parameter Gpos : t -> list RobotConf.
  Parameter Bpos : t -> list RobotConf.
  Parameter list : t -> list RobotConf.
  Declare Instance Gpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Gpos.
  Declare Instance Bpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Bpos.
  Declare Instance list_compat : Proper (eq ==> eqlistA eq_RobotConf) list.

  Parameter Gpos_spec : forall config, Gpos config = List.map (fun g => config (Good g)) Names.Gnames.
  Parameter Bpos_spec : forall config, Bpos config = List.map (fun g => config (Byz g)) Names.Bnames.
  Parameter list_spec : forall config, list config = List.map config Names.names.

  Parameter Gpos_InA : forall l config,
    InA eq_RobotConf l (Gpos config) <-> exists g, eq_RobotConf l (config (Good g)).
  Parameter Bpos_InA : forall l config,
    InA eq_RobotConf l (Bpos config) <-> exists b, eq_RobotConf l (config (Byz b)).
  Parameter list_InA : forall l config,
    InA eq_RobotConf l (list config) <-> exists id, eq_RobotConf l (config id).

  Parameter Gpos_length : forall config, length (Gpos config) = N.nG.
  Parameter Bpos_length : forall config, length (Bpos config) = N.nB.
  Parameter list_length : forall config, length (list config) = N.nG + N.nB.

  Parameter list_map : forall f, Proper (eq_RobotConf ==> eq_RobotConf) f -> 
    forall config, list (map f config) = List.map f (list config).
  Parameter map_merge : forall f g, Proper (eq_RobotConf ==> eq_RobotConf) f ->
    Proper (eq_RobotConf ==> eq_RobotConf) g ->
    forall config, eq (map g (map f config)) (map (fun x => g (f x)) config).
  Parameter map_id : forall config, eq (map Datatypes.id config) config.
End Configuration.


Module Make (Location : DecidableType)
            (N : Size)
            (Names : Robots(N))
            (Info : DecidableTypeWithApplication(Location))
  : Configuration(Location)(N)(Names)(Info).

Record RobotConf := { loc :> Location.t; info: Info.t }.

Definition eq_RobotConf g1 g2 := Location.eq (loc g1) (loc g2)
                                 /\ Info.eq (info g1) (info g2).

Instance eq_info_equiv :  Equivalence Info.eq := Info.eq_equiv. 

Instance eq_RobotConf_equiv : Equivalence eq_RobotConf.
Proof.
split.
+ split; reflexivity.
+ split; symmetry; apply H.
+ split. unfold eq_RobotConf in *.
  transitivity (loc y).
  apply H.
  apply H0.
  transitivity (info y).
  apply H.
  apply H0.
Qed.

Lemma eq_RobotConf_dec : forall rc1 rc2, {eq_RobotConf rc1 rc2} + {~ eq_RobotConf rc1 rc2 }.
Proof.
intros rc1 rc2.
unfold eq_RobotConf.
destruct (Location.eq_dec rc1 rc2),
         (Info.eq_dec (info rc1) (info rc2));
intuition.
Qed.

Set Printing Implicit.

Instance Build_RobotConf_compat : Proper (Location.eq ==> Info.eq ==> eq_RobotConf) Build_RobotConf.
Proof. intros l1 l2 Hl info1 info2 Hinfo. split; apply Hl || apply Hinfo. Qed.

Instance loc_compat : Proper (eq_RobotConf ==> Location.eq) loc.
Proof. now intros ? ? []. Qed.

Instance info_compat : Proper (eq_RobotConf ==> Info.eq) info.
Proof. now intros ? ? []. Qed.

Definition app f rc := {| loc := f (loc rc); info := Info.app f (info rc) |}.

Instance app_compat : Proper ((Location.eq ==> Location.eq) ==> eq_RobotConf ==> eq_RobotConf) app.
Proof.
intros f g Hfg rc1 rc2 [? Heq]. split; simpl.
- now apply Hfg.
- now apply Info.app_compat.
Qed.

Lemma app_id : (eq_RobotConf ==> eq_RobotConf)%signature (app Datatypes.id) Datatypes.id.
Proof.
intros rc1 rc2 [? Heq]. split; simpl.
- assumption.
- now apply Info.app_id.
Qed.

Lemma app_compose : forall f g, Proper (Location.eq ==> Location.eq) f -> Proper (Location.eq ==> Location.eq) g ->
  (eq_RobotConf ==> eq_RobotConf)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
Proof.
intros f g Hf Hg rc1 rc2 [? Heq]. split; simpl.
- now apply Hf, Hg.
- now apply Info.app_compose.
Qed.

Lemma loc_app : forall f, Proper (Location.eq ==> Location.eq) f ->
  (eq_RobotConf ==> Location.eq)%signature (fun x => loc (app f x)) (fun x => f (loc x)).
Proof. repeat intro. simpl. now do 2 f_equiv. Qed.

(** A configuration is a mapping from identifiers to locations.  Equality is extensional. *)
Definition t := Names.ident -> RobotConf. 

Definition eq (config₁ config₂ : t) := forall id, eq_RobotConf (config₁ id) (config₂ id).

Instance eq_equiv : Equivalence eq.
Proof. split.
+ intros config x. split; reflexivity.
+ intros d1 d2 H r. split; symmetry; apply H.
+ intros d1 d2 d3 H12 H23 x. 
  split;
  unfold eq in *.
  transitivity (loc (d2 x)).
  apply H12.
  apply H23.
  transitivity (info (d2 x)).
  apply H12.
  apply H23.
Qed.

Instance eq_subrelation : subrelation eq (Logic.eq ==> eq_RobotConf)%signature.
Proof.
intros ? ? Hconfig ? id ?.
subst.
destruct Hconfig with id.
unfold eq_RobotConf.
auto.
Qed.

(** Pointwise mapping of a function on a configuration *)
Definition map (f : RobotConf -> RobotConf) (config : t) := fun id => f (config id).

Instance map_compat : Proper ((eq_RobotConf ==> eq_RobotConf) ==> eq ==> eq) map.
Proof.
intros f g Hfg ? ? Hconfig id.
unfold map.
apply Hfg.
unfold eq in Hconfig.
auto.
Qed.

(** Configurations seen as lists *)
Definition Gpos (config : t) := List.map (fun g => config (Good g)) Names.Gnames.
Definition Bpos (config : t) := List.map (fun b => config (Byz b)) Names.Bnames.
Definition list (config : t) := List.map config Names.names.

Instance Gpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Gpos.
Proof. repeat intro. unfold Gpos. f_equiv. repeat intro. now subst. Qed.

Instance Bpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Bpos.
Proof. repeat intro. unfold Bpos. f_equiv. repeat intro. now subst. Qed.

Instance list_compat : Proper (eq ==> eqlistA eq_RobotConf) list.
Proof. repeat intro. unfold list. f_equiv. repeat intro. now subst. Qed.
(* Proof. repeat intro. unfold list. apply (eqlistA_app _); apply Gpos_compat || apply Bpos_compat; auto. Qed. *)

Lemma Gpos_spec : forall config, Gpos config = List.map (fun g => config (Good g)) Names.Gnames.
Proof. reflexivity. Qed.

Lemma Bpos_spec : forall config, Bpos config = List.map (fun g => config (Byz g)) Names.Bnames.
Proof. reflexivity. Qed.

Lemma list_spec : forall config, list config = List.map config Names.names.
Proof. reflexivity. Qed.

Lemma Gpos_InA : forall l config, InA eq_RobotConf l (Gpos config) <-> exists g, eq_RobotConf l (config (Good g)).
Proof.
intros. unfold Gpos. rewrite InA_map_iff; autoclass; []. setoid_rewrite InA_Leibniz.
split; intros [g Hg]; exists g; intuition. apply Names.In_Gnames.
Qed.

Lemma Bpos_InA : forall l config, InA eq_RobotConf l (Bpos config) <-> exists b, eq_RobotConf l (config (Byz b)).
Proof.
intros. unfold Bpos. rewrite InA_map_iff; autoclass; []. setoid_rewrite InA_Leibniz.
split; intros [b Hb]; exists b; intuition. apply Names.In_Bnames.
Qed.

Lemma list_InA : forall l config, InA eq_RobotConf l (list config) <-> exists id, eq_RobotConf l (config id).
Proof.
intros. unfold list. rewrite InA_map_iff; autoclass; []. setoid_rewrite InA_Leibniz.
split; intros [id Hid]; exists id; intuition. apply Names.In_names.
Qed.

Lemma Gpos_length : forall config, length (Gpos config) = N.nG.
Proof. intro. unfold Gpos. rewrite List.map_length. apply Names.Gnames_length. Qed.

Lemma Bpos_length : forall config, length (Bpos config) = N.nB.
Proof. intro. unfold Bpos. rewrite List.map_length. apply Names.Bnames_length. Qed.

Lemma list_length : forall config, length (list config) = N.nG + N.nB.
Proof. intro. unfold list, Names.ident. now rewrite map_length, Names.names_length. Qed.

Lemma list_map : forall f, Proper (eq_RobotConf ==> eq_RobotConf) f -> 
  forall config, list (map f config) = List.map f (list config).
Proof. intros f Hf conf. unfold list, map, Gpos, Bpos. now repeat rewrite ?List.map_app, List.map_map. Qed.

Lemma map_merge : forall f g, Proper (eq_RobotConf ==> eq_RobotConf) f -> Proper (eq_RobotConf ==> eq_RobotConf) g ->
  forall config, eq (map g (map f config)) (map (fun x => g (f x)) config).
Proof. repeat intro. split; reflexivity. Qed.

Lemma map_id : forall config, eq (map Datatypes.id config) config.
Proof. repeat intro. split; reflexivity. Qed.

Lemma neq_equiv : forall config₁ config₂,
  ~eq config₁ config₂ <-> exists id, ~eq_RobotConf (config₁ id) (config₂ id).
Proof.
intros config₁ config₂. split; intro Hneq.
* assert (Hlist : ~eqlistA eq_RobotConf (List.map config₁ Names.names) (List.map config₂ Names.names)).
  { intro Habs. apply Hneq. intro id.
    assert (Hin : List.In id Names.names) by apply Names.In_names.
    induction Names.names as [| id' l].
    - inversion Hin.
    - inversion_clear Habs. inversion_clear Hin; solve [now subst | now apply IHl]. }
  induction Names.names as [| id l].
  + now elim Hlist.
  + cbn in Hlist. destruct (eq_RobotConf_dec (config₁ id) (config₂ id)) as [Hid | Hid].
    - apply IHl. intro Heq. apply Hlist. now constructor.
    - eauto.
* destruct Hneq as [id Hneq]. intro Habs. apply Hneq, Habs.
Qed.

Lemma eq_dec : forall config₁ config₂, {eq config₁ config₂} + {~eq config₁ config₂}.
Proof.
intros config₁ config₂.
destruct (eqlistA_dec _ eq_RobotConf_dec (list config₁) (list config₂)) as [Heq | Hneq].
+ left. unfold eq. apply Names.fun_names_eq, Heq.
+ right. intro Habs. apply Hneq. now rewrite Habs.
Qed.

End Make.


(** **  Spectra  **)

Module Type Spectrum (Location : DecidableType)
                     (N : Size)
                     (Names : Robots(N))
                     (Info : DecidableTypeWithApplication(Location))
                     (Config : Configuration(Location)(N)(Names)(Info)). (* <: DecidableType *)
  
  (** Spectra are a decidable type *)
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  Parameter eq_dec : forall x y : t, {eq x y} + {~eq x y}.
  
  (** A predicate characterizing correct spectra for a given local configuration *)
  Parameter from_config : Config.t -> t.
  Declare Instance from_config_compat : Proper (Config.eq ==> eq) from_config.
  Parameter is_ok : t -> Config.t -> Prop.
  Parameter from_config_spec : forall config, is_ok (from_config config) config.
End Spectrum.
*)