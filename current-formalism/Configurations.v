(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 
   T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)


Require Import Omega.
Require Import Equalities.
Require Import SetoidList.
Require Import ZArith.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.


Module Type DecidableTypeWithApplication(Location : DecidableType) <: DecidableType.
  Include DecidableType.
  Parameter app : (Location.t -> Location.t) -> t -> t.
  Declare Instance app_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) app.
  Axiom app_id : (eq ==> eq)%signature (app Datatypes.id) Datatypes.id.
  Axiom app_compose : forall f g,
    Proper (Location.eq ==> Location.eq) f ->
    Proper (Location.eq ==> Location.eq) g ->
    (eq ==> eq)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
End DecidableTypeWithApplication.


(** [unit] is a valid information type that does not contain any information. *)
Module Unit(Loc : DecidableType) <: DecidableTypeWithApplication(Loc).
  Definition t := unit.
  Definition eq := @Logic.eq unit.
  Instance eq_equiv : Equivalence eq := @eq_equivalence unit.
  
  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof. intros [] []. now left. Defined.
  
  Definition app (f : Loc.t -> Loc.t) (x : t) := tt : t.
  
  Instance app_compat : Proper ((Loc.eq ==> Loc.eq) ==> eq ==> eq) app.
  Proof. now repeat intro. Qed.
  
  Lemma app_id : (eq ==> eq)%signature (app Datatypes.id) Datatypes.id.
  Proof. now intros [] [] _. Qed.
  
  Lemma app_compose : forall f g, Proper (Loc.eq ==> Loc.eq) f -> Proper (Loc.eq ==> Loc.eq) g ->
    (eq ==> eq)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
  Proof. now intros f g _ _ [] [] _. Qed.
End Unit.

(** A pair of locations (source, target) also constitutes a valid information type. *)
Module SourceTarget (Loc : DecidableType) <: DecidableTypeWithApplication(Loc).
  Record t' := {source : Loc.t; target : Loc.t}.
  Definition t := t'.
  
  Definition eq state1 state2 := Loc.eq state1.(source) state2.(source) /\ Loc.eq state1.(target) state2.(target).
  
  Instance eq_equiv : Equivalence eq.
  Proof. split.
  + intros []; split; simpl; reflexivity.
  + intros [] [] []; split; simpl in *; now symmetry.
  + intros [] [] [] [] []; split; simpl in *; etransitivity; eauto.
  Qed.
  
  Instance source_compat : Proper (eq ==> Loc.eq) source.
  Proof. now intros [] [] []. Qed.
  
  Instance target_compat : Proper (eq ==> Loc.eq) target.
  Proof. now intros [] [] []. Qed.
  
  Lemma eq_dec : forall x y : t, {eq x y} + {~eq x y}.
  Proof.
  intros [s1 t1] [s2 t2].
  destruct (Loc.eq_dec s1 s2); [destruct (Loc.eq_dec t1 t2) |].
  + now left.
  + right. intros []. contradiction.
  + right. intros []. contradiction.
  Qed.
  
  Definition app f state := {| source := f state.(source); target := f state.(target) |}.
  
  Instance app_compat : Proper ((Loc.eq ==> Loc.eq) ==> eq ==> eq) app.
  Proof. intros f g Hfg x y Hxy. unfold app. split; simpl; apply Hfg, Hxy. Qed.
  
  Lemma app_id : (eq ==> eq)%signature (app Datatypes.id) Datatypes.id.
  Proof. intros x y Hxy. apply Hxy. Qed.
  
  Lemma app_compose : forall f g, Proper (Loc.eq ==> Loc.eq) f -> Proper (Loc.eq ==> Loc.eq) g ->
    (eq ==> eq)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
  Proof. intros ? ? ? ? [] [] []. split; simpl in *; now do 2 f_equiv. Qed.
End SourceTarget.

(** We can also keep only the target location. *)
Module Target (Loc : DecidableType) <: DecidableTypeWithApplication(Loc).
  Definition t := Loc.t.
  Definition eq := Loc.eq.
  Instance eq_equiv : Equivalence eq := Loc.eq_equiv.
  Definition eq_dec : forall x y : t, {eq x y} + {~eq x y} := Loc.eq_dec.
  
  Definition app (f : Loc.t -> Loc.t) info := f info.
  
  Instance app_compat : Proper ((Loc.eq ==> Loc.eq) ==> eq ==> eq) app.
  Proof. intros f g Hfg x y Hxy. unfold app. apply Hfg, Hxy. Qed.
  
  Lemma app_id : (eq ==> eq)%signature (app Datatypes.id) Datatypes.id.
  Proof. intros x y Hxy. apply Hxy. Qed.
  
  Lemma app_compose : forall f g, Proper (Loc.eq ==> Loc.eq) f -> Proper (Loc.eq ==> Loc.eq) g ->
    (eq ==> eq)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
  Proof. repeat intro. unfold app. now do 2 f_equiv. Qed.
End Target.

(** * Configurations *)

(** This module signature represents the space in which robots evolve.
    It can be anything as long as it is a non-trivial real metric space.

    The framework for robots should be more general as for instance a ring is not a metric space.
    It seems that we only need a decidable type for locations and a notion of distance.  *)

Module Type Configuration (Location : DecidableType)
                          (N : Size)
                          (Names : Robots(N))
                          (Info : DecidableTypeWithApplication(Location)).

  Record RobotConf := { loc :> Location.t; state: Info.t }.

  Definition t := Names.ident -> RobotConf.

  Definition eq_RobotConf g1 g2 := Location.eq (loc g1) (loc g2)
                                /\ Info.eq (state g1) (state g2).

  Definition app f rc := {| loc := f (loc rc); state := Info.app f (state rc) |}.
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
  Declare Instance state_compat : Proper (eq_RobotConf ==> Info.eq) state.

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

Record RobotConf := { loc :> Location.t; state: Info.t }.

Definition eq_RobotConf g1 g2 := Location.eq (loc g1) (loc g2)
                                 /\ Info.eq (state g1) (state g2).

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
  transitivity (state y).
  apply H.
  apply H0.
Qed.

Lemma eq_RobotConf_dec : forall rc1 rc2, {eq_RobotConf rc1 rc2} + {~ eq_RobotConf rc1 rc2 }.
Proof.
intros rc1 rc2.
unfold eq_RobotConf.
destruct (Location.eq_dec rc1 rc2),
         (Info.eq_dec (state rc1) (state rc2));
intuition.
Qed.

Set Printing Implicit.

Instance Build_RobotConf_compat : Proper (Location.eq ==> Info.eq ==> eq_RobotConf) Build_RobotConf.
Proof. intros l1 l2 Hl state1 state2 Hstate. split; apply Hl || apply Hstate. Qed.

Instance loc_compat : Proper (eq_RobotConf ==> Location.eq) loc.
Proof. now intros ? ? []. Qed.

Instance state_compat : Proper (eq_RobotConf ==> Info.eq) state.
Proof. now intros ? ? []. Qed.

Definition app f rc := {| loc := f (loc rc); state := Info.app f (state rc) |}.

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
  transitivity (state (d2 x)).
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

Module Type PointedSpectrum (Location : DecidableType)
                            (N : Size)
                            (Names : Robots(N))
                            (Info : DecidableTypeWithApplication(Location))
                            (Config : Configuration(Location)(N)(Names)(Info)).
  (* <: DecidableType *)
  
  (** Spectra are a decidable type *)
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  Parameter eq_dec : forall x y : t, {eq x y} + {~eq x y}.
  
  (** A predicate characterizing correct spectra for a given local configuration *)
  Parameter from_config : Config.t -> Location.t -> t.
  Declare Instance from_config_compat : Proper (Config.eq ==> Location.eq ==> eq) from_config.
  Parameter is_ok : t -> Config.t -> Prop.
  Parameter from_config_spec : forall config l, is_ok (from_config config l) config.
  
  Parameter get_current : t -> Location.t.
  Parameter get_current_ok : forall config l, Location.eq (get_current (from_config config l)) l.
  
End PointedSpectrum.