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
Require Import Pactole.Preliminary.
Require Import Robots.
Require Import ZArith.
Require Import Decidable.


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
Module Unit(Location : DecidableType)
  : DecidableTypeWithApplication(Location) with Definition t := unit
                                           with Definition eq := @Logic.eq unit.
  Definition t := unit.
  Definition eq := @Logic.eq unit.
  Instance eq_equiv : Equivalence eq := @eq_equivalence unit.
  
  Lemma eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof. intros [] []. now left. Defined.
  
  Definition app (f : Location.t -> Location.t) (x : t) := tt : t.
  
  Instance app_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) app.
  Proof. now repeat intro. Qed.
  
  Lemma app_id : (eq ==> eq)%signature (app Datatypes.id) Datatypes.id.
  Proof. now intros [] [] _. Qed.
  
  Lemma app_compose : forall f g,
    Proper (Location.eq ==> Location.eq) f ->
    Proper (Location.eq ==> Location.eq) g ->
    (eq ==> eq)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
  Proof. now intros f g _ _ [] [] _. Qed.
End Unit.

(** A pair of locations (source, target) also constitutes a valid information type. *)
Module SourceTarget (Loc : DecidableType) <: DecidableTypeWithApplication(Loc).
  Record t' := {source : Loc.t; target : Loc.t}.
  Definition t := t'.
  
  Definition eq info1 info2 := Loc.eq info1.(source) info2.(source) /\ Loc.eq info1.(target) info2.(target).
  
  Instance eq_equiv : Equivalence eq.
  Proof. split.
  + intros []; split; simpl; reflexivity.
  + intros [] [] []; split; simpl in *; now symmetry.
  + intros [] [] [] [] []; split; simpl in *; etransitivity; eauto.
  Qed.
  
  Lemma eq_dec : forall x y : t, {eq x y} + {~eq x y}.
  Proof.
  intros [s1 t1] [s2 t2].
  destruct (Loc.eq_dec s1 s2); [destruct (Loc.eq_dec t1 t2) |].
  + now left.
  + right. intros []. contradiction.
  + right. intros []. contradiction.
  Qed.
  
  Definition app f info := {| source := f info.(source); target := f info.(target) |}.
  
  Instance app_compat : Proper ((Loc.eq ==> Loc.eq) ==> eq ==> eq) app.
  Proof. intros f g Hfg x y Hxy. unfold app. split; simpl; apply Hfg, Hxy. Qed.
  
  Lemma app_id : (eq ==> eq)%signature (app Datatypes.id) Datatypes.id.
  Proof. intros x y Hxy. apply Hxy. Qed.
  
  Lemma app_compose : forall f g, Proper (Loc.eq ==> Loc.eq) f -> Proper (Loc.eq ==> Loc.eq) g ->
    (eq ==> eq)%signature (app (fun x => f (g x))) (fun x => app f (app g x)).
  Proof. intros ? ? ? ? [] [] []. split; simpl in *; now do 2 f_equiv. Qed.
End SourceTarget.


(** * Configurations *)

(** This module signature represents the space in which robots evolve.
    It can be anything as long as it is a non-trivial real metric space.

    The framework for robots should be more general as for instance a ring is not a metric space.
    It seems that we only need a decidable type for locations and a notion of distance.  *)

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


  Definition map (f : RobotConf -> RobotConf) (conf : t) : t := fun id => f (conf id).
  Declare Instance map_compat : Proper ((eq_RobotConf ==> eq_RobotConf) ==> eq ==> eq) map.

  Parameter Gpos : t -> list RobotConf.
  Parameter Bpos : t -> list RobotConf.
  Parameter list : t -> list RobotConf.
  Declare Instance Gpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Gpos.
  Declare Instance Bpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Bpos.
  Declare Instance list_compat : Proper (eq ==> eqlistA eq_RobotConf) list.

  Parameter Gpos_spec : forall conf, Gpos conf = List.map (fun g => conf (Good g)) Names.Gnames.
  Parameter Bpos_spec : forall conf, Bpos conf = List.map (fun g => conf (Byz g)) Names.Bnames.
  Parameter list_spec : forall conf, list conf = List.map conf Names.names.

  Parameter Gpos_InA : forall l conf, InA eq_RobotConf l (Gpos conf) <-> exists g, eq_RobotConf l (conf (Good g)).
  Parameter Bpos_InA : forall l conf, InA eq_RobotConf l (Bpos conf) <-> exists b, eq_RobotConf l (conf (Byz b)).
  Parameter list_InA : forall l conf, InA eq_RobotConf l (list conf) <-> exists id, eq_RobotConf l (conf id).

  Parameter Gpos_length : forall conf, length (Gpos conf) = N.nG.
  Parameter Bpos_length : forall conf, length (Bpos conf) = N.nB.
  Parameter list_length : forall conf, length (list conf) = N.nG + N.nB.

  Parameter list_map : forall f, Proper (eq_RobotConf ==> eq_RobotConf) f -> 
    forall conf, list (map f conf) = List.map f (list conf).
  Parameter map_merge : forall f g, Proper (eq_RobotConf ==> eq_RobotConf) f ->
    Proper (eq_RobotConf ==> eq_RobotConf) g ->
    forall conf, eq (map g (map f conf)) (map (fun x => g (f x)) conf).
  Parameter map_id : forall conf, eq (map Datatypes.id conf) conf.
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
+ intros conf x. split; reflexivity.
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
intros ? ? Hconf ? id ?.
subst.
destruct Hconf with id.
unfold eq_RobotConf.
auto.
Qed.

(** Pointwise mapping of a function on a configuration *)
Definition map (f : RobotConf -> RobotConf) (conf : t) := fun id => f (conf id).

Instance map_compat : Proper ((eq_RobotConf ==> eq_RobotConf) ==> eq ==> eq) map.
Proof.
intros f g Hfg ? ? Hconf id.
unfold map.
apply Hfg.
unfold eq in Hconf.
auto.
Qed.

(** Configurations seen as lists *)
Definition Gpos (conf : t) := Names.Internals.fin_map (fun g => conf (Good g)).
Definition Bpos (conf : t) := Names.Internals.fin_map (fun b => conf (Byz b)).
Definition list conf := Gpos conf ++ Bpos conf.

Instance Gpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Gpos.
Proof. repeat intro. unfold Gpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance Bpos_compat : Proper (eq ==> eqlistA eq_RobotConf) Bpos.
Proof. repeat intro. unfold Bpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance list_compat : Proper (eq ==> eqlistA eq_RobotConf) list.
Proof. repeat intro. unfold list. apply (eqlistA_app _); apply Gpos_compat || apply Bpos_compat; auto. Qed.

Lemma Gpos_spec : forall conf, Gpos conf = List.map (fun g => conf (Good g)) Names.Gnames.
Proof. intros. unfold Gpos, Names.Gnames, Names.Internals.Gnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma Bpos_spec : forall conf, Bpos conf = List.map (fun g => conf (Byz g)) Names.Bnames.
Proof. intros. unfold Bpos, Names.Bnames, Names.Internals.Bnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma list_spec : forall conf, list conf = List.map conf Names.names.
Proof.
intros. unfold list. unfold Names.names, Names.Internals.names.
rewrite map_app, Gpos_spec, Bpos_spec. now do 2 rewrite map_map.
Qed.

Lemma Gpos_InA : forall l conf, InA eq_RobotConf l (Gpos conf) <-> exists g, eq_RobotConf l (conf (Good g)).
Proof. intros. unfold Gpos,eq_RobotConf. rewrite (Names.Internals.fin_map_InA _ eq_RobotConf_dec). reflexivity. Qed.

Lemma Bpos_InA : forall l conf, InA eq_RobotConf l (Bpos conf) <-> exists b, eq_RobotConf l (conf (Byz b)).
Proof. intros. unfold Bpos. rewrite (Names.Internals.fin_map_InA _ eq_RobotConf_dec). reflexivity. Qed.

Lemma list_InA : forall l conf, InA eq_RobotConf l (list conf) <-> exists id, eq_RobotConf l (conf id).
Proof.
intros. unfold list. rewrite (InA_app_iff _). split; intro Hin.
+ destruct Hin as [Hin | Hin]; rewrite Gpos_InA in Hin || rewrite Bpos_InA in Hin; destruct Hin; eauto.
+ rewrite Gpos_InA, Bpos_InA. destruct Hin as [[g | b] Hin]; eauto.
Qed.

Lemma Gpos_length : forall conf, length (Gpos conf) = N.nG.
Proof. intro. unfold Gpos. apply Names.Internals.fin_map_length. Qed.

Lemma Bpos_length : forall conf, length (Bpos conf) = N.nB.
Proof. intro. unfold Bpos. apply Names.Internals.fin_map_length. Qed.

Lemma list_length : forall conf, length (list conf) = N.nG + N.nB.
Proof. intro. unfold list. now rewrite app_length, Gpos_length, Bpos_length. Qed.

Lemma list_map : forall f, Proper (eq_RobotConf ==> eq_RobotConf) f -> 
  forall conf, list (map f conf) = List.map f (list conf).
Proof.
intros f Hf conf. unfold list, map, Gpos, Bpos.
repeat rewrite Names.Internals.map_fin_map. rewrite List.map_app. reflexivity.
Qed.

Lemma map_merge : forall f g, Proper (eq_RobotConf ==> eq_RobotConf) f -> Proper (eq_RobotConf ==> eq_RobotConf) g ->
  forall conf, eq (map g (map f conf)) (map (fun x => g (f x)) conf).
Proof. repeat intro. split; reflexivity. Qed.

Lemma map_id : forall conf, eq (map Datatypes.id conf) conf.
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
+ left. unfold list in *. apply eqlistA_app_split in Heq; try (now repeat rewrite Gpos_length); [].
  destruct Heq as [Heq1 Heq2]. intros [g | b].
  - apply (Names.Internals.fin_map_eq Heq1 g).
  - apply (Names.Internals.fin_map_eq Heq2 b).
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
  Parameter is_ok : t -> Config.t -> Location.t -> Prop.
  Parameter from_config_spec : forall config l, is_ok (from_config config l) config l.
  
  Parameter get_location : t -> Location.t.
  Parameter get_location_ok : forall config l, Location.eq (get_location (from_config config l)) l.
  
End PointedSpectrum.