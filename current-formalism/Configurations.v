(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Omega.
Require Import Equalities.
Require Import SetoidList.
Require Import Reals.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Robots.


(* TODO: find an existing alternative? *)
Class Location (loc : Type) := {
  loc_eq : loc -> loc -> Prop;
  loc_eq_equiv : Equivalence loc_eq;
  loc_eq_dec : forall x y : loc, {loc_eq x y} + {~loc_eq x y}}.

(** * Configurations *)

Class Configuration (loc : Type) (Loc : Location loc) `(N : Names) := {
  config := ident -> loc;
  config_eq := fun config₁ config₂ => forall id : ident, loc_eq (config₁ id) (config₂ id);
  config_eq_equiv : Equivalence config_eq;

(*   Declare Instance eq_subrelation : subrelation eq (Logic.eq ==> Location.eq)%signature. *)
  
  config_neq_equiv : forall config₁ config₂, ~config_eq config₁ config₂ <-> exists id, ~loc_eq (config₁ id) (config₂ id);
  
  map_config := fun (f : loc -> loc) (conf : config) => fun id => f (conf id);
  map_config_compat : Proper ((loc_eq ==> loc_eq) ==> config_eq ==> config_eq) map_config;
  
  Gpos : config -> list loc;
  Bpos : config -> list loc;
  list : config -> list loc;
  Gpos_compat : Proper (eq ==> eqlistA loc_eq) Gpos;
  Bpos_compat : Proper (eq ==> eqlistA loc_eq) Bpos;
  list_compat : Proper (eq ==> eqlistA loc_eq) list;
  
  Gpos_spec : forall conf, Gpos conf = List.map (fun g => conf (Good g)) Gnames;
  Bpos_spec : forall conf, Bpos conf = List.map (fun g => conf (Byz g)) Bnames;
  list_spec : forall conf, list conf = List.map conf names;

  Gpos_InA : forall l conf, InA loc_eq l (Gpos conf) <-> exists g, loc_eq l (conf (Good g));
  Bpos_InA : forall l conf, InA loc_eq l (Bpos conf) <-> exists b, loc_eq l (conf (Byz b));
  list_InA : forall l conf, InA loc_eq l (list conf) <-> exists id, loc_eq l (conf id);
  
  Gpos_length : forall conf, length (Gpos conf) = nG;
  Bpos_length : forall conf, length (Bpos conf) = nB;
  list_length : forall conf, length (list conf) = nG + nB;
  
  list_map : forall f, Proper (loc_eq ==> loc_eq) f -> 
    forall conf, list (map_config f conf) = List.map f (list conf);
  map_merge : forall f g, Proper (loc_eq ==> loc_eq) f ->
    Proper (loc_eq ==> loc_eq) g ->
    forall conf, config_eq (map_config g (map_config f conf)) (map_config (fun x => g (f x)) conf);
  map_id : forall conf, config_eq (map_config Datatypes.id conf) conf}.


Module Make(Location : DecidableType)(N : Size)(Names : Robots(N)) : Configuration(Location)(N)(Names)
  with Definition t := Names.ident -> Location.t.

(** A configuration is a mapping from identifiers to locations.  Equality is extensional. *)
Definition t := Names.ident -> Location.t.
Definition eq (conf₁ conf₂ : t) : Prop := forall id, Location.eq (conf₁ id) (conf₂ id).

Instance eq_equiv : Equivalence eq.
Proof. split.
+ intros conf x. reflexivity.
+ intros d1 d2 H r. symmetry. apply H.
+ intros d1 d2 d3 H12 H23 x. transitivity (d2 x); auto.
Qed.

Instance eq_bisim : Bisimulation t.
Proof. exists eq. apply eq_equiv. Defined.

Instance eq_subrelation : subrelation eq (Logic.eq ==> Location.eq)%signature.
Proof. intros ? ? Hconf ? id ?. subst. apply Hconf. Qed.

(** Pointwise mapping of a function on a configuration *)
Definition map (f : Location.t -> Location.t) (conf : t) := fun id => f (conf id).

Instance map_compat : Proper ((Location.eq ==> Location.eq) ==> eq ==> eq) map.
Proof. intros f g Hfg ? ? Hconf id. unfold map. apply Hfg, Hconf. Qed.

(** Configurations seen as lists *)
Definition Gpos (conf : t) := Names.Internals.fin_map (fun g => conf (Good g)).
Definition Bpos (conf : t) := Names.Internals.fin_map (fun b => conf (Byz b)).
Definition list conf := Gpos conf ++ Bpos conf.

Instance Gpos_compat : Proper (eq ==> eqlistA Location.eq) Gpos.
Proof. repeat intro. unfold Gpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance Bpos_compat : Proper (eq ==> eqlistA Location.eq) Bpos.
Proof. repeat intro. unfold Bpos. apply Names.Internals.fin_map_compatA. repeat intro. now subst. Qed.

Instance list_compat : Proper (eq ==> eqlistA Location.eq) list.
Proof. repeat intro. unfold list. now apply (eqlistA_app _); apply Gpos_compat || apply Bpos_compat. Qed.

Lemma Gpos_spec : forall conf, Gpos conf = List.map (fun g => conf (Good g)) Names.Gnames.
Proof. intros. unfold Gpos, Names.Gnames, Names.Internals.Gnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma Bpos_spec : forall conf, Bpos conf = List.map (fun g => conf (Byz g)) Names.Bnames.
Proof. intros. unfold Bpos, Names.Bnames, Names.Internals.Bnames. now rewrite <- Names.Internals.map_fin_map. Qed.

Lemma list_spec : forall conf, list conf = List.map conf Names.names.
Proof.
intros. unfold list. unfold Names.names, Names.Internals.names.
rewrite map_app, Gpos_spec, Bpos_spec. now do 2 rewrite map_map.
Qed.

Lemma Gpos_InA : forall l conf, InA Location.eq l (Gpos conf) <-> exists g, Location.eq l (conf (Good g)).
Proof. intros. unfold Gpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma Bpos_InA : forall l conf, InA Location.eq l (Bpos conf) <-> exists b, Location.eq l (conf (Byz b)).
Proof. intros. unfold Bpos. rewrite (Names.Internals.fin_map_InA _ Location.eq_dec). reflexivity. Qed.

Lemma list_InA : forall l conf, InA Location.eq l (list conf) <-> exists id, Location.eq l (conf id).
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

Lemma list_map : forall f, Proper (Location.eq ==> Location.eq) f -> 
  forall conf, list (map f conf) = List.map f (list conf).
Proof.
intros f Hf conf. unfold list, map, Gpos, Bpos.
repeat rewrite Names.Internals.map_fin_map. rewrite List.map_app. reflexivity.
Qed.

Lemma map_merge : forall f g, Proper (Location.eq ==> Location.eq) f -> Proper (Location.eq ==> Location.eq) g ->
  forall conf, eq (map g (map f conf)) (map (fun x => g (f x)) conf).
Proof. repeat intro. reflexivity. Qed.

Lemma map_id : forall conf, eq (map Datatypes.id conf) conf.
Proof. repeat intro. reflexivity. Qed.

Lemma neq_equiv : forall config₁ config₂,
  ~eq config₁ config₂ <-> exists id, ~Location.eq (config₁ id) (config₂ id).
Proof.
intros config₁ config₂. split; intro Hneq.
* assert (Hlist : ~eqlistA Location.eq (List.map config₁ Names.names) (List.map config₂ Names.names)).
  { intro Habs. apply Hneq. intro id.
    assert (Hin : List.In id Names.names) by apply Names.In_names.
    induction Names.names as [| id' l].
    - inversion Hin.
    - inversion_clear Habs. inversion_clear Hin; solve [now subst | now apply IHl]. }
  induction Names.names as [| id l].
  + now elim Hlist.
  + cbn in Hlist. destruct (Location.eq_dec (config₁ id) (config₂ id)) as [Hid | Hid].
    - apply IHl. intro Heq. apply Hlist. now constructor.
    - eauto.
* destruct Hneq as [id Hneq]. intro Habs. apply Hneq, Habs.
Qed.

End Make.


(** **  Spectra  **)

Module Type Spectrum(Location : DecidableType)(N : Size). (* <: DecidableType *)
  Module Names := Robots.Make(N).
  Module Config := Make(Location)(N)(Names).
  
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
