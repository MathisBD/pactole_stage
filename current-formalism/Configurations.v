(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Omega.
Require Import Equalities.
Require Import SetoidList.
Require Import Reals.
Require Import Pactole.Preliminary.
Require Import Robots.
Require Import ZArith.
Require Import Decidable.


(** * Configurations *)

(** This module signature represents the space in which robots evolve.
    It can be anything as long as it is a non-trivial real metric space.

    The framework for robots should be more general as for instance a ring is not a metric space.
    It seems that we only need a decidable type for locations and a notion of distance.  *)
Module Type RealMetricSpaceDef <: DecidableType.
  Parameter t : Type.
  Parameter origin : t.
  Parameter eq : t -> t -> Prop.
  Parameter dist : t -> t -> R.
  Parameter eq_dec : forall x y, {eq x y} + {~eq x y}.
  
  Parameter add : t -> t -> t.
  Parameter mul : R -> t -> t. (* the underlying field is R *)
  Parameter opp : t -> t.
  
  Declare Instance add_compat : Proper (eq ==> eq ==> eq) add.
  Declare Instance mul_compat : Proper (Logic.eq ==> eq ==> eq) mul.
  Declare Instance opp_compat : Proper (eq ==> eq) opp.
  
  Parameter eq_equiv : Equivalence eq.
  Parameter dist_defined : forall x y, dist x y = 0%R <-> eq x y.
  Parameter dist_sym : forall y x, dist x y = dist y x.
  Parameter triang_ineq : forall x y z, (dist x z <= dist x y + dist y z)%R.
  
  Parameter add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Parameter add_comm : forall u v, eq (add u v) (add v u).
  Parameter add_origin : forall u, eq (add u origin) u.
  Parameter add_opp : forall u, eq (add u (opp u)) origin.
  Parameter mul_distr_add : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Parameter mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Parameter add_morph : forall a b u, eq (add (mul a u) (mul b u)) (mul (a + b) u).
  
  Parameter mul_1 : forall u, eq (mul 1 u) u.
  Parameter unit : t. (* TODO: is it really a good name? *)
  Parameter non_trivial : ~eq unit origin.
End RealMetricSpaceDef.

Module Type RealMetricSpace.
  Include RealMetricSpaceDef.
  
  Declare Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Parameter dist_pos : forall x y, (0 <= dist x y)%R.
  Parameter mul_opp : forall a u, eq (mul a (opp u)) (opp (mul a u)).
  Parameter add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Parameter add_reg_r : forall w u v, eq (add u w) (add v w) -> eq u v.
  Parameter opp_origin : eq (opp origin) origin.
  Parameter opp_opp : forall u, eq (opp (opp u)) u.
  Parameter opp_distr_add : forall u v, eq (opp (add u v)) (add (opp u) (opp v)).
  Parameter mul_0 : forall u, eq (mul 0 u) origin.
  Parameter mul_origin : forall a, eq (mul a origin) origin.
  Parameter mul_reg_l : forall k u v, k <> 0%R -> eq (mul k u) (mul k v) -> eq u v.
  Parameter mul_reg_r : forall k k' u, ~eq u origin -> eq (mul k u) (mul k' u) -> k = k'.
  Parameter minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).
  Parameter mul_integral : forall k u, eq (mul k u) origin -> k = 0%R \/ eq u origin.

  Definition middle u v := mul (1/2)%R (add u v).
End RealMetricSpace.


Module MakeRealMetricSpace (Def : RealMetricSpaceDef) : RealMetricSpace
    with Definition t := Def.t
    with Definition eq := Def.eq
    with Definition eq_dec := Def.eq_dec
    with Definition origin := Def.origin
    with Definition dist := Def.dist
    with Definition add := Def.add
    with Definition mul := Def.mul
    with Definition opp := Def.opp.
  
  Include Def.

  (** Proofs of two derivable properties about MetricSpace *)
  Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Proof.
  intros x x' Hx y y' Hy. apply Rle_antisym.
  + replace (dist x' y') with (0 + dist x' y' + 0)%R by ring. symmetry in Hy.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply triang_ineq.
    rewrite Rplus_assoc. apply Rplus_le_compat_l, triang_ineq.
  + replace (dist x y) with (0 + dist x y + 0)%R by ring. symmetry in Hx.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply triang_ineq.
    rewrite Rplus_assoc. apply Rplus_le_compat_l, triang_ineq.
  Qed.
  
  Lemma dist_pos : forall x y, (0 <= dist x y)%R.
  Proof.
  intros x y. apply Rmult_le_reg_l with 2%R.
  + apply Rlt_R0_R2.
  + do 2 rewrite double. rewrite Rplus_0_r.
    assert (Hx : eq x x) by reflexivity. rewrite <- dist_defined in Hx. rewrite <- Hx.
    setoid_rewrite dist_sym at 3. apply triang_ineq.
  Qed.
  
  Lemma add_reg_r : forall w u v, eq (add u w) (add v w) -> eq u v.
  Proof.
  intros w u v Heq. setoid_rewrite <- add_origin.
  now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
  Qed.
  
  Lemma add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Proof. setoid_rewrite add_comm. apply add_reg_r. Qed.
  
  Lemma opp_origin : eq (opp origin) origin.
  Proof. apply (add_reg_r origin). now rewrite add_comm, add_opp, add_origin. Qed.
  
  Lemma opp_opp : forall u, eq (opp (opp u)) u.
  Proof. intro u. apply (add_reg_l (opp u)). now rewrite add_opp, add_comm, add_opp. Qed.
  
  Lemma opp_distr_add : forall u v, eq (opp (add u v)) (add (opp u) (opp v)).
  Proof.
  intros u v. apply (add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
  setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
  Qed.
  
  Lemma mul_0 : forall u, eq (mul 0 u) origin.
  Proof.
  intro u. apply (add_reg_l u).
  rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite add_morph.
  ring_simplify (1 + 0)%R. now rewrite mul_1.
  Qed.
  
  Lemma minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).
  Proof.
  intros k u. apply (add_reg_l (mul k u)).
  rewrite add_opp. rewrite add_morph. ring_simplify (k + - k)%R.
  apply mul_0.
  Qed.
  
  Lemma mul_origin : forall k, eq (mul k origin) origin.
  Proof.
  intro k. apply add_reg_l with (mul k origin).
  rewrite <- mul_distr_add. setoid_rewrite add_origin. reflexivity.
  Qed.
  
  Lemma mul_opp : forall a u, eq (mul a (opp u)) (opp (mul a u)).
  Proof.
  intros a u. apply (add_reg_l (mul a u)). rewrite <- mul_distr_add.
  setoid_rewrite add_opp. now rewrite mul_origin.
  Qed.
  
  Lemma mul_reg_l : forall k u v, k <> 0%R -> eq (mul k u) (mul k v) -> eq u v.
  Proof.
  intros k u v Hk Heq. setoid_rewrite <- mul_1.
  replace 1%R with (/k * k)%R by now field.
  setoid_rewrite <- mul_morph. rewrite Heq.
  reflexivity.
  Qed.
  
  Lemma mul_reg_r : forall k k' u, ~eq u origin -> eq (mul k u) (mul k' u) -> k = k'.
  Proof.
  intros k k' u Hu Heq. destruct (Rdec k k') as [| Hneq]; trivial.
  assert (Heq0 : eq (mul (k -k') u)  origin).
  { unfold Rminus. rewrite <- add_morph, minus_morph, Heq. apply add_opp. }
  elim Hu. rewrite <- mul_1. rewrite <- (Rinv_l (k - k')).
  - rewrite <- mul_morph. rewrite Heq0. apply mul_origin.
  - intro Habs. apply Hneq. now apply Rminus_diag_uniq.
  Qed.
  
  Definition middle u v := mul (1/2)%R (add u v).
  
  Lemma mul_integral : forall k u, eq (mul k u) origin -> k = 0%R \/ eq u origin.
  Proof.
  intros k u Heq. destruct (Rdec k 0%R).
  - now left.
  - right. apply mul_reg_l with k; trivial; []. now rewrite Heq, mul_origin.
  Qed.
  
End MakeRealMetricSpace.

Module Type DiscretSpaceDef <: DecidableType.
  Parameter t : Type.
  Parameter origin : t.
  Parameter eq : t -> t -> Prop.
  Parameter dist : t -> t -> Z.
  Parameter eq_dec : forall x y, {eq x y} + {~ eq x y}.
  
  Parameter add : t -> t -> t.
  Parameter mul : Z -> t -> t.
  Parameter opp : t -> t.
  
  Declare Instance add_compact : Proper (eq ==> eq ==> eq) add.
  Declare Instance mul_compact : Proper (Logic.eq ==> eq  ==> eq) mul.
  Declare Instance opp_compact : Proper (eq  ==> eq) opp.
  
  Parameter eq_equiv : Equivalence eq.
  Parameter dist_defined : forall x y, dist x y = 0%Z <-> eq x y.
  Parameter dist_sym : forall x y, dist x y = dist y x.
  Parameter triang_ineq : forall x y z, (dist x z <= dist x y + dist y z)%Z.

  Parameter add_assoc : forall u v w, eq (add u (add v w)) (add (add u v) w).
  Parameter add_comm : forall u v, eq (add u v) (add v u).
  Parameter add_origin : forall u, eq (add u origin) u.
  Parameter add_opp: forall u, eq (add u (opp u)) origin.
  Parameter mul_distr_add : forall a u v, eq (mul a (add u v)) (add (mul a u) (mul a v)).
  Parameter mul_morph : forall a b u, eq (mul a (mul b u)) (mul (a * b) u).
  Parameter add_morph : forall a b u, eq (add (mul a u ) (mul b u ) ) (mul (a + b) u ).
  
  Parameter mul_1 : forall u, eq (mul 1 u ) u.
  Parameter unit : t. (* TODO: is it really a good name? *)
  Parameter non_trivial : ~eq unit origin.
End DiscretSpaceDef.

Module Type DiscretSpace.
  Include DiscretSpaceDef.
  
  Declare Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Parameter dist_pos : forall x y, (0 <= dist x y)%Z.
  Parameter mul_opp : forall a u, eq (mul a (opp u)) (opp (mul a u)).
  Parameter add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Parameter add_reg_r : forall w u v, eq (add u w) (add v w) -> eq u v.
  Parameter opp_origin : eq (opp origin) origin.
  Parameter opp_opp : forall u, eq (opp (opp u)) u.
  Parameter opp_distr_add : forall u v, eq (opp (add u v)) (add (opp u) (opp v)).
  Parameter mul_0 : forall u, eq (mul 0 u) origin.
  Parameter mul_origin : forall a, eq (mul a origin) origin.
  Parameter minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).

End DiscretSpace.


Module MakeDiscretSpace (Def : DiscretSpaceDef) : DiscretSpace
    with Definition t := Def.t
    with Definition eq := Def.eq
    with Definition eq_dec := Def.eq_dec
    with Definition origin := Def.origin
    with Definition dist := Def.dist
    with Definition add := Def.add
    with Definition mul := Def.mul
    with Definition opp := Def.opp.
  
  Include Def.

  (** Proofs of two derivable properties about DiscretSpace *)
  Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Proof.
  intros x x' Hx y y' Hy. apply Zle_antisym.
  + replace (dist x' y') with (0 + dist x' y' + 0)%Z by ring. symmetry in Hy.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply Zle_trans. apply triang_ineq.
    rewrite <- Zplus_assoc. apply Zplus_le_compat_l, triang_ineq.
  + replace (dist x y) with (0 + dist x y + 0)%Z by ring. symmetry in Hx.
    rewrite <- dist_defined in Hx. rewrite <- dist_defined in Hy.
    rewrite <- Hx at 1. rewrite <- Hy. eapply Zle_trans. apply triang_ineq.
    rewrite <- Zplus_assoc. apply Zplus_le_compat_l, triang_ineq.
  Qed.


  Lemma dist_pos : forall x y, (0 <= dist x y)%Z.
  Proof.
  intros. unfold dist. apply Zmult_le_reg_r with 2%Z. 
  + omega.
  + do 2 rewrite <- Zplus_diag_eq_mult_2. simpl.
    assert (Hx : eq x x) by reflexivity. rewrite <- dist_defined in Hx. rewrite <- Hx.
    setoid_rewrite dist_sym at 3. apply triang_ineq.
  Qed.

  Lemma add_reg_r : forall w u v, eq (add u w) (add v w) -> eq u v.
  Proof.
  intros w u v Heq. setoid_rewrite <- add_origin.
  now rewrite <- (add_opp w), add_assoc, Heq, <- add_assoc.
  Qed.
  
  Lemma add_reg_l : forall w u v, eq (add w u) (add w v) -> eq u v.
  Proof. setoid_rewrite add_comm. apply add_reg_r. Qed.
  
  Lemma opp_origin : eq (opp origin) origin.
  Proof. apply (add_reg_r origin). now rewrite add_comm, add_opp, add_origin. Qed.
  
  Lemma opp_opp : forall u, eq (opp (opp u)) u.
  Proof. intro u. apply (add_reg_l (opp u)). now rewrite add_opp, add_comm, add_opp. Qed.
  
  Lemma opp_distr_add : forall u v, eq (opp (add u v)) (add (opp u) (opp v)).
  Proof.
  intros u v. apply (add_reg_l (add u v)). rewrite add_opp, add_assoc. setoid_rewrite add_comm at 3.
  setoid_rewrite <- add_assoc at 2. now rewrite add_opp, add_origin, add_opp.
  Qed.
  
  Lemma mul_0 : forall u, eq (mul 0 u) origin.
  Proof.
  intro u. apply (add_reg_l u).
  rewrite add_origin. rewrite <- (mul_1 u) at 1. rewrite add_morph.
  ring_simplify (1 + 0)%Z. now rewrite mul_1.
  Qed.
  
  Lemma minus_morph : forall k u, eq (mul (-k) u) (opp (mul k u)).
  Proof.
  intros k u. apply (add_reg_l (mul k u)).
  rewrite add_opp. rewrite add_morph. ring_simplify (k + - k)%Z.
  apply mul_0.
  Qed.
  
  Lemma mul_origin : forall k, eq (mul k origin) origin.
  Proof.
  intro k. apply add_reg_l with (mul k origin).
  rewrite <- mul_distr_add. setoid_rewrite add_origin. reflexivity.
  Qed.
  
  Lemma mul_opp : forall a u, eq (mul a (opp u)) (opp (mul a u)).
  Proof.
  intros a u. apply (add_reg_l (mul a u)). rewrite <- mul_distr_add.
  setoid_rewrite add_opp. now rewrite mul_origin.
  Qed.
  
End MakeDiscretSpace.




Module Type Configuration(Location : DecidableType)(N : Size)(Names : Robots(N)).


  Inductive State :=
    | RDY2LookCompute
    | RDY2Move (targets: Location.t*Location.t).
 
  Record RobotConf := { Loc :> Location.t; Sta : State}.

  Definition t := Names.ident -> RobotConf. 

  Definition eq_State (st1 st2 : State) :=  match st1 with 
    | RDY2LookCompute => match st2 with | RDY2LookCompute => True | _ => False end
    | RDY2Move (loc,loc0) => match st2 with 
                            | RDY2Move (loc1,loc2) => Location.eq loc loc1 /\ Location.eq loc0 loc2 
                            | _ => False end
    
  end.
 
  Definition eq_RobotConf g1 g2 := Location.eq (Loc g1) (Loc g2) /\ eq_State (Sta g1) (Sta g2).

  Definition eq (config₁ config₂ : t) := forall id, eq_RobotConf (config₁ id) (config₂ id).
  
  Declare Instance eq_equiv : Equivalence eq.
  Declare Instance eq_RobotConf_equiv : Equivalence eq_RobotConf.
  Declare Instance eq_State_equiv : Equivalence eq_State.
  Declare Instance eq_bisim : Bisimulation t.
  Declare Instance eq_subrelation : subrelation eq (Logic.eq ==> eq_RobotConf)%signature.
  
  Parameter neq_equiv : forall config₁ config₂,
    ~eq config₁ config₂ <-> exists id, ~eq_RobotConf (config₁ id) (config₂ id).

  Definition get_State (r: RobotConf) := Sta r.
  Declare Instance get_State_compat : Proper (eq_RobotConf ==> eq_State) get_State.

  Definition get_Loc (r:RobotConf) := Loc r.
  Declare Instance get_Loc_compat : Proper (eq_RobotConf ==> Location.eq) get_Loc.

  Definition map (f : RobotConf -> RobotConf) (conf : t) : t := fun id => f (conf id).
  Declare Instance map_compat : Proper ((eq_RobotConf ==> eq_RobotConf) ==> eq ==> eq) map.

  Definition set (conf:t) (id:Names.ident) (rc:RobotConf) : t := 
   fun name => if Names.eq_dec id name then rc else conf name.
  Declare Instance set_compat : Proper (eq ==> Logic.eq ==> eq_RobotConf ==> eq) set.

  Definition mk_RC loc sta : RobotConf := {| Loc := loc; Sta := sta|}.
  Declare Instance mk_RC_compat : Proper (Location.eq ==> eq_State ==> eq_RobotConf) mk_RC.

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


Module Make(Location : DecidableType)(N : Size)(Names : Robots(N)) : Configuration(Location)(N)(Names).
  Inductive State :=
    | RDY2LookCompute
    | RDY2Move (targets: Location.t*Location.t).

  Record RobotConf := { Loc :> Location.t; Sta : State}.

  Definition t := Names.ident -> RobotConf. 

  Definition eq_State (st1 st2 : State) :=  match st1 with 
    | RDY2Move (loc,loc0) => match st2 with 
                            | RDY2Move (loc1,loc2) => Location.eq loc loc1 /\ Location.eq loc0 loc2 
                            | _ => False end
    | RDY2Look => match st2 with | RDY2LookCompute => True | _ => False end
  end.

 
  Lemma State_eq_dec: forall (s1 s2 : State), {eq_State s1 s2} + {~ eq_State s1 s2}.
  Proof.
  intros.
  unfold eq_State; destruct s1,s2; intuition.
  destruct (Location.eq_dec a a0), (Location.eq_dec b b0); intuition.
  Qed.

 

(** A configuration is a mapping from identifiers to locations.  Equality is extensional. *)

  Definition eq_RobotConf g1 g2 := Location.eq (Loc g1) (Loc g2) /\ eq_State (Sta g1) (Sta g2).
  Definition eq (config₁ config₂ : t) := forall id, eq_RobotConf (config₁ id) (config₂ id).
  

Instance eq_State_equiv : Equivalence eq_State.
Proof.
split.
+ intros x. unfold eq_State. destruct x; try reflexivity. destruct targets. split; reflexivity.
+ intros x y. unfold eq_State. destruct x,y; auto; try symmetry; try apply H; try destruct targets; auto.
  destruct targets0. intros H; destruct H; split; symmetry. apply H. apply H0.
+ intros x y z H12 H23. unfold eq_State in *. destruct x,y,z; intuition.
  destruct targets, targets0 in *. auto.
  destruct targets, targets0, targets1, H12, H23 in *; split.
  transitivity t2. apply H. apply H1.
  transitivity t3. apply H0. apply H2.
Qed.
 

Instance eq_RobotConf_equiv : Equivalence eq_RobotConf.
Proof.
split.
+ split; reflexivity.
+ split; symmetry; apply H.
+ split. unfold eq_RobotConf in *.
  transitivity (Loc y).
  apply H.
  apply H0.
  transitivity (Sta y).
  apply H.
  apply H0.
Qed.

Instance eq_equiv : Equivalence eq.
Proof. split.
+ intros conf x. split; reflexivity.
+ intros d1 d2 H r. split; symmetry; apply H.
+ intros d1 d2 d3 H12 H23 x. 
  split;
  unfold eq in *.
  transitivity (Loc (d2 x)).
  apply H12.
  apply H23.
  transitivity (Sta (d2 x)).
  apply H12.
  apply H23.
Qed.



Instance eq_bisim : Bisimulation t.
Proof. exists eq. apply eq_equiv. Defined.

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

Definition get_State (r: RobotConf) := Sta r.

Instance get_State_compat : Proper (eq_RobotConf ==> eq_State) get_State.
Proof.
intros r1 r2 Hr.
unfold eq_RobotConf in *.
destruct Hr.
unfold get_State.
assumption.
Qed.


Definition get_Loc (r:RobotConf) := Loc r.

Instance get_Loc_compat : Proper (eq_RobotConf ==> Location.eq) get_Loc.
Proof. intros r1 r2 Hr. unfold eq_RobotConf, get_Loc in *. destruct Hr; auto. Qed.


Definition set (conf:t) (id:Names.ident) (rc:RobotConf) : t :=  
  fun name => if Names.eq_dec id name then rc else conf name.
 
Instance set_compat : Proper (eq ==> Logic.eq ==> eq_RobotConf ==> eq) set.
Proof.
intros c1 c2 Hconf id1 id2 Hid rc1 rc2 Hrc. 
unfold eq,set, eq_RobotConf.
intros id.
split;
destruct (Names.eq_dec id1 id), (Names.eq_dec id2 id).
apply Hrc.
rewrite <- e in n. exfalso. auto.
exfalso; rewrite <- e in n; auto.
apply Hconf.
apply Hrc.
exfalso; rewrite <- e in n; auto.
exfalso; rewrite <- e in n; auto.
apply Hconf.
Qed.


Definition mk_RC loc sta : RobotConf := {|Loc := loc ; Sta := sta|}.
Instance mk_RC_compat : Proper (Location.eq ==> eq_State ==> eq_RobotConf) mk_RC.
Proof. intros l1 l2 Hl s1 s2 Hs. unfold mk_RC, eq_RobotConf. auto. Qed. 

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

Lemma eq_RobotConf_dec: forall x y, {eq_RobotConf x y} + {~ eq_RobotConf x y}.
Proof.
intros. unfold eq_RobotConf, eq_State.
destruct (Location.eq_dec (Loc x) (Loc y)), (State_eq_dec (Sta x) (Sta y)); intuition.
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
