(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain              
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)


Require Import Psatz SetoidDec ZArith Rbase.
Require Import Pactole.Util.Coqlib.
(*Require Import Pactole.Core.Robots.*)
Require Export Pactole.Spaces.Graph.


Typeclasses eauto := (bfs).
Remove Hints eq_setoid.
Open Scope Z_scope.


(** Four cardinal points + self loop *)
Inductive direction :=
  North | South | East | West | Self.

Instance direction_Setoid : Setoid direction := eq_setoid _.

Instance direction_EqDec : EqDec direction_Setoid.
Proof.
intros x y. simpl. change (x = y -> False) with (x <> y). decide equality.
Defined.

(** Vertices are points in Z² and edges are defined by their origin point plus a direction. *)
Notation node := (Z*Z)%type.
Notation edge := (Z*Z*direction)%type.

Instance node_Setoid : Setoid node := eq_setoid _.
Instance node_EqDec : EqDec node_Setoid.
Proof.
intros x y.
destruct (fst x =?= fst y).
+ destruct (snd x =?= snd y).
  - left. abstract (destruct x, y; cbn in *; subst; reflexivity).
  - right. abstract (destruct x, y; injection; auto).
+ right. abstract (destruct x, y; injection; auto).
Defined.

Instance edge_Setoid : Setoid edge := eq_setoid _.
Instance edge_EqDec : EqDec edge_Setoid.
Proof.
intros x y.
destruct (fst x =?= fst y).
+ destruct (snd x =?= snd y).
  - left. abstract (destruct x, y; cbn in *; subst; reflexivity).
  - right. abstract (destruct x, y; injection; auto).
+ right. abstract (destruct x, y; injection; auto).
Defined.

Definition edge_tgt (e : edge) : node :=
  match snd e with
    | North => (fst (fst e), snd (fst e) + 1)
    | South => (fst (fst e), snd (fst e) - 1)
    | East  => (fst (fst e) + 1, snd (fst e))
    | West  => (fst (fst e) - 1, snd (fst e))
    | Self  => fst e
  end.
Arguments edge_tgt !e.

(** The Z² grid is a graph. *)
Instance Z2 : Graph (Z*Z)%type (Z*Z*direction) := {
  src := fst;
  tgt := edge_tgt;
  threshold := fun _ => (1 / 2)%R;
  find_edge := fun x y => if y =?= x then Some (x, Self) else
                          if y =?= (fst x + 1, snd x) then Some (x, East) else
                          if y =?= (fst x, snd x + 1) then Some (x, North) else
                          if y =?= (fst x - 1, snd x) then Some (x, West) else
                          if y =?= (fst x, snd x - 1) then Some (x, South) else None}.
Proof.
* intros _. lra.
* (* find_edge_None *)
  intros x y. repeat destruct_match.
  + abstract (split; try tauto; []; intro He; apply (He (x, Self)); auto).
  + abstract (split; try tauto; []; intro He; apply (He (x, East)); auto).
  + abstract (split; try tauto; []; intro He; apply (He (x, North)); auto).
  + abstract (split; try tauto; []; intro He; apply (He (x, West)); auto).
  + abstract (split; try tauto; []; intro He; apply (He (x, South)); auto).
  + split; intros _; auto; [].
    abstract (intros [x' d] [Hx He]; simpl in Hx; subst x';
              rewrite <- He in *; destruct d; unfold edge_tgt in *; simpl in *; auto).
* (* find_edge_Some *)
  intros x y e. repeat destruct_match; simpl;
  try abstract (solve [ split; intro Heq; subst; unfold edge_tgt; simpl in *; try tauto; [];
              destruct e as [p d], Heq as [? Heq]; simpl in *; f_equal; trivial; [];
              subst; unfold edge_tgt in *;
              destruct p, d; simpl in *; reflexivity || (injection Heq; omega) ]); [].
  split; try tauto; []. intros [].
  abstract (subst; destruct e as [? []]; unfold edge_tgt in *; simpl in *; auto).
Defined.

(** **  Change of frame of reference in Z²  **)

Require Pactole.Util.Bijection.
Require Import Pactole.Core.State.
Require Import Pactole.Core.Formalism.

Instance Loc : Location := {| location := node |}.
(** angle: anglei represents the possible angles for a rotation of reflection:
    - for a rotation: angle i/2 * pi;
    - for a reflection: angle i/4 * pi *)
Inductive angle := angle0 | angle1 | angle2 | angle3.
Instance angle_Setoid : Setoid angle := eq_setoid _.
Instance angle_EqDec : EqDec angle_Setoid.
Proof.
intros x y. simpl.
change (x = y -> False) with (x <> y).
decide equality.
Defined.

Definition opp_angle (r : angle) :=
  match r with
    | angle0 => angle0
    | angle1 => angle3
    | angle2 => angle2
    | angle3 => angle1
  end.

(** ***  Some bijections used in changes of frame of reference  **)

(** Translation *)
Definition translation (v : Z*Z) : Bijection.bijection (Z*Z).
 refine {| Bijection.section := fun x => (fst x + fst v, snd x + snd v);
           Bijection.retraction := fun x => (fst x - fst v, snd x - snd v) |}.
Proof.
intros x y. simpl.
abstract (split; intro; subst; destruct x || destruct y; f_equal; simpl; omega).
Defined.

Instance translation_compat : Proper (equiv ==> equiv) translation.
Proof. intros ? ? Heq x. now rewrite Heq. Qed.

(** Rotation *)
Definition mk_rotation r : Z*Z -> Z*Z :=
  match r with
    | angle0 => fun x => x
    | angle1 => fun x => (- snd x, fst x)
    | angle2 => fun x => (- fst x, - snd x)
    | angle3 => fun x => (snd x, - fst x)
  end.

Definition rotation (r : angle) : Bijection.bijection (Z*Z).
 refine {| Bijection.section := mk_rotation r;
           Bijection.retraction := mk_rotation (opp_angle r) |}.
Proof.
intros x y. simpl.
abstract (split; intro; subst; destruct r; simpl; destruct x || destruct y; simpl; f_equal; omega).
Defined.

Instance rotation_compat : Proper (equiv ==> equiv) rotation := reflexive_proper _.

(** Reflection *)
Definition mk_reflection r : Z*Z -> Z*Z :=
  match r with
    | angle0 => fun x => (fst x, - snd x)
    | angle1 => fun x => (snd x, fst x)
    | angle2 => fun x => (- fst x, snd x)
    | angle3 => fun x => (- snd x, - fst x)
  end.

Definition reflection (r : angle) : Bijection.bijection (Z*Z).
 refine {| Bijection.section := mk_reflection r;
           Bijection.retraction := mk_reflection r |}.
Proof.
intros x y. simpl.
abstract (split; intro; subst; destruct r; simpl; destruct x || destruct y; simpl; f_equal; omega).
Defined.

Instance reflection_compat : Proper (equiv ==> equiv) reflection := reflexive_proper _.

(** ***  Change of frame of reference  **)

(** Translation  **)
Instance FCTranslation : frame_choice (Z*Z) := {|
  frame_choice_bijection := translation;
  frame_choice_Setoid := _;
  frame_choice_bijection_compat := _ |}.

(** Rigid Motion  **)
Instance FCRigidMotion : frame_choice (Z*Z*angle) := {|
  frame_choice_bijection := fun rm => compose (rotation (snd rm)) (translation (fst rm));
  frame_choice_Setoid := prod_Setoid node_Setoid angle_Setoid |}.
Proof. abstract (intros ? ? [Hv Ha]; do 2 f_equiv; assumption). Defined.

(** Similarities *)
Instance FCSimilarity : frame_choice (bool*(Z*Z)*angle)%type := {|
  frame_choice_bijection := fun '(b,v,a) =>
    compose (rotation a)
   (compose (translation v)
            (if b : bool then reflection angle0 else @Bijection.id node _));
  frame_choice_Setoid := prod_Setoid (prod_Setoid bool_Setoid node_Setoid) angle_Setoid |}.
Proof.
intros [[b1 v1] a1] [[b2 v2] a2] [[Hb Hv] Ha]. cbn -[equiv] in *.
repeat f_equiv; trivial; []. now rewrite Hb.
Qed.
