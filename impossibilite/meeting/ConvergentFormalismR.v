(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, X. Urbain                                     *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Set Implicit Arguments.
Require Import Utf8.
Require Import Reals.
Open Scope R_scope.


Lemma Rdec : forall x y : R, {x = y} + {x <> y}.
Proof.
intros x y. destruct (Rle_dec x y). destruct (Rle_dec y x).
  left. now apply Rle_antisym.
  right; intro; subst. contradiction.
  right; intro; subst. pose (Rle_refl y). contradiction.
Qed.

Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].


(** * Byzantine Robots *)

(** ** Agents *)

(** We have finetely many robots. Some are good, other are evil. *)
Record finite :=
 { name :> Set
 ; next : option name → option name
 ; prev : option name → option name
 ; NextRel := fun x y => next (Some x) = Some y
 ; PrevRel := fun x y => prev (Some x) = Some y
 ; NextPrev : ∀ x y, next x = y ↔ prev y = x
 ; RecNext : ∀ z, Acc NextRel z
 ; RecPrev : ∀ z, Acc PrevRel z
 }.

(* For clarity's sake we will write location for robots location, and Qc for
   zooming factor and translation vectors. Obviously these ar all rationals and
   we will:
 - multiply locations by zooming factor and obtain new locations
 - add locations and vectors and obtain new locations. *)
Notation location := R (only parsing).

Section goodbyz. (* Remove to have notations outside it *)

(** Here are the two kinds of robots. *)
Variable G B : finite.

(** Disjoint union of both kinds od robots is obtained by a sum type. *)
Inductive ident :=
 | Good : G → ident
 | Byz : B → ident.
(* TODO: rename into robots? GB? *)

Record automorphism (t : Set)  :=
 { section :> t → t
 ; retraction : t → t
 ; Inversion : ∀ x y, section x = y ↔ retraction y = x
 }.

Notation "s ⁻¹" := (s.(retraction)) (at level 99).

(** Renaming of agents are bijections *)
Definition permutation := automorphism.

Definition id_perm : automorphism (ident).
refine {| section := fun x => x
        ; retraction := fun x => x
        |}.
abstract (unfold id; split; auto).
Defined.

(* [automorphism (ident good byz)] is a group (not worth proving it, I guess)
   and acts on positions (not worth proving it is an action group) *)

(** ** Positions *)

(** We explicitely say that a permutation has a different treatment for good and
   byzantine robots, because later we will consider that byzantine positions are
   chosen by the demon whereas positions of good robots will be computed by its
   algorithm. *)
Record position :=
 { gp : G → location
 ; bp : B → location
 }.
(* TODO rename it into gpbp? notation gp+bp? *)


(** Locating a robot in a position. *)
Definition locate p (id: ident): location :=
  match id with
  | Good g => p.(gp) g
  | Byz b => p.(bp) b
  end.

(** Extension of a robots substitution to a subtitution of robots locations in a
    position. *)
Definition subst_pos σ (p:position) :=
  {| gp := fun g => locate p (σ (Good g)) ;
     bp := fun b => locate p (σ (Byz b)) |}.

(** Notation of the paper *)
Notation "p '∘' s" := (subst_pos s p) (at level 20, only parsing).

(** ** Similarities  *)

(** [similarity k t p] returns a position [p] centered in [t] and zoomed of
    a factor [k]; this function is used to set the frame of reference for
    a given robot. *)
Definition similarity (k t : R) p : position :=
 {| gp := fun n => k * (p.(gp) n - t)
  ; bp := fun n => k * (p.(bp) n - t)
  |}.

(** Notation of the paper. *)
Notation "'⟦' k ',' t '⟧'" := (similarity k t) (at level 99, format "'⟦' k ','  t '⟧'").

(** ** Equalities on positions *)

(** A position is a pair of location functions. Equality on positions is the
    extentional equality of the two location functions. *)
Record PosEq (p q : position) : Prop :=
 { good_ext : ∀ n, p.(gp) n = q.(gp) n
 ; byz_ext  : ∀ n, p.(bp) n = q.(bp) n }.

(** ** The program of correct robots *)

(** ** Good robots have a common program, which we call a robogram
    |Todo: find a better name| *)
Record robogram :=
 { algo : position → location
 ; AlgoMorph : ∀ p q σ, PosEq q (p ∘ (σ ⁻¹)) → algo p = algo q }.

(** ** Demonic schedulers *)
(** A [demonic_action] moves all byz robots
    as it whishes, and sets the referential of all good robots it selects.
    A reference of 0 is a special reference meaning that the robot will not
    be activated. Any other reference gives a factor for zooming.
    Note that we do not want the demon give a zoom factor k of 0,
    since to compute the new position we then need to multiply the
    computed result by the inverse of k (which is not defined in this case). *)
Record demonic_action :=
  {
    locate_byz : B → location
    ; frame : G → R
  }.



(** A [demon] is just a stream of [demonic_action]s. *)
CoInductive demon :=
  NextDemon : demonic_action → demon → demon.

(** *** Destructors *)

Definition demon_head (d : demon) : demonic_action :=
  match d with NextDemon da _ => da end.

Definition demon_tail (d : demon) : demon :=
  match d with NextDemon _ d => d end.

(** ** Fairness *)

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
Inductive LocallyFairForOne g (d : demon) : Prop :=
  | ImmediatelyFair : frame (demon_head d) g ≠ 0 → LocallyFairForOne g d
  | LaterFair : frame (demon_head d) g = 0 → 
                LocallyFairForOne g (demon_tail d) → LocallyFairForOne g d.

CoInductive Fair (d : demon) : Prop :=
  AlwaysFair : (∀ g, LocallyFairForOne g d) → Fair (demon_tail d) →
               Fair d.

(** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the demon never
  return a null reference. *)


(** A demon is fully synchronous for one particular good robot g at the first
    step. *)
Inductive FullySynchronousForOne g d:Prop :=
  ImmediatelyFair2:
    (frame (demon_head d) g) ≠ 0 → 
                      FullySynchronousForOne g d.
(* instead of ≠ 0, we may put:
 ∀ l H, inv (frame (demon_head d) g) = @Inv _ l H → *)

(** A demon is fully synchronous if it is fully synchronous for all good robots
    at all step. *)
CoInductive FullySynchronous d :=
  NextfullySynch:
    (∀ g, FullySynchronousForOne g d)
    → FullySynchronous (demon_tail d)
    → FullySynchronous d.


Lemma local_fully_synchronous_implies_fair: ∀ g d, FullySynchronousForOne g d → LocallyFairForOne g d.
Proof. induction 1. now constructor. Qed.


Lemma fully_synchronous_implies_fair: ∀ d, FullySynchronous d → Fair d.
Proof.
coinduction fully_fair.
- intro. apply local_fully_synchronous_implies_fair. apply H.
- now inversion H.
Qed.

(** ** Executions *)

(** Now we can [execute] some robogram from a given position with a [demon] *)
CoInductive execution :=
  NextExecution : (G → location) → execution → execution.

(** *** Destructors *)

Definition execution_head (e : execution) : (G → location) :=
  match e with NextExecution gp _ => gp end.

Definition execution_tail (e : execution) : execution :=
  match e with NextExecution _ e => e end.

Definition round (r : robogram) (da : demonic_action) (gp : G → location) : G → location
:= fun g =>
   let k := da.(frame) g in
   let t := gp g in
   (* l allows getting back the move in the scheduler reference from the move in
      the robot's local reference *)
   if Rdec k 0 then t else t + /k * (algo r (⟦k, t⟧ {| gp := gp; bp := locate_byz da |})).

Definition execute (r : robogram): demon → (G → location) → execution :=
  cofix execute d gp :=
  NextExecution gp (execute (demon_tail d) (round r (demon_head d) gp)).

Lemma execute_tail : forall (r : robogram) (d : demon) gp,
  execution_tail (execute r d gp) = execute r (demon_tail d) (round r (demon_head d) gp).
Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.

(** ** Properties of executions  *)

(** Expressing that all good robots are confined in a small disk. *)
CoInductive imprisonned (center : location) (radius : R) (e : execution) : Prop
:= InDisk : (∀ g, Rabs (center - execution_head e g) <= radius)
            → imprisonned center radius (execution_tail e)
            → imprisonned center radius e.

(** The execution will end in a small disk. *)
Inductive attracted (center : location) (radius : R) (e : execution) : Prop :=
  | Captured : imprisonned center radius e → attracted center radius e
  | WillBeCaptured : attracted center radius (execution_tail e) → attracted center radius e.

(** A solution is just convergence property for any demon. *)
Definition solution (r : robogram) : Prop :=
  ∀ (gp : G → location),
  ∀ (d : demon), Fair d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : location), attracted lim_app epsilon (execute r d gp).


(** A solution is just convergence property for any demon. *)
Definition solution_FSYNC (r : robogram) : Prop :=
  ∀ (gp : G → location),
  ∀ (d : demon), FullySynchronous d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : location), attracted lim_app epsilon (execute r d gp).


Lemma solution_FAIR_FSYNC : ∀ r, solution r → solution_FSYNC r.
Proof.
  intros r H.
  unfold solution_FSYNC, solution in *.
  intros gp d H0.
  apply H.
  now apply fully_synchronous_implies_fair.
Qed.

End goodbyz.

Notation "s ⁻¹" := (s.(retraction)) (at level 99).
Notation "p '∘' s" := (subst_pos s p) (at level 20, only parsing).
Notation "'⟦' k ',' t '⟧'" := (similarity k t) (at level 40, format "'⟦' k ','  t '⟧'").

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)