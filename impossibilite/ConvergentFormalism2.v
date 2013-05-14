Set Implicit Arguments.
Require Import Qcanon.
Require Import Qcabs.
(** * Byzantine Robots *)

(** ** Agents *)

(** We have finetely many robots. Some are good, other are evil. *)
Record finite := Fin
 { name : Set
 ; next : option name -> option name
 ; prev : option name -> option name
 ; NextRel := fun x y => next (Some x) = Some y
 ; PrevRel := fun x y => prev (Some x) = Some y
 ; NextPrev : forall x y, next x = y <-> prev y = x
 ; RecNext : forall z, Acc NextRel z
 ; RecPrev : forall z, Acc PrevRel z
 }.

(** Here are the two kind of robots. *)
Inductive ident (good bad : finite) :=
 | Good : name good -> ident good bad
 | Bad : name bad -> ident good bad.

(** Renaming of agents *)
Record automorphism (t : Set)  := Aut
 { section : t -> t
 ; retraction : t -> t
 ; Automorphism : forall x y, section x = y <-> retraction y = x
 }.

(** Invertible rationals *)
Record invertible := Inv
  { self :> Qc
  ; inverse : Qc
  ; Invertible : self * inverse = 1
  }.

Definition invert (i : invertible) : invertible :=
  {| self := inverse i
   ; inverse := i
   ; Invertible := match Qcmult_comm (inverse i) i in _=x return x = 1 -> _ with
                   | eq_refl => fun H => H end (Invertible i)
   |}.

(** Similarity *)
Record similarity := Sim
  { homo : invertible
  ; centre : Qc
  }.

Bind Scope sim_scope with similarity.
Delimit Scope sim_scope with sim.

Notation "{ k # - c }" := {| homo := k ; centre := c |}.

Definition sim_inv (s : similarity) : similarity :=
  { invert (homo s) # - - inverse (homo s) * centre s }.

(** [sim_fin s] is the function linked to the similarity [s]. *)
Definition sim_fun (s : similarity) : Qc -> Qc :=
  fun q => (homo s) * (q - centre s).

Notation "[: s :]" := (sim_fun s) (format "[: s :]").

(** ** Positions *)
Definition position (t : Set) := t -> Qc.

Bind Scope pos_scope with position.
Delimit Scope pos_scope with pos.

Definition mix_g_b good bad
                   (gp : position (name good)) (bp : position (name bad))
                   : position (ident good bad) :=
  fun x => match x with Good g => gp g | Bad b => bp b end.

Notation "{ gp <+> bp }" := (mix_g_b gp bp) : pos_scope.

(** [automorphism t] is a group (not worth proving it, I guess)
    and acts on positions (not worth proving it is an action group) *)
Definition auto_act (t : Set) (s : automorphism t) (p : position t) :=
  (fun x => p (retraction s x)) : position t.

Notation "s |> p" := (auto_act s p) (at level 20).

(** [similarity] is also a group which acts on a positions.
    This action is used to set the frame of reference for a given robot. *)
Definition sim_act (t : Set) (s : similarity) (p : position t) :=
  (fun x => [:s:] (p x)) : position t.

Notation "s <| p" := (sim_act s p) (at level 20).

(** Equality on positions *)
Definition PosEq (t : Set) (p q : position t) : Prop :=
  forall x, p x = q x.

(** ** Good robots have a common program, which we call a robogram
    |Todo: find a better name| *)
Record robogram (good bad : finite) :=
 { algo : position (ident good bad) -> Qc
 ; AlgoMorph : forall p q s, PosEq q (s |> p) -> algo p = algo q
 }.

(** ** Demonic schedulers *)
(** A [demonic_action] moves all bad robots
    as it whishes, and sets the referential of all good robots it selects.
    A reference of 0 is a special reference meaning that the robot will not
    be activated. Any other reference gives a factor for zooming.
    Note that we do not want the demon give a zoom factor k of 0,
    since to compute the new position we then need to multiply the
    computed result by the inverse of k (which is not defined in this case). *)
Record demonic_action (good bad : finite) :=
 { bad_replace : position (name bad)
 ; good_reference : (name good) -> option invertible
 }.

(** A [demon] is just a stream of [demonic_action]s. *)
CoInductive demon (good bad : finite) :=
  NextDemon : demonic_action good bad -> demon good bad -> demon good bad.

Definition demon_head good bad (d : demon good bad) : demonic_action good bad :=
  match d with NextDemon da _ => da end.

Definition demon_tail good bad (d : demon good bad) : demon good bad :=
  match d with NextDemon _ d => d end.

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
Inductive LocallyFairForOne good bad g (d : demon good bad) : Prop :=
  | ImmediatelyFair : forall i,
                      good_reference (demon_head d) g = Some i ->
                      LocallyFairForOne g d
  | LaterFair : good_reference (demon_head d) g = None ->
                LocallyFairForOne g (demon_tail d) -> LocallyFairForOne g d
  .

CoInductive Fair good bad (d : demon good bad) : Prop :=
  AlwaysFair : Fair (demon_tail d) -> (forall g, LocallyFairForOne g d) ->
               Fair d.

(** Now we can [execute] some robogram from a given position with a [demon] *)
CoInductive execution good :=
  NextExecution : position (name good) -> execution good -> execution good.

Definition execution_head good (e : execution good) : (name good -> Qc) :=
  match e with NextExecution gp _ => gp end.

Definition execution_tail good (e : execution good) : execution good :=
  match e with NextExecution _ e => e end.

Definition new_goods good bad (r : robogram good bad)
                     (da : demonic_action good bad) (gp : name good -> Qc)
                     : name good -> Qc
:= fun g =>
   let t := gp g in
   match good_reference da g with
   | None => t
   | Some i => [:sim_inv {i # - t}:]
               (algo r ({i # - t} <| {gp <+> bad_replace da }))
   end.

Definition execute good bad (r : robogram good bad)
: demon good bad -> (name good -> Qc) -> execution good
:= cofix execute d gp :=
   NextExecution gp (execute (demon_tail d) (new_goods r (demon_head d) gp)).

(** Expressing that all good robots are confined in a small disk. *)
CoInductive imprisonned (prison_center : Qc) (radius : Qc) good
                        (e : execution good) : Prop
:= InDisk : (forall g, [(prison_center - execution_head e g)] <= radius)
            -> imprisonned prison_center radius (execution_tail e)
            -> imprisonned prison_center radius e.

(** The execution will end in a small disk. *)
Inductive attracted (pc : Qc) (r : Qc) good (e : execution good) : Prop :=
  | Captured : imprisonned pc r e -> attracted pc r e
  | WillBeCaptured : attracted pc r (execution_tail e) -> attracted pc r e
  .

(** A solution is just convergence property for any demon. *)
Definition solution good bad (r : robogram good bad) : Prop :=
  forall (gp : name good -> Qc),
  forall (d : demon good bad), Fair d ->
  forall (epsilon : Qc), 0 < epsilon ->
  exists (lim_app : Qc), attracted lim_app epsilon (execute r d gp).

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)