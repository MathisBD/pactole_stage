Set Implicit Arguments.
Require Import Qcanon.
Require Import Qcabs.
(** * Byzantine Robots *)

(** ** Agents *)

(** We have finetely many robots. Some are good, other are evil. *)
Record finite :=
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
Record automorphism (t : Set)  :=
 { section : t -> t
 ; retraction : t -> t
 ; Inversion : forall x y, section x = y <-> retraction y = x
 }.

(** ** Positions *)
Record position (good bad : finite) :=
 { good_places : (name good) -> Qc
 ; bad_places : (name bad) -> Qc
 }.

(** [automorphism (ident good bad)] is a group (not worth proving it, I guess)
    and acts on positions (not worth proving it is an action group) *)
Definition pos_remap_aux good bad s p (i : ident good bad) :=
  match retraction s i with
  | Good g => good_places p g
  | Bad g => bad_places p g
  end.
Definition pos_remap (k : Qc) good bad s p : position good bad :=
 {| good_places := fun n => k * pos_remap_aux s p (Good good bad n)
  ; bad_places := fun n => k * pos_remap_aux s p (Bad good bad n)
  |}.

(** Equality on positions *)
Record PosEq good bad (p q : position good bad) : Prop :=
 { good_ext : forall n, good_places p n = good_places q n
 ; bad_ext : forall n, bad_places p n = bad_places q n
 }.

(** Imlication on positions.
    A position [p] 'k-implies' a position [q] if there is
    a permutation [s] on the identifiers such that k*s(p)
    (zooming [retraction s p] with a coefficient of [k]) is equal to [q].

    Note that '1-implication' is in fact an equivalence,
    and 'p 0-implies q' is equivalent to saying that [q] is a position
    where every robot is on '0' ([p] is fully unconstrained). *)
Record PosImpl (k : Qc) good bad (p q : position good bad) : Prop :=
 { remap : automorphism (ident good bad)
 ; good_remap : PosEq p (pos_remap k remap q)
 }.

(** Recentering the view (required to be passed to a robogram) for a robot
    centered on this view. *)
Definition center good bad (p : position good bad) (z : Qc) : position good bad
:= {| good_places := fun n => ((good_places p n) - z)%Qc
    ; bad_places := fun n => ((bad_places p n) - z)%Qc
    |}.

(** ** Good robots have a common program, which we call a robogram
    |Todo: find a better name| *)
Record robogram (good bad : finite) :=
 { algo : position good bad -> Qc
 ; AlgoMorph : forall k p q, PosImpl k p q -> algo p = k * algo q
 ; cmove := fun (activated : bool)
                (pos : position good bad)
                (g : name good)
            => let offset := good_places pos g in
               if activated then offset + algo (center pos offset) else offset
 }.

(** ** Demonic schedulers *)
(** A [demonic_action] moves all bad robots
    as it whishes, and select the good robots to be activated for computation *)
Record demonic_action (good bad : finite) :=
 { bad_replace : (name bad) -> Qc
 ; good_activation : (name good) -> bool
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
  | ImmediatelyFair : good_activation (demon_head d) g = true ->
                      LocallyFairForOne g d
  | LaterFair : good_activation (demon_head d) g = false ->
                LocallyFairForOne g (demon_tail d) -> LocallyFairForOne g d
  .

CoInductive Fair good bad (d : demon good bad) : Prop :=
  AlwaysFair : Fair (demon_tail d) -> (forall g, LocallyFairForOne g d) ->
               Fair d.

(** Now we can [execute] some robogram from a given position with a [demon] *)
CoInductive execution good :=
  NextExecution : (name good -> Qc) -> execution good -> execution good.

Definition execution_head good (e : execution good) : (name good -> Qc) :=
  match e with NextExecution gp _ => gp end.

Definition execution_tail good (e : execution good) : execution good :=
  match e with NextExecution _ e => e end.

Definition new_goods good bad (r : robogram good bad)
                     (da : demonic_action good bad) (gp : name good -> Qc)
                     : name good -> Qc
:= fun g => cmove r (good_activation da g)
                  {| good_places := gp ; bad_places := bad_replace da |} g.

Definition execute good bad (r : robogram good bad)
: demon good bad -> (name good -> Qc) -> execution good
:= cofix execute d gp :=
   let ngp := new_goods r (demon_head d) gp in
   NextExecution ngp (execute (demon_tail d) ngp).

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