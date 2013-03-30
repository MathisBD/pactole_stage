Set Implicit Arguments.
Require Import Qcanon.
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
 ; AlgoMorph : forall k p q, PosImpl k p q -> k * algo p = algo q
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

(** How to go from one position to the other. *)
Definition itere good bad (p : position good bad) (r : robogram good bad)
                 (d : demonic_action good bad) : position good bad :=
 {| good_places := fun g => cmove r (good_activation d g) p g
  ; bad_places := bad_replace d
  |}.

(** Execution of a demon. *)
Definition run good bad (r : robogram good bad)
                        (d : position good bad -> demonic_action good bad)
                        (p : position good bad)
: nat -> position good bad
:= fix run n :=
   match n with
   | O => p
   | S n => itere (run n) r (d (run n))
   end.

(** A [demon] is a strategy for the scheduler. *)
Record demon (good bad : finite) (r : robogram good bad) :=
 { strategy : position good bad -> demonic_action good bad
 ; Fairness : forall g p, exists n,
              good_activation (strategy (run r strategy p n)) g = true
 }.

(** Expressing that all good robots are confined in a small disk. *)
Definition imprisonned (prison_center : Qc) (square_radius : Qc)
                       good bad (r : robogram good bad) (d : demon r)
                       (p : position good bad) :=
  forall g n, let d := good_places (run r (strategy d) p n) g - prison_center in
              d*d < square_radius.

(** A solution is just convergence property for any demon. *)
Definition solution good bad (r : robogram good bad) : Prop :=
  forall (d : demon r) (p : position good bad) (epsilon : Qc),
  (epsilon <> 0)%Qc ->
  exists (N : nat) (pc : Qc),
  imprisonned pc (epsilon * epsilon) d (run r (strategy d) p N).

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)