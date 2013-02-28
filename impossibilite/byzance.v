Set Implicit Arguments.
Require Import ZArith.
(** * Byzantine Robots *)

(** ** Agents *)

(** We have finetely many robots. Some are good, other are evil. *)
Record finite :=
 { name : Set
 ; next : option name -> option name
 ; rec_on_names : forall z, Acc (fun x y => next (Some x) = Some y) z
 }.

(** Here are the two kind of robots. *)
Inductive ident (good bad : finite) :=
 | Good : name good -> ident good bad
 | Bad : name bad -> ident good bad.

(** Renaming of agents *)
Record ident_split (good bad : finite)  :=
 { section : ident good bad -> ident good bad
 ; retraction : ident good bad -> ident good bad
 ; inversion : forall a, retraction (section a) = a
 }.

(** ** Positions *)
Record position (good bad : finite) :=
 { good_places : (name good) -> Z
 ; bad_places : (name bad) -> Z
 }.

(** [ident_split] is a group (not worth proving it, I guess)
    and acts on positions (not worth proving it is an action group) *)
Definition pos_remap good bad (s : ident_split good bad)
                              (p : position good bad) : position good bad :=
 let pos_remap_aux := fun i => match retraction s i with
                               | Good g => good_places p g
                               | Bad b => bad_places p b
                               end
 in
 {| good_places := fun n => pos_remap_aux (Good good bad n)
  ; bad_places := fun n => pos_remap_aux (Bad good bad n)
  |}.

(** Equality on positions *)
Record pos_eq good bad (p q : position good bad) : Prop :=
 { good_ext : forall n, good_places p n = good_places q n
 ; bad_ext : forall n, bad_places p n = bad_places q n
 }.

(** Flipping a position (left <-> right) *)
Definition flip good bad (p : position good bad) : position good bad :=
 {| good_places := fun n => (-(good_places p n))%Z
  ; bad_places := fun n => (-(bad_places p n))%Z
  |}.

(** Equivalence of positions. Two positions are equivalent, if they
    are equal up to a full renaming of robots regardless of their nastiness. *)
Record pos_equiv good bad (p q : position good bad) : Prop :=
 { remap : ident_split good bad
 ; good_remap : pos_eq p (pos_remap remap q)
 }.

(** ** Good robots have a common program, which we call a robogram
    |Todo: find a better name| *)
Record robogram (good bad : finite) :=
 { move : position good bad -> Z
 ; move_morph : forall p q, pos_equiv p q -> move p = move q
 ; move_antimorph : forall p, move (flip p) = (-(move p))%Z
 }.

(** Recentering the view (required to be passed to a robogram) for a robot
    centered on this view. *)
Definition center good bad (p : position good bad) (z : Z) : position good bad
:= {| good_places := fun n => ((good_places p n) - z)%Z
    ; bad_places := fun n => ((bad_places p n) - z)%Z
    |}.

(** ** Demonic schedulers *)
(** A [demonic_action] moves all bad robots
    as it whishes, and select the good robots to be activated for computation *)
Record demonic_action (good bad : finite) :=
 { bad_replace : (name bad) -> Z
 ; good_activation : (name good) -> bool
 }.

(** How to go from one position to the other. *)
Definition itere good bad (p : position good bad) (r : robogram good bad)
                 (d : demonic_action good bad) : position good bad :=
 {| good_places :=
    fun n => let z := good_places p n in
             if good_activation d n
             then (z + move r (center p z))%Z
             else z
  ; bad_places := bad_replace d
  |}.

(** Now we expect some fairness property: from a given position, a given
    robot will be moved by an iteration sooner or later. *)
Inductive fair_for_one good bad (r : robogram good bad)
          (s : position good bad -> demonic_action good bad)
          (g : name good) (p : position good bad) : Prop :=
 | Immediate : (if good_activation (s p) g then True else False)
               -> fair_for_one r s g p
 | Delayed : fair_for_one r s g (itere p r (s p)) ->
             fair_for_one r s g p.

(** A [demon] is a strategy for the scheduler. *)
Record demon (good bad : finite) (r : robogram good bad) :=
 { strategy : position good bad -> demonic_action good bad
 ; fairness : forall g p, fair_for_one r strategy g p
 }.
