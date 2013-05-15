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
Definition pos_remap good bad s p :=
  let pos_remap := fun i =>
  match retraction s i with
  | Good g => good_places p g
  | Bad g => bad_places p g
  end
  in {| good_places := fun g => pos_remap (Good good bad g)
      ; bad_places := fun b => pos_remap (Bad good bad b) |}.

(** [similarity k t p] returns a position [p] centered in [t] and zoomed of
    a factor [k]; this function is used to set the frame of reference for
    a given robot. *)
Definition similarity (k t : Qc) good bad p : position good bad :=
 {| good_places := fun n => k * (good_places p n - t)
  ; bad_places := fun n => k * (bad_places p n - t)
  |}.

(** Equality on positions *)
Record PosEq good bad (p q : position good bad) : Prop :=
 { good_ext : forall n, good_places p n = good_places q n
 ; bad_ext : forall n, bad_places p n = bad_places q n
 }.

(** ** Good robots have a common program, which we call a robogram
    |Todo: find a better name| *)
Record robogram (good bad : finite) :=
 { algo : position good bad -> Qc
 ; AlgoMorph : forall p q s, PosEq q (pos_remap s p) -> algo p = algo q
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
 { bad_replace : (name bad) -> Qc
 ; good_reference : (name good) -> Qc
 }.

(** A [demon] is just a stream of [demonic_action]s. *)
CoInductive demon (good bad : finite) :=
  NextDemon : demonic_action good bad -> demon good bad -> demon good bad.

Definition demon_head good bad (d : demon good bad) : demonic_action good bad :=
  match d with NextDemon da _ => da end.

Definition demon_tail good bad (d : demon good bad) : demon good bad :=
  match d with NextDemon _ d => d end.

Inductive inverse (k : Qc) :=
  | IsNul : k = 0 -> inverse k
  | Inv : forall l, l * k = 1 -> inverse k.

Definition inv (k : Qc) : inverse k :=
  match Qc_eq_dec k 0 with
  | left H => IsNul H
  | right H => Inv (Qcmult_inv_l k H)
  end.

(** A [demon] is [Fair] if at any time it will later activate any robot. *)
Inductive LocallyFairForOne good bad g (d : demon good bad) : Prop :=
  | ImmediatelyFair : forall l H,
                      inv (good_reference (demon_head d) g) = @Inv _ l H ->
                      LocallyFairForOne g d
  | LaterFair : forall H, inv (good_reference (demon_head d) g) = IsNul H ->
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
:= fun g =>
   let k := good_reference da g in
   let t := gp g in
   match inv k with
   | IsNul _ => t
   | Inv l _ => t + l * (algo r (similarity k t {| good_places := gp
                                                 ; bad_places := bad_replace da
                                                 |}))
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