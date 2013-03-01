Set Implicit Arguments.
Require Import ZArith.
(** * Byzantine Robots *)

(** ** Agents *)

(** We have finetely many robots. Some are good, other are evil. *)
Record finite :=
 { name : Set
 ; next : name -> option name
 ; prev : name -> option name
 ; NextRel := fun x y => next x = Some y
 ; PrevRel := fun x y => prev x = Some y
 ; NextPrev : forall x y, NextRel x y <-> PrevRel y x
 ; RecNext : forall z, Acc NextRel z
 ; RecPrev : forall z, Acc PrevRel z
 }.

(** Here are the two kind of robots. *)
Inductive ident (good bad : finite) :=
 | Good : name good -> ident good bad
 | Bad : name bad -> ident good bad.

(** Renaming of agents *)
Record ident_split (good bad : finite)  :=
 { section : ident good bad -> ident good bad
 ; retraction : ident good bad -> ident good bad
 ; Inversion : forall a, retraction (section a) = a
 }.

(** ** Positions *)
Record position (good bad : finite) :=
 { good_places : (name good) -> Z
 ; bad_places : (name bad) -> Z
 }.
(* Je ne suis pas sur que prendre Z soit ideal.
   Le probleme avec deux robots gentils, zero mechants,
   un scheduler qui active systematiquement tout le monde,
   et deux robots separes de seulement une case n'a pas de solution
   dans mon formalisme (l'espace entre les robots reste constamment
   impair)
*)

(** [ident_split] is a group (not worth proving it, I guess)
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
Record PosEq good bad (p q : position good bad) : Prop :=
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
Record PosEquiv good bad (p q : position good bad) : Prop :=
 { remap : ident_split good bad
 ; good_remap : PosEq p (pos_remap remap q)
 }.

(** ** Good robots have a common program, which we call a robogram
    |Todo: find a better name| *)
Record robogram (good bad : finite) :=
 { move : position good bad -> Z
 ; MoveMorph : forall p q, PosEquiv p q -> move p = move q
 ; MoveAntimorph : forall p, move (flip p) = (-(move p))%Z
 }.
(* Je commente un peu ici.
   Dans cette situation, le robogram a tout de même une info pas forcement
   souhaitable : le nombre de robots byzantins. On ne sait pas qui est
   byzantin, mais on sait combien il y en a. Cependant, je ne pense pas
   que ce soit genant : un robogramme doit être robuste contre un nombre
   maximal de byzantins. Ce nombre maximal peut etre connu du robogramme,
   et n'importe quel robogramme robuste contre n byzantins l'est aussi
   automatiquement pour m byzantins avec m<n (sinon il suffirait que
   le demon utilise le robogramme pour (n-m) mechants robots).

   Si j'ai bien compris votre code initial et ce que m'a dit Xavier une
   fois, move ne devrait pas etre une fonction, mais une relation
   (non determinisme). Cela pourrait peut etre resoudre le probleme des
   positions (voir mon commentaire sur [position]), mais ca risque de
   compliquer des trucs.
*)

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
(* Si on utilise une relation pour les gentils robots, itere doit
   etre transforme en relation.
*)

(** Now we expect some fairness property: from a given position, a given
    robot will be moved by an iteration sooner or later. *)
Inductive FairForOne good bad (r : robogram good bad)
          (s : position good bad -> demonic_action good bad)
          (g : name good) (p : position good bad) : Prop :=
 | immediate : (if good_activation (s p) g then True else False)
               -> FairForOne r s g p
 | delayed : FairForOne r s g (itere p r (s p)) ->
             FairForOne r s g p.
(* C'est la que les choses se compliquent si [move] est une relation,
   puisqu'il faut preciser si la fairness doit ou non etre independante
   du choix de transition. *)

(** A [demon] is a strategy for the scheduler. *)
Record demon (good bad : finite) (r : robogram good bad) :=
 { strategy : position good bad -> demonic_action good bad
 ; Fairness : forall g p, FairForOne r strategy g p
 }.

(* Je n'ai pas encore decrit ce qu'est une solution au probleme.
   La encore se pose le probleme de [move] fonctionnel ou relationnel,
   avec pas mal de subtilites. Il faut en discuter pour voir ce qu'on
   veut exactement.
*)
