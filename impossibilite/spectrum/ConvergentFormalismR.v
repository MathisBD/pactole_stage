(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, X. Urbain, L. Rieg                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Set Implicit Arguments.
Require Import Utf8.
Require Import Sorting.
Import Permutation.
Require Import Reals.
Open Scope R_scope.
Require Import List.
Open Scope list_scope.
Require Import MSets.
Require Export Preliminary.
Require Vector.

Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].


(** * Byzantine Robots *)

(** ** Agents *)


(* For clarity's sake we will write location for robots location, and R for
   zooming factor and translation vectors. Obviously these ar all reals and
   we will:
 - multiply locations by zooming factor and obtain new locations
 - add locations and vectors and obtain new locations. *)
Notation location := R (only parsing).


(** We have finetely many robots. Some are good, other are evil. *)

Fixpoint Vfin_map n A (f : Fin.t n -> A) {struct n} : Vector.t A n :=
  match n as n' return n = n' -> Vector.t A n' with
    | 0 => fun _ => (Vector.nil _)
    | S m => fun Heq => Vector.cons A (f (eq_rec_r _ Fin.F1 Heq)) m
                                      (Vfin_map (fun x => f (eq_rec_r _ (Fin.FS x) Heq)))
  end (reflexivity n).

Fixpoint fin_map n A (f : Fin.t n -> A) {struct n} : list A :=
  match n as n' return n = n' -> list A with
    | 0 => fun _ => nil
    | S m => fun Heq => cons (f (eq_rec_r _ Fin.F1 Heq)) (fin_map (fun x => f (eq_rec_r _ (Fin.FS x) Heq)))
  end (reflexivity n).

Lemma Vfin_fin_map : forall n A (f : Fin.t n -> A), fin_map f = Vector.to_list (Vfin_map f).
Proof.
induction n; intros A f; simpl; unfold Vector.to_list.
  reflexivity.
  f_equal. rewrite IHn. reflexivity.
Qed.

Theorem In_fin_map : forall n A g (f : Fin.t n -> A), In (f g) (fin_map f).
Proof.
intros n A g f. destruct n.
  now apply Fin.case0.
  revert n g f. apply (Fin.rectS (fun n g => ∀ f : Fin.t (S n) → A, In (f g) (fin_map f))).
    intros n f. now left.
    intros n g IHn f. right. apply (IHn (fun x => f (Fin.FS x))).
Qed.

Theorem map_fin_map : forall n A B (f : A -> B) (h : Fin.t n -> A),
  fin_map (fun x => f (h x)) = List.map f (fin_map h).
Proof.
intros n A B f h. induction n.
  reflexivity.
  simpl. f_equal. now rewrite IHn.
Qed.

Lemma fin_map_length : forall n A (f : Fin.t n -> A), length (fin_map f) = n.
Proof.
intros n A f. induction n.
  reflexivity.
  simpl. now rewrite IHn.
Qed.

Section goodbyz. (* Remove to have notations outside it *)

Variables nG nB : nat.
Definition G : Set := Fin.t nG.
Definition B := Fin.t nB.

(** Disjoint union of both kinds of robots is obtained by a sum type. *)
(* TODO: replace this by (G ⊎ B). *)
Inductive ident :=
 | Good : G → ident
 | Byz : B → ident.
(* TODO: rename into robots? GB? *)

Record automorphism (t : Type) :=
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
Definition locate pos (id: ident): location :=
  match id with
  | Good g => pos.(gp) g
  | Byz b => pos.(bp) b
  end.

(** Extension of a robots substitution to a subtitution of robots locations in a
    position. *)
Definition subst_pos σ (pos : position) :=
  {| gp := fun g => locate pos (σ (Good g)) ;
     bp := fun b => locate pos (σ (Byz b)) |}.

(** Notation of the paper *)
Notation "pos '∘' s" := (subst_pos s pos) (at level 40, only parsing, left associativity).

(** ** Similarities  *)

(** Pointwise mapping of a function on a position *)
Definition map_pos (f : location -> location) (pos : position) :=
 {| gp := fun g => f (pos.(gp) g)
  ; bp := fun b => f (pos.(bp) b)
  |}.

(** [similarity k t p] returns a position [p] centered in [t] and zoomed of
    a factor [k]; this function is used to set the frame of reference for
    a given robot. *)
Definition similarity (k t : R) p : position := map_pos (fun x => k * (x - t)) p.

(** Notation of the paper. *)
Notation "'⟦' k ',' t '⟧'" := (similarity k t) (at level 99, format "'⟦' k ','  t '⟧'").

(** ** Equalities on positions *)

Definition ExtEq {T U} (f g : T -> U) := forall x, f x = g x.

(** A position is a pair of location functions. Equality on positions is the
    extentional equality of the two location functions. *)
Record PosEq (pos₁ pos₂ : position) : Prop := {
  good_ext : ∀g, pos₁.(gp) g = pos₂.(gp) g;
  byz_ext  : ∀b, pos₁.(bp) b = pos₂.(bp) b}.

Lemma map_inverse : forall (f g : location -> location) (pos : position),
  (forall x, f (g x) = x) -> PosEq (map_pos f (map_pos g pos)) pos.
Proof. intros f g pos Hinv. now split; intros; simpl; rewrite Hinv. Qed.

Corollary similarity_inverse : forall k t pos, k <> 0 -> PosEq (⟦ /k, -k*t⟧ (⟦k, t⟧ pos)) pos.
Proof. intros k t pos Hk. split; intros; simpl; now field. Qed.

Definition spectrum := list location.

Definition nominal_spectrum (pos : position): spectrum := fin_map pos.(gp) ++ fin_map pos.(bp).

Lemma In_spectrum : forall (pos : position) (r : ident), List.In (locate pos r) (nominal_spectrum pos).
Proof.
intros pos r. unfold nominal_spectrum. rewrite in_app_iff. destruct r as [g | b]; simpl.
  left. now apply In_fin_map.
  right. now apply In_fin_map.
Qed.

Lemma nominal_spectrum_map : forall f pos, nominal_spectrum (map_pos f pos) = List.map f (nominal_spectrum pos).
Proof.
intros. unfold nominal_spectrum. simpl. rewrite map_fin_map. rewrite map_app. f_equal. now rewrite map_fin_map.
Qed.

Corollary nominal_spectrum_similarity : forall k t pos,
  nominal_spectrum (⟦ k, t⟧ pos) = List.map (fun x => k * (x - t)) (nominal_spectrum pos).
Proof. intros. apply nominal_spectrum_map. Qed.

Lemma size_nominal_spectrum : forall pos, length (nominal_spectrum pos) = (nG + nB)%nat.
Proof. intro. unfold nominal_spectrum. rewrite app_length. now do 2 rewrite fin_map_length. Qed.

Definition is_spectrum s p: Prop := Permutation s (nominal_spectrum p).

(** ** The program of correct robots *)

(** ** Good robots have a common program, which we call a robogram
    |Todo: find a better name| *)
Definition robogram := spectrum → location.
(*Record robogram :=
 { algo : position → location
 ; AlgoMorph : ∀ p q σ, PosEq q (p ∘ (σ ⁻¹)) → algo p = algo q }.*)

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
    ; spectrum_of : G → (position → spectrum)
    ; spectrum_ok : forall g:G, forall p:position, is_spectrum (spectrum_of g p) p
    ; spectrum_exteq : forall g pos1 pos2, PosEq pos1 pos2 -> spectrum_of g pos1 = spectrum_of g pos2
      (* can be omitted if we sort the spectra in [round]. *)
  }.



(** A [demon] is just a stream of [demonic_action]s. *)
CoInductive demon :=
  NextDemon : demonic_action → demon → demon.

(** Destructors for demons, getting the head demonic action or the
    tail of the demon. *)

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

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k, frame (demon_head d) g <> 0 -> Between g h d k
| kReduce : forall k, frame (demon_head d) g = 0 -> frame (demon_head d) h <> 0 ->
                      Between g h (demon_tail d) k -> Between g h d (S k)
| kStall : forall k, frame (demon_head d) g = 0 -> frame (demon_head d) h = 0 ->
                     Between g h (demon_tail d) k -> Between g h d k.



(* k-fair: every robot g is activated within at most k activation of any other robot h *)
CoInductive kFair k (d : demon) :=
  AlwayskFair : (forall g h, Between g h d k) -> kFair k (demon_tail d) ->
                kFair k d.

Lemma Between_LocallyFair : forall g (d : demon) h k,
  Between g h d k -> LocallyFairForOne g d.
Proof.
  intros g h d k Hg. induction Hg.
  now constructor 1.
  now constructor 2.
  now constructor 2.
Qed.

(** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
Lemma Between_same :
  forall g (d : demon) k, LocallyFairForOne g d -> Between g g d k.
Proof.
  intros g d k Hd. induction Hd.
  now constructor 1.
  now constructor 3.
Qed.

(** A k-fair demon is fair. *)
Theorem kFair_Fair : forall k (d : demon), kFair k d -> Fair d.
Proof.
  coinduction kfair_is_fair.
  destruct H. intro. apply Between_LocallyFair with g k. now apply b.
  apply (kfair_is_fair k). now destruct H.
Qed.

(* FIXME: rename? *)
(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_ord : forall g h (d : demon) k,
  Between g h d k -> forall k', (k <= k')%nat -> Between g h d k'.
Proof.
  intros g h d k Hd. induction Hd; intros k' Hk.
  now constructor 1.
  destruct k'.
    now inversion Hk.
    constructor 2; assumption || now (apply IHHd; omega).
  constructor 3; assumption || now (apply IHHd; omega).
Qed.

(* FIXME: rename? *)
(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_ord : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
  coinduction fair; destruct H.
  - intros. now apply Between_ord with k.
  - now apply (fair k).
Qed.

Theorem Fair0 : forall d, kFair 0 d ->
  forall g h, (demon_head d).(frame) g = 0 <-> (demon_head d).(frame) h = 0.
Proof.
intros d Hd g h. destruct Hd as [Hd _]. split; intro H.
  assert (Hg := Hd g h). inversion Hg. contradiction. assumption.
  assert (Hh := Hd h g). inversion Hh. contradiction. assumption.
Qed.

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


(** A locally synchronous demon is fair *)
Lemma local_fully_synchronous_implies_fair:
  ∀ g d, FullySynchronousForOne g d → LocallyFairForOne g d.
Proof. induction 1. now constructor. Qed.

(** A synchronous demon is fair *)
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

(** *** Destructors for demons *)

Definition execution_head (e : execution) : (G → location) :=
  match e with NextExecution gp _ => gp end.

Definition execution_tail (e : execution) : execution :=
  match e with NextExecution _ e => e end.

(** [round r da gp] return the new position of good robots (that is a function
    giving the position of each good robot) from the previous one [gp] by
    applying the robogram [r] on [gp] where demonic_action [da] has been applied
    beforehand (to set what each robot actually sees (zoom factor + bad robots
    position)). *)
Definition round (r : robogram) (da : demonic_action) (gp : G → location) : G → location :=
  (** for a given robot, we compute the new position *)
  fun g => 
    let k := da.(frame) g in (** first see what is the zooming factor set by the demon *)
    let spectr := da.(spectrum_of) g in
    let t := gp g in (** t is the current position of g seen by the demon *)
    if Rdec k 0 then t (** If g is not activated (zooming factor = 0), do nothing *)
    else (** otherwise compute the position [g] actually sees, apply robogram
            [r] on it and translate the destination location back in the global
            reference *)
      let pos_seen_by_r := ⟦k, t⟧ {| gp := gp; bp := locate_byz da |} in
      t + /k * (r (spectr pos_seen_by_r)).

(** [execute r d gp] returns an (infinite) execution from an initial global
    position [gp], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon → (G → location) → execution :=
  cofix execute d gp :=
  NextExecution gp (execute (demon_tail d) (round r (demon_head d) gp)).

(** Decomposition lemma for [execute]. *)
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

(** [solution r] means that robogram [r] is a solution, i.e. is convergent
    ([attracted]) for any demon. *)
Definition solution (r : robogram) : Prop :=
  ∀ (gp : G → location),
  ∀ (d : demon), Fair d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : location), attracted lim_app epsilon (execute r d gp).


(** Solution restricted to fully synchronous demons. *)
Definition solution_FSYNC (r : robogram) : Prop :=
  ∀ (gp : G → location),
  ∀ (d : demon), FullySynchronous d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : location), attracted lim_app epsilon (execute r d gp).


(** A Solution is also a solution restricted to fully synchronous demons. *)
Lemma solution_FAIR_FSYNC : ∀ r, solution r → solution_FSYNC r.
Proof.
  intros r H.
  unfold solution_FSYNC, solution in *.
  intros gp d H0.
  apply H.
  now apply fully_synchronous_implies_fair.
Qed.

End goodbyz.

(** Exporting notations of section above. *)
Notation "s ⁻¹" := (s.(retraction)) (at level 99).
Notation "p '∘' s" := (subst_pos s p) (at level 40, left associativity, only parsing).
Notation "'⟦' k ',' t '⟧'" := (similarity k t) (at level 40, format "'⟦' k ','  t '⟧'").

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
