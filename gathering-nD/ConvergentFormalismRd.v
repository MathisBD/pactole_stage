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
Require Import Arith_base.
Require Import Omega.
Require Import Morphisms.
Require Import Reals.
Import Permutation.
Require Import SetoidList.
Require Import Preliminary.
Open Scope list_scope.
Require Vector.


Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

(* TODO: adapt it to setoid equality *)
Definition ExtEq {T U} (f g : T -> U) := forall x, f x = g x.

Lemma if_ExtEq : forall A B (cond : A -> bool) (f : A -> B), ExtEq (fun x => if cond x then f x else f x) f.
Proof. intros ? ? cond ? x. now destruct (cond x). Qed.


(** *  Identification of robots  **)

(** The number of good and byzantine robots *)
Module Type Size.
  Parameter nG : nat.
  Parameter nB : nat.
End Size.

Module Names (N : Size).

(** **  Finite sets of names  **)

Fixpoint Vfin_map n A (f : Fin.t n -> A) {struct n} : Vector.t A n :=
  match n as n' return n = n' -> Vector.t A n' with
    | 0 => fun _ => (Vector.nil _)
    | S m => fun Heq => Vector.cons A (f (eq_rec_r _ Fin.F1 Heq)) m
                                      (Vfin_map (fun x => f (eq_rec_r _ (Fin.FS x) Heq)))
  end (eq_refl n).

Fixpoint fin_map n A (f : Fin.t n -> A) {struct n} : list A :=
  match n as n' return n = n' -> list A with
    | 0 => fun _ => nil
    | S m => fun Heq => cons (f (eq_rec_r _ Fin.F1 Heq)) (fin_map (fun x => f (eq_rec_r _ (Fin.FS x) Heq)))
  end (eq_refl n).
(*
Fixpoint fin_map n A (f : Fin.t n -> A) {struct n} : list A :=
  match n as n' return n = n' -> list A with
    | 0 => fun _ => nil
    | S m => fun Heq => cons (f (eq_rec_r _ Fin.F1 Heq)) (fin_map (fun x => f (Fin.FS x)))
  end (eq_refl n).
*)
Lemma Vfin_fin_map : forall n A (f : Fin.t n -> A), fin_map f = Vector.to_list (Vfin_map f).
Proof.
induction n; intros A f; simpl; unfold Vector.to_list.
  reflexivity.
  f_equal. rewrite IHn. reflexivity.
Qed.

Instance fin_map_compatA n A eqA : Proper ((eq ==> eqA) ==> eqlistA eqA) (@fin_map n A).
Proof.
intros f g Hext. induction n; simpl.
+ constructor.
+ constructor.
  - apply Hext. reflexivity.
  - apply IHn. repeat intro. apply Hext. subst. reflexivity.
Qed.

Lemma eqlistA_Leibniz A : forall (l1 l2 : list A), eqlistA eq l1 l2 <-> l1 = l2.
Proof.
intro l1. induction l1 as [| x1 l1]; intros l2.
* destruct l2.
  + split; intro; reflexivity.
  + split; intro Habs; inversion Habs.
* destruct l2.
  + split; intro Habs; inversion Habs.
  + split; intro Heq; inversion_clear Heq.
    - subst. f_equal. rewrite <- IHl1. assumption.
    - reflexivity.
Qed.

Instance fin_map_compat n A : Proper (ExtEq ==> eq) (@fin_map n A).
Proof. intros f g Hext. rewrite <- eqlistA_Leibniz. apply fin_map_compatA. repeat intro. subst. apply Hext. Qed.

Theorem InA_fin_map : forall n A eqA `(Equivalence A eqA) g (f : Fin.t n -> A), InA eqA (f g) (fin_map f).
Proof.
intros n A eqA HeqA g f. destruct n.
+ now apply Fin.case0.
+ revert n g f. apply (Fin.rectS (fun n g => ∀ f : Fin.t (S n) → A, InA eqA (f g) (fin_map f))).
  - intros n f. now left.
  - intros n g IHn f. right. apply (IHn (fun x => f (Fin.FS x))).
Qed.

Corollary In_fin_map : forall n A g (f : Fin.t n -> A), In (f g) (fin_map f).
Proof. intros. rewrite <- InA_Leibniz. apply (InA_fin_map _). Qed.

Theorem fin_map_InA : forall A eqA `(Equivalence A eqA) (eq_dec : forall x y : A, {eqA x y} + {~eqA x y}),
  forall n (f : Fin.t n -> A) x, InA eqA x (fin_map f) <-> exists id : Fin.t n, eqA x (f id).
Proof.
intros A eqA HeqA eq_dec n. induction n; intros f x.
* simpl. rewrite InA_nil. split; intro Habs; try elim Habs. destruct Habs. now apply Fin.case0.
* destruct (eq_dec x (f Fin.F1)) as [Heq | Heq].
  + subst. split; intro Hin. 
    - firstorder.
    - rewrite Heq. apply (InA_fin_map _).
  + simpl. unfold eq_rec_r. simpl. split; intro Hin.
    - inversion_clear Hin; try contradiction. rewrite (IHn (fun id => f (Fin.FS id)) x) in H.
      destruct H as [id Hin]; subst; try now elim Heq. now exists (Fin.FS id).
    - right. destruct Hin as [id Hin]. rewrite Hin in *. clear Hin.
      rewrite (IHn (fun id => f (Fin.FS id)) (f id)). revert f Heq.
      apply (Fin.caseS  (λ n (t : Fin.t (S n)), ∀ f : Fin.t (S n) → A,
                         ~eqA (f t) (f Fin.F1) → ∃ id0 : Fin.t n, eqA (f t) (f (Fin.FS id0)))).
        clear -HeqA. intros n f Hn. elim Hn. reflexivity.
        clear -HeqA. intros n id f Hn. exists id. reflexivity.
Qed.

Corollary fin_map_In : forall A (eq_dec : forall x y : A, {x =  y} + {x <> y}),
  forall n (f : Fin.t n -> A) x, In x (fin_map f) <-> exists id : Fin.t n, x = (f id).
Proof. intros. rewrite <- InA_Leibniz. rewrite (fin_map_InA _); trivial. reflexivity. Qed.

Theorem map_fin_map : forall n A B (f : A -> B) (h : Fin.t n -> A),
  fin_map (fun x => f (h x)) = List.map f (fin_map h).
Proof.
intros n A B f h. induction n.
  reflexivity.
  simpl. f_equal. now rewrite IHn.
Qed.

Corollary fin_map_id : forall n A (f : Fin.t n -> A), fin_map f = List.map f (fin_map (fun x => x)).
Proof. intros. apply map_fin_map. Qed.

Lemma fin_map_length : forall n A (f : Fin.t n -> A), length (fin_map f) = n.
Proof.
intros n A f. induction n.
  reflexivity.
  simpl. now rewrite IHn.
Qed.

Unset Implicit Arguments.

Fixpoint Rinv n m (Hm : m <> 0) (x : Fin.t (n + m)) : Fin.t m.
  refine (match n as n', x in Fin.t x' return n = n' -> x' = n + m -> Fin.t m with
            | 0, _ => fun Hn _ => _
            | S n', Fin.F1 _ => fun _ _ => _
            | S n', Fin.FS _ x' => fun Hn Heq => Rinv n' m Hm _
          end eq_refl eq_refl).
- subst n. exact x.
- destruct m. now elim Hm. now apply Fin.F1.
- rewrite Hn in Heq. simpl in Heq. apply eq_add_S in Heq. rewrite <- Heq. exact x'.
Defined.

Theorem Rinv_R : forall n m (Hm : m <> 0) x, Rinv n m Hm (Fin.R n x) = x.
Proof. now induction n. Qed.

(*
Fixpoint Linv n m (Hn : n <> 0) (x : Fin.t (n + m)) {struct n} : Fin.t n.
  refine (match n as n' return n = n' -> Fin.t n' with
    | 0 => fun Hn => _
    | 1 => fun Hn => Fin.F1
    | S (S n'' as rec) => fun Hn => 
      match x in Fin.t x' return x' = n + m -> Fin.t (S rec) with
        | Fin.F1 _ => fun Heq => Fin.F1
        | Fin.FS _ x' => fun Heq => Fin.FS (Linv rec m _ _)
      end eq_refl
  end eq_refl).
- apply False_rec. now apply Hn.
- abstract (unfold rec0 in *; omega).
- subst n. simpl in Heq. apply eq_add_S in Heq. rewrite Heq in x'. exact x'. (* bug *)
Defined.
*)
Set Implicit Arguments.

Definition combine n m A (f : Fin.t n -> A) (g : Fin.t m -> A) : Fin.t (n + m) -> A.
  refine (fun x =>
      if eq_nat_dec m 0 then f _ else
      if (lt_dec (projS1 (Fin.to_nat x)) n) then f (Fin.of_nat_lt _) else g (Rinv n m _ x)).
- subst m. rewrite plus_0_r in x. exact x.
- eassumption.
- assumption.
Defined.

Lemma combine_0_r : forall n A f g, ExtEq (@combine n 0 A f g) (fun x => f (eq_rec (n+0) Fin.t x n (plus_0_r n))).
Proof. intros. intro x. unfold combine. destruct (Fin.to_nat x) eqn:Hx. simpl. reflexivity. Qed.

Lemma combine_0_l : forall m A f g, ExtEq (@combine 0 m A f g) g.
Proof.
intros m *. intro x. unfold combine. destruct (eq_nat_dec m) as [Hm | Hm]; simpl.
- apply Fin.case0. now rewrite Hm in x.
- reflexivity.
Qed.

Instance combine_compat n m A : Proper (ExtEq ==> ExtEq ==> ExtEq) (@combine n m A).
Proof.
intros f₁ f₂ Hf g₁ g₂ Hg x. unfold combine.
destruct (Fin.to_nat x). destruct m; simpl.
- now rewrite Hf.
- destruct (lt_dec x0 n). now rewrite Hf. now rewrite Hg.
Qed.

(* To illustrate
Example ex_f := fun x : Fin.t 2 => 10 + projS1 (Fin.to_nat x).
Example ex_g := fun x : Fin.t 3 => 20 + projS1 (Fin.to_nat x).

Eval compute in combine ex_f ex_g (Fin.F1).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.F1)).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.F1))).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
Fail Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.FS (Fin.F1))))).
*)

Theorem fin_map_app : forall n m A (f : Fin.t n -> A) (g : Fin.t m -> A),
  fin_map f ++ fin_map g = fin_map (combine f g).
Proof.
intros n m A f g. destruct m; simpl.
+ rewrite (combine_0_r f g). rewrite app_nil_r. now rewrite plus_0_r.
+ induction n; simpl.
  - reflexivity.
  - f_equal. rewrite IHn. apply fin_map_compat. intro x. unfold eq_rec_r. simpl.
    unfold combine. simpl. destruct (Fin.to_nat x). simpl.
    destruct (lt_dec x0 n); destruct (lt_dec (S x0) (S n)); try omega.
      now rewrite (le_unique _ _ (lt_S_n x0 n l1) l0).
      reflexivity.
Qed.


(** ** Byzantine Robots *)

(** We have finetely many robots. Some are good, other are evil. *)

Definition G : Set := Fin.t N.nG.
Definition B := Fin.t N.nB.

(** Disjoint union of both kinds of robots is obtained by a sum type. *)
(* TODO: replace this by (G ⊎ B). *)
Inductive ident :=
 | Good : G → ident
 | Byz : B → ident.
(* TODO: rename into robots? GB? *)


(** Names of robots **)

Definition Gnames : list G := fin_map (fun x : G => x).
Definition Bnames : list B := fin_map (fun x : B => x).
Definition names : list ident := List.map Good Gnames ++ List.map Byz Bnames.

End Names.


(** * Positions *)

(** This module signature represents the metric space in which robots evolve.
    It can be anything (discrete or continuous) as long as it is a metric space. *)
Module Type MetricSpace.
  Parameter t : Type.
  Parameter origin : t.
  Parameter eq : t -> t -> Prop.
  Parameter dist : t -> t -> R.
  Parameter eq_dec : forall x y, {eq x y} + {~eq x y}.
  
  Parameter eq_equiv : Equivalence eq.
  Parameter dist_defined : forall x y, dist x y = 0%R <-> eq x y.
  Parameter dist_sym : forall y x, dist x y = dist y x.
  Parameter triang_ineq : forall x y z, (dist x z <= dist x y + dist y z)%R.
  
  (* These properties can be actually derived *)
  Declare Instance dist_compat : Proper (eq ==> eq ==> Logic.eq) dist.
  Parameter dist_pos : forall x y, (0 <= dist x y)%R.
End MetricSpace.

(** **  Spectra  **)

Module Type Spectrum (Location : MetricSpace) (N : Size). (* <: DecidableType *)
  Module Names := Names(N).
  
  (** Spectra are a decidable type *)
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.
  Parameter eq_equiv : Equivalence eq.
  
  (** Positions *)
  Definition position := Names.ident -> Location.t.
  
  (** A position is a mapping from identifiers to locations.  Equality is extensional. *)
  Definition PosEq (pos₁ pos₂ : position) : Prop := ∀id, Location.eq (pos₁ id) (pos₂ id).
  
  (** A predicate characterizing correct spectra for a given local position *)
  (* TODO: maybe a function [from_pos : position -> t] is a better idea as the demon will need it. 
           Then this [is_ok] is simply the specification of [from_pos]. *)
  Parameter is_ok : t -> position -> Prop.
End Spectrum.


Module ConvergentFormalism (Location : MetricSpace)(N : Size)(Spec : Spectrum(Location)(N)).

Module Import Names := Spec.Names.
Notation position := Spec.position.
Notation PosEq := Spec.PosEq.

(** Proofs of the two derivable properties in MertricSpace *)
Instance dist_compat2 : Proper (Location.eq ==> Location.eq ==> eq) (Location.dist).
Proof.
intros x x' Hx y y' Hy. apply Rle_antisym.
+ replace (Location.dist x' y') with (0 + Location.dist x' y' + 0)%R by ring. symmetry in Hy.
  rewrite <- Location.dist_defined in Hx. rewrite <- Location.dist_defined in Hy.
  rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply Location.triang_ineq.
  rewrite Rplus_assoc. apply Rplus_le_compat_l, Location.triang_ineq.
+ replace (Location.dist x y) with (0 + Location.dist x y + 0)%R by ring. symmetry in Hx.
  rewrite <- Location.dist_defined in Hx. rewrite <- Location.dist_defined in Hy.
  rewrite <- Hx at 1. rewrite <- Hy. eapply Rle_trans. apply Location.triang_ineq.
  rewrite Rplus_assoc. apply Rplus_le_compat_l, Location.triang_ineq.
Qed.

Lemma dist_pos : forall x y, (0 <= Location.dist x y)%R.
Proof.
intros x y. apply Rmult_le_reg_l with 2%R.
+ apply Rlt_R0_R2.
+ do 2 rewrite double. rewrite Rplus_0_r.
  assert (Hx : Location.eq x x) by reflexivity. rewrite <- Location.dist_defined in Hx. rewrite <- Hx.
  setoid_rewrite Location.dist_sym at 3. apply Location.triang_ineq.
Qed.

(** ** Programs for good robots *)

Record bijection (T : Type) eqT (Heq : @Equivalence T eqT) := {
  section :> T → T;
  retraction : T → T;
  section_exteq : Proper (eqT ==> eqT) section;
  Inversion : ∀ x y, eqT (section x) y ↔ eqT (retraction y) x}.

Notation "s ⁻¹" := (s.(retraction)) (at level 99).

Definition bij_eq (bij1 bij2 : bijection Location.eq_equiv) :=
  (Location.eq ==> Location.eq)%signature bij1.(section) bij2.

Unset Implicit Arguments.
(** ** Good robots have a common program, which we call a robogram *)
Record robogram := {
  pgm :> Spec.t → Location.t;
  pgm_compat : Proper (Spec.eq ==> Location.eq) pgm}.

(** A robot is either inactive (case [Off]) or activated and observing with the [obs]-applied local vision. *)
(* TODO: We need to parametrize the type of bijection, to express assumptions about them.
         Otherwise robots cannot detect spheres as not all bijetions are isometric! *)
Inductive phase :=
  | Off
  | On (obs : Location.t → bijection Location.eq_equiv)
       (Hobs : Proper (Location.eq ==> bij_eq) obs).
Arguments On obs Hobs. (* does not seeem to have any effect *)

Definition phase_eq (ph1 ph2 : phase) :=
  match ph1, ph2 with 
    | Off, Off => True
    | Off, On _ _ => False
    | On _ _, Off => False
    | On obs1 Hobs1, On obs2 Hobs2 => (Location.eq ==> bij_eq)%signature obs1 obs2
  end.

(** ** Demonic schedulers *)
(** A [demonic_action] moves all byz robots
    as it whishes, and sets the referential of all good robots it selects. *)
Record demonic_action := {
  relocate_byz : B → Location.t;
  step : ident → phase;
  step_ok : forall pos r o Ho, step r = On o Ho -> o (pos r) (pos r) = Location.origin;
  step_exteq : Proper (eq ==> phase_eq) step;
  spectrum_of : G → (position → Spec.t);
  spectrum_ok : forall g:G, forall p:position, Spec.is_ok (spectrum_of g p) p;
  spectrum_exteq : Proper (eq ==> PosEq ==> Spec.eq) spectrum_of}.
Set Implicit Arguments.


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
  | ImmediatelyFair : step (demon_head d) g ≠ Off → LocallyFairForOne g d
  | LaterFair : step (demon_head d) g = Off → 
                LocallyFairForOne g (demon_tail d) → LocallyFairForOne g d.

CoInductive Fair (d : demon) : Prop :=
  AlwaysFair : (∀ g, LocallyFairForOne g d) → Fair (demon_tail d) →
               Fair d.

(** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
Inductive Between g h (d : demon) : nat -> Prop :=
| kReset : forall k, step (demon_head d) g <> Off -> Between g h d k
| kReduce : forall k, step (demon_head d) g = Off -> step (demon_head d) h <> Off ->
                      Between g h (demon_tail d) k -> Between g h d (S k)
| kStall : forall k, step (demon_head d) g = Off -> step (demon_head d) h = Off ->
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

(** [Between g h d k] is monotonic on [k]. *)
Lemma Between_mon : forall g h (d : demon) k,
  Between g h d k -> forall k', (k <= k')%nat -> Between g h d k'.
Proof.
  intros g h d k Hd. induction Hd; intros k' Hk.
  now constructor 1.
  destruct k'.
    now inversion Hk.
    constructor 2; assumption || now (apply IHHd; omega).
  constructor 3; assumption || now (apply IHHd; omega).
Qed.

(** [kFair k d] is monotonic on [k] relation. *)
Theorem kFair_mon : forall k (d: demon),
  kFair k d -> forall k', (k <= k')%nat -> kFair k' d.
Proof.
  coinduction fair; destruct H.
  - intros. now apply Between_mon with k.
  - now apply (fair k).
Qed.

Theorem Fair0 : forall d, kFair 0 d ->
  forall g h, (demon_head d).(step) g = Off <-> (demon_head d).(step) h = Off.
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
    (step (demon_head d) g) ≠ Off → 
                      FullySynchronousForOne g d.

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
  NextExecution : position → execution → execution.

(** *** Destructors for demons *)

Definition execution_head (e : execution) : position :=
  match e with NextExecution pos _ => pos end.

Definition execution_tail (e : execution) : execution :=
  match e with NextExecution _ e => e end.

(** Pointwise mapping of a function on a position *)
Definition map_pos (f : Location.t -> Location.t) (pos : position) := fun id => f (pos id).

(** [round r da pos] return the new position of robots (that is a function
    giving the position of each robot) from the previous one [pos] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
Definition round (r : robogram) (da : demonic_action) (pos : position) : position :=
  (** for a given robot, we compute the new position *)
  fun id => 
    let t := pos id in (** t is the current position of g seen by the demon *)
    match da.(step) id with (** first see whether the robot is activated *)
      | Off => t (** If g is not activated, do nothing *)
      | On f _ => (** g is activated and f is its frame (phase) *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robot are relocated by the demon *)
        | Good g => 
          let spectr := da.(spectrum_of) g in (* spectrum function chosen by the demon *)
          let pos_seen_by_r := map_pos (f t) pos in (* position expressed in the frame of g *)
          (f t) ⁻¹ (r (spectr pos_seen_by_r)) (* apply r on spectrum + back to demon ref. *)
        end
    end.

(** [execute r d pos] returns an (infinite) execution from an initial global
    position [pos], a demon [d] and a robogram [r] running on each good robot. *)
Definition execute (r : robogram): demon → position → execution :=
  cofix execute d pos :=
  NextExecution pos (execute (demon_tail d) (round r (demon_head d) pos)).

(** Decomposition lemma for [execute]. *)
Lemma execute_tail : forall (r : robogram) (d : demon) (pos:position),
  execution_tail (execute r d pos) = execute r (demon_tail d) (round r (demon_head d) pos).
Proof. intros. destruct d. unfold execute, execution_tail. reflexivity. Qed.

(** ** Properties of executions  *)

Open Scope R_scope.
(** Expressing that all good robots are confined in a small disk. *)
CoInductive imprisonned (center : Location.t) (radius : R) (e : execution) : Prop
:= InDisk : (∀ g : G, Rabs (Location.dist center (execution_head e (Good g))) <= radius)
            → imprisonned center radius (execution_tail e)
            → imprisonned center radius e.

(** The execution will end in a small disk. *)
Inductive attracted (center : Location.t) (radius : R) (e : execution) : Prop :=
  | Captured : imprisonned center radius e → attracted center radius e
  | WillBeCaptured : attracted center radius (execution_tail e) → attracted center radius e.

(** [solution r] means that robogram [r] is a solution, i.e. is convergent
    ([attracted]) for any demon. *)
Definition solution (r : robogram) : Prop :=
  ∀ (pos : position),
  ∀ (d : demon), Fair d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : Location.t), attracted lim_app epsilon (execute r d pos).


(** Solution restricted to fully synchronous demons. *)
Definition solution_FSYNC (r : robogram) : Prop :=
  ∀ (pos : position),
  ∀ (d : demon), FullySynchronous d →
  ∀ (epsilon : R), 0 < epsilon →
  exists (lim_app : Location.t), attracted lim_app epsilon (execute r d pos).


(** A Solution is also a solution restricted to fully synchronous demons. *)
Lemma solution_FAIR_FSYNC : ∀ r, solution r → solution_FSYNC r.
Proof.
  intros r H.
  unfold solution_FSYNC, solution in *.
  intros pos d H0.
  apply H.
  now apply fully_synchronous_implies_fair.
Qed.

End ConvergentFormalism.

(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)
