Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import FiniteSum.
Require Import MeetingTheorem_FAIR.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.
Require Import ContractionTheorem_FAIR.

Definition endo t := t -> t.

(* Useful permutations *)
Definition swap_aux1 g b : endo (ident (fplus (fplus b g) g) (fplus b g)) :=
  fun x =>
  match x with
  | Byz a => Good (fplus _ _) _ (inl a)
  | Good (inl a) => Byz _ _ a
  | Good (inr a) => Good (fplus _ _) _ (inr a)
  end.

Definition swap_aux2 g b : endo (ident (fplus (fplus b g) g) (fplus b g)) :=
  fun x =>
  match x with
  | Byz (inl a) => Byz _ (fplus _ _) (inl a)
  | Byz (inr a) => Good (fplus _ _) _ (inr a)
  | Good (inr a) => Byz _ (fplus _ _) (inr a)
  | Good (inl a) => Good (fplus _ _) _ (inl a)
  end.

Definition swap_perm1 g b
: automorphism (ident (fplus (fplus b g) g) (fplus b g)).
refine {| section := @swap_aux1 g b ; retraction := @swap_aux1 g b |}.
abstract (
  intros x y; split; intros; subst;
  [destruct x as [[a|a]|a]|destruct y as [[a|a]|a]]; simpl; auto
).
Defined.

Definition swap_perm2 g b
: automorphism (ident (fplus (fplus b g) g) (fplus b g)).
refine {| section := @swap_aux2 g b ; retraction := @swap_aux2 g b |}.
abstract (
  intros x y; split; intros; subst;
  [destruct x as [[a|a]|[a|a]]|destruct y as [[a|a]|[a|a]]]; simpl; auto
).
Defined.

(* Second part of the proof with the lazy demon *)
Definition da1 g b : demonic_action (fplus (fplus b g) g) (fplus b g) :=
  {| byz_replace := fun _ => 1
   ; frame := fun x : name (fplus _ _) =>
                       match x with inl _ => 0 | _ => -(1) end
   |}.

Definition da2 g b : demonic_action (fplus (fplus b g) g) (fplus b g) :=
  {| byz_replace := fun x : name (fplus _ _) =>
                    match x with inl _ => 1 | _ => 0 end
   ; frame := fun x : name (fplus _ _) =>
                       match x with inl _ => 1 | _ => 0 end
   |}.

Definition demon_trick g b : demon_tactic (fplus (fplus b g) g) (fplus b g) :=
  (da1 g b, cons (da2 g b) nil).

Lemma fair_demon_trick g b : fair_tactic (demon_trick g b).
Proof. intros [a|a]; split. Qed.


Require Import Utf8.


Inductive LocallyStronglyKtBoundedForOne good byz (k:nat) g (d:demon good byz): Prop :=
  ImmediatelyKBounded:
    (frame (demon_head d) g) ≠ 0 →
    LocallyStronglyKtBoundedForOne k g d
| LaterKBounded:
    (k>0)%nat →  (frame (demon_head d) g) = 0 →
                     LocallyStronglyKtBoundedForOne (k-1) g (demon_tail d)
                     → LocallyStronglyKtBoundedForOne k g d.

CoInductive StronglyKBounded good byz k (d:demon good byz) :=
  NextKBounded: (∀ g, LocallyStronglyKtBoundedForOne k g d)
    → StronglyKBounded k (demon_tail d)
    → StronglyKBounded k d.



Definition goodies g b : name (fplus (fplus b g) g) -> Qc :=
  fun x => match x with inl _ => 0 | inr _ => 1 end.

Definition unity : inv_pair.
refine {| alpha := 1 ; beta := 1 |}.
abstract (ring).
Defined.

Lemma LocallyStronglyTwoBounded_demon_trick g b r:
  LocallyStronglyKtBoundedForOne 2 r (simili_demon unity 0 (demon_trick g b)).
Proof.
  destruct r;simpl.
  - eapply LaterKBounded.
    + auto.
    + simpl. reflexivity.
    + eapply ImmediatelyKBounded.
      simpl.
      discriminate.
  - eapply ImmediatelyKBounded.
    simpl.
    discriminate.
Qed.

Lemma LocallyStronglyTwoBounded_demon_trick' g b r:
  LocallyStronglyKtBoundedForOne 2 r (demon_tail (simili_demon unity 0 (demon_trick g b))).
Proof.
  destruct r.
  - eapply ImmediatelyKBounded.
    simpl.
    discriminate.
  - eapply LaterKBounded.
    + auto.
    + simpl. reflexivity.
    + eapply ImmediatelyKBounded.
      simpl.
      discriminate.
Qed.

(*
CoInductive bisimilar g b: demon g b -> demon g b -> Prop :=
  bisim_samehead:forall d1 d2,
                   bisimilar (demon_tail (demon_tail d1))
                             (demon_tail (demon_tail d2)) -> 
                   (demon_head d1) = (demon_head d2) -> 
                   (demon_head (demon_tail d1)) = (demon_head (demon_tail d2)) -> 
                   bisimilar d1 d2.

Variable g b: finite.

Lemma bisim g b:
  forall x, bisimilar x (simili_demon unity 0 (demon_trick g b)) ->
            bisimilar (demon_tail (demon_tail x)) x.
Proof.
  cofix.
  intros x H.
  destruct x eqn:h.
  simpl in *.
  destruct d0 eqn:hh.
  subst. simpl in *.
  constructor;simpl.
  
  unfold simili_demon in H.

  - admit.
    (*specialize (bisim (demon_tail (demon_tail d2))).
    destruct d2;simpl in *.
    apply bisim.*)
  - 
  apply bisim.



  cofix.
  destruct x eqn:h.
  simpl in *.
  destruct d0 eqn:hh.
  subst. simpl in *.
  intros H.
  constructor;simpl.
  constructor;simpl.
  
  unfold simili_demon in H.

  - admit.
    (*specialize (bisim (demon_tail (demon_tail d2))).
    destruct d2;simpl in *.
    apply bisim.*)
  - 
  apply bisim.

Qed.

Lemma eqda1da2 g b :
  forall d,  bisimilar d (simili_demon unity 0 (demon_trick g b))
             -> (NextDemon (da1 g b) (NextDemon (da2 g b) d)) = d.
Proof.
  intros d H.
  destruct d eqn:h.
  rewrite <- h at 1.
  assert (d0=(da1 g b)).
  eapply f_equal.
  simpl.
  destruct (d1) eqn:hh.
  simpl.
  rewrite h.
  unfold simili_demon in H.
  simpl in h.


  forall d, d = (simili_demon unity 0 (demon_trick g b)) ->
            d = demon_tail (demon_tail d).
Proof.
  intros d H.
  destruct d eqn:h.
  rewrite <- h at 1.
  simpl.
  destruct (d1) eqn:hh.
  simpl.
  rewrite h.
  unfold simili_demon in H.
  simpl in h.


  destruct 
  destruct (simili_demon unity 0 (demon_trick g b)).
  destruct d0.



Lemma TwoStronglyBounded_demon_trick g b :
  StronglyKBounded 2 (simili_demon unity 0 (demon_trick g b)).
Proof.
  cofix.
  constructor;intros.
  - apply LocallyStronglyTwoBounded_demon_trick.
  - constructor;intros. 
    + apply LocallyStronglyTwoBounded_demon_trick'.
    +  unfold demon_tail.
      change 
      apply TwoStronglyBounded_demon_trick.     Guarded.

Qed.
*)
Lemma demon_trick_similitude g b
      (r : robogram (fplus (fplus b g) g) (fplus b g))
      (Hr : solution r) (u : name (fplus (fplus b g) g)) :
  similitude unity 0 (fplus (fplus b g) g) (goodies (b := b))
             (after_tactic unity 0 r (demon_trick g b) (goodies (b := b))).
Proof.
  unfold similitude, after_tactic, unity; simpl.
  generalize (meeting_theorem u Hr).
  unfold delta.
  intros K.
  assert (forall y, goodies (b:=b) y = round r (da1 g b)(goodies (b:=b)) y).
  + unfold round; intros [a|a]; simpl; auto.
    generalize (
     @AlgoMorph _ _ r (pos0 (fplus (fplus b g) g) (fplus b g))
     (similarity (-(1)) 1{|gp:=goodies(b:=b);bp:=fun _ => 1 |})
     (swap_perm1 g b));
    simpl; intros []; [|rewrite K; ring].
    split; simpl; intros; [|ring].
    destruct n; simpl; ring.
  + revert H.
    generalize (round r (da1 g b) (goodies (b := b))).
    intros gp L.
    unfold round; intros [a|a]; simpl; auto; [|case L; simpl; ring].
    repeat case L; simpl.
    generalize (
     @AlgoMorph _ _ r (pos0 (fplus (fplus b g) g) (fplus b g))
     (similarity 1 0 {|gp:=gp;bp:=byz_replace (da2 g b)|})
     (swap_perm2 g b));
    simpl; intros []; [|rewrite K; simpl; ring].
    split; simpl; intros.
    - case L; destruct n; simpl; ring.
    - destruct n; simpl; ring.
Qed.

(******************************************************************************)
(* The main theorem : there is no solution to the N vs N problem.             *)
(******************************************************************************)
Theorem no_solution g b (r : robogram (fplus (fplus b g) g) (fplus b g))
: forall (u : name g), solution r -> False.
Proof.
  intros u Hs.
  assert (K : goodies (b := b) (inl (inr u)) <>
              goodies (b := b) (inr u)).
  + simpl; clear; discriminate.
  + generalize (Contraction Hs (@fair_demon_trick g b)
                            (demon_trick_similitude Hs (inr u)) _ _ K).
    simpl; clear.
    discriminate.
Qed.


