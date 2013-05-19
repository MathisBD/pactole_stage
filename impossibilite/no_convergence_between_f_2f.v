Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import FiniteSum.
Require Import MeetingTheorem.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.
Require Import ContractionTheorem.

Definition endo t := t -> t.

(* Useful permutations *)

Definition one : finite.
refine {| name := unit
        ; next := fun x => match x with None => Some tt | _ => None end
        ; prev := fun x => match x with None => Some tt | _ => None end
        |}.
Proof.
  abstract (
    split; [destruct x as [[]|]|destruct y as [[]|]]; intros; subst; auto
  ).
  abstract (split; discriminate).
  abstract (split; discriminate).
Defined.

Definition fS (f : finite) : finite := fplus one f.

Definition swap_aux1 g b : endo (ident (fS g) (fplus b (fS g))) :=
  fun x =>
  match x with
  | Bad (inr (inl _)) => Good (fS _) _ (inl tt)
  | Bad a => Bad _ _ a
  | Good (inl _) => Bad _ (fplus _ (fS _)) (inr (inl tt))
  | Good (inr a) => Good (fS _) _ (inr a)
  end.

Definition swap_perm1 g b
: automorphism (ident (fS g) (fplus b (fS g))).
refine {| section := @swap_aux1 g b ; retraction := @swap_aux1 g b |}.
Proof.
  abstract (
    intros x y; split; intros; subst;
    [destruct x as [[[]|]|[|[[]|]]]|destruct y as [[[]|]|[|[[]|]]]]; simpl; auto
  ).
Defined.

Definition swap_aux2 g b : endo (ident (fS g) (fplus b (fS g))) :=
  fun x =>
  match x with
  | Bad (inr (inr a)) => Good (fS _) _ (inr a)
  | Bad a => Bad _ _ a
  | Good (inl _) => Good (fS _) _ (inl tt)
  | Good (inr a) => Bad _ (fplus _ (fS _)) (inr (inr a))
  end.

Definition swap_perm2 g b
: automorphism (ident (fS g) (fplus b (fS g))).
refine {| section := @swap_aux2 g b ; retraction := @swap_aux2 g b |}.
Proof.
  abstract (
    intros x y; split; intros; subst;
    [destruct x as [[[]|]|[|[[]|]]]|destruct y as [[[]|]|[|[[]|]]]]; simpl; auto
  ).
Defined.

(* Second part of the proof with the lazy demon *)
Definition da1 g b : demonic_action (fS g) (fplus b (fS g)) :=
  {| bad_replace := fun x : name (fplus b (fS g)) =>
                    match x with inr (inl _) => 0 | _ => 1 end
   ; good_reference := fun x : name (fS g) =>
                       match x with inl _ => 0 | _ => 1 end
   |}.

Definition da2 g b : demonic_action (fS g) (fplus b (fS g)) :=
  {| bad_replace := fun x : name (fplus b (fS g)) =>
                    match x with inr (inr _) => 1 | _ => 0 end
   ; good_reference := fun x : name (fS g) =>
                       match x with inl _ => -(1) | _ => 0 end
   |}.

Definition demon_trick g b : demon_tactic (fS g) (fplus b (fS g)) :=
  (da1 g b, cons (da2 g b) nil).

Lemma fair_demon_trick g b : fair_tactic (demon_trick g b).
Proof. intros [a|a]; split. Qed.

Definition goodies g : name (fS g) -> Qc :=
  fun x => match x with inl _ => 1 | inr _ => 0 end.

Definition unity : inv_pair.
refine {| alpha := 1 ; beta := 1 |}.
abstract (ring).
Defined.

Lemma demon_trick_similitude g b
      (r : robogram (fS g) (fplus b (fS g)))
      (Hr : solution r) :
  similitude unity 0 (fS g) (goodies (g := g))
             (after_tactic unity 0 r (demon_trick g b) (goodies (g := g))).
Proof.
  unfold similitude, after_tactic, unity; simpl.
  generalize (meeting_theorem (inl tt : name (fS g)) Hr).
  unfold delta.
  intros K.
  assert (forall y, goodies (g:=g) y = new_goods r (da1 g b)(goodies (g:=g)) y).
  + unfold new_goods; intros [a|a]; simpl; auto.
    generalize (
     @AlgoMorph _ _ r (pos0 (fS g) (fplus b (fS g)))
     (similarity 1 0 {|good_places:=goodies(g:=g);
                       bad_places:=bad_replace (da1 g b)|})
     (swap_perm1 g b));
    simpl; intros []; [|rewrite K; ring].
    split; simpl; intros; destruct n; simpl; try ring.
    destruct s; ring.
  + revert H.
    generalize (new_goods r (da1 g b) (goodies (g := g))).
    intros gp L.
    unfold new_goods; intros [a|a]; simpl; auto; [|case L; simpl; ring].
    repeat case L; simpl.
    generalize (
     @AlgoMorph _ _ r (pos0 (fS g) (fplus b (fS g)))
     (similarity (-(1)) 1 {|good_places:=gp;bad_places:=bad_replace (da2 g b)|})
     (swap_perm2 g b));
    simpl; intros []; [|rewrite K; simpl; ring].
    split; simpl; intros.
    - case L; destruct n; simpl; ring.
    - destruct n; simpl; try ring.
      destruct s; ring.
Qed.

(******************************************************************************)
(* The main theorem : there is no solution to the N vs N problem.             *)
(******************************************************************************)
Theorem no_solution g b (r : robogram (fS g) (fplus b (fS g)))
: forall (u : name g), solution r -> False.
Proof.
  intros u Hs.
  assert (K : goodies (g := g) (inl tt) <>
              goodies (g := g) (inr u)).
  + simpl; clear; discriminate.
  + generalize (Contraction Hs (@fair_demon_trick g b)
                            (demon_trick_similitude Hs) _ _ K).
    simpl; clear.
    discriminate.
Qed.



Require Import Finites.

(* Here we would like to have a quantitfication on any non empy set of
   good robots, but since our finite sets are isomorphic to segments
   of N, we chose one concrete representation of a non empty set,
   namely (fS g), for any g whose carrier is itself non empty. *)
Theorem no_solution_paper_version: 
  forall g b (u:name g) (r: robogram (fS g) (fplus b (fS g))),
    ~ solution r.
Proof.
  intros g b u r.
  intro.
  eapply no_solution;eauto.
Qed.


