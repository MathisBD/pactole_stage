Set Implicit Arguments.
Require Import ConvergentFormalism3.
Require Import FiniteSum3.
Require Import XMT3.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.
Require Import XCT3.

Definition endo t := t -> t.

(* Useful permutations *)

Definition swap_aux1 g b : endo (ident (fS g) (fplus b (fS g))) :=
  fun x =>
  match x with
  | Byz (inr (inl _)) => Good (fS _) _ (inl tt)
  | Byz a => Byz _ _ a
  | Good (inl _) => Byz _ (fplus _ (fS _)) (inr (inl tt))
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
  | Byz (inr (inr a)) => Good (fS _) _ (inr a)
  | Byz a => Byz _ _ a
  | Good (inl _) => Good (fS _) _ (inl tt)
  | Good (inr a) => Byz _ (fplus _ (fS _)) (inr (inr a))
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
Definition demon_trick g b : demonic_action (fS g) (fplus b (fS g)) :=
  {| byz_replace := fun x : name (fplus b (fS g)) =>
                    match x with inr (inl _) => 0 | _ => 1 end
   ; frame := fun x : name (fS g) => 1
   |}.

Lemma fair_demon_trick g b : fair_action (demon_trick g b).
Proof. intros x; discriminate. Qed.

Definition goodies g : name (fS g) -> Qc :=
  fun x => if x then 1 else 0.

Definition unity : inv_pair.
refine {| alpha := 1 ; beta := 1 |}.
abstract (ring).
Defined.

Lemma demon_trick_similitude g b
      (r : robogram (fS g) (fplus b (fS g)))
      (Hr : solution_fully_synchronous r) :
  similitude' unity 0 (fS g) (goodies (g := g))
             (after_tactic unity 0 r (demon_trick g b) (goodies (g := g))).
Proof.
  unfold similitude', after_tactic, unity; simpl.
  generalize (fun bp => meeting_theorem' (inl tt : name (fS g)) bp Hr).
  clear; intros K [[]|x]; simpl; unfold round, similarity; simpl.
  - generalize (K (fun x => if x then 0 else -(1))); clear.
    unfold delta, round; simpl; set (a:=0) at 3; intros []; subst a.
    cut (forall a b, a = b -> 1 + / 1 * a = 1 * 1 + b);
    [intros H; apply H|intros a _ []; field; discriminate].
    apply AlgoMorph with (swap_perm2 g b); clear.
    split; simpl; [intros []|intros [|[]]]; simpl; intros _; ring.
  - unfold round, similarity; simpl.
    generalize (K (fun _ => 1)); clear.
    set (a:=0) at 1 7; unfold delta, round; simpl; intros []; subst a.
    cut (forall a b, a = b -> 0 + / 1 * a = 1 * 0 + b);
    [intros H; apply H|intros a _ []; field; discriminate].
    apply AlgoMorph with (swap_perm1 g b); clear.
    split; simpl; [intros []|intros [|[]]]; simpl; intros _; ring.
Qed.

(******************************************************************************)
(* The main theorem : there is no solution to the N vs N problem.             *)
(******************************************************************************)

(* Note that u : name g means that g is non-empty *)

Theorem no_solution g b (r : robogram (fS g) (fplus b (fS g)))
: forall (u : name g), solution_fully_synchronous r -> False.
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
