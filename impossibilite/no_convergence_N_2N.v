Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import FiniteSum.
Require Import MeetingTheorem.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.

(* Impossibility in a N robots vs N robots *)

(* Useful permutations *)
Definition swap_aux1 f (x : ident (fplus f f) f) : ident (fplus f f) f :=
  match x with
  | Bad a => Good (fplus f f) f (inl a)
  | Good (inl a) => Bad (fplus f f) f a
  | Good (inr a) => Good (fplus f f) f (inr a)
  end.

Definition swap_aux2 f (x : ident (fplus f f) f) : ident (fplus f f) f :=
  match x with
  | Bad a => Good (fplus f f) f (inr a)
  | Good (inr a) => Bad (fplus f f) f a
  | Good (inl a) => Good (fplus f f) f (inl a)
  end.

Definition swap_perm1 f : automorphism (ident (fplus f f) f).
refine {| section := @swap_aux1 f ; retraction := @swap_aux1 f |}.
abstract (
  intros x y; split; intros; subst;
  [destruct x as [[a|a]|a]|destruct y as [[a|a]|a]]; simpl; auto
).
Defined.

Definition swap_perm2 f : automorphism (ident (fplus f f) f).
refine {| section := @swap_aux2 f ; retraction := @swap_aux2 f |}.
abstract (
  intros x y; split; intros; subst;
  [destruct x as [[a|a]|a]|destruct y as [[a|a]|a]]; simpl; auto
).
Defined.

(* Second part of the proof with the lazy demon *)
Definition periodic_action f (b : bool) : demonic_action (fplus f f) f :=
  {| bad_replace := fun x => if b then 0 else 1
   ; good_activation := fun (x : name (fplus f f)) =>
                        match x with inl _ => b | inr _ => negb b end
   |}.

Definition demon2 f : bool -> demon (fplus f f) f :=
  cofix demon2 b := NextDemon (periodic_action f b) (demon2 (negb b)).

Lemma demon2_is_fair f : forall b, Fair (demon2 f b).
Proof.
  cofix.
  intros b; split; simpl; fold (demon2 f); auto.
  clear; destruct b; intros [a|a]; [|right|right|]; auto; left; auto.
Qed.

Definition goodies f : name (fplus f f) -> Qc :=
  fun x => match x with inl _ => 0 | inr _ => 1 end.

Lemma stable_goodies f (r : robogram (fplus f f) f) (Hd : 0 = delta r)
: forall gp, (forall g, gp g = goodies g) ->
              forall g b, new_goods r (periodic_action f b) gp g = goodies g.
Proof.
  intros.
  unfold new_goods; simpl; unfold cmove, center; simpl.
  case H.
  case_eq (match g with inl _ => b | inr _ => negb b end); intros K; try ring.
  rewrite
  (@AlgoMorph (fplus f f) f r (if b then 1 else -1%Qc) _ (pos0 (fplus f f) f)).
  + fold (delta r); case Hd; ring.
  + split with (if b then swap_perm2 f else swap_perm1 f).
    cut (b = match g with inl _ => true | _ => false end);
    [intros L; clear K; subst|destruct g; auto; destruct b; auto].
    split; simpl; unfold pos_remap_aux; simpl; intros; repeat rewrite H; simpl.
    - clear; destruct g; destruct n; simpl; ring.
    - destruct g; simpl; ring.
Qed.

Lemma L1 f (r : robogram (fplus f f) f) (l : Qc) (H : 0 = delta r)
: forall (gp : name f -> Qc), (forall x, gp x = goodies f x) ->
  imprisonned l (1/(1+1+1)) (execute r (demon2 f) gp) ->
  False.
Proof.
  intros; destruct H1; revert H1 Htwo;
  generalize (stable_goodies r H gp H0); clear.
  intros Hgp K Htwo.
  revert Htwo; unfold two.
  case_eq (prev f None); [|intros L; rewrite L; auto].
  intros _x_ H_x_; assert (Hx := proj2 (NextPrev f _ _) H_x_); clear H_x_.
  case_eq (prev f (Some _x_)); [|auto].
  intros _y_ H_y_ _; assert (Hy := proj2 (NextPrev f _ _) H_y_); clear H_y_.
  generalize (K _x_), (K _y_).
  clear - Hgp Hx Hy.
  simpl; repeat rewrite Hgp.
  unfold goodies; rewrite Hx; rewrite Hy; clear.
  cut (l = l - 0); [intros []|ring].
  intros K H; revert K.
  rewrite Qcabs_Qcminus.
  intros K; generalize (Qcle_trans _ _ _ (Qcabs_triangle_reverse 1 l) K).
  intros L; generalize (Qcplus_le_compat _ _ _ _ H L); clear.
  cut ([1] = [l] + ([1] - [l])); [intros []|ring].
  intros K; apply K; split.
Qed.

Lemma L2 f (Htwo : two f) (r : robogram f f) : solution r -> ~ 0 = delta r.
Proof.
  intros Hs H.
  destruct (Hs (goodies f) (demon2 f) (demon2_is_fair _) (1/(1+1+1))
               (eq_refl _)) as [lim Hlim].
  cut (forall (gp : name f -> Qc), (forall g, gp g = goodies f g) ->
       attracted lim (1/(1+1+1)) (execute r (demon2 f) gp) -> False).
  + intros K.
    exact (K (goodies f) (fun x => eq_refl _) Hlim).
  + clear - H Htwo; intros.
    remember (execute r (demon2 f) gp).
    revert gp H0 Heqe.
    induction H1; intros; subst.
    - eapply L1; eauto.
    - clear H1.
      apply (IHattracted (new_goods r (lazy_action f) gp)); auto.
      now apply stable_goodies.
Qed.

(******************************************************************************)
(* The main theorem : there is no solution to the N vs N problem.             *)
(******************************************************************************)
Theorem no_solution f (Htwo : two f) (r : robogram f f) : solution r -> False.
Proof.
  intros Hs.
  apply (L2 Htwo Hs).
  symmetry.
  apply meeting_theorem; auto.
  revert Htwo; unfold two.
  destruct (prev f (prev f None)); auto.
  intros [].
Qed.
