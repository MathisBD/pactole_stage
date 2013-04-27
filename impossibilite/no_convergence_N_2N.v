Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import FiniteSum.
Require Import MeetingTheorem.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.

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
   ; good_reference := fun (x : name (fplus f f)) =>
                       match x with inl _ => if b then 1 else 0
                                  | inr _ => if b then 0 else -1%Qc
                                  end
   |}.

Definition demon2 f : bool -> demon (fplus f f) f :=
  cofix demon2 b := NextDemon (periodic_action f b) (demon2 (negb b)).

Lemma demon2_is_fair f : forall b, Fair (demon2 f b).
Proof.
  cofix.
  intros b; split; simpl; fold (demon2 f); auto.
  clear; destruct b; intros [a|a]; (eright; [esplit|]||idtac); eleft; split.
Qed.

Definition goodies f : name (fplus f f) -> Qc :=
  fun x => match x with inl _ => 0 | inr _ => 1 end.

Lemma stable_goodies f (r : robogram (fplus f f) f) (Hd : 0 = delta r)
: forall gp, (forall g, gp g = goodies g) ->
              forall b g, new_goods r (periodic_action f b) gp g = goodies g.
Proof.
  intros.
  unfold new_goods; simpl; unfold similarity; simpl.
  case H.
  case_eq (inv match g with inl _ => if b then 1 else 0
           | inr _ => if b then 0 else -1%Qc end); auto.
  intros x K M.
  rewrite
  (@AlgoMorph (fplus f f) f r _ (pos0 (fplus f f) f)
              (if b then swap_perm2 f else swap_perm1 f)).
  + fold (delta r); case Hd; ring.
  + cut (b = match g with inl _ => true | _ => false end);
    [|destruct g; destruct b; auto; discriminate].
    intros L; clear x M K; subst; unfold pos_remap; simpl.
    rewrite H; unfold goodies.
    split; simpl; intros n; destruct g; simpl;
    try (rewrite H; unfold goodies; ring);
    destruct n; (try rewrite H); simpl; ring.
Qed.

Lemma L1 f (x : name f) (r : robogram (fplus f f) f) (l : Qc) (H : 0 = delta r)
: forall (gp : name (fplus f f) -> Qc), (forall x, gp x = goodies x) ->
  forall b, imprisonned l (1/(1+1+1)) (execute r (demon2 f b) gp) ->
  False.
Proof.
  intros; destruct H1.
  generalize (H0 (inl x)), (H0 (inr x)), (H1 (inl x)), (H1 (inr x)); clear.
  simpl; repeat (intros H; rewrite H; clear).
  cut (l = l - 0); [intros []|ring].
  intros H; rewrite Qcabs_Qcminus.
  intros K; generalize (Qcle_trans _ _ _ (Qcabs_triangle_reverse 1 l) K).
  intros L; generalize (Qcplus_le_compat _ _ _ _ H L); clear.
  cut ([1] = [l] + ([1] - [l])); [intros []|ring].
  intros K; apply K; split.
Qed.

Lemma L2 f (x : name f) (r : robogram (fplus f f) f)
: solution r -> ~ 0 = delta r.
Proof.
  intros Hs H.
  destruct (Hs (@goodies f) (demon2 f true) (demon2_is_fair _ true) (1/(1+1+1))
               (eq_refl _)) as [lim Hlim].
  cut (forall b (gp : name (fplus f f) -> Qc), (forall g, gp g = goodies g) ->
       attracted lim (1/(1+1+1)) (execute r (demon2 f b) gp) -> False).
  + intros K.
    exact (K true (@goodies f) (fun x => eq_refl _) Hlim).
  + clear - H x; intros.
    remember (execute r (demon2 f b) gp).
    revert gp H0 b Heqe.
    induction H1; intros; subst.
    - eapply L1; eauto.
    - clear H1.
      now apply (IHattracted _ (stable_goodies r H gp H0 b) (negb b)).
Qed.

(******************************************************************************)
(* The main theorem : there is no solution to the N vs N problem.             *)
(******************************************************************************)
Theorem no_solution f (x : name f) (r : robogram (fplus f f) f)
: solution r -> False.
Proof.
  intros Hs.
  apply (L2 x Hs).
  symmetry.
  apply meeting_theorem; auto.
  left; auto.
Qed.
