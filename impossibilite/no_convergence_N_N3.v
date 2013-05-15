Set Implicit Arguments.
Require Import ConvergentFormalism3.
Require Import MeetingTheorem3.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.

(* Impossibility in a N robots vs N robots *)

(* Useful permutations *)
Definition swap_p f (n s : name f -> ident f f) : name f -> ident f f :=
  fun x => match next f (Some x) with None => n x | _ => s x end.

Definition swaper f (g b : name f -> ident f f) : ident f f -> ident f f :=
  fun x => match x with Good x => g x | Bad x => b x end.

Definition swap_perm1 f : automorphism (ident f f).
refine (let s := swaper (swap_p(Bad f f)(Good f f)) (swap_p(Good f f)(Bad f f))
        in {| section := s ; retraction := s |}).
abstract (
intros x y; split; intros; subst; [destruct x as [t|t]|destruct y as [t|t]];
subst s; unfold swap_p, swaper; simpl;
(case_eq (next f (Some t)); simpl;
[intros n H|intros H]; rewrite H); auto
).
Defined.

Definition swap_perm2 f : automorphism (ident f f).
refine (let s := swaper (swap_p(Good f f)(Bad f f)) (swap_p(Bad f f)(Good f f))
        in {| section := s ; retraction := s |}).
abstract (
intros x y; split; intros; subst; [destruct x as [t|t]|destruct y as [t|t]];
subst s; unfold swap_p, swaper; simpl;
(case_eq (next f (Some t)); simpl;
[intros n H|intros H]; rewrite H); auto
).
Defined.

(* Second part of the proof with the lazy demon *)
Definition lazy_action f : demonic_action f f :=
  {| bad_replace := fun x => match next f (Some x) with None => 0 | _ => 1 end
   ; good_reference := fun x => match next f (Some x) with None => -1%Qc
                                                         | _ => 1 end
   |}.

Definition demon2 f : demon f f :=
  cofix demon2 := NextDemon (lazy_action f) demon2.

Lemma demon2_is_fair f : Fair (demon2 f).
Proof.
  cofix; split; auto.
  intros g; case_eq (inv (good_reference (demon_head (demon2 f)) g)).
  + intros K; exfalso; simpl in *.
    destruct (next f (Some g)); discriminate.
  + intros l e; left with l e; auto.
Qed.



Lemma demon2_is_fully_synchronous: forall f, FullySynchronous (demon2 f).
Proof.
  cofix.
  intros f.
  constructor.  
  - unfold demon2.
    intros g.
    constructor.
    simpl.
    destruct (next f (Some g));discriminate.
  - apply demon2_is_fully_synchronous.
Qed.    

(* With the other version of FullySynchronous:
    unfold lazy_action.
    destruct (next f (Some g)) eqn:h.
    assert (h':1 *
               good_reference
                 (demon_head
                    (cofix demon2  : demon f f :=
                       NextDemon
                         {|
                           bad_replace := fun x : name f =>
                                            match next f (Some x) with
                                              | Some _ => 1
                                              | None => 0
                                            end;
                           good_reference := fun x : name f =>
                                               match next f (Some x) with
                                                 | Some _ => 1
                                                 | None => - (1)
                                               end |} demon2)) g = 1).
    { admit. }
    
    simpl.
    rewrite h.
    discriminate.
    apply ImmediatelyFair2 with (l:=1) (H:=h').
    Show Existentials.
    unfold lazy_action;simpl.
    destruct (next f (Some n));discriminate.
*)



Definition goodies f : name f -> Qc :=
  fun x => match next f (Some x) with None => 1 | _ => 0 end.

Definition two f :=
  match prev f (prev f None) with None => False | _ => True end.

Lemma stable_goodies f (r : robogram f f) (Hd : 0 = delta r)
: forall gp, (forall g : name f, gp g = goodies f g) ->
              forall g : name f, new_goods r (lazy_action f) gp g = goodies f g.
Proof.
  intros.
  unfold new_goods; simpl; unfold similarity; simpl.
  rewrite (@AlgoMorph f f r _ (pos0 f f)
           (match next f (Some g) with None => swap_perm2 f
            | _ => swap_perm1 f end)).
  + fold (delta r); case Hd; case H; clear.
    destruct (inv match next f (Some g) with None => -1%Qc | _ => 1 end); ring.
  + split; simpl; rewrite H; simpl;
    intros x; generalize (H x); unfold goodies; clear;
    destruct (next f (Some g));simpl;unfold swap_p;
    case_eq (next f (Some x)); intros;simpl; (rewrite H0||rewrite H); ring.
Qed.

Lemma L1 f (Htwo : two f) (r : robogram f f) (l : Qc) (H : 0 = delta r)
: forall (gp : name f -> Qc), (forall x, gp x = goodies f x) ->
  imprisonned l (1/(1+1+1)) (execute r (demon2 f) gp) ->
  False.
Proof.
  intros ; destruct H1; revert H0 H1 Htwo; clear.
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

Lemma L2' f (Htwo : two f) (r : robogram f f) : solution_fully_synchronous r -> ~ 0 = delta r.
Proof.
  intros Hs H.
  destruct (Hs (goodies f) (demon2 f) (demon2_is_fully_synchronous _) (1/(1+1+1))
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


Theorem no_solution_fully_synchronous f (Htwo : two f) (r : robogram f f) :
  solution_fully_synchronous r -> False.
Proof.
  intros Hs.
  apply (L2' Htwo Hs).
  symmetry.
  apply meeting_theorem'; auto.
  revert Htwo; unfold two.
  destruct (prev f (prev f None)); auto.
  intros [].
Qed.
