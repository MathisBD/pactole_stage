Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.

(* Impossibility in a N robots vs N robots *)

(* Useful permutations *)
Definition id_perm f : automorphism (ident f f).
refine {| section := id
        ; retraction := id
        |}.
abstract (unfold id; split; auto).
Defined.

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

(* Useful initial position and a special rational depending on a robogram *)
Definition pos0 f := {| good_places := fun _:name f => 0
                      ; bad_places := fun _:name f => 1
                      |}.

Definition delta f (r : robogram f f) := algo r (pos0 f).

(* First part of the proof with the shifting demon *)
Definition demon1 (d : Qc) f : Qc -> demon f f :=
  cofix demon1 k :=
  NextDemon {| bad_replace := fun _ => k
             ; good_activation := fun _ => true
             |} (demon1 (k+d)).

Lemma demon1_is_fair (d : Qc) f : forall q, Fair (demon1 d f q).
Proof.
  cofix; intros q; split.
  + simpl.
    fold (demon1 d f).
    apply demon1_is_fair.
  + left; split.
Qed.

Lemma S1 f (x : name f) (r : robogram f f) (l : Qc)
: forall (gp : name f -> Qc) (k : Qc), (forall g, gp g = k) ->
  imprisonned l [delta r] (execute r (demon1 (delta r) f (1 + k)) gp) ->
  [delta r] = 0.
Proof.
  intros.
  set (p_plus_nd := fun p => nat_rec _ p (fun _ y => y + (delta r))).
  assert (forall n,
          exists gp, (forall g, gp g = p_plus_nd k n) /\
          imprisonned l [delta r] (execute r (demon1 (delta r) f
                      (1 + p_plus_nd k n)) gp)
  ).
  + induction n.
    - exists gp; split; auto.
    - clear - IHn x.
      destruct IHn as [gp [Hgp Himp]].
      exists (new_goods r(demon_head(demon1(delta r)f(1+(p_plus_nd k n))))gp).
      split.
      * simpl.
        unfold new_goods; simpl; unfold center; simpl; intros; rewrite Hgp.
        rewrite (@AlgoMorph f f r 1 _ (pos0 f)); [fold (delta r); ring|].
        split with (id_perm f); split; simpl; intros; (try rewrite Hgp);
        ring_simplify; split.
      * destruct Himp.
        revert Himp; clear.
        simpl; fold (demon1 (delta r) f) (execute r).
        now rewrite Qcplus_assoc.
  + clear - H1 x.
    generalize (H1 0%nat), (H1 3%nat).
    simpl; clear - x.
    intros [gp0 [Hgp0 Himp0]] [gp3 [Hgp3 Himp3]].
    destruct Himp0 as [H0 _].
    destruct Himp3 as [H3 _].
    generalize (H0 x), (H3 x); clear - Hgp0 Hgp3.
    simpl; unfold new_goods; simpl; unfold center; simpl.
    rewrite Hgp0, Hgp3.
    repeat (rewrite (@AlgoMorph f f r 1 _ (pos0 f)); fold (delta r)).
    - clear.
      cut (forall a b, [a] <= [b] -> [a - (b + b + b)] <= [b] -> [b] = 0).
      * intros H K L; apply H with (l - (k + 1 * delta r)); auto.
        clear - L.
        cut (l - (k + delta r + delta r + delta r + 1 * delta r) =
             l - (k + 1 * delta r) - (delta r + delta r + delta r));
        [intros []; auto|ring].
      * { clear; intros a b K L.
          apply Qcle_antisym; [|apply Qcabs_nonneg].
          rewrite Qcabs_Qcminus in L.
          generalize (Qcplus_le_compat _ _ _ _ K
                      (Qcle_trans _ _ _ (Qcabs_triangle_reverse _ _) L)).
          clear; intros K; generalize (proj1 (Qcle_minus_iff _ _) K); clear K.
          cut (-[b] = [b]+[b]+-([a]+([b+b+b]-[a]))).
          - intros [].
            intros H; generalize (Qcopp_le_compat _ _ H).
            now rewrite Qcopp_involutive.
          - cut ([b]+[b]+[b]=[b+b+b]); [intros []; ring|].
            cut ((1+1+1)*b=b+b+b); [intros []|ring].
            cut ((1+1+1)*[b]=[b]+[b]+[b]); [intros []|ring].
            now rewrite Qcabs_Qcmult.
        }
    - split with (id_perm f).
      split; simpl; intros; (try rewrite Hgp3); ring_simplify; split.
    - split with (id_perm f).
      split; simpl; intros; (try rewrite Hgp0); ring_simplify; split.
Qed.

Lemma S2 f (x : name f) (r : robogram f f) : solution r -> ~ 0 < [delta r].
Proof.
  intros Hs H.
  destruct (Hs (fun _=>0) (demon1 (delta r) f 1) (demon1_is_fair _ _ _)
               [delta r] H) as [lim Hlim].
  cut (forall (gp : name f -> Qc) (k : Qc), (forall g, gp g = k) ->
       attracted lim [delta r] (execute r (demon1 (delta r) f (1 + k)) gp) ->
       [delta r] = 0).
  + intros K.
    generalize (K (fun _ => 0) 0 (fun x => eq_refl 0)); clear K.
    rewrite Qcplus_0_r; intros K; rewrite (K Hlim) in H; clear - H.
    discriminate.
  + clear - x.
    intros.
    remember (execute r (demon1 (delta r) f (1+k)) gp).
    revert gp k H Heqe.
    induction H0; intros; subst.
    - eapply S1; eauto.
    - clear H0.
      apply (IHattracted (new_goods r {|bad_replace:=fun _=>1+k
                                       ;good_activation:=fun _=>true|} gp)
                         (k + delta r)).
      * clear - H.
        intros g; unfold new_goods; simpl; unfold center; simpl.
        rewrite (@AlgoMorph f f r 1 _ (pos0 f));
        [fold (delta r); rewrite H; ring|].
        split with (id_perm f).
        split; intros; simpl; repeat rewrite H; ring_simplify; split.
      * simpl; clear.
        fold (demon1 (delta r) f) (execute r).
        now rewrite Qcplus_assoc.
Qed.

(* Second part of the proof with the lazy demon *)
Definition lazy_action f : demonic_action f f :=
  {| bad_replace := fun x => match next f (Some x) with None => 0 | _ => 1 end
   ; good_activation := fun _ => true
   |}.

Definition demon2 f : demon f f :=
  cofix demon2 := NextDemon (lazy_action f) demon2.

Lemma demon2_is_fair f : Fair (demon2 f).
Proof. cofix; split; auto; left; split. Qed.

Definition goodies f : name f -> Qc :=
  fun x => match next f (Some x) with None => 1 | _ => 0 end.

Definition two f :=
  match prev f (prev f None) with None => False | _ => True end.

Lemma stable_goodies f (r : robogram f f) (Hd : 0 = delta r)
: forall gp, (forall g : name f, gp g = goodies f g) ->
              forall g : name f, new_goods r (lazy_action f) gp g = goodies f g.
Proof.
  intros.
  unfold new_goods; simpl; unfold center; simpl.
  rewrite (@AlgoMorph f f r (match next f (Some g) with None => -1%Qc
                             | _ => 1 end) _ (pos0 f)).
  + fold (delta r); case Hd; case H; clear.
    destruct (next f (Some g)); ring.
  + split with (match next f (Some g) with
                | None => swap_perm2 f | _ => swap_perm1 f end).
    split; simpl; intros n; repeat rewrite H; unfold goodies;
    destruct (next f (Some g)); unfold pos_remap_aux; simpl;
    unfold swap_p; simpl; destruct (next f (Some n)); ring.
Qed.

Lemma L1 f (Htwo : two f) (r : robogram f f) (l : Qc) (H : 0 = delta r)
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
  generalize (L2 Htwo Hs).
  generalize (fun x => S2 x Hs).
  revert Htwo; unfold two.
  destruct (prev f (prev f None)); auto.
  intros _ H; generalize (delta r), (H n); clear.
  intros a Ka Ha.
  destruct (proj1 (Qcabs_Qcle_condition _ _) (Qcnot_lt_le _ _ Ka)).
  apply Ha.
  apply Qcle_antisym; auto.
Qed.
