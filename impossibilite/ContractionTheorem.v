Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import Qcanon.
Require Import Qcabs.
Require Import Field.
Require Import List.

Definition finite_run good bad (r : robogram good bad)
: (list (demonic_action good bad)) -> (demonic_action good bad) ->
  (name good -> Qc) -> (name good -> Qc) :=
  fix finite_run l da gp :=
  let gp := new_goods r da gp in
  match l with
  | nil => gp
  | cons da l => finite_run l da gp
  end.

Definition demon_tactic good bad :=
  prod (demonic_action good bad) (list (demonic_action good bad)).

Record inv_pair :=
  { alpha : Qc
  ; beta : Qc
  ; Hinv : beta * alpha = 1
  }.

Definition simili_action good bad (k : inv_pair) (t : Qc)
                                  (da : demonic_action good bad)
: demonic_action good bad
:= {| bad_replace := fun x => (alpha k) * (bad_replace da x) + t
    ; good_reference := fun x => (beta k) * (good_reference da x)
    |}.

Definition tactic_rot good bad k t (dt : demon_tactic good bad)
: demon_tactic good bad
:= let (da, l) := dt in
   let sda := simili_action k t da in
   match l with
   | nil => (sda, nil)
   | da :: l => (da, l ++ sda :: nil)
   end.

Definition simili_demon good bad k t
: demon_tactic good bad -> demon good bad
:= cofix simili_demon dt :=
   let (da, l) := dt in NextDemon da (simili_demon (tactic_rot k t dt)).
(******************************************************************************)
Definition fair_tactic_ good bad (x : name good)
: demonic_action good bad -> list (demonic_action good bad) -> Prop
:= fix fair_tactic da l :=
   match inv (good_reference da x) with
   | IsNul _ => match l with nil => False | da :: l => fair_tactic da l end
   | Inv _ _ => True
   end.

Definition fair_tactic good bad (dt : demon_tactic good bad) : Prop :=
  forall x, fair_tactic_ x (fst dt) (snd dt).

Lemma simili_demon_fairness good bad k t (dt : demon_tactic good bad)
: fair_tactic dt -> Fair (simili_demon k t dt).
Proof.
  revert dt; cofix.
  split.
  + destruct dt; simpl in *.
    fold (@simili_demon good bad k t).
    apply simili_demon_fairness; intros x; generalize (H x); simpl; clear.
    destruct l; simpl; auto.
    - destruct (inv (good_reference d x)); intros [].
      destruct (inv (beta k * good_reference d x)); auto.
      destruct (Qcmult_integral _ _ e0).
      * clear - H; destruct k; simpl in *; subst; discriminate.
      * rewrite H in e; clear - e; rewrite Qcmult_comm in e; discriminate.
    - revert d0; induction l; simpl in *; intros.
      * destruct (inv (good_reference d0 x)); auto.
        destruct (inv (good_reference d x)); destruct H.
        destruct (inv (beta k * good_reference d x)); auto.
        destruct (Qcmult_integral _ _ e1);
        [ clear - H; destruct k; simpl in *; subst; discriminate
        | rewrite H in e0; clear - e0; rewrite Qcmult_comm in e0; discriminate
        ].
      * destruct (inv (good_reference d0 x)); auto.
  + intros g.
    generalize (H g); clear.
    destruct dt; revert d; simpl.
    set (s := l) at 1; rewrite (app_nil_end l); subst s.
    generalize (@nil (demonic_action good bad)).
    induction l; simpl; auto.
    - intros l d; case_eq (inv (good_reference d g)).
      * intros e _ [].
      * eleft; simpl; eauto.
    - intros m d; case_eq (inv (good_reference d g)).
      * eright; simpl; eauto.
        fold (@simili_demon good bad k t).
        now case app_assoc; apply IHl.
      * eleft; simpl; eauto.
Qed.
(******************************************************************************)
Definition similitude k t good (gp1 gp2 : name good -> Qc) : Prop :=
  forall x, gp2 x = (alpha k) * (gp1 x) + t.

Definition fpower A (f : A -> A) (a : A) : nat -> A :=
  fix fpower n :=
  match n with
  | O => a
  | S n => f (fpower n)
  end.

Definition after_tactic (k : inv_pair) (t : Qc) good bad (r : robogram good bad)
                        (dt : demon_tactic good bad) (gp :name good -> Qc)
: (name good -> Qc)
:= execution_head
   (fpower (@execution_tail good) (execute r (simili_demon k t dt) gp)
           (S (length (snd dt)))).

Lemma fpower_com A (f : A -> A)
: forall p q x, fpower f x (q + p) = fpower f (fpower f x p) q.
Proof. intros p q x; induction q; simpl; auto; f_equal; auto. Qed.

Definition inv_power (k : inv_pair) (n : nat) : inv_pair.
refine {| alpha := Qcpower (alpha k) n ; beta := Qcpower (beta k) n |}.
abstract (induction n; simpl; auto; rewrite (Qcmult_comm (beta k));
          case (Qcmult_assoc (beta k ^ n)); rewrite (Qcmult_assoc (beta k));
          rewrite Hinv; rewrite Qcmult_1_l; assumption
).
Defined.

Lemma Qcabs_nonnull : forall q, q <> 0 -> 0 < [q].
Proof.
  intros u Hu; destruct (Qclt_le_dec 0 [u]); auto; destruct Hu.
  destruct (proj1 (Qcabs_Qcle_condition _ _) q); apply Qcle_antisym; auto.
Qed.

Lemma cycle k t good bad dt (r : robogram good bad) gp
: fpower (@execution_tail good)
  (execute r (simili_demon k t dt) gp) (S (length (snd dt))) =
  execute r
   (simili_demon k t (fpower (tactic_rot k t) dt (S (length (snd dt)))))
   (after_tactic k t r dt gp).
Proof.
  unfold after_tactic.
  generalize (S (length (snd dt))); intros n; induction n; auto.
  simpl; rewrite IHn; clear IHn.
  unfold execution_tail; fold (@execution_tail good);
  unfold execution_head; unfold execute; fold (execute r); f_equal; clear.
  generalize (fpower (tactic_rot k t) dt n); intros []; split.
Qed.

Definition big_rot good bad k t (dt : demon_tactic good bad) :=
  (simili_action k t (fst dt), map (simili_action k t) (snd dt))
  : demon_tactic good bad.

Lemma big_step good bad k t (dt : demon_tactic good bad)
: fpower (tactic_rot k t) dt (S (length (snd dt))) = big_rot k t dt.
Proof.
  destruct dt; unfold fst, snd.
  set (a := l) at 1; rewrite (app_nil_end a); subst a.
  change (big_rot k t (d, l))
  with (match nil with
        | nil => big_rot k t (d, l)
        | a :: m => let (x, y) := big_rot k t (d, l) in (a, m++x::y)
        end).
  generalize (@nil (demonic_action good bad)).
  revert d; induction l; auto.
  intros d n.
  generalize (IHl a (n ++ (simili_action k t d) :: nil)); clear.
  change (S (length (a :: l))) with (plus (S O) (S (length l))).
  rewrite Plus.plus_comm; rewrite fpower_com.
  generalize (S (length l)); simpl.
  intros m H; case app_assoc; rewrite H; clear.
  destruct n; auto; simpl; f_equal; clear.
  case app_assoc; auto.
Qed.

Lemma X
(good : finite)
(bad : finite)
(r : robogram good bad)
(gp : name good -> Qc)
(dt : demon_tactic good bad)
(k : inv_pair)
(t : Qc)
(Hsim : similitude k t good gp
         (after_tactic k t r dt gp))
:
forall m : nat,
exists u : Qc,
  similitude (inv_power k m) u good gp
    (execution_head
       (fpower (execution_tail (good:=good))
          (execute r (simili_demon k t dt) gp) (m * S (length (snd dt))))).
Proof.
intros m; revert gp dt Hsim.
induction m.
simpl.
exists 0; intros x; simpl; ring.
unfold mult; fold (mult m).
intros.
rewrite Plus.plus_comm.
rewrite fpower_com.
rewrite cycle.
assert (Z : forall n (dt : demon_tactic good bad),
length (snd (fpower (tactic_rot k t) dt n))
= length (snd dt)).
clear; intros n dt.
induction n; simpl; auto.
destruct (fpower (tactic_rot k t) dt n); simpl in *.
destruct l; simpl in *; auto.
generalize (simili_action k t d); case IHn; clear.
intros; induction l; simpl in *; auto.

destruct (IHm (after_tactic k t r dt gp) (fpower (tactic_rot k t) dt
(S (length (snd dt))))); clear IHm.

revert Hsim.
unfold similitude.
unfold after_tactic.
rewrite Z.
Notation "'η'" := (@execution_head _).
Notation "'τ'" := (@execution_tail _).
Notation "« k ∞ t ∞ dt »" := (simili_demon k t dt) (format "« k ∞ t ∞ dt »").
Notation "« k 'ρ' t »" := (tactic_rot k t) (format "« k 'ρ' t »").
Notation "'α'" := (@alpha _).
Notation "⦃ dt ⦄" := (S (length (snd dt))) (format "⦃ dt ⦄").
Notation "⟦ r ∷ gp ↠ d ⟧" := (execute r d gp) (format "⟦ r ∷ gp ↠ d ⟧").
Notation "« f ↑ n ∷ x »" := (fpower f x n) (format "« f ↑ n ∷ x »").
idtac.

generalize (η «τ↑⦃dt⦄∷⟦r∷gp↠«k∞t∞dt»⟧») at 1 2.
generalize (⦃dt⦄) at 2 3.
clear - Z.
intros.
revert gp q Hsim dt; induction n; auto.
intros.
cut (forall x, new_goods r (simili_action k t (fst dt)) q x =
        (alpha k) * (new_goods r (fst dt) gp) x + t).
intros P; generalize (IHn _ _ P (tactic_rot k t dt)).
clear - Hsim Z.
change (S n) with (plus (S O) n).
rewrite Plus.plus_comm.
rewrite fpower_com.
rewrite fpower_com.
unfold fpower at 5 8.
unfold execution_tail at 4 6.
unfold execute at 3 4.
fold (execute r (demon_tail «k∞t∞dt»)).
fold (execute r (demon_tail «k∞t∞««k ρ t»↑⦃dt⦄∷dt»»)).
unfold demon_head.
unfold demon_tail.
unfold simili_demon.
fold (@simili_demon good bad k t).
generalize (big_step k t dt).
destruct ««k ρ t»↑⦃dt⦄∷dt».
intros Heq;
cut (d = fst (big_rot k t dt));
[cut (l = snd (big_rot k t dt));
[clear Heq; intros A B; subst|case Heq; split]|case Heq; split].
unfold big_rot.
destruct dt.
unfold fst, snd.
intros [].
fold (snd («k ρ t» (d, l))).

f_equal.
f_equal.
f_equal.
f_equal.
clear - Z.
rewrite (big_step k t («k ρ t» (d, l))).
unfold big_rot.
simpl.
destruct l; simpl.
split.
f_equal.
rewrite map_app.
split.

clear - Hsim.
destruct dt; simpl.
intros x; clear - Hsim.
unfold new_goods.
simpl.
destruct (inv (good_reference d x)).
rewrite e.
rewrite (Qcmult_comm (beta k)).
simpl.
auto.
destruct (inv (beta k * good_reference d x)).
revert e e0; generalize (good_reference d x); intros y B A; exfalso.
clear - A B.
revert B.
case (Qcmult_1_l y).
set (a := 1) at 2; case (Hinv k); subst a.
rewrite (Qcmult_comm (beta k)).
case Qcmult_assoc; rewrite A; clear.
cut (0 = l * (alpha k * 0)); [intros []|ring].
discriminate.
unfold similarity; simpl.
assert (forall x y : ident good bad, x = y <-> y = x).
clear; split; auto.
rewrite (@AlgoMorph good bad r
  {|
  good_places := fun n : name good =>
                 good_reference d x * (gp n - gp x);
  bad_places := fun n : name bad =>
                good_reference d x *
                (bad_replace d n - gp x) |}
  {|
  good_places := fun n : name good =>
                 beta k * good_reference d x *
                 (q n - q x);
  bad_places := fun n : name bad =>
                beta k * good_reference d x *
                (alpha k * bad_replace d n + t - q x) |}
  {|Inversion := H|}).
generalize (algo r
  {|
  good_places := fun n : name good =>
                 beta k * good_reference d x *
                 (q n - q x);
  bad_places := fun n : name bad =>
                beta k * good_reference d x *
                (alpha k * bad_replace d n + t - q x) |}).
clear - Hsim e e0.
intros.
rewrite Hsim.
cut (l * alpha k = l0); [intros []; ring|].
revert e e0; generalize (good_reference d x); clear.
intros.
case (Qcmult_1_l (l * alpha k)).
case e0; clear e0.
cut ((beta k * alpha k) * (l * q) * l0 = l0 * (beta k * q) * (l * alpha k));
[intros []|ring].
rewrite Hinv.
rewrite e.
ring.
unfold pos_remap; simpl.
generalize (good_reference d x), (bad_replace d).
split; simpl.
intros n.
case (Qcmult_1_l (q0 * (gp n - gp x))).
case (Hinv k).
repeat rewrite Hsim; ring.
intros n.
case (Qcmult_1_l (q0 * (q1 n - gp x))).
case (Hinv k).
rewrite Hsim; ring.

exists ((alpha k) ^ m * t + x).
revert H.
rewrite Z; clear Z.
revert Hsim.
unfold similitude.
unfold after_tactic.

generalize (S (length (snd dt))).
intros l.
generalize (execute r (simili_demon k t dt) gp).
intros e.
generalize (execution_head (fpower (@execution_tail good) e l)).
intros f.
generalize (fpower (tactic_rot k t) dt l).
intros d.
generalize (execute r (simili_demon k t d) f).
intros g.
generalize (fpower (@execution_tail good) g (m * l)).
clear.
intros e H I y.
rewrite I.
rewrite H.
clear.
simpl.
ring.
Qed.

Theorem Contraction good bad (r : robogram good bad) (Hr : solution r)
: forall gp dt k t,
  (fair_tactic dt) ->
  (similitude k t good gp (after_tactic k t r dt gp)) ->
  forall x y, gp x <> gp y ->
  [alpha k] < 1.
Proof.
  intros gp dt k t Hfair Hsim x y Hxy.
  assert (gp x - gp y <> 0).
  - intros K; apply Hxy; clear Hxy.
    case (Qcplus_0_r (gp y)).
    case K; ring.
  - destruct (Hr gp (simili_demon k t dt) (simili_demon_fairness k t Hfair)
                    ([gp x - gp y] / (1 + 1 + 1))).
    + revert H; generalize (gp x - gp y); clear.
      intros q Hq.
      unfold Qcdiv.
      cut (0 * (/ (1 + 1 + 1)) = 0); [intros []|ring].
      apply Qcmult_lt_compat_r; [split|].
      apply Qcabs_nonnull; auto.
    + clear Hxy.
      destruct (Qclt_le_dec [alpha k] 1); auto; exfalso.
      cut (forall e, attracted x0 ([gp x - gp y] / (1 + 1 + 1)) e ->
           forall n, e = fpower (@execution_tail good)
                                (execute r (simili_demon k t dt) gp) n ->
           False);
      [intros K; exact (K _ H0 O (eq_refl _))|clear H0].
      intros e K; induction K.
      * { clear - Hsim H q H0.
          intros; subst.
          assert (forall m, exists u,
                  similitude (inv_power k m) u good gp
                  (execution_head
                   (fpower (@execution_tail good)
                   (execute r (simili_demon k t dt) gp)
                   (mult m (S (length (snd dt))))))).
          - clear - Hsim.
            apply X; auto.
          - destruct (H1 n) as [u Hu]; revert H0 Hu; clear - H q.
            rewrite Mult.mult_comm; simpl.
            rewrite Plus.plus_comm; rewrite fpower_com.
            generalize (fpower (@execution_tail good)
                        (execute r (simili_demon k t dt) gp) n).
            generalize (mult (length (snd dt)) n); clear - H q.
            unfold similitude; simpl; intros m e Himp Hsim.
            assert (1 <= [alpha k ^ n]).
            + revert q; generalize (alpha k); clear.
              intros q Hq; induction n; simpl.
              * discriminate.
              * rewrite Qcabs_Qcmult.
                apply Qcle_trans with [q ^ n]; auto.
                set (a:=q) at 3; case (Qcmult_1_l [q ^ n]); subst a.
                apply Qcmult_le_compat_r; auto.
                apply Qcle_trans with 1; auto.
                discriminate.
            + revert H0 H e Himp Hsim; generalize (alpha k ^ n); clear.
              intros q Hq Hxy; induction m; simpl; intros e He Hsim.
              * destruct He.
                generalize (H x), (H y); repeat rewrite Hsim; revert Hxy.
                generalize (gp x), (gp y); clear - Hq; intros a b Hab.
                intros K L; case (Qcabs_opp (x0 - (q * a + u))) in K.
                generalize (Qcle_trans _ _ _ (Qcabs_triangle _ _)
                                             (Qcplus_le_compat _ _ _ _ K L)).
                cut (q * (a - b) = - (x0 - (q * a + u)) + (x0 - (q * b + u)));
                [intros []|ring].
                revert Hab; generalize (a - b); clear - Hq; intros u Hu.
                rewrite Qcabs_Qcmult.
                intros P.
                generalize (Qcle_trans _ _ _
                            (Qcmult_le_compat_r _ _ _ Hq (Qcabs_nonneg u)) P).
                cut (((1+1)/(1+1+1))*[u]=[u]/(1+1+1)+[u]/(1+1+1));
                [intros []|field; discriminate].
                clear - Hu; intros R.
                apply (Qcmult_lt_0_le_reg_r _ _ _ (Qcabs_nonnull Hu) R); split.
              * destruct He; apply (IHm _ He); intros; case Hsim; clear.
                f_equal; revert e; induction m; simpl; intros; f_equal; auto.
        }
      * now intros; apply (IHK (S n)); subst.
Qed.
