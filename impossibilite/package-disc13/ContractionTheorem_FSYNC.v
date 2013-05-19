Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import Qcanon.
Require Import Qcabs.
Require Import Field.

Record inv_pair :=
  { alpha : Qc
  ; beta : Qc
  ; Hinv : beta * alpha = 1
  }.

Definition simili_action' good bad (k : inv_pair) (t : Qc)
                                   (da : demonic_action good bad)
: demonic_action good bad
:= {| byz_replace := fun x => (alpha k) * (byz_replace da x) + t
    ; frame := fun x => (beta k) * (frame da x)
    |}.

Definition simili_demon' good bad k t
: demonic_action good bad -> demon good bad
:= cofix simili_demon' da :=
   NextDemon da (simili_demon' (simili_action' k t da)).
(******************************************************************************)
Definition fair_action good bad (da : demonic_action good bad)
: Prop
:= forall x : name good, frame da x <> 0.

Lemma simili_demon_fairness' good bad k t (da : demonic_action good bad)
: fair_action da -> FullySynchronous (simili_demon' k t da).
Proof.
  revert da; cofix.
  split.
  + clear - H.
    intros; split; simpl; auto.
  + simpl.
    fold (simili_demon' k t (simili_action' k t da)).
    apply simili_demon_fairness'.
    intros x Hx; apply (H x); simpl in *; clear - Hx.
    destruct (Qcmult_integral _ _ Hx); auto.
    exfalso; generalize (Hinv k); rewrite H; clear.
    discriminate.
Qed.
(******************************************************************************)
Definition similitude' k t good (gp1 gp2 : name good -> Qc) : Prop :=
  forall x, gp2 x = (alpha k) * (gp1 x) + t.

Definition fpower' A (f : A -> A) (a : A) : nat -> A :=
  fix fpower' n :=
  match n with
  | O => a
  | S n => f (fpower' n)
  end.

Definition after_tactic (k : inv_pair) (t : Qc) good bad (r : robogram good bad)
                        (da : demonic_action good bad) (gp :name good -> Qc)
: (name good -> Qc)
:= execution_head
   (execution_tail (execute r (simili_demon' k t da) gp)).

Lemma fpower_com' A (f : A -> A)
: forall p x, f (fpower' f x p) = fpower' f (f x) p.
Proof. intros p x; induction p; simpl; auto; f_equal; auto. Qed.

Definition inv_power (k : inv_pair) (n : nat) : inv_pair.
refine {| alpha := Qcpower (alpha k) n ; beta := Qcpower (beta k) n |}.
abstract (induction n; simpl; auto; rewrite (Qcmult_comm (beta k));
          case (Qcmult_assoc (beta k ^ n)); rewrite (Qcmult_assoc (beta k));
          rewrite Hinv; rewrite Qcmult_1_l; assumption
).
Defined.

Lemma demon_trick good bad (r : robogram good bad) gp dt k t
: similitude' k t good gp (after_tactic k t r dt gp) ->
  forall m : nat,
    exists u : Qc,
      similitude' (inv_power k m) u good gp
        (execution_head
          (fpower' (execution_tail (G:=good))
             (execute r (simili_demon' k t dt) gp) m)).
Proof.
  intros Hsim m; revert gp dt Hsim.
  induction m.
  + simpl; exists 0; intros x; simpl; ring.
  + intros.

    simpl.
    destruct (IHm (after_tactic k t r dt gp)(simili_action' k t dt)); clear IHm.
    * { revert Hsim; unfold similitude', after_tactic.
        simpl; clear; intros Hsim x.
        unfold simili_action'; unfold round at 1; simpl; rewrite Hsim.
        generalize (Hsim x); unfold round at 1; simpl.
        unfold similarity; simpl.
        revert Hsim; generalize (round r dt gp); clear.
        destruct (inv (frame dt x)).
        + rewrite e; rewrite (Qcmult_comm (beta k)); simpl.
          intros q Hq X; repeat case X; split.
        + destruct (inv (beta k * frame dt x)).
          - exfalso; destruct (Qcmult_integral _ _ e0).
            * generalize (Hinv k); rewrite H; discriminate.
            * revert e; rewrite H; rewrite Qcmult_comm; discriminate.
          - intros q Hq.
            generalize (alpha k * gp x + t) at 1 5; intros _x_ [].
            cut (forall a b, a = b -> alpha k * gp x + t + l0 * a =
                 (alpha k)*((gp x)+l*b)+t); [intros H; apply H|intros a _ []].
            * apply (AlgoMorph r
              {|Inversion := fun x y => conj (@eq_sym _ x y) (@eq_sym _ y x)|});
              split; simpl; intros; repeat rewrite Hq;
              case (Qcmult_1_l (frame dt x * _)); case (Hinv k); ring.
            * case (Qcmult_1_l l0); case e; clear e; case (Qcmult_1_l l).
              set (p := 1) at 1; case e0; subst p; case (Hinv k); ring.
      }
    * exists ((alpha k) ^ m * t + x).
      intros y; generalize (H y), (Hsim y); clear.
      unfold similitude', after_tactic; simpl.
      rewrite fpower_com'; simpl.
      fold (@simili_demon' good bad k t) (execute r).
      repeat (intros K; rewrite K; clear K).
      ring.
Qed.

Theorem Contraction good bad (r : robogram good bad)
 (Hr : solution_FSYNC r)
: forall gp dt k t,
  (fair_action dt) ->
  (similitude' k t good gp (after_tactic k t r dt gp)) ->
  forall x y, gp x <> gp y ->
  [alpha k] < 1.
Proof.
  intros gp dt k t Hfair Hsim x y Hxy.
  assert (gp x - gp y <> 0).
  - intros K; apply Hxy; clear Hxy.
    case (Qcplus_0_r (gp y)).
    case K; ring.
  - destruct (Hr gp (simili_demon' k t dt) (simili_demon_fairness' k t Hfair)
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
           forall n, e = fpower' (@execution_tail good)
                                 (execute r (simili_demon' k t dt) gp) n ->
           False);
      [intros K; exact (K _ H0 O (eq_refl _))|clear H0].
      intros e K; induction K.
      * { clear - Hsim H q H0.
          intros; subst.
          assert (forall m, exists u,
                  similitude' (inv_power k m) u good gp
                  (execution_head (fpower' (@execution_tail good)
                                  (execute r (simili_demon' k t dt) gp) m))).
          - clear - Hsim.
            apply demon_trick; auto.
          - destruct (H1 n) as [u Hu]; revert H0 Hu; clear - H q.
            generalize (fpower' (@execution_tail good)
                        (execute r (simili_demon' k t dt) gp) n).
            clear - H q.
            unfold similitude'; simpl; intros e Himp Hsim.
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
              intros q Hq Hxy; simpl; intros e He Hsim.
              destruct He.
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
              apply (Qcmult_lt_0_le_reg_r _ _ _ (Qcabs_nonnull _ Hu) R);split.
        }
      * now intros; apply (IHK (S n)); subst.
Qed.
