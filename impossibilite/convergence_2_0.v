(* line 78, Qc must be archimedian (to be proven) *)
Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import Field.
Require Import Qcabs.
Require Import Qcanon.

Definition no_elements : finite.
refine
 {| name := Empty_set
  ; next := fun b => match b with None => None | Some x => match x with end end
  ; prev := fun b => match b with None => None | Some x => match x with end end
  |}.
Proof. abstract (intros [[]|] [[]|]; split; split).
Proof. abstract (intros []).
Proof. abstract (intros []).
Defined.

Definition two_elements : finite.
refine
 {| name := bool
  ; next := fun b => match b with
                     | None => Some true
                     | Some true => Some false
                     | Some false => None
                     end
  ; prev := fun b => match b with
                     | None => Some false
                     | Some false => Some true
                     | Some true => None
                     end
  |}.
Proof.
  abstract (
    split; intros; subst; [destruct x as [[]|]|destruct y as [[]|]]; split
  ).
Proof.
  abstract (
    intros z; split; intros y Hy; split;
    intros [] H; inversion H; subst; inversion Hy
  ).
Proof.
  abstract (
    intros z; split; intros y Hy; split;
    intros [] H; inversion H; subst; inversion Hy
  ).
Defined.

Definition converger (p : position two_elements no_elements) : Qc :=
  (good_places p true + good_places p false)/(1+1).

Lemma converger_morph p q s
: PosEq q (pos_remap s p) -> converger p = converger q.
Proof.
  intros Heq; simpl in *.
  unfold converger.
  rewrite (good_ext Heq true).
  rewrite (good_ext Heq false).
  f_equal.
  destruct s as [sec ret Hsplit]; simpl.
  case_eq (ret (Good two_elements no_elements true)); simpl; [|intros []].
  case_eq (ret (Good two_elements no_elements false)); simpl; [|intros []].
  intros n Hn m Hm.
  generalize (proj2 (Hsplit _ _) Hn), (proj2 (Hsplit _ _) Hm); clear.
  destruct n, m; intros A B; [|ring|ring|]; rewrite A in B; inversion B.
Qed.

Record div2_e_rel (eps : Qc) (p1 p2 : Qc) : Prop :=
  { lesser_diameter : [p1 * (1+1)] <= [p2]
  ; bigger_diameter : eps < [p2]
  }.

Lemma decr_diameter_acc eps (H : 0<eps) : forall p, Acc (div2_e_rel eps) p.
Proof. (* TODO *)
admit.
Qed.

(******************************************************************************)

Definition solver_2_0 := {|algo:=converger;AlgoMorph:=converger_morph|}.

Theorem RegTest_2_0 : solution solver_2_0.
Proof.
  unfold solution.
  intros init_gp some_demon fair_some_demon eps pos_eps.
  remember (init_gp true - init_gp false) as diameter.
  revert some_demon fair_some_demon init_gp Heqdiameter.
  generalize (decr_diameter_acc pos_eps diameter).
  intros H; induction H.
  clear H.
  intros.
  assert (K := fun d Hd gp Hr => H0 _ Hr d Hd gp (eq_refl)); clear H0.
  destruct (Qclt_le_dec eps [x]) as [Hcomp|Hcomp].
  + assert (L := fun d Hd gp Hr => K d Hd gp {| lesser_diameter := Hr
                                              ; bigger_diameter := Hcomp |}).
    clear K; destruct fair_some_demon.
    assert (M := H true); clear H.
    generalize (fun x => eq_refl (init_gp x)); generalize init_gp at 1 3.
    induction M.
    - intros gp Hgp.
      destruct (L _ fair_some_demon (new_goods solver_2_0 (demon_head d) gp))
      as [lim Hlim]; [|exists lim; right; auto].
      clear - Heqdiameter H H0 Hgp.
      unfold new_goods; rewrite H0; clear H0; simpl; unfold converger; simpl.
      repeat rewrite Hgp; clear gp Hgp.
      subst; generalize (init_gp true), (init_gp false).
      revert H; generalize (good_reference (demon_head d) true).
      destruct (inv (good_reference (demon_head d) false)).
      * clear; intros.
        cut (q0-q1=((q0+l*((q*(q0-q0)+q*(q1-q0))/(1+1))-q1)*(1+1)));
        [intros []; apply Qcle_refl|].
        case Qcmult_plus_distr_r; unfold Qcdiv; repeat rewrite Qcmult_assoc.
        rewrite H; field; discriminate.
      * revert e; generalize (good_reference (demon_head d) false).
        clear; intros.
        cut (0 = ((q1+l*((q0*(q1-q1)+q0*(q2-q1))/(1+1))-
                  (q2+l0*((q*(q1-q2)+q*(q2-q2))/(1+1))))*(1+1)));
        [intros []; apply Qcabs_nonneg|].
        unfold Qcdiv.
        repeat case Qcmult_plus_distr_r; repeat rewrite Qcmult_assoc.
        rewrite H; rewrite e; field; discriminate.
    - case_eq (inv (good_reference (demon_head d) false)).
      * clear - H L Heqdiameter fair_some_demon.
        intros K _ gp Hgp.
        destruct (L _ fair_some_demon (new_goods solver_2_0 (demon_head d) gp))
        as [lim Hlim]; [|exists lim; right; auto].
        revert H K; subst; case (Hgp true); case (Hgp false); clear.
        unfold demon_head; destruct d; clear.
        intros H K; unfold new_goods; rewrite H, K; simpl; clear H K.
        unfold converger; simpl; generalize (gp true), (gp false).
        intros a b.
        cut (forall x y, x=y -> [x]<=[y]); [|intros x y []; apply Qcle_refl].
        intros H; apply H; clear H.
        field_simplify; [|discriminate].
        unfold Qcdiv; field_simplify; auto; discriminate.
      * intros K gp Hgp.
        destruct fair_some_demon.
        generalize (IHM fair_some_demon); clear - H K Hgp.
        intros L; destruct (L (new_goods solver_2_0 (demon_head d) gp))
        as [lim Hlim]; [|exists lim; right; auto].
        clear - H K Hgp.
        destruct d; simpl in *; unfold new_goods.
        intros []; simpl; [rewrite H|rewrite K]; simpl; auto.
  + clear K; exists (init_gp true); subst; clear - Hcomp pos_eps; left.
    cut (forall g, [init_gp true - init_gp g] <= eps).
    - generalize (init_gp true); intros pc; generalize init_gp.
      revert some_demon; clear; cofix; intros [da d] gp Hgp.
      cut (forall g, [pc - new_goods solver_2_0 da gp g] <= eps).
      * split; auto; apply RegTest_2_0; auto.
      * intros g; generalize (Hgp true), (Hgp false); clear.
        unfold solver_2_0, new_goods, converger, cmove; simpl.
        case (good_activation da g); [|case g; auto].
        generalize (gp true), (gp false), (gp g); clear.
        intros a b c.
        cut (((pc - a) + (pc - b)) / (1 + 1) =
             pc - (c + (a - c + (b - c)) / (1 + 1)));
        [intros []|field; discriminate].
        generalize (pc - a), (pc - b); clear; intros a b A B.
        apply Qcmult_lt_0_le_reg_r with [1+1]; [split|].
        case Qcabs_Qcmult.
        unfold Qcdiv;case Qcmult_assoc;rewrite Qcmult_inv_l;[|discriminate].
        rewrite Qcmult_1_r.
        apply Qcle_trans with ([a]+[b]); [apply Qcabs_triangle|].
        apply Qcle_trans with (eps + eps); [now apply Qcplus_le_compat|].
        rewrite Qcabs_pos; [|discriminate].
        rewrite Qcmult_plus_distr_r, Qcmult_1_r; apply Qcle_refl.
    - intros []; auto; generalize (init_gp true); clear - pos_eps.
      unfold Qcminus; intros k; rewrite Qcplus_opp_r.
      unfold Qclt, QArith_base.Qlt, BinInt.Zlt in pos_eps.
      intros H; simpl in *; rewrite pos_eps in H; clear pos_eps.
      discriminate.
Qed.
