Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import FiniteSum.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.

Definition id_perm g b : automorphism (ident g b).
refine {| section := id
        ; retraction := id
        |}.
abstract (unfold id; split; auto).
Defined.

(* Useful initial position and a special rational depending on a robogram *)
Definition pos0 g b := {| gp := fun _:name g => 0
                        ; bp := fun _:name b => 1
                        |}.

Definition delta g b (r : robogram g b) := algo r (pos0 g b).

(* First part of the proof with the shifting demon *)
Definition demon1 (d : Qc) g b : Qc -> demon g b :=
  cofix demon1 k :=
  NextDemon {| byz_replace := fun _ => k
             ; frame := fun _ => 1
             |} (demon1 (k+d)).

Lemma demon1_is_fair (d : Qc) g b : forall q, Fair (demon1 d g b q).
Proof.
  cofix; intros q; split.
  + simpl.
    fold (demon1 d g b).
    apply demon1_is_fair.
  + eleft; simpl; unfold inv; split.
Qed.

Lemma S1 g b (x : name g) (r : robogram g b) (l : Qc)
: forall (gp : name g -> Qc) (k : Qc), (forall g, gp g = k) ->
  imprisonned l [delta r] (execute r (demon1 (delta r) g b (1 + k)) gp) ->
  [delta r] = 0.
Proof.
  intros.
  set (p_plus_nd := fun p => nat_rec _ p (fun _ y => y + (delta r))).
  assert (forall n,
          exists gp, (forall g, gp g = p_plus_nd k n) /\
          imprisonned l [delta r] (execute r (demon1 (delta r) g b
                      (1 + p_plus_nd k n)) gp)
  ).
  + induction n.
    - exists gp; split; auto.
    - clear - IHn x.
      destruct IHn as [gp [Hgp Himp]].
      exists (round r(demon_head(demon1(delta r)g b(1+(p_plus_nd k n))))gp).
      split.
      * simpl.
        unfold round; simpl; unfold similarity; simpl; intros; rewrite Hgp.
        rewrite (@AlgoMorph g b r _ (pos0 g b) (id_perm g b));
        [fold (delta r); field; discriminate|].
        split;simpl; intros; [rewrite Hgp|] ; ring.
      * destruct Himp.
        revert Himp; clear.
        simpl; fold (demon1 (delta r) g b) (execute r).
        now rewrite Qcplus_assoc.
  + clear - H1 x.
    generalize (H1 0%nat), (H1 3%nat).
    simpl; clear - x.
    intros [gp0 [Hgp0 Himp0]] [gp3 [Hgp3 Himp3]].
    destruct Himp0 as [H0 _].
    destruct Himp3 as [H3 _].
    generalize (H0 x), (H3 x); clear - Hgp0 Hgp3.
    simpl; unfold round; simpl; unfold similarity; simpl.
    rewrite Hgp0, Hgp3.
    cut (forall a b, [a] <= [b] -> [a - (b + b + b)] <= [b] -> [b] = 0).
    * intros H K L; apply H with (l - k); auto.
      clear - L.
      cut (l - (k + delta r + delta r + delta r) =
           l - k - (delta r + delta r + delta r));
      [intros []; auto|ring].
    * clear; intros a b K L.
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
Qed.

Lemma S2 g b (x : name g) (r : robogram g b) : solution r -> ~ 0 < [delta r].
Proof.
  intros Hs H.
  destruct (Hs (fun _=>0) (demon1 (delta r) g b 1) (demon1_is_fair _ _ _ _)
               [delta r] H) as [lim Hlim].
  cut (forall (gp : name g -> Qc) (k : Qc), (forall g, gp g = k) ->
       attracted lim [delta r] (execute r (demon1 (delta r) g b (1 + k)) gp) ->
       [delta r] = 0).
  + intros K.
    generalize (K (fun _ => 0) 0 (fun x => eq_refl 0)); clear K.
    rewrite Qcplus_0_r; intros K; rewrite (K Hlim) in H; clear - H.
    discriminate.
  + clear - x.
    intros.
    remember (execute r (demon1 (delta r) g b (1+k)) gp).
    revert gp k H Heqe.
    induction H0; intros; subst.
    - eapply S1; eauto.
    - clear H0.
      apply (IHattracted (round r {|byz_replace:=fun _=>1+k
                                       ;frame:=fun _=>1|} gp)
                         (k + delta r)).
      * clear - H.
        intros g0; unfold round; simpl; unfold similarity; simpl.
        rewrite (@AlgoMorph g b r _ (pos0 g b) (id_perm g b));
        [fold (delta r); rewrite H; field; discriminate|].
        split; intros; simpl; repeat rewrite H; ring_simplify; split.
      * simpl; clear.
        fold (demon1 (delta r) g b) (execute r).
        now rewrite Qcplus_assoc.
Qed.

Theorem meeting_theorem g b (x : name g) (r : robogram g b)
: solution r -> delta r = 0.
Proof.
  intros Hs.
  generalize (S2 x Hs); generalize (delta r); clear.
  intros q Hneg.
  generalize (proj1 (Qcabs_Qcle_condition _ _) (Qcnot_lt_le _ _ Hneg)); clear.
  intros [A B]; apply Qcle_antisym; auto.
Qed.
