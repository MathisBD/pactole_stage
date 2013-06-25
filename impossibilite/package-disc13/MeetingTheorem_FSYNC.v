(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, X. Urbain                                     *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Set Implicit Arguments.
Require Import ConvergentFormalism.
(* Require Import FiniteSum. *)
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
Definition pos0 g b (bp_ : name b -> Qc) :=
  {| gp := fun _:name g => 0
   ; bp := bp_
   |}.

Definition delta g b (r : robogram g b) bp :=
  algo r (pos0 g b bp).

(* First part of the proof with the shifting demon *)
Definition demon1 (d : Qc) g b (bp : name b -> Qc) : Qc -> demon g b :=
  cofix demon1 k :=
  NextDemon {| locate_byz := fun x => bp x + k
             ; frame := fun _ => 1
             |} (demon1 (k+d)).

Lemma demon1_is_fully_synchronous (g b : finite) (bp : name b -> Qc)
: forall q d, FullySynchronous (demon1 d g b bp q).
Proof.
  cofix.
  intros q.
  constructor.
  - unfold demon1.
    intros g'.
    constructor.
    simpl.
    discriminate.
  - simpl. 
    fold (demon1 d g b bp).
    apply demon1_is_fully_synchronous.
Qed.

Lemma S1' g b (x : name g) (r : robogram g b) (l : Qc) (bp : name b -> Qc)
: forall (gp : name g -> Qc) (k : Qc), (forall g, gp g = k) ->
  imprisonned l [delta r bp]
                (execute r (demon1 (delta r bp) g b bp k) gp) ->
  [delta r bp] = 0.
Proof.
  intros.
  set (p_plus_nd := fun p => nat_rec _ p (fun _ y => y + (delta r bp))).
  assert (forall n,
          exists gp, (forall g, gp g = p_plus_nd k n) /\
          imprisonned l [delta r bp] (execute r (demon1 (delta r bp) g b
                      bp (p_plus_nd k n)) gp)
  ).
  + induction n.
    - exists gp; split; auto.
    - clear - IHn x.
      destruct IHn as [gp [Hgp Himp]].
      exists (round r (demon_head (demon1 (delta r bp) g b bp
                      (p_plus_nd k n))) gp).
      split.
      * simpl.
        unfold round; simpl; unfold similarity; simpl; intros; rewrite Hgp.
        rewrite (@AlgoMorph g b r _ (pos0 g b bp) (id_perm g b));
        [fold (delta r bp); field; discriminate|].
        split; simpl; intros; [rewrite Hgp|]; ring.
      * destruct Himp; auto.
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
      cut (l - (k + delta r bp + delta r bp + delta r bp) =
           l - k - (delta r bp + delta r bp + delta r bp));
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

Lemma S2' g b (x : name g) (r : robogram g b) (bp : name b -> Qc)
: solution_FSYNC r -> ~ 0 < [delta r bp].
Proof.
  intros Hs H.
  assert ([delta r bp] = 0).
  + destruct (Hs (fun _=>0) (demon1 (delta r bp) g b bp 0)
             (demon1_is_fully_synchronous _ _ _ _ _)
                 [delta r bp] H) as [lim Hlim].
    remember (execute r (demon1 (delta r bp) g b bp 0) (fun _ => 0)).
    revert Heqe.
    generalize (fun x : name g => eq_refl 0).
    change (g -> 0 = 0) with (forall x, (fun _ : g => 0) x = 0).
    generalize (fun _ : g => 0).
    generalize 0 at 1 2.
    induction Hlim; intros; subst.
    - eapply S1'; eauto.
    - apply (fun K => IHHlim _ _ K (eq_refl _)); clear - H0.
      unfold round; simpl; intros.
      rewrite (@AlgoMorph g b r _ (pos0 g b bp) (id_perm g b)).
      * rewrite H0; unfold delta; field; discriminate.
      * split; simpl; intros; repeat rewrite H0; ring.
  + revert H0 H; generalize [delta r bp]; clear.
    intros q A B; subst; discriminate.
Qed.

Theorem meeting_theorem' g b (x : name g) (r : robogram g b) (bp : name b -> Qc)
: solution_FSYNC r -> delta r bp = 0.
Proof.
  intros Hs.
  generalize (S2' x bp Hs); generalize (delta r); clear.
  intros q Hneg.
  generalize (proj1 (Qcabs_Qcle_condition _ _) (Qcnot_lt_le _ _ Hneg)); clear.
  intros [A B]; apply Qcle_antisym; auto.
Qed.
