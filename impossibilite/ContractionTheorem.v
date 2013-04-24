Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import Qcanon.
Require Import Qcabs.
Require Import Field.
Require Import Equivalences.
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

Definition simili_action good bad (k t : Qc) (da : demonic_action good bad)
: demonic_action good bad
:= {| bad_replace := fun x => k * (bad_replace da x) + t
    ; good_activation := good_activation da
    |}.

Definition tactic_rot good bad (k t : Qc) (dt : demon_tactic good bad)
: demon_tactic good bad
:= let (da, l) := dt in
   let sda := simili_action k t da in
   match l with
   | nil => (sda, nil)
   | da :: l => (da, l ++ sda :: nil)
   end.

Definition simili_demon good bad (k t : Qc)
: demon_tactic good bad -> demon good bad
:= cofix simili_demon dt :=
   let (da, l) := dt in NextDemon da (simili_demon (tactic_rot k t dt)).
(******************************************************************************)
Definition fair_tactic_ good bad (x : name good)
: demonic_action good bad -> list (demonic_action good bad) -> Prop
:= fix fair_tactic da l :=
   if good_activation da x
   then True
   else match l with nil => False | cons da l => fair_tactic da l end.

Definition fair_tactic good bad (dt : demon_tactic good bad) : Prop :=
  forall x, fair_tactic_ x (fst dt) (snd dt).

Lemma simili_demon_fairness good bad (k t : Qc) (dt : demon_tactic good bad)
: fair_tactic dt -> Fair (simili_demon k t dt).
Proof.
  revert dt; cofix.
  split.
  + destruct dt; simpl in *.
    fold (@simili_demon good bad k t).
    apply simili_demon_fairness; intros x; generalize (H x); simpl; clear.
    destruct l; simpl; auto.
    intros K.
    revert K; case_eq (good_activation d x); intros Heq K.
    - clear - Heq; induction l; simpl; case_eq (good_activation d0 x); auto.
      * now rewrite Heq.
      * destruct l; simpl in *; destruct (good_activation a x); auto;
        intros H; rewrite H in IHl; auto.
    - revert d0 K; clear; induction l; simpl in *; intros d0;
      case_eq (good_activation d0 x); auto.
      intros _ [].
  + intros g.
    generalize (H g); clear.
    destruct dt; revert d; simpl.
    set (s := l) at 1; rewrite (app_nil_end l); subst s.
    generalize (@nil (demonic_action good bad)).
    induction l; simpl; auto.
    - left; simpl.
      destruct (good_activation d g), H; auto.
    - intros m d; case_eq (good_activation d g).
      * left; simpl; auto.
      * right; simpl; auto.
        fold (@simili_demon good bad k t).
        now case app_assoc; apply IHl.
Qed.
(******************************************************************************)
Definition similitude (k t : Qc) good (gp1 gp2 : name good -> Qc) : Prop :=
  forall x, gp2 x = k * (gp1 x) + t.

Definition after_tactic good bad (r : robogram good bad)
                        (dt : demon_tactic good bad) (gp :name good -> Qc)
: (name good -> Qc)
:= fold_left (fun gp da => new_goods r da gp) (snd dt) (new_goods r (fst dt) gp)
.

Theorem Contraction good bad (r : robogram good bad) (Hr : solution r)
: forall gp dt k t,
  (fair_tactic dt) ->
  (similitude k t good gp (after_tactic r dt gp)) ->
  forall x y, gp x <> gp y ->
  [k] < 1.
Proof.
  intros gp dt k t Hfair Hsim x y Hxy.
  assert (gp x - gp y <> 0).
  - intros K; apply Hxy; clear Hxy.
    case (Qcplus_0_r (gp y)).
    case K; ring.
  - destruct (Hr gp (simili_demon k t dt) (simili_demon_fairness k t Hfair)
              ([gp x - gp y] / (1+1+1))).
    +
admit.
    + clear Hxy.
      set (jump := fun gp dt n => nat_rec (fun _ => execution good) (execute r
                   (simili_demon k t dt) gp) (fun _ => @execution_tail good)
                   (mult n (S (length (snd dt))))).
      assert (exists l, exists n, imprisonned l ([gp x - gp y]/(1+1+1))
              (jump gp dt n)).
      * { subst jump; revert H0.
          generalize (execute r (simili_demon k t dt) gp).
          generalize ([gp x - gp y] / (1 + 1 + 1)).
          generalize (length (snd dt)).
          clear; intros.
          induction H0.
          - now split with x0; split with O.
          - destruct IHattracted as [l [m Hlm]].
            split with l; split with (S m); revert Hlm; simpl; clear.
            generalize (mult m (S n)); intros k H.
            induction n; simpl; [|destruct IHn; auto].
            cut (nat_rec (fun _ => execution good) (execution_tail e)
                         (fun _ => execution_tail (good:=good)) k =
                 execution_tail (nat_rec (fun _ => execution good) e
                                 (fun _ => execution_tail (good:=good)) k));
            [intros []; auto|clear].
            induction k; simpl in *; auto.
            now case IHk.
        }
      * clear H0.
        destruct H1 as [lim [iter Himp]].
        assert (forall gp dt,
                similitude k t good gp (after_tactic r dt gp) ->
                forall iter,
                exists gp', exists dt',
                similitude k t good gp' (after_tactic r dt' gp') /\
                jump gp dt (S iter) = jump gp' dt' iter).
admit.

revert Hsim Himp.


destruct IHn.
auto.
            + induction k; simpl in *; auto.
      destruct (Qclt_le_dec [k] 1); auto.
      exfalso.




      cut (forall exec, attracted x0 ([gp x - gp y]/(1+1+1)) exec ->
           forall n, exec <> nat_rec (fun _ => execution good)
                     (execute r (simili_demon k t dt) gp)
                     (fun _ => @execution_tail good) n);
      [intros K; exact (K _ H0 O (eq_refl _))|].
      clear - Hsim H q.
      intros e He; induction He; intros n Hn; subst; simpl in *;
      [|apply (IHHe (S n)); simpl; auto].

      induction n; simpl in *.
destruct H0 as [K _]; simpl in *.
generalize (K x), (K y); clear - H.
admit.

apply IHn.
split; auto.
clear  - Hsim H0 q H.
      destruct H0 as [K _]; simpl in *.
      fold (@simili_demon good bad k t) in *.
      destruct dt.
      assert (exists n, []<[k]^n).
admit.
Qed.
