Set Implicit Arguments.
Require Import ConvergentFormalism.
Require Import Field.
Require Import Qcanon.
Require Import Qcabs.

Require Import Utf8.

Inductive LocallyStronglyKBoundedForOne good byz (k:nat) g (d:demon good byz): Prop :=
  ImmediatelyKBounded:
    (frame (demon_head d) g) ≠ 0 → LocallyStronglyKBoundedForOne k g d
| LaterKBounded:
    (k>0)%nat →  (frame (demon_head d) g) = 0 →
    LocallyStronglyKBoundedForOne (k-1) g (demon_tail d) →
    LocallyStronglyKBoundedForOne k g d.

CoInductive StronglyKBounded good byz k (d:demon good byz) :=
  NextKBounded: (∀ g, LocallyStronglyKBoundedForOne k g d)
    → StronglyKBounded k (demon_tail d)
    → StronglyKBounded k d.

Definition da_similar g d (d1 d2:demonic_action g d): Prop :=
  (forall x, d1.(frame) x = d2.(frame) x) /\
  (forall x, d1.(locate_byz) x = d2.(locate_byz) x).

CoInductive bisimilar g b: demon g b -> demon g b -> Prop :=
  bisim_samehead:
    forall d1 d2,
      bisimilar (demon_tail d1) (demon_tail d2) -> 
      da_similar (demon_head d1) (demon_head d2) -> 
      bisimilar d1 d2.


(** Devrait être évident. *)
Lemma bisimilar_kbounded : forall good byz k (d d':demon good byz),
                             bisimilar d d' -> StronglyKBounded k d
                             -> StronglyKBounded k d'.
Proof.
  intros good byz k.
  cofix.
  intros d d' Hdd' Hd.
  split.
  + intros g; revert Hdd'; destruct Hd as [Hd _]; generalize (Hd g); clear.
    intros Hd; revert d'; induction Hd; simpl.
    - left; destruct Hdd' as [h t _ [L _]]; simpl in *.
      now case (L g).
    - right; auto.
      * destruct Hdd' as [h t _ [L _]]; simpl in *.
        now case (L g).
      * apply IHHd.
        now destruct Hdd'.
  + apply bisimilar_kbounded with (demon_tail d).
    - now destruct Hdd'.
    - now destruct Hd.
Qed.

Require Import ContractionTheorem_FAIR.
Require Import NoSolutionFAIR_3f.

Lemma LocallyStronglyTwoBounded_demon_trick g b r:
  LocallyStronglyKBoundedForOne 2 r (simili_demon unity 0 (demon_trick g b)).
Proof.
  destruct r;simpl.
  - eapply LaterKBounded.
    + auto.
    + simpl. reflexivity.
    + eapply ImmediatelyKBounded.
      simpl.
      discriminate.
  - eapply ImmediatelyKBounded.
    simpl.
    discriminate.
Qed.

Lemma LocallyStronglyTwoBounded_demon_trick' g b r:
  LocallyStronglyKBoundedForOne 2 r (demon_tail (simili_demon unity 0 (demon_trick g b))).
Proof.
  destruct r.
  - eapply ImmediatelyKBounded.
    simpl.
    discriminate.
  - eapply LaterKBounded.
    + auto.
    + simpl. reflexivity.
    + eapply ImmediatelyKBounded.
      simpl.
      discriminate.
Qed.



Lemma bisim g b:
  forall X Y, da_similar X Y ->
  bisimilar (demon_tail (@simili_demon g b unity 0 (X, nil)))
            (@simili_demon g b unity 0 (Y, nil)).
Proof.
  unfold simili_demon. simpl.
  unfold simili_action. simpl.
  replace (cofix simili_demon (dt : demon_tactic g b) : 
       demon g b :=
         let (da, _) := dt in
         NextDemon da (simili_demon (tactic_rot unity 0 dt)))
  with (@simili_demon g b unity 0);[|reflexivity].
  cofix.
  intros X Y H.
  set (NEWDT:={|
           locate_byz := λ x : b, 1 * locate_byz X x + 0;
           frame := λ x : g, 1 * frame X x |}).
  assert (da_similar NEWDT Y).
  { inversion H.
    constructor;intros;simpl;ring_simplify;auto. }
  clearbody NEWDT.
  constructor.
  - simpl.
    replace (cofix simili_demon (dt : demon_tactic g b) : 
       demon g b :=
         let (da, _) := dt in
         NextDemon da (simili_demon (tactic_rot unity 0 dt)))
    with (@simili_demon g b unity 0);[|reflexivity].
    assert (da_similar (simili_action unity 0 NEWDT)
                       (simili_action unity 0 Y)).
    { constructor;intros;simpl;ring_simplify; inversion H0;auto. }
    apply bisim.
    constructor;simpl;intros;inversion H0;ring_simplify;auto.
  - constructor;simpl;intros;inversion H0;ring_simplify;auto.
Qed.

Ltac simpl_simili :=
  match goal with
    | |- context [@simili_demon ?g ?b _ _ _] => 
      unfold simili_demon; simpl;
      unfold simili_action; simpl;
      replace (cofix simili_demon (dt : demon_tactic g b) : 
                 demon g b :=
                 let (da, _) := dt in
                 NextDemon da (simili_demon (tactic_rot unity 0 dt)))
      with (@simili_demon g b unity 0);[|reflexivity]
  end.

Ltac da_simil :=
  repeat (match goal with
            | H: da_similar _ _ |- _ => inversion H; clear H;subst
          end); constructor;intros;simpl;try ring_simplify;now auto.


Lemma bisim' g b:
  forall X Y, da_similar X Y ->
  bisimilar (demon_tail (@simili_demon g b unity 0 (X, nil)))
            (@simili_demon g b unity 0 (Y, nil)).
Proof.
  simpl_simili.
  cofix.
  intros X Y H.
  set (NEWDT:={|
           locate_byz := λ x : b, 1 * locate_byz X x + 0;
           frame := λ x : g, 1 * frame X x |}).
  assert (da_similar NEWDT Y) by da_simil.
  clearbody NEWDT.
  constructor.
  - simpl_simili.
    assert (da_similar (simili_action unity 0 NEWDT)
                       (simili_action unity 0 Y)) by da_simil.
    apply bisim.
    da_simil.
  - da_simil.
Qed.


Lemma bisim'' g b:
  forall X Y X' Y', da_similar X Y -> da_similar X' Y' ->
  bisimilar
    (demon_tail (demon_tail (@simili_demon g b unity 0 (X, cons X' nil))))
    (@simili_demon g b unity 0 (Y, cons Y' nil))
.
Proof.
  simpl_simili.
  cofix.
  intros X Y X' Y' H H0.
  set (NEWDT:={|
           locate_byz := λ x : b, 1 * locate_byz X x + 0;
           frame := λ x : g, 1 * frame X x |}).
  set (NEWDT':={|
           locate_byz := λ x : b, 1 * locate_byz X' x + 0;
           frame := λ x : g, 1 * frame X' x |}).
  assert (da_similar NEWDT Y) by da_simil.
  assert (da_similar NEWDT' Y') by da_simil.
  clearbody NEWDT.
  clearbody NEWDT'.
  constructor.
  - simpl_simili.
    set (NEWDT2:={|
         locate_byz := λ x : b, 1 * locate_byz NEWDT x + 0;
         frame := λ x : g, 1 * frame NEWDT x |}).
    set (NEWDT2':={|
         locate_byz := λ x : b, 1 * locate_byz Y x + 0;
         frame := λ x : g, 1 * frame Y x |}).
    assert (da_similar NEWDT2 Y) by da_simil.
    assert (da_similar NEWDT2' Y) by da_simil.
    constructor.
    + apply bisim''.
      da_simil.
      da_simil.
    + da_simil.
  - da_simil.
Qed.


Lemma eqda1da2 g b :
  bisimilar 
            (demon_tail (demon_tail (simili_demon unity 0 (demon_trick g b))))
            (simili_demon unity 0 (demon_trick g b))
            .
Proof.
  apply bisim''.
  da_simil.
  da_simil.
Qed.

Lemma eqda1da2' g b :
  bisimilar 
            (simili_demon unity 0 (demon_trick g b))
            (demon_tail (demon_tail (simili_demon unity 0 (demon_trick g b))))
            .
Proof.
  admit.
Qed.


Lemma TwoStronglyBounded_demon_trick g b :
  forall d X X',
  bisimilar d (@simili_demon g b unity 0 (X, cons X' nil)) -> 
  StronglyKBounded 2 d.
Proof.
  cofix coHI.
  intros d X X' H.
  constructor.
  - admit. (* Lemme supplementaire à prouver. *)
  - constructor.
    + admit.
    + destruct d.
      destruct d0.
      apply coHI with X X'. Guarded.



  forall d, bisimilar d (simili_demon unity 0 (demon_trick g b)) ->
            StronglyKBounded 2 d.
Proof.
  cofix coHI.
  intros d H.
  destruct d.
  destruct d0.
  constructor.
  - admit. (* Lemme supplementaire à prouver. *)
  - constructor.
    + admit.
    + simpl. 
      apply coHI. Guarded.

 simpl_simili.
      apply bisimilar_kbounded with (simili_demon unity 0 (demon_trick g b)).
      - admit.
      * apply eqda1da2'.
      * apply coHI. Guarded.
  apply eqda1da2.
  simpl_simili.
  apply TwoStronglyBounded_demon_trick.

  constructor;intros.
  - apply LocallyStronglyTwoBounded_demon_trick.
  - constructor;intros. 
    + apply LocallyStronglyTwoBounded_demon_trick'.
    + 
      apply bisimilar_kbounded with (simili_demon unity 0 (demon_trick g b)).
      apply eqda1da2.
      assumption.
Qed.
