Require Import Reals.
Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.GatheringinR.Definitions.


Set Implicit Arguments.


Import GatheringinR.
Coercion Sim.sim_f : Sim.t >-> Similarity.bijection.
Coercion Similarity.section : Similarity.bijection >-> Funclass.
Close Scope R_scope.


Axiom even_nG : Nat.Even N.nG.
Axiom nG_non_0 : N.nG <> 0.

Lemma half_size_pos : Nat.div2 N.nG > 0.
Proof.
assert (Heven := even_nG). assert (H0 := nG_non_0).
destruct N.nG as [| [| n]].
- omega.
- destruct Heven. omega.
- simpl. omega.
Qed.

(** [Always_forbidden e] means that (infinite) execution [e] is [forbidden]
    forever. We will prove that with [bad_demon], robots are always apart. *)
CoInductive Always_forbidden (e : execution) :=
  CAF : forbidden (execution_head e) ->
        Always_forbidden (execution_tail e) -> Always_forbidden e.

Lemma Always_forbidden_compat_lemma : forall e1 e2, eeq e1 e2 -> Always_forbidden e1 -> Always_forbidden e2.
Proof.
coinduction diff.
- rewrite <- H. now destruct H0.
- destruct H. apply (diff _ _ H1). now destruct H0.
Qed.

Instance Always_forbidden_compat : Proper (eeq ==> iff) Always_forbidden.
Proof.
intros e1 e2 He; split; intro.
- now apply (Always_forbidden_compat_lemma He).
- now apply (Always_forbidden_compat_lemma (symmetry He)).
Qed.

(** ** Linking the different properties *)

Theorem different_no_gathering : forall (e : execution),
  N.nG <> 0%nat -> Always_forbidden e -> forall pt, ~WillGather pt e.
Proof.
intros e HnG He pt Habs. induction Habs.
+ destruct H as [Hnow Hlater]. destruct He as [Hforbidden He].
  destruct Hforbidden as [_ [pt1 [pt2 [Hdiff [Hin1 Hin2]]]]].
  apply Hdiff. transitivity pt.
  - assert (Hin : Spect.In pt1 (!! (execution_head e))).
    { unfold Spect.In. rewrite Hin1. now apply half_size_pos. }
    rewrite Spect.from_config_In in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    destruct id as [g | b]. apply Hnow. apply Fin.case0. exact b.
  - assert (Hin : Spect.In pt2 (!! (execution_head e))).
    { unfold Spect.In. rewrite Hin2. now apply half_size_pos. }
    rewrite Spect.from_config_In in Hin. destruct Hin as [id Hin]. rewrite <- Hin.
    symmetry. destruct id as [g | b]. apply Hnow. apply Fin.case0. exact b.
+ inversion He. now apply IHHabs.
Qed.


(** We split robots into two halves. *)

Definition left  := half1 Names.Gnames.
Definition right := half2 Names.Gnames.

Definition left_dec (e : Names.G) := List.in_dec Fin.eq_dec e left.

Lemma not_left_is_right : forall g : Names.G, ~In g left -> In g right.
Proof.
intros g Hleft.
assert (Hin : In g Names.Gnames) by apply Names.In_Gnames.
rewrite <- merge_halves, in_app_iff in Hin.
destruct Hin; contradiction || assumption.
Qed.

Lemma left_right_exclusive : forall g, In g left -> In g right -> False.
Proof.
unfold left, right, half1, half2. intros.
eapply firstn_skipn_nodup_exclusive; try eassumption.
apply Names.Gnames_NoDup.
Qed.

(* Seems like a bad idea because it hides some properties.
Definition left_right_dec (g : Names.G) := half_dec Fin.eq_dec Names.Gnames_NoDup g (Names.In_Gnames g).
*)

(** First and last robots are resp. in the first and in the second half. *)

(*
Section foo.
Variable nG : nat.
Hypothesis nG_non_0 : nG <> 0.

Definition gfirst' : Fin.t nG :=
  match nG as n0 return (nG = n0 -> Fin.t n0) with
    | 0 => fun Habs : nG = 0 => False_rec (Fin.t 0) (nG_non_0 Habs)
    | S n0 => fun _ => Fin.F1
  end (reflexivity nG).

Definition glast' : Fin.t nG :=
  match nG as n return (nG = n -> Fin.t n) with
    | 0 => fun Habs : nG = 0 => False_rec _ (nG_non_0 Habs)
    | S n => fun _ => nat_rec _ Fin.F1 (fun m (IHn : Fin.t (S m)) => Fin.FS IHn) n
  end (reflexivity nG).
End foo.

Require Import Coq.Program.Equality.
Lemma gfirst'_in : forall nG nG_non_0 (even_nG : Nat.Even nG),
  In (@gfirst' nG nG_non_0) (firstn (Nat.div2 nG) (Names.Internals.fin_map (fun x => x))).
Proof.
intros nG nG_non_0.
dependent destruction nG; intros.
+ exfalso; omega.
+ dependent destruction nG0.
  - exfalso; destruct even_nG0; omega.
  - simpl. compute. Print Spect.Names.Internals.fin_map.
      intro abs.
      inversion abs.
Qed.
*)

Definition gfirst : Names.G :=
  match N.nG as n0 return (N.nG = n0 -> Fin.t n0) with
    | 0 => fun Habs : N.nG = 0 => False_rec (Fin.t 0) (nG_non_0 Habs)
    | S n0 => fun _ => Fin.F1
  end (reflexivity N.nG).

Definition glast :=
  match N.nG as n return (N.nG = n -> Fin.t n) with
    | 0 => fun Habs : N.nG = 0 => False_rec _ (nG_non_0 Habs)
    | S n => fun _ => nat_rec _ Fin.F1 (fun m (IHn : Fin.t (S m)) => Fin.FS IHn) n
  end (reflexivity N.nG).

Lemma gfirst_left : In gfirst left.
Proof.
destruct N.nG as [| [| nG]] eqn:HnG.
+ now elim nG_non_0.
+ elim even_nG. intros. omega.
+ unfold left, gfirst.
Admitted.

Lemma glast_right : In glast right.
Proof.
Admitted.

Corollary gfirst_glast : gfirst <> glast.
Proof.
intro Habs. apply (firstn_skipn_nodup_exclusive Names.Gnames_NoDup (Nat.div2 (length Names.Gnames)) gfirst).
- apply gfirst_left.
- rewrite Habs. apply glast_right.
Qed.

Hint Immediate gfirst_left glast_right left_right_exclusive.

(* As there is no byzantine robot, we can lift positions for good robots as a full configuration.  *)
Definition lift_pos {A} (pos : Names.G -> A) : Names.ident -> A := fun id =>
  match id with
    | Good g => pos g
    | Byz b => Fin.case0 _ b
  end.

(** Names of robots only contains good robots. *)
Lemma names_Gnames : Spect.Names.names = map (@Good Spect.Names.G Spect.Names.B) Spect.Names.Gnames.
Proof.
unfold Spect.Names.names, Spect.Names.Internals.names, Spect.Names.Gnames.
cut (Spect.Names.Internals.Bnames = nil).
- intro Hnil. rewrite Hnil. simpl. now rewrite app_nil_r.
- rewrite <- length_zero_iff_nil. apply Spect.Names.Internals.fin_map_length.
Qed.

(** * Proof of the impossiblity of gathering for two robots
    From now on and until the final theorem we give us a robogram [r]. *)

Section GatheringEven.

Variable r : robogram.

(* A demon that makes the robogram fail:
   - if robots go on the position of the other one (symmetrical by definition of robogram), 
     activate both and they swap positions;
   - otherwise, just activate one and the distance between them does not become zero
     and you can scale it back on the next round. *)

Open Scope R_scope.
(** The reference starting position **)
Definition pos1 : Pos.t := fun id =>
  match id with
    | Good g => if left_dec g then 0 else 1
    | Byz b => 0
  end.

(** The symmetrical position of the starting position **)
Definition pos2 : Pos.t := fun id =>
  match id with
    | Good g => if left_dec g then 1 else 0
    | Byz b => 0
  end.

Definition spectrum := Spect.add 0 (Nat.div2 N.nG) (Spect.singleton 1 (Nat.div2 N.nG)).

Theorem pos1_pos2_spect_eq : Spect.eq (!! pos1) (!! pos2).
Proof.
intro pt. unfold pos1, pos2.
do 2 rewrite Spect.from_config_spec, Spect.Pos.list_spec. rewrite names_Gnames. do 2 rewrite map_map.
unfold left_dec, left. generalize (Names.Gnames_NoDup).
apply (@first_last_even_ind _
(fun l => NoDup l ->
          countA_occ eq Rdec pt (map (fun x => if in_dec Fin.eq_dec x (half1 l) then 0 else 1) l) =
          countA_occ eq Rdec pt (map (fun x => if in_dec Fin.eq_dec x (half1 l) then 1 else 0) l))).
* reflexivity.
* intros gl gr l Heven Hrec Hnodup.
  (* Inversing the NoDup property *)
  inversion_clear Hnodup as [| ? ? Helt Hnodup'].
  assert (Hneq : gl <> gr). { intro Habs. subst. intuition. }
  assert (Hgl : ~In gl l) by intuition.
  rewrite <- NoDupA_Leibniz, PermutationA_app_comm, NoDupA_Leibniz in Hnodup'; refine _.
  simpl in Hnodup'. inversion_clear Hnodup' as [| ? ? Hgr Hnodup]. specialize (Hrec Hnodup). clear Helt.
  (* Rewriting in the goal *)
  do 2 rewrite map_app. simpl. repeat rewrite countA_occ_app. simpl. rewrite half1_cons2.
  destruct (in_dec Fin.eq_dec gl (gl :: half1 l)) as [_ | Habs].
  destruct (in_dec Fin.eq_dec gr (gl :: half1 l)) as [Habs | _].
  + (* absurd case : gr ∈ gl :: half1 l *)
    exfalso. destruct Habs.
    - contradiction.
    - apply Hgr. now apply half1_incl.
  + (* valid case *)
    assert (Heq : forall a b : R,
                  map (fun x : Fin.t N.nG => if in_dec Fin.eq_dec x (gl :: half1 l) then a else b) l
                = map (fun x : Fin.t N.nG => if in_dec Fin.eq_dec x (half1 l) then a else b) l).
    { intros a b. apply map_f_dependent_compat. intros g Hg.
      destruct (in_dec Fin.eq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try now subst; contradiction.
        destruct (in_dec Fin.eq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Fin.eq_dec g (half1 l)); trivial. elim Hout. intuition. }
    do 2 rewrite Heq.
    Rdec_full; subst; Rdec; try Rdec_full; subst; Rdec; setoid_rewrite plus_comm; simpl; auto.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* change (Fin.t N.nG) with Spect.Names.Internals.G. rewrite Spect.Names.Gnames_length. apply even_nG.
Qed.

Theorem spect_pos1 : Spect.eq (!! pos1) spectrum.
Proof.
intro pt. unfold pos1, spectrum.
rewrite Spect.from_config_spec, Spect.Pos.list_spec. rewrite names_Gnames, map_map.
unfold left_dec, left. rewrite <- Names.Gnames_length at 1 2. generalize (Names.Gnames_NoDup).
apply (@first_last_even_ind _
(fun l => NoDup l ->
          countA_occ eq Rdec pt (map (fun x => if in_dec Fin.eq_dec x (half1 l) then 0 else 1) l)
        = (Spect.add 0 (Nat.div2 (length l)) (Spect.singleton 1 (Nat.div2 (length l))))[pt])).
* intros _. simpl. rewrite Spect.add_0, Spect.singleton_0, Spect.empty_spec. reflexivity.
* intros gl gr l Heven Hrec Hnodup.
  (* Inversing the NoDup property *)
  inversion_clear Hnodup as [| ? ? Helt Hnodup'].
  assert (Hneq : gl <> gr). { intro Habs. subst. intuition. }
  assert (Hgl : ~In gl l) by intuition.
  rewrite <- NoDupA_Leibniz, PermutationA_app_comm, NoDupA_Leibniz in Hnodup'; refine _.
  simpl in Hnodup'. inversion_clear Hnodup' as [| ? ? Hgr Hnodup]. specialize (Hrec Hnodup). clear Helt.
  (* Rewriting in the goal *)
  rewrite app_length, plus_comm.
  simpl. repeat rewrite map_app, countA_occ_app. simpl. rewrite half1_cons2.
  destruct (in_dec Fin.eq_dec gl (gl :: half1 l)) as [_ | Habs].
  destruct (in_dec Fin.eq_dec gr (gl :: half1 l)) as [Habs | _].
  + (* absurd case : gr ∈ gl :: half1 l *)
    exfalso. destruct Habs.
    - contradiction.
    - apply Hgr. now apply half1_incl.
  + (* valid case *)
    assert (Heq : map (fun x => if in_dec Fin.eq_dec x (gl :: half1 l) then 0 else 1) l
                = map (fun x => if in_dec Fin.eq_dec x (half1 l) then 0 else 1) l).
    { apply map_f_dependent_compat. intros g Hg.
      destruct (in_dec Fin.eq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try now subst; contradiction.
        destruct (in_dec Fin.eq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Fin.eq_dec g (half1 l)); trivial. elim Hout. intuition. }
    rewrite Heq, Hrec.
    assert (~R.eq 0 1) by auto using R1_neq_R0. assert (~R.eq 1 0) by auto using R1_neq_R0.
    Rdec_full; subst; Rdec; try Rdec_full; subst; Rdec;
    repeat rewrite ?Spect.add_same, ?Spect.add_other, ?Spect.singleton_same, ?Spect.singleton_other; trivial;
    omega || unfoldR; auto.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* change (Fin.t N.nG) with Spect.Names.Internals.G. rewrite Spect.Names.Gnames_length. apply even_nG.
Qed.

Corollary pos1_forbidden : forbidden pos1.
Proof.
split; try exact even_nG.
exists 0, 1. rewrite spect_pos1. repeat split.
+ intro. now apply R1_neq_R0.
+ unfold spectrum. rewrite Spect.add_same, Spect.singleton_spec. now Rdec.
+ unfold spectrum. rewrite Spect.add_other, Spect.singleton_spec; try apply R1_neq_R0. now Rdec.
Qed.

Corollary pos2_forbidden : forbidden pos2.
Proof. split; try exact even_nG. cbn. setoid_rewrite <- pos1_pos2_spect_eq. apply pos1_forbidden. Qed.

(** Two similarities used: the identity and the symmetry wrt a point c. *)

(** The swapping similarity *)
Definition bij_swap (c : R) : Similarity.bijection R.eq.
refine {|
  Similarity.section := fun x => c - x;
  Similarity.retraction := fun x => c - x |}.
Proof.
abstract (intros; unfold R.eq, Rdef.eq; split; intro; subst; field).
Defined.

Lemma bij_swap_ratio : forall c x y : R.t, R.dist (bij_swap c x) (bij_swap c y) = 1 * R.dist x y.
Proof.
intros c x y. rewrite Rmult_1_l. compute.
destruct (Rcase_abs (x + - y)), (Rcase_abs (c + - x + - (c + - y))); lra.
Qed.

(* We need to define it with a general center although only 1 will be used. *)
Definition swap (c : R) : Sim.t.
refine {|
  Sim.sim_f := bij_swap c;
  Sim.zoom := 1;
  Sim.center := c |}.
Proof.
- abstract (compute; field).
- exact (bij_swap_ratio c).
Defined.

Lemma swap_pos1 : Pos.eq (Pos.map (swap 1) pos1) pos2.
Proof.
intros [g | b].
- unfold Pos.map. simpl. destruct (left_dec g); hnf; ring.
- apply Fin.case0. exact b.
Qed.

Lemma swap_pos2 : Pos.eq (Pos.map (swap 1) pos2) pos1.
Proof.
intros [g | b].
- unfold Pos.map. simpl. destruct (left_dec g); hnf; ring.
- apply Fin.case0. exact b.
Qed.

(** The movement of robots in the reference position **)
Definition move := r (!! pos1).

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : move = 1.

Lemma da1_ratio : forall id sim c,
  lift_pos (fun _ => Some (fun c => if Rdec c 0 then Sim.id else swap c)) id = Some sim -> Sim.zoom (sim c) <> 0.
Proof.
intros id sim c Heq. destruct id; simpl in Heq.
- inversion_clear Heq. Rdec_full; simpl; apply R1_neq_R0.
- apply Fin.case0. exact b.
Qed.

Lemma da1_center : forall id sim c,
  lift_pos (fun _ => Some (fun c => if Rdec c 0 then Sim.id else swap c)) id = Some sim ->
  R.eq (Sim.center (sim c)) c.
Proof.
intros id sim c Heq. destruct id; simpl in Heq.
- inversion_clear Heq. Rdec_full; simpl; subst; reflexivity.
- apply Fin.case0. exact b.
Qed.

Definition da1 : demonic_action.
refine {|
  relocate_byz := fun b => 0;
  step := lift_pos (fun g => Some (fun c => if Rdec c 0 then Sim.id else swap c)) |}.
Proof.
+ exact da1_ratio.
+ exact da1_center.
Defined.

CoFixpoint bad_demon1 : demon := NextDemon da1 bad_demon1.

Lemma bad_demon1_tail : demon_tail bad_demon1 = bad_demon1.
Proof. reflexivity. Qed.

Lemma bad_demon1_head : demon_head bad_demon1 = da1.
Proof. reflexivity. Qed.

Lemma kFair_bad_demon1 : kFair 0 bad_demon1.
Proof.
coinduction bad_fair1.
intros id1 id2. constructor. destruct id1; simpl. discriminate. apply Fin.case0. exact b.
Qed.

Lemma round_simplify_1_1 : Pos.eq (round r da1 pos1) pos2.
Proof.
intros [g | b]; unfold round; simpl.
+ destruct (left_dec g) as [Hleft | Hright].
  - Rdec. simpl.
  (* BUG?: rewrite Pos.map_id should be enough. *)
    assert (Heq : Pos.eq (Pos.map (fun x : R.t => x) pos1) pos1) by apply Pos.map_id.
    apply Spect.from_config_compat, (pgm_compat r) in Heq. rewrite Heq.
    fold move. apply Hmove.
  - Rdec. setoid_rewrite swap_pos1. simpl. replace 0 with (1 - 1) by ring. hnf. f_equal.
    rewrite <- pos1_pos2_spect_eq. apply Hmove.
+ apply Fin.case0. exact b.
Qed.

Lemma round_simplify_1_2 : Pos.eq (round r da1 pos2) pos1.
Proof.
intros [g | b]; unfold round; simpl.
+ destruct (left_dec g) as [Hleft | Hright].
  - Rdec. rewrite swap_pos2. simpl. replace 0 with (1 - 1) by ring. hnf. f_equal. apply Hmove.
  - Rdec. simpl.
  (* BUG?: rewrite Pos.map_id should be enough. *)
    assert (Heq : Pos.eq (Pos.map (fun x : R.t => x) pos2) pos2) by apply Pos.map_id.
    apply Spect.from_config_compat, (pgm_compat r) in Heq. rewrite Heq.
    rewrite <- pos1_pos2_spect_eq. fold move. apply Hmove.
+ apply Fin.case0. exact b.
Qed.

(* Trick to perform rewriting in coinductive proofs : assert your property on any configuration
   equal to the one you want, then apply the cofixpoint before performing the required rewrites. *)
Theorem Always_forbidden1_by_eq : forall conf : Pos.t, Pos.eq conf pos1 ->
  Always_forbidden (execute r bad_demon1 conf).
Proof.
cofix differs. intros conf Heq. constructor.
+ simpl. rewrite Heq. apply pos1_forbidden.
+ cbn. constructor.
  - simpl. rewrite Heq, round_simplify_1_1. apply pos2_forbidden.
  - cbn. apply differs. now rewrite Heq, round_simplify_1_1, round_simplify_1_2. 
Qed.

Corollary Always_forbidden1 : Always_forbidden (execute r bad_demon1 pos1).
Proof. apply Always_forbidden1_by_eq. reflexivity. Qed.

End Move1.

(** **  Second case: Only one robot is activated at a time **)

Section MoveNot1.

Hypothesis Hmove : move <> 1.

Lemma minus_1_move : 1 - move <> 0.
Proof. apply Rminus_eq_contra. intro. now apply Hmove. Qed.

Hint Immediate minus_1_move.

Lemma ratio_inv : forall ρ, ρ <> 0 -> ρ / (1 - move) <> 0.
Proof.
  intros ρ Hρ Habs. apply Hρ. apply (Rmult_eq_compat_l (1 - move)) in Habs.
  unfold Rdiv in Habs. 
  replace ( (1 - move) * (ρ * / (1 - move))) with (ρ * ((1 - move) * / (1 - move))) in Habs by ring.
  rewrite Rinv_r in Habs.
  - now ring_simplify in Habs.
  - auto.
Qed.

Lemma homothecy_ratio_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_pos (fun g => if left_dec g then Some (fun c => Sim.homothecy c Hρ) else None) id = Some sim ->
  Sim.zoom (sim c) <> 0.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_dec g).
  - intro H. inversion_clear H. simpl. now apply Rabs_no_R0.
  - discriminate.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_center_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_pos (fun g => if left_dec g then Some (fun c => Sim.homothecy c Hρ) else None) id = Some sim ->
  R.eq (Sim.center (sim c)) c.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_dec g).
  - intro H. inversion_clear H. reflexivity.
  - discriminate.
+ apply Fin.case0. exact b.
Qed.

Definition da2_left (ρ : R) (Hρ : ρ <> 0) : demonic_action.
refine {|
  relocate_byz := fun b => 0;
  step := lift_pos (fun g => if left_dec g then Some (fun c => Sim.homothecy c Hρ) else None) |}.
Proof.
+ apply homothecy_ratio_1.
+ apply homothecy_center_1.
Defined.

Lemma homothecy_ratio_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_pos (fun g => if left_dec g 
                     then None else Some (fun c => Sim.homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  Sim.zoom (sim c) <> 0.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_dec g).
  - discriminate.
  - intro H. inversion_clear H. simpl. now apply Rabs_no_R0, Ropp_neq_0_compat.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_center_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_pos (fun g => if left_dec g 
                     then None else Some (fun c => Sim.homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  R.eq (Sim.center (sim c)) c.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_dec g).
  - discriminate.
  - intro H. inversion_clear H. reflexivity.
+ apply Fin.case0. exact b.
Qed.

Definition da2_right (ρ : R) (Hρ : ρ <> 0) : demonic_action.
refine {|
  relocate_byz := fun b => 0;
  step := lift_pos (fun g => if left_dec g
                             then None else Some (fun c => Sim.homothecy c (Ropp_neq_0_compat _ Hρ))) |}.
Proof.
+ apply homothecy_ratio_2.
+ apply homothecy_center_2.
Defined.

CoFixpoint bad_demon2 ρ (Hρ : ρ <> 0) : demon :=
  NextDemon (da2_left Hρ)
  (NextDemon (da2_right (ratio_inv Hρ))
  (bad_demon2 (ratio_inv (ratio_inv Hρ)))). (* ρ updated *)

Lemma bad_demon_head2_1 : forall ρ (Hρ : ρ <> 0), demon_head (bad_demon2 Hρ) = da2_left Hρ.
Proof. reflexivity. Qed.

Lemma bad_demon_head2_2 : forall ρ (Hρ : ρ <> 0),
  demon_head (demon_tail (bad_demon2 Hρ)) = da2_right (ratio_inv Hρ).
Proof. reflexivity. Qed.

Lemma bad_demon_tail2 :
  forall ρ (Hρ : ρ <> 0), demon_tail (demon_tail (bad_demon2 Hρ)) = bad_demon2 (ratio_inv (ratio_inv Hρ)).
Proof. reflexivity. Qed.

Lemma da_eq_step_None : forall d1 d2, deq d1 d2 ->
  forall g, step (demon_head d1) (Good g) = None <-> step (demon_head d2) (Good g) = None.
Proof.
intros d1 d2 Hd g.
assert (Hopt_eq : opt_eq (R.eq ==> Sim.eq)%signature
                    (step (demon_head d1) (Good g)) (step (demon_head d2) (Good g))).
{ apply step_da_compat; trivial. now rewrite Hd. }
  split; intro Hnone; rewrite Hnone in Hopt_eq; destruct step; reflexivity || elim Hopt_eq.
Qed.

Theorem kFair_bad_demon2_by_eq : forall ρ (Hρ : ρ <> 0) d, deq d (bad_demon2 Hρ) -> kFair 1 d.
Proof.
cofix fair_demon. intros ρ Hρ d Heq.
constructor; [| constructor].
* setoid_rewrite Heq.
  intros [g1 | b1] [g2 | b2]; try now apply Fin.case0; assumption.
  destruct (left_dec g1).
  + constructor 1. rewrite bad_demon_head2_1. simpl. destruct (left_dec g1); eauto. discriminate.
  + destruct (left_dec g2).
    - constructor 2.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_dec g2); eauto. discriminate.
      -- constructor 1. rewrite bad_demon_head2_2. simpl. destruct (left_dec g1); eauto. discriminate.
    - constructor 3.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_dec g2); eauto. exfalso. eauto.
      -- constructor 1. rewrite bad_demon_head2_2. simpl. destruct (left_dec g1); eauto. discriminate.
* setoid_rewrite Heq.
  intros [g1 | b1] [g2 | b2]; try now apply Fin.case0; assumption.
  destruct (left_dec g1).
  + destruct (left_dec g2).
    - constructor 3.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_dec g2); eauto. exfalso. eauto.
      -- rewrite bad_demon_tail2. constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
    - constructor 2.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_dec g2); eauto. discriminate.
      -- rewrite bad_demon_tail2. constructor 1. simpl. destruct (left_dec g1); eauto. discriminate.
  + constructor 1. rewrite bad_demon_head2_2. simpl. destruct (left_dec g1); eauto. discriminate.
* eapply fair_demon. now rewrite Heq, bad_demon_tail2.
Qed.

Theorem kFair_bad_demon2 : forall ρ (Hρ : ρ <> 0), kFair 1 (bad_demon2 Hρ).
Proof. intros. eapply kFair_bad_demon2_by_eq. reflexivity. Qed.

(* In a bivalent position, half of the robots are in the same place. *)
Lemma dist_left : forall d (Hd : d <> 0) (config : Pos.t),
  (forall gr gl, In gr right -> In gl left -> config (Good gr) - config (Good gl) = d) ->
  forall g, In g left -> config (Good g) = config (Good gfirst).
Proof.
intros d Hd config Hconfig g Hg.
cut (config (Good glast) - config (Good g) = config (Good glast) - config (Good gfirst)).
+ intro Heq. unfold Rminus in Heq. apply Rplus_eq_reg_l in Heq. setoid_rewrite <- Ropp_involutive.
  now apply Ropp_eq_compat.
+ assert (Hright := glast_right). repeat rewrite Hconfig; auto.
Qed.

Lemma dist_right : forall d (Hd : d <> 0) (config : Pos.t),
  (forall gr gl, In gr right -> In gl left -> config (Good gr) - config (Good gl) = d) ->
  forall g, In g right -> config (Good g) = config (Good glast).
Proof.
intros d Hd config Hconfig g Hg.
cut (config (Good g) - config (Good gfirst) = config (Good glast) - config (Good gfirst)).
+ intro Heq. unfold Rminus in Heq. now apply Rplus_eq_reg_r in Heq.
+ assert (Hleft := gfirst_left). repeat rewrite Hconfig; auto.
Qed.


Lemma dist_homothecy_spectrum_centered_left : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g, In g left -> Spect.eq (!! (Pos.map (fun x : R => ρ * (x - config (Good g))) config)) (!! pos1).
Proof.
intros ρ Hρ config Hconfig g Hg. f_equiv. intro id. unfold Pos.map.
destruct id as [id | b]; try now apply Fin.case0; [].
unfold pos1. destruct (left_dec id).
- setoid_rewrite (dist_left (Rinv_neq_0_compat _ Hρ) _ Hconfig); trivial. ring_simplify. reflexivity.
- rewrite Hconfig; trivial. now rewrite Rinv_r. now apply not_left_is_right.
Qed.

(* To prove this equality, we use !! pos1. *)
Lemma dist_spectrum : forall d (Hd : d <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = d) ->
  Spect.eq (!! config) (Spect.add (config (Good gfirst)) (Nat.div2 N.nG)
                 (Spect.singleton (config (Good glast)) (Nat.div2 N.nG))).
Proof.
intros d Hd config Hconfig.
rewrite <- (Rinv_involutive d) in Hconfig; trivial.
assert (Hd' := Rinv_neq_0_compat _ Hd).
rewrite <- Pos.map_id at 1. change Datatypes.id with (Similarity.section Sim.id).
rewrite <- (Sim.compose_inverse_l (Sim.homothecy (config (Good gfirst)) Hd')). cbn -[Sim.homothecy].
rewrite <- Pos.map_merge, <- Spect.from_config_map; refine _. simpl. unfoldR.
change (fun x : R => / d * (x + - config (Good gfirst))) with (fun x : R => / d * (x - config (Good gfirst))).
rewrite (dist_homothecy_spectrum_centered_left Hd'); auto.
rewrite spect_pos1. unfold spectrum. rewrite Spect.map_add, Spect.map_singleton; refine _.
ring_simplify (// d * 0). rewrite Rplus_0_l. rewrite <- (Hconfig glast gfirst); auto.
f_equiv. f_equiv. compute; field.
Qed.

Lemma dist_forbidden : forall d (Hd : d <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = d) -> forbidden config.
Proof.
intros d Hd config Hconfig. unfold forbidden. split; try apply even_nG; [].
assert (Hdiff : config (Good gfirst) <> config (Good glast)).
{ apply Rminus_not_eq_right. rewrite Hconfig; auto. }
exists (config (Good gfirst)), (config (Good glast)). repeat split.
- assumption.
- rewrite dist_spectrum; try eassumption. rewrite Spect.add_same, Spect.singleton_other; auto.
- rewrite dist_spectrum; try eassumption. rewrite Spect.add_other, Spect.singleton_same; auto.
Qed.

Lemma round_dist2_left : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 left -> round r (da2_left Hρ) config (Good g1)
                                             - round r (da2_left Hρ) config (Good g2) = (1 - move) / ρ.
Proof.
intros ρ Hρ config Hconfig g1 g2 Hg1 Hg2. unfold round. simpl.
destruct (left_dec g1), (left_dec g2); try now exfalso.
(* TODO: correct the type conversion problem, the first case should diseappear with eauto *)
- change  (Fin.t N.nG) with Names.Internals.G in i, i0. exfalso. now apply (left_right_exclusive g1).
- cbn. replace ((1 - move) / ρ) with (/ρ - move / ρ) by now field.
  rewrite <- (Hconfig _ _ Hg1 Hg2) at 2. unfoldR. ring_simplify.
  replace (config (Good g1) - config (Good g2) - move / ρ)
    with (config (Good g1) - move / ρ - config (Good g2)) by ring.
   field_simplify; trivial. do 2 f_equal.
   unfold move. apply pgm_compat. now apply dist_homothecy_spectrum_centered_left.
Qed.

Corollary round2_left_right : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 right ->
    round r (da2_left Hρ) config (Good g1) = round r (da2_left Hρ) config (Good g2).
Proof.
intros. apply Rplus_eq_reg_l with (- round r (da2_left Hρ) config (Good gfirst)).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

Corollary round2_left_left : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 left -> In g2 left ->
    round r (da2_left Hρ) config (Good g1) = round r (da2_left Hρ) config (Good g2).
Proof.
intros. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
apply Rplus_eq_reg_r with (round r (da2_left Hρ) config (Good glast)).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

Corollary round2_left_forbidden : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forbidden (round r (da2_left Hρ) config).
Proof.
intros ρ Hρ config Hconfig.
apply (dist_forbidden (d := (1 - move) / ρ)).
- rewrite <- Rinv_Rdiv; trivial. now apply Rinv_neq_0_compat, ratio_inv. lra.
- intros. now apply round_dist2_left.
Qed.

Lemma dist_homothecy_spectrum_centered_right : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g, In g right -> Spect.eq (!! (Pos.map (fun x : R => -ρ * (x - config (Good g))) config)) (!! pos2).
Proof.
intros ρ Hρ config Hconfig g Hg. f_equiv. intro id. unfold Pos.map.
destruct id as [id | b]; try now apply Fin.case0; [].
unfold pos2. destruct (left_dec id).
- replace (- ρ * (config (Good id) - config (Good g))) with (ρ * (config (Good g) - config (Good id))) by ring.
  rewrite Hconfig; trivial. now rewrite Rinv_r.
- setoid_rewrite (dist_right (Rinv_neq_0_compat _ Hρ) _ Hconfig); trivial.
  ring_simplify. reflexivity. now apply not_left_is_right.
Qed.

Lemma round_dist2_right : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 left -> round r (da2_right Hρ) config (Good g1)
                                             - round r (da2_right Hρ) config (Good g2) = (1 - move) / ρ.
Proof.
intros ρ Hρ config Hconfig g1 g2 Hg1 Hg2. unfold round. simpl.
destruct (left_dec g1), (left_dec g2); try now exfalso; eauto.
(* TODO: correct the type conversion problem, the first case should diseappear with eauto *)
- change  (Fin.t N.nG) with Names.Internals.G in i, i0. exfalso. now apply (left_right_exclusive g1).
- cbn. replace ((1 - move) / ρ) with (/ρ - move / ρ) by now field.
  rewrite <- (Hconfig _ _ Hg1 Hg2). unfoldR. rewrite <- Ropp_inv_permute; trivial. field_simplify; trivial.
  do 3 f_equal. unfold move. apply pgm_compat. rewrite pos1_pos2_spect_eq.
  now apply dist_homothecy_spectrum_centered_right.
Qed.

Ltac shift := let Hm := fresh "Hm" in intro Hm; apply Rminus_diag_uniq in Hm;
  try (contradiction || symmetry in Hm; contradiction).

Theorem Always_forbidden2 : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  Always_forbidden (execute r (bad_demon2 Hρ) config).
Proof.
cofix differs. intros ρ Hρ config Hconfig.
constructor; [| constructor].
  (* Inital state *)
- cbn. apply (dist_forbidden (Rinv_neq_0_compat _ Hρ)). assumption.
  (* State after one step *)
- cbn. now apply round2_left_forbidden.
(* State after two steps *)
- do 2 rewrite execute_tail.
  rewrite bad_demon_tail2, bad_demon_head2_1, bad_demon_head2_2.
  apply differs. intros g1 g2 Hg1 Hg2.
  replace (/ (ρ / (1 - move) / (1 - move))) with ((1 - move) / (ρ / (1 - move))) by (field; auto).
  apply round_dist2_right; trivial.
  replace (/ (ρ / (1 - move))) with ((1 - move) / ρ) by (field; auto).
  apply round_dist2_left; trivial.
Qed.

End MoveNot1.

(** **  Merging both cases  **)

Definition bad_demon : demon.
  destruct (Rdec move 1) as [Hmove | Hmove].
  (** Robots exchange positions **)
  - exact bad_demon1.
    (** Robots do no exchange positions **)
  - exact (bad_demon2 Hmove R1_neq_R0).
Defined.

Theorem kFair_bad_demon : kFair 1 bad_demon.
Proof.
intros. unfold bad_demon.
destruct (Rdec move 1).
- apply kFair_mon with 0%nat. exact kFair_bad_demon1. omega.
- now apply kFair_bad_demon2.
Qed.

Theorem kFair_bad_demon' : forall k, (k>=1)%nat -> kFair k bad_demon.
Proof.
intros.
eapply kFair_mon with 1%nat.
- apply kFair_bad_demon;auto.
- auto.
Qed.

(** * Final theorem

Given a non empty finite even set [G] and a robogram [r] on ([G]) × ∅,
there is no (k>0)-fair demon  for which the gathering problem is solved for any starting position. *)

Theorem noGathering :
  forall k, (1<=k)%nat -> ~(forall d, kFair k d -> FullSolGathering r d).
Proof.
intros k h Habs.
specialize (Habs bad_demon (kFair_bad_demon' h) pos1).
(* specialize (Habs 1%nat (bad_demon 1) (kFair_bad_demon R1_neq_R0) gpos1). *)
destruct Habs as [pt Habs]. revert Habs. apply different_no_gathering.
* exact nG_non_0.
* unfold bad_demon.
  destruct (Rdec move 1) as [Hmove | Hmove].
  + now apply Always_forbidden1.
  + apply (Always_forbidden2 Hmove R1_neq_R0 pos1); try reflexivity.
    intros. simpl. destruct (left_dec g1), (left_dec g2); field || exfalso; eauto.
(* TODO: correct the type conversion problem, eauto should solve this goal *)
change  (Fin.t N.nG) with Names.Internals.G in i, i0. exfalso. now apply (left_right_exclusive g1).
Qed.

End GatheringEven.

Print Assumptions noGathering.