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
Close Scope R_scope.


Axiom even_nG : Nat.Even nG.

Lemma half_size_pos : N.nG <> 0 -> Nat.div2 N.nG > 0.
Proof.
assert (Heven := even_nG). fold N.nG in Heven.
destruct N.nG as [| [| n]].
- tauto.
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

Definition left := firstn (Nat.div2 N.nG) Names.Gnames.
Definition right := skipn (Nat.div2 N.nG) Names.Gnames.

Lemma left_length : length left = div2 N.nG.
Proof. apply firstn_length_le. rewrite Names.Gnames_length. apply Nat.div2_decr. omega. Qed.

Theorem skipn_length : forall {A} (l : list A) n, length (skipn n l) = length l - n.
Proof.
induction l.
+ now intros [| n].
+ intros [| n]; trivial. simpl. apply IHl.
Qed.

Lemma right_length : length right = div2 N.nG.
Proof.
unfold right. rewrite skipn_length, Names.Gnames_length. unfold N.nG. rewrite <- (even_div2 even_nG) at 1. omega.
Qed.

Lemma firstn_In : forall {A} (l : list A) n, incl (firstn n l) l.
Proof.
induction l; intros n x Hin.
+ destruct n; elim Hin.
+ destruct n; try now elim Hin. simpl in Hin. destruct Hin.
  - subst. now left.
  - right. now apply IHl in H.
Qed.

Lemma left_NoDup : NoDup left.
Proof.
unfold left. assert (Hnodup := Names.Gnames_NoDup).
generalize (Nat.div2 N.nG). induction Names.Gnames as [| e l].
- intros [| n]; simpl; constructor.
- inversion_clear Hnodup. intros [| n]; simpl; constructor; auto.
  intro Hin. apply firstn_In in Hin. contradiction.
Qed.

Lemma skipn_In : forall {A} (l : list A) n, incl (skipn n l) l.
Proof.
induction l; intros n x Hin.
+ destruct n; elim Hin.
+ destruct n; try now elim Hin. simpl in Hin. apply IHl in Hin. now right.
Qed.

Lemma In_skipn : forall {A} l l' (pt : A) n, n <= length l -> In pt (skipn n (l ++ pt :: l')).
Proof.
intros A l l' pt. generalize (le_refl (length l)). generalize l at -2. induction l; simpl.
* intros [| x l] Hl [| n] ?; simpl in *; try tauto || omega.
* intros [| x l''] Hl'' n Hn; simpl in *; try tauto.
  + destruct n; simpl; tauto || omega.
  + destruct n; simpl.
    - right. change (In pt (skipn 0 (l'' ++ pt :: l'))). apply IHl; omega.
    - apply IHl; omega.
Qed.

Corollary In_skipn_half : forall {A} l (pt : A), In pt (skipn (Nat.div2 (length l)) (l ++ pt :: nil)).
Proof. intros. apply In_skipn. apply Nat.div2_decr. omega. Qed.

Lemma right_NoDup : NoDup right.
Proof.
unfold right. assert (Hnodup := Names.Gnames_NoDup).
generalize (Nat.div2 N.nG). induction Names.Gnames as [| e l].
- intros [| n]; simpl; constructor.
- intros [| n]; simpl; trivial. apply IHl. now inversion Hnodup.
Qed.


Lemma left_right_exclusive : forall g, In g left -> In g right -> False.
Proof.
assert (Hnodup := Names.Gnames_NoDup). rewrite <- (firstn_skipn (Nat.div2 N.nG)) in Hnodup.
rewrite <- NoDupA_Leibniz, Preliminary.NoDupA_app_iff in Hnodup; refine _.
destruct Hnodup as [Hleft [Hright Hboth]]. now setoid_rewrite InA_Leibniz in Hboth.
Qed.

Hint Resolve left_right_exclusive.

Definition in_left (id : Names.ident) :=
  match id with
    | Good g => if List.in_dec Fin.eq_dec g left then true else false
    | Byz b => false
  end.

Theorem left_right_dec : forall g, {In g left} + {In g right}.
Proof.
intro g. destruct (List.in_dec Fin.eq_dec g left) as [? | Hg].
+ now left.
+ right. assert (Hin : List.In g (left ++ right)).
  { unfold left, right. rewrite List.firstn_skipn. apply Names.In_Gnames. }
 apply List.in_app_or in Hin. tauto.
Qed.

Axiom nG_non_0 : N.nG <> 0.
Definition gleft : Names.G.
unfold Names.G, Names.Internals.G.
destruct N.nG eqn:HnG. assert (HnG0 := nG_non_0). contradiction.
apply (@Fin.F1 n).
Defined.

Lemma gleft_left : In gleft left.
Proof. Admitted.

(* Take the last element *)
Definition gright : Names.G. Admitted.

Lemma gright_right : In gright right.
Proof. Admitted.

Hint Immediate gleft_left gright_right.

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
    | Good g => if left_right_dec g then 0 else 1
    | Byz b => 0
  end.

(** The symmetrical position of the starting position **)
Definition pos2 : Pos.t := fun id =>
  match id with
    | Good g => if left_right_dec g then 1 else 0
    | Byz b => 0
  end.

Definition spectrum := Spect.add 0 (Nat.div2 N.nG) (Spect.singleton 1 (Nat.div2 N.nG)).

Theorem pos1_pos2_spect_eq : Spect.eq (!! pos1) (!! pos2).
Proof. Admitted.
(* This proof should decompose the list names by one element on the front and one in the back,
   that is, one in left and one in right.*)

Theorem spect_pos1 : Spect.eq (!! pos1) spectrum.
Proof.
intro pt. unfold spectrum. assert (Hlength := Names.Gnames_length).
assert (Hleft := eq_refl left). unfold left at 2 in Hleft.
assert (Hright := eq_refl right). unfold right at 2 in Hright.
rewrite Spect.from_config_spec, Spect.Pos.list_spec. rewrite names_Gnames. rewrite <- Hlength in *.
change Names.Gnames with Spect.Names.Gnames in *.
induction Spect.Names.Gnames using first_last_ind.
* elim nG_non_0. now symmetry.
* elim even_nG. intros ? Habs. change nG with N.nG in Habs.
  rewrite <- Hlength in Habs. simpl in Habs. omega.
* rewrite app_length, plus_comm in *. cbn in *.
  assert (Hx : In x left). { rewrite Hleft. now left. }
  assert (Hy : In y right). { rewrite Hright. apply In_skipn_half. }
  repeat rewrite map_app. cbn.
  destruct (left_right_dec x); try now elim (left_right_exclusive x).
  destruct (left_right_dec y); try now elim (left_right_exclusive y).
  change identifier with Spect.Names.ident in *. change (Spect.Names.Internals.G) with (Spect.Names.G).
  rewrite countA_occ_app. rewrite IHl.
  + Rdec_full; cbn; subst; Rdec || Rdec_full; subst.
    - subst. repeat rewrite Spect.add_same, Spect.singleton_other; try now intro Habs; apply R1_neq_R0.
      simpl. Rdec. now ring_simplify.
    - repeat rewrite Spect.add_other, Spect.singleton_same; try now intro; apply Hneq. now ring_simplify.
    - repeat rewrite Spect.add_other, Spect.singleton_other; try intro; auto.
  + admit. (* Induction hypothesis is not well written *)
  + admit.
  + admit.
Admitted.

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

(** The identity similarity *)
Definition bij_id : bijection R.eq_equiv.
refine {|
  section := fun x => x;
  retraction := fun x => x |}.
Proof.
abstract (now split; intro; symmetry).
Defined.

Definition identity : similarity.
refine {|
  f := bij_id;
  ratio := 1;
  center := 0 |}.
Proof.
+ reflexivity.
+ abstract (intros; rewrite Rmult_1_l; reflexivity).
Defined.

(** The swapping similarity *)
Definition bij_swap (c : R) : bijection R.eq_equiv.
refine {|
  section := fun x => c - x;
  retraction := fun x => c - x |}.
Proof.
abstract (intros; unfold R.eq, Rdef.eq; split; intro; subst; field).
Defined.

Lemma bij_swap_ratio : forall c x y : R.t, R.dist (bij_swap c x) (bij_swap c y) = 1 * R.dist x y.
Proof.
intros c x y. rewrite Rmult_1_l. compute.
destruct (Rcase_abs (x + - y)), (Rcase_abs (c + - x + - (c + - y))); lra.
Qed.

(* We need to define it with a general center although only 1 will be used. *)
Definition swap (c : R) : similarity.
refine {|
  f := bij_swap c;
  ratio := 1;
  center := c |}.
Proof.
- abstract (compute; field).
- exact (bij_swap_ratio c).
Defined.

(** The homothetic similarity *)
Definition bij_homothecy (c ρ : R) (Hρ : ρ <> 0) : bijection R.eq_equiv.
refine {|
  section := fun x => ρ * (x - c);
  retraction := fun x => x / ρ + c |}.
Proof.
abstract (now intros; compute; split; intro Heq; rewrite <- Heq; field).
Defined.

Lemma bij_homothecy_ratio : forall c ρ (Hρ : ρ <> 0) (x y : R.t),
R.dist ((bij_homothecy c Hρ) x) ((bij_homothecy c Hρ) y) = Rabs ρ * R.dist x y.
Proof.
intros c ρ Hρ x y. cbn. compute.
destruct (Rcase_abs (ρ * (x + - c) + - (ρ * (y + - c)))), (Rcase_abs (x + - y)), (Rcase_abs ρ); try field.
+ ring_simplify in r0. exfalso. revert r0. apply Rle_not_lt.
  replace (ρ * x - ρ * y) with (-ρ * - (x + -y)) by ring.
  rewrite <- Rmult_0_r with (-ρ). apply Rmult_le_compat_l; lra.
+ ring_simplify in r0. exfalso. revert r0. apply Rle_not_lt.
  replace (ρ * x - ρ * y) with (ρ * (x + -y)) by ring. rewrite <- Rmult_0_r with ρ. apply Rmult_le_compat_l; lra.
+ ring_simplify in r0. exfalso. revert r0. apply Rlt_not_ge.
  replace (ρ * x - ρ * y) with (ρ * (x + -y)) by ring. rewrite <- Rmult_0_r with ρ. apply Rmult_lt_compat_l; lra.
+ destruct (Rdec x y).
  - subst. ring.
  - ring_simplify in r0. exfalso. revert r0. apply Rlt_not_ge.
    replace (ρ * x - ρ * y) with (ρ * (x + -y)) by ring.
    rewrite <- Rmult_0_l with (x + - y). apply Rmult_lt_compat_r; lra.
Qed.

Definition homothecy (c ρ : R) (Hρ : ρ <> 0): similarity.
refine {|
  f := bij_homothecy c Hρ;
  ratio := Rabs ρ;
  center := c |}.
Proof.
- abstract (compute; field).
- exact (bij_homothecy_ratio c Hρ).
Defined.


Lemma swap_pos1 : Pos.eq (Pos.map (swap 1) pos1) pos2.
Proof.
intros [g | b].
- unfold Pos.map. simpl. destruct (left_right_dec g); hnf; ring.
- apply Fin.case0. exact b.
Qed.

Lemma swap_pos2 : Pos.eq (Pos.map (swap 1) pos2) pos1.
Proof.
intros [g | b].
- unfold Pos.map. simpl. destruct (left_right_dec g); hnf; ring.
- apply Fin.case0. exact b.
Qed.

(** The movement of robots in the reference position **)
Definition move := r (!! pos1).

(** **  First case: the robots exchange their positions  **)

Section Move1.

Hypothesis Hmove : move = 1.

Lemma da1_ratio : forall id sim c,
  lift_pos (fun _ => Some (fun c => if Rdec c 0 then identity else swap c)) id = Some sim -> ratio (sim c) <> 0.
Proof.
intros id sim c Heq. destruct id; simpl in Heq.
- inversion_clear Heq. Rdec_full; simpl; apply R1_neq_R0.
- apply Fin.case0. exact b.
Qed.

Lemma da1_center : forall id sim c,
  lift_pos (fun _ => Some (fun c => if Rdec c 0 then identity else swap c)) id = Some sim ->
  R.eq (center (sim c)) c.
Proof.
intros id sim c Heq. destruct id; simpl in Heq.
- inversion_clear Heq. Rdec_full; simpl; subst; reflexivity.
- apply Fin.case0. exact b.
Qed.

Definition da1 : demonic_action.
refine {|
  relocate_byz := fun b => 0;
  step := lift_pos (fun g => Some (fun c => if Rdec c 0 then identity else swap c)) |}.
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
+ destruct (left_right_dec g) as [Hleft | Hright].
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
+ destruct (left_right_dec g) as [Hleft | Hright].
  - Rdec. rewrite swap_pos2. simpl. replace 0 with (1 - 1) by ring. hnf. f_equal. apply Hmove.
  - Rdec. simpl.
  (* BUG?: rewrite Pos.map_id should be enough. *)
    assert (Heq : Pos.eq (Pos.map (fun x : R.t => x) pos2) pos2) by apply Pos.map_id.
    apply Spect.from_config_compat, (pgm_compat r) in Heq. rewrite Heq.
    rewrite <- pos1_pos2_spect_eq. fold move. apply Hmove.
+ apply Fin.case0. exact b.
Qed.

Theorem Always_forbidden1 : Always_forbidden (execute r bad_demon1 pos1).
Proof.
cofix differs. constructor.
+ simpl. apply pos1_forbidden.
+ cbn. constructor.
  - simpl. rewrite round_simplify_1_1. apply pos2_forbidden.
  - cbn. rewrite round_simplify_1_1, round_simplify_1_2. apply differs.
Admitted.
(* Le retour des problèmes avec les cofix! *)

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
  lift_pos (fun g => if left_right_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  ratio (sim c) <> 0.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_right_dec g).
  - intro H. inversion_clear H. simpl. now apply Rabs_no_R0.
  - discriminate.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_center_1 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_pos (fun g => if left_right_dec g then Some (fun c => homothecy c Hρ) else None) id = Some sim ->
  R.eq (center (sim c)) c.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_right_dec g).
  - intro H. inversion_clear H. reflexivity.
  - discriminate.
+ apply Fin.case0. exact b.
Qed.

Definition da2_left (ρ : R) (Hρ : ρ <> 0) : demonic_action.
refine {|
  relocate_byz := fun b => 0;
  step := lift_pos (fun g => if left_right_dec g then Some (fun c => homothecy c Hρ) else None) |}.
Proof.
+ apply homothecy_ratio_1.
+ apply homothecy_center_1.
Defined.

Lemma homothecy_ratio_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_pos (fun g => if left_right_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  ratio (sim c) <> 0.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_right_dec g).
  - discriminate.
  - intro H. inversion_clear H. simpl. now apply Rabs_no_R0, Ropp_neq_0_compat.
+ apply Fin.case0. exact b.
Qed.

Lemma homothecy_center_2 : forall ρ (Hρ : ρ <> 0) id sim c,
  lift_pos (fun g => if left_right_dec g 
                     then None else Some (fun c => homothecy c (Ropp_neq_0_compat ρ Hρ))) id = Some sim ->
  R.eq (center (sim c)) c.
Proof.
intros ρ Hρ [g | b] sim c.
+ simpl. destruct (left_right_dec g).
  - discriminate.
  - intro H. inversion_clear H. reflexivity.
+ apply Fin.case0. exact b.
Qed.

Definition da2_right (ρ : R) (Hρ : ρ <> 0) : demonic_action.
refine {|
  relocate_byz := fun b => 0;
  step := lift_pos (fun g => if left_right_dec g
                             then None else Some (fun c => homothecy c (Ropp_neq_0_compat _ Hρ))) |}.
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

Theorem kFair_bad_demon2 : forall ρ (Hρ : ρ <> 0), kFair 1 (bad_demon2 Hρ).
Proof.
cofix fair_demon. intros ρ Hρ. constructor; [| constructor].
* intros [g1 | b1] [g2 | b2]; try now apply Fin.case0; assumption.
  destruct (left_right_dec g1).
  + constructor 1. rewrite bad_demon_head2_1. simpl. destruct (left_right_dec g1); eauto. discriminate.
  + destruct (left_right_dec g2).
    - constructor 2.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_right_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_right_dec g2); eauto. discriminate.
      -- constructor 1. rewrite bad_demon_head2_2. simpl. destruct (left_right_dec g1); eauto. discriminate.
    - constructor 3.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_right_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_1. simpl. destruct (left_right_dec g2); eauto. exfalso. eauto.
      -- constructor 1. rewrite bad_demon_head2_2. simpl. destruct (left_right_dec g1); eauto. discriminate.
* intros [g1 | b1] [g2 | b2]; try now apply Fin.case0; assumption.
  destruct (left_right_dec g1).
  + destruct (left_right_dec g2).
    - constructor 3.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_right_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_right_dec g2); eauto. exfalso. eauto.
      -- rewrite bad_demon_tail2. apply fair_demon.
    - constructor 2.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_right_dec g1); eauto. exfalso. eauto.
      -- rewrite bad_demon_head2_2. simpl. destruct (left_right_dec g2); eauto. discriminate.
      -- rewrite bad_demon_tail2. constructor 1. simpl. destruct (left_right_dec g1); eauto. discriminate.
  + constructor 1. rewrite bad_demon_head2_2. simpl. destruct (left_right_dec g1); eauto. discriminate.
* rewrite bad_demon_tail2. apply fair_demon.
Admitted.

(* In a bivalent position, half of the robots are in the same place. *)
Lemma dist_left : forall d (Hd : d <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = d) ->
  forall g1 g2, In g1 left -> In g2 left -> config (Good g1) = config (Good g2).
Proof.
intros d Hd config Hconfig g1 g2 Hg1 Hg2.
cut (config (Good gright) - config (Good g1) = config (Good gright) - config (Good g2)).
+ intro Heq. unfold Rminus in Heq. apply Rplus_eq_reg_l in Heq. setoid_rewrite <- Ropp_involutive.
  now apply Ropp_eq_compat.
+ assert (Hright := gright_right). repeat rewrite Hconfig; auto.
Qed.

Lemma dist_right : forall d (Hd : d <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = d) ->
  forall g1 g2, In g1 right -> In g2 right -> config (Good g1) = config (Good g2).
Proof.
intros d Hd config Hconfig g1 g2 Hg1 Hg2.
cut (config (Good g1) - config (Good gleft) = config (Good g2) - config (Good gleft)).
+ intro Heq. unfold Rminus in Heq. now apply Rplus_eq_reg_r in Heq.
+ assert (Hleft := gleft_left). repeat rewrite Hconfig; auto.
Qed.

Lemma dist_spectrum : forall d (Hd : d <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = d) ->
  Spect.eq (!! config) (Spect.add (config (Good gleft)) (Nat.div2 N.nG)
                 (Spect.singleton (config (Good gright)) (Nat.div2 N.nG))).
Proof.
intros d Hd config Hconfig pt. assert (Heven := even_nG). fold N.nG in Heven.
assert (Hleft : forall g, In g left -> config (Good g) = config (Good gleft)).
{ intros g Hg. apply (dist_left Hd); auto. }
assert (Hright : forall g, In g right -> config (Good g) = config (Good gright)).
{ intros g Hg. apply (dist_right Hd); auto. }
remember (config (Good gleft)) as ptl. remember (config (Good gright)) as ptr.
assert (Hdiff : ~R.eq ptl ptr).
{ rewrite Heqptl, Heqptr. apply Rminus_not_eq_right. rewrite Hconfig; auto. }
unfold left, right in *.
rewrite <- Spect.Names.Gnames_length, Spect.from_config_spec, Spect.Pos.list_spec in *. rewrite names_Gnames.
change Names.Gnames with Spect.Names.Gnames in *.
induction Spect.Names.Gnames as [| pt' | pt1 pt2 l] using first_last_ind; simpl.
* now rewrite Spect.singleton_0, Spect.add_0, Spect.empty_spec.
* simpl in Heven. inversion_clear Heven. omega.
* rewrite app_length, plus_comm. simpl. repeat rewrite map_app. rewrite countA_occ_app, plus_comm. simpl.
  assert (Heven' : Nat.Even (length l)).
  { destruct Heven as [n Heq]. exists (pred n). rewrite app_length in Heq. simpl in Heq. omega. }
  apply IHl in Heven'.
  + do 2 Rdec_full; simpl.
    - (* absurd case: first and last elements are the same *)
      exfalso. rewrite <- Heq0 in Heq. symmetry in Heq. apply Rminus_diag_eq in Heq. rewrite Hconfig in Heq.
      -- contradiction.
      -- simpl. rewrite app_length, plus_comm. simpl. apply In_skipn_half.
      -- simpl. rewrite app_length, plus_comm. simpl. now left.
    - (* pt ∈ left *)
      unfold R.eq_dec, Rdef.eq_dec in Heven'. change identifier with Spect.Names.ident in *.
      change Spect.Names.Internals.G with Spect.Names.G. rewrite Heven'. subst pt. rewrite Hleft.
      -- now repeat rewrite Spect.add_same, Spect.singleton_other.
      -- simpl. rewrite app_length, plus_comm. simpl. now left.
    - (* pt ∈ right *)
      unfold R.eq_dec, Rdef.eq_dec in Heven'. change identifier with Spect.Names.ident in *.
      change Spect.Names.Internals.G with Spect.Names.G. rewrite Heven'. subst pt. rewrite Hright.
      -- repeat rewrite Spect.add_other, Spect.singleton_same; auto; intro; apply Hdiff; now symmetry.
      -- simpl. rewrite app_length, plus_comm. simpl. apply In_skipn_half.
    - (* absurd case: pt <> left, right *)
      exfalso. admit.
  + 
Admitted.

Lemma dist_forbidden : forall d (Hd : d <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = d) -> forbidden config.
Proof.
intros d Hd config Hconfig. unfold forbidden. split; try apply even_nG; [].
assert (Hdiff : config (Good gleft) <> config (Good gright)).
{ apply Rminus_not_eq_right. rewrite Hconfig; auto. }
exists (config (Good gleft)), (config (Good gright)). repeat split.
- assumption.
- rewrite dist_spectrum; try eassumption. rewrite Spect.add_same, Spect.singleton_other; auto.
- rewrite dist_spectrum; try eassumption. rewrite Spect.add_other, Spect.singleton_same; auto.
Qed.

Lemma dist_homothecy_spectrum : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g, In g left -> Spect.eq (!! (Pos.map (fun x : R => ρ * (x - config (Good g))) config)) (!! pos1).
Proof.
intros ρ Hρ config Hconfig g Hg. f_equiv. intro id. unfold Pos.map.
destruct id as [id | b]; try now apply Fin.case0; [].
unfold pos1. destruct (left_right_dec id).
- rewrite (dist_left (Rinv_neq_0_compat _ Hρ) _ Hconfig id g); trivial. ring_simplify. reflexivity.
- rewrite Hconfig; trivial. now rewrite Rinv_r.
Qed.

Lemma round_dist2_left : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 left -> round r (da2_left Hρ) config (Good g1)
                                             - round r (da2_left Hρ) config (Good g2) = (1 - move) / ρ.
Proof.
intros ρ Hρ config Hconfig g1 g2 Hg1 Hg2. unfold round. simpl.
destruct (left_right_dec g1), (left_right_dec g2); try now exfalso; eauto.
cbn. replace ((1 - move) / ρ) with (/ρ - move / ρ) by now field.
rewrite <- (Hconfig _ _ Hg1 Hg2). ring_simplify.
replace (config (Good g1) - config (Good g2) - move / ρ)
   with (config (Good g1) - move / ρ - config (Good g2)) by ring.
do 3 f_equal. unfold move. apply pgm_compat. now apply dist_homothecy_spectrum.
Qed.

Corollary round2_left_right : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 right ->
    round r (da2_left Hρ) config (Good g1) = round r (da2_left Hρ) config (Good g2).
Proof.
intros. apply Rplus_eq_reg_l with (- round r (da2_left Hρ) config (Good gleft)).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

Corollary round2_left_left : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 left -> In g2 left ->
    round r (da2_left Hρ) config (Good g1) = round r (da2_left Hρ) config (Good g2).
Proof.
intros. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
apply Rplus_eq_reg_r with (round r (da2_left Hρ) config (Good gright)).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

Corollary round2_left_forbidden : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forbidden (round r (da2_left Hρ) config).
Proof.
intros ρ Hρ config Hconfig.
Check dist_forbidden.
apply (dist_forbidden (d := (1 - move) / ρ)).
- admit. (* [lra] should be enough *)
- intros. now apply round_dist2_left.
Admitted.

Lemma round_dist2_right : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 left -> round r (da2_right Hρ) config (Good g1)
                                             - round r (da2_right Hρ) config (Good g2) = (1 - move) / ρ.
Proof.
Admitted.
(*
Corollary round2_left_differ : forall config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) <> config (Good g2)) ->
  forall g1 g2 g3 g4, In g1 right -> In g2 left -> In g3 right -> In g4 left ->
    round r (da2_left (/(config (Good g1) - config (Good g2)))) config (Good g3)
    <> round r (da2_left (/(config (Good g1) - config (Good g2)))) config (Good g4).
Proof.
  intros pos Hx Hy Hpos x y x' y' Habs.
  assert (pos (inr x) - pos (inl y) <> 0) as Hρ.
  { intro. apply (Hpos x y). now apply Rminus_diag_uniq. }
  apply Rminus_diag_eq in Habs.
  rewrite (@round_dist2_1 _ pos (Rinv_neq_0_compat _ Hρ)) in Habs.
  - unfold Rdiv in Habs. rewrite Rinv_involutive in Habs; trivial.
    apply Rmult_integral in Habs. destruct Habs as [Habs | Habs].
    + apply Rminus_diag_uniq in Habs. symmetry in Habs. contradiction.
    + contradiction.
  - intros. rewrite Rinv_involutive; trivial. now rewrite (Hx x0 x), (Hy y0 y).
Qed.
*)

(*
Lemma round_dist2_right : forall ρ (Hρ : ρ <> 0) (config : Pos.t),
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 left -> round r (da2_right Hρ) config (Good g1)
                                             - round r (da2_right Hρ) config (Good g2) = (1 - move) / ρ.
Proof.
intros ρ Hρ config Hconfig g1 g2 Hg1 Hg2. unfold round. simpl.
destruct (left_right_dec g1), (left_right_dec g2); try now exfalso; eauto.
cbn. replace ((1 - move) / ρ) with (/ρ - move / ρ) by now field.
rewrite <- (Hconfig _ _ Hg1 Hg2).
replace (config (Good g1) - config (Good g2) - move / ρ)
   with (move / -ρ + config (Good g1) - config (Good g2)) by now field.
do 3 f_equal. unfold move. apply pgm_compat. apply dist_homothecy_spectrum.
Qed.

Corollary round2_left_right : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 right -> In g2 right ->
    round r (da2_left Hρ) config (Good g1) = round r (da2_left Hρ) config (Good g2).
Proof.
intros. apply Rplus_eq_reg_l with (- round r (da2_left Hρ) config (Good gleft)).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

Corollary round2_left_left : forall ρ (Hρ : ρ <> 0) config,
  (forall g1 g2, In g1 right -> In g2 left -> config (Good g1) - config (Good g2) = /ρ) ->
  forall g1 g2, In g1 left -> In g2 left ->
    round r (da2_left Hρ) config (Good g1) = round r (da2_left Hρ) config (Good g2).
Proof.
intros. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
apply Rplus_eq_reg_r with (round r (da2_left Hρ) config (Good gright)).
setoid_rewrite Rplus_comm. setoid_rewrite round_dist2_left; auto.
Qed.

(* Old version
Lemma round_dist2_right : forall ρ (Hρ : ρ <> 0),
 (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall x y, round r (da2_2 ρ) pos (inr x) - round r (da2_2 ρ) pos (inl y) = (1 - move) / ρ.
Proof.
  intros ρ pos Hρ Hpos. unfold round. simpl. Rdec.
  destruct (Rdec (-ρ) 0) as [Heq | _].
  - elim (Ropp_neq_0_compat ρ Hρ Heq).
  - intros x y.
    erewrite (@AlgoMorph _ _ r _ pos1 (swap0 G)).
    { fold move.
      replace (pos (inr x) + / - ρ * move - pos (inl y)) with (pos (inr x) - pos (inl y) + / - ρ * move) by ring.
      rewrite Hpos. now field. }
    split; intros []; intro n; simpl.
    + assert (forall x y, pos (inr x) = pos (inr y)) as Heq.
      intros. apply Rplus_eq_reg_l with (- (pos (inl x))).
      setoid_rewrite Rplus_comm. unfold Rminus in Hpos. now do 2 rewrite Hpos.
      rewrite (Heq n x). ring.
    + replace (- ρ * (pos (inl n) - pos (inr x))) with (ρ * (pos (inr x) - pos (inl n))) by ring.
      rewrite Hpos. now rewrite Rinv_r.
Qed.

Corollary round_sameX2_2 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall x x', round r (da2_2 ρ) pos (inr x) = round r (da2_2 ρ) pos (inr x').
Proof.
  intros. apply Rplus_eq_reg_l with (- round r (da2_2 ρ) pos (inl x)).
  setoid_rewrite Rplus_comm.
  change (round r (da2_2 ρ) pos (inr x) - round r (da2_2 ρ) pos (inl x)
          = round r (da2_2 ρ) pos (inr x') - round r (da2_2 ρ) pos (inl x)).
  now setoid_rewrite round_dist2_2.
Qed.

Corollary round_sameY2_2 : forall ρ pos, ρ <> 0 -> (forall x y, pos (inr x) - pos (inl y) = /ρ) ->
  forall y y', round r (da2_2 ρ) pos (inl y) = round r (da2_2 ρ) pos (inl y').
Proof.
  intros. setoid_rewrite <- Ropp_involutive. apply Ropp_eq_compat.
  apply Rplus_eq_reg_l with (round r (da2_2 ρ) pos (inr y)).
  change (round r (da2_2 ρ) pos (inr y) - round r (da2_2 ρ) pos (inl y) =
          round r (da2_2 ρ) pos (inr y) - round r (da2_2 ρ) pos (inl y')).
  now setoid_rewrite round_dist2_2.
Qed.

Corollary round_differ2_2 : forall pos,
  (forall x x', pos (inr x) = pos (inr x')) ->
  (forall y y', pos (inl y) = pos (inl y')) ->
  (forall x y, pos (inr x) <> pos (inl y)) ->
  forall x y x' y', round r (da2_2 (/(pos(inr x)-pos(inl y)))) pos (inr x')
                 <> round r (da2_2 (/(pos(inr x)-pos(inl y)))) pos (inl y').
Proof.
  intros pos Hx Hy Hpos x y x' y' Habs.
  assert (pos (inr x) - pos (inl y) <> 0) as Hρ.
  { intro. apply (Hpos x y). now apply Rminus_diag_uniq. }
  apply Rminus_diag_eq in Habs.
  rewrite (@round_dist2_2 _ pos (Rinv_neq_0_compat _ Hρ)) in Habs.
  - unfold Rdiv in Habs. rewrite Rinv_involutive in Habs; trivial.
    apply Rmult_integral in Habs.
    destruct Habs as [Habs | Habs].
    + apply Rminus_diag_uniq in Habs. symmetry in Habs. contradiction.
    + contradiction.
  - intros. rewrite Rinv_involutive; trivial. now rewrite (Hx x0 x), (Hy y0 y).
Qed.
*)
*)
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

Given a non empty finite even set [G ⊎ G] and a robogram [r] on ([G] ⊎
[G]) × ∅, there is no (k>0)-fair demon  for which the
gathering problem is solved for any starting position. *)

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
    intros. simpl. destruct (left_right_dec g1), (left_right_dec g2); field || exfalso; eauto.
Qed.

End GatheringEven.

Check noGathering.
Print Assumptions noGathering.
