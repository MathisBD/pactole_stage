Require Import Arith.Div2.
Require Import Omega.
Require Import Reals.
Require Import List.
Require Import Morphisms.
Require Import Sorting.Permutation.
Require Import Psatz.
Require Import SetoidList.
Require Export SetoidPermutation.
Require Import Bool.


Set Implicit Arguments.


Lemma nat_compare_Eq_comm : forall n m, nat_compare n m = Eq <-> nat_compare m n = Eq.
Proof. intros n m. do 2 rewrite nat_compare_eq_iff. now split. Qed.

Lemma nat_compare_Lt_Gt : forall n m, nat_compare n m = Lt <-> nat_compare m n = Gt.
Proof. intros n m. rewrite <- nat_compare_lt, <- nat_compare_gt. now split. Qed.

Definition injective {A B : Type} eqA eqB (f : A -> B) := (forall x y, eqB (f x) (f y) -> eqA x y).
(*
Lemma div2_lt : forall n m, n < div2 m -> n + n < m.
Proof.
intros n m Hlt. induction m using ind_0_1_SS.
+ inversion Hlt.
+ destruct n; auto; inversion Hlt.
+ simpl in *. destruct (eq_nat_dec n (div2 m)) as [Heq | Heq].
  - subst. simpl. clear. induction m using ind_0_1_SS; auto.
    simpl. rewrite <- plus_n_Sm. omega.
  - transitivity m; auto. apply IHm. omega.
Qed.
*)
Lemma div2_le_compat : Proper (le ==> le) div2.
Proof.
intro n. induction n using ind_0_1_SS; intros m Heq; auto with arith.
destruct m as [| [| m]]; try now inversion Heq.
simpl. do 2 apply le_S_n in Heq. apply IHn in Heq. omega.
Qed.


(* ************************************ *)
(** * Some necessary results on Lists.  *)
(* ************************************ *)

Section List_results.
Context (A B : Type).
Context (eqA eqA' : relation A) (eqB : relation B).
Context (HeqA : Equivalence eqA) (HeqB : Equivalence eqB).

(* Found in SetoidList
Lemma In_InA_weak : forall x l, In x l -> InA eqA x l.
Proof.
intros x l Hin. induction l.
- inversion Hin.
- destruct Hin. subst. now left. right. auto.
Qed. *)

Lemma nil_or_In_dec : forall l : list A, {l = nil} + {exists x, In x l}.
Proof. intros [| x l]; auto. right. exists x. now left. Qed.

Lemma not_nil_In : forall l : list A, l <> nil -> exists x, In x l.
Proof.
intros [| x l] Hl.
- now elim Hl.
- exists x. now left.
Qed.

Lemma InA_Leibniz : forall (x : A) l, InA Logic.eq x l <-> In x l.
Proof.
intros x l. split; intro Hl; induction l; inversion_clear Hl; (subst; now left) || (right; now apply IHl).  
Qed.

Lemma NoDupA_Leibniz : forall l : list A, NoDupA Logic.eq l <-> NoDup l.
Proof.
intro l. split; intro Hl; induction l; inversion_clear Hl; constructor;
(now rewrite <- InA_Leibniz in *) || now apply IHl.
Qed.

Lemma inclA_Leibniz : forall l1 l2 : list A, inclA Logic.eq l1 l2 <-> incl l1 l2.
Proof. intros. unfold inclA, incl. setoid_rewrite InA_Leibniz. reflexivity. Qed.

Instance eqlistA_PermutationA_subrelation : subrelation (eqlistA eqA) (PermutationA eqA).
Proof. intros ? ? Heq. induction Heq; constructor; auto. Qed.

Lemma Permutation_PermutationA_weak : forall l1 l2, Permutation l1 l2 -> PermutationA eqA l1 l2.
Proof. intros ? ? Heq. induction Heq; try now constructor. now transitivity l'. Qed.

Global Instance PermutationA_compat A eqA (HeqA : @Equivalence A eqA) :
  Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (PermutationA eqA).
Proof. intros l1 l2 Hl12 l3 l4 Hl34. now rewrite Hl12, Hl34. Qed.

Lemma PermutationA_Leibniz : forall l1 l2 : list A, PermutationA Logic.eq l1 l2 <-> Permutation l1 l2.
Proof.
intros l1 l2. split; intro Hl.
  induction Hl; try now constructor.
    subst. now constructor.
    now transitivity l₂.
  induction Hl; try now constructor. now transitivity l'.
Qed.

Lemma PermutationA_subrelation_compat : Proper (subrelation ==> eq ==> eq ==> impl) (@PermutationA A).
Proof.
intros eqA1 eqA2 Hrel l1 l2 H12 l3 l4 H34 Hperm. subst. induction Hperm.
- constructor.
- constructor. now apply Hrel. assumption.
- constructor 3.
- now constructor 4 with l₂.
Qed.

Lemma NoDupA_2 : forall x y, ~eqA x y -> NoDupA eqA (x :: y :: nil).
Proof.
intros x y Hdiff. constructor.
  intro Habs. inversion_clear Habs.
    now elim Hdiff.
    inversion H.
  apply NoDupA_singleton.
Qed.

Lemma NoDupA_3 : forall x y z, ~eqA x y -> ~eqA y z -> ~eqA x z -> NoDupA eqA (x :: y :: z :: nil).
Proof.
intros x y z Hxy Hyz Hxz. constructor.
  intro Habs. inversion_clear Habs. contradiction. inversion_clear H. contradiction. inversion_clear H0.
  now apply NoDupA_2.
Qed.

Instance PermutationA_eq_compat : Proper ((eq ==> eq ==> iff) ==> eq ==> eq ==> iff) (@PermutationA A).
Proof.
intros f g Hfg l1 l2 Hl12 l3 l4 Hl34. subst l4 l2. split; intro H.
+ induction H.
  - constructor.
  - constructor. now rewrite <- (Hfg _ _ (eq_refl x₁) _ _ (eq_refl x₂)). assumption.
  - constructor 3.
  - now constructor 4 with l₂.
+ induction H.
  - constructor.
  - constructor. now rewrite (Hfg _ _ (eq_refl x₁) _ _ (eq_refl x₂)). assumption.
  - constructor 3.
  - now constructor 4 with l₂.
Qed.

Instance Permutation_length_compat : Proper (@Permutation A ==> eq) (@length A).
Proof. now intros ? ? ?; apply Permutation_length. Qed.

Instance In_perm_compat : Proper (eq ==> @Permutation A ==> iff) (@In A).
Proof. intros x y ? l l' Hl. subst. split; apply Permutation_in; assumption || now symmetry. Qed.

Instance In_permA_compat : Proper (eq ==> @PermutationA A eq ==> iff) (@In A).
Proof. repeat intro. rewrite PermutationA_Leibniz in *. now apply In_perm_compat. Qed.

Lemma last_In : forall l (x : A), l <> List.nil -> List.In (List.last l x) l.
Proof.
induction l; intros x Hx. now elim Hx.
destruct l. now left. 
change (List.In (List.last (a0 :: l) x) (a :: a0 :: l)).
right. apply IHl. discriminate.
Qed.

Lemma hd_last_diff : forall l d d', length l > 1 -> NoDupA eqA l ->
  ~eqA (hd d l) (last l d').
Proof.
intros l d d' Hl Hnodup Heq.
destruct l as [| x [| y l]]; simpl in Hl; try omega.
inversion_clear Hnodup. change (eqA x (last (y :: l) d')) in Heq.
apply H. rewrite Heq. rewrite InA_alt. eexists; split; try reflexivity.
apply last_In. discriminate.
Qed.

Lemma map_singleton : forall (f : A -> B) l x, map f l = x :: nil <-> exists y, l = y :: nil /\ x = f y.
Proof.
intros f l x. destruct l as [| y [| ? ?]]; simpl.
+ split; intro Heq.
  - inversion Heq.
  - destruct Heq as [? [Heq _]]. inversion Heq.
+ split; intro Heq.
  - exists y. inversion Heq. auto.
  - destruct Heq as [? [Heq ?]]. subst. now inversion Heq.
+ split; intro Heq.
  - inversion Heq.
  - destruct Heq as [? [Heq _]]. inversion Heq.
Qed.

Lemma map_hd : forall (f : A -> B) l d, List.hd (f d) (map f l) = f (List.hd d l).
Proof. intros f l d. now destruct l. Qed.

Lemma map_last : forall (f : A -> B) l d, last (map f l) (f d) = f (last l d).
Proof.
intros f l d. induction l; simpl.
  reflexivity.
  destruct l. simpl. reflexivity. apply IHl.
Qed.

Theorem InA_map_iff : forall f, Proper (eqA ==> eqB) f ->
  forall l y, InA eqB y (map f l) <-> exists x, eqB (f x) y /\ InA eqA x l.
Proof.
intros f Hf l y. induction l.
+ split; intro Hin.
  - inversion Hin.
  - destruct Hin as [x [_ Hin]]. inversion Hin.
+ split; intro Hin.
  - inversion_clear Hin.
      exists a. split. now symmetry. now left.
      rewrite IHl in H. destruct H as [x [Hx H]]. exists x; auto.
  - destruct Hin as [x [Hx Hin]]. inversion_clear Hin.
      left. now rewrite <- Hx, H.
      simpl. right. rewrite IHl. exists x. now split.
Qed.

Fixpoint alls (x : A) n :=
  match n with
    | 0 => Datatypes.nil
    | S m => x :: alls x m
  end.

Lemma alls_length : forall (x : A) n, length (alls x n) = n.
Proof. intros x n. induction n; simpl; auto. Qed.

Lemma alls_In : forall x y n, In y (alls x n) -> y = x.
Proof. intros x y n Hin. induction n; inversion Hin. auto. now apply IHn. Qed.

Lemma alls_In_iff : forall (x y : A) n, n > 0 -> (In y (alls x n) <-> y = x).
Proof.
intros x y n Hn. split; intro H.
+ eapply alls_In; eassumption.
+ induction n. now inversion Hn. left; auto.
Qed.

Corollary alls_not_In : forall (x y : A) n, x <> y -> ~In y (alls x n).
Proof.
intros x y n Hxy Habs. apply Hxy. symmetry.
destruct n. now inversion Habs. rewrite alls_In_iff in Habs; assumption || omega.
Qed.

Lemma alls_inj1 : forall x1 x2 n1 n2, alls x1 (S n1) = alls x2 n2 -> x1 = x2.
Proof. intros x1 x2 n1 [] Heq; simpl in *. discriminate Heq. now inversion Heq. Qed.

Lemma alls_inj2 : forall x1 x2 n1 n2, alls x1 n1 = alls x2 n2 -> n1 = n2.
Proof.
intros x1 x2 n1. induction n1; intros [] Heq; try reflexivity || discriminate Heq.
f_equal. apply IHn1. now inversion Heq.
Qed.

Lemma alls_app : forall x n1 n2, alls x n1 ++ alls x n2 = alls x (n1 + n2).
Proof.
intros x n1 n2. induction n1; simpl.
+ reflexivity.
+ f_equal. assumption.
Qed.

Lemma alls_carac : forall x l, (forall y, In y l -> y = x) <-> l = alls x (length l).
Proof.
intros x l. split; intro H.
  induction l. reflexivity. simpl. f_equal.
    apply H. now left.
    apply IHl. intros y Hy. apply H. now right.
  rewrite H. intro. apply alls_In.
Qed. 

Lemma Forall_Perm_trans : forall (l1 l2 : list A) (P Q : A -> Prop),
  (eq ==> iff)%signature P Q -> Permutation l1 l2 -> List.Forall P l1 -> List.Forall Q l2.
Proof.
intros l1 l2 P Q HPQ Hperm Hfor. 
rewrite List.Forall_forall in *. intros. rewrite <- (HPQ _ _ eq_refl). 
apply Hfor. revert H. apply Permutation_in. now symmetry.
Qed.

Lemma Forall_Permutation_compat : Proper ((eq ==> iff) ==> @Permutation A ==> iff) (@List.Forall A).
Proof. repeat intro. split; apply Forall_Perm_trans; easy || (repeat intro; symmetry; auto). Qed.

Lemma Permutation_alls : forall (x : A) n l,
  Permutation l (alls x n) <-> l = alls x n.
Proof.
intros x n l. split.
+ revert l. induction n; intros l Hl.
  - simpl in *. apply Permutation_nil. now symmetry.
  - destruct l.
      apply Permutation_nil in Hl. discriminate Hl.
      assert (a = x). { apply alls_In with (S n). simpl alls. rewrite <- Hl. now left. }
      subst. simpl in *. f_equal. apply IHn. apply (Permutation_cons_inv Hl).
+ intro Hl. now rewrite Hl.
Qed.

Lemma map_alls : forall f pt n, map f (alls pt n) = alls (f pt) n.
Proof. intros f pt n. induction n. reflexivity. simpl. now rewrite IHn. Qed.

Lemma map_cst_alls : forall pt l, map (fun _ : B => pt) l = alls pt (length l).
Proof. intros pt l. induction l; simpl; try rewrite IHl; reflexivity. Qed.

Lemma In_nth : forall d x (l : list A), In x l -> exists n, (n < length l)%nat /\ nth n l d = x.
Proof.
intros x d l Hin. induction l.
- inversion Hin.
- destruct Hin.
    subst. exists 0%nat. split. simpl. now auto with arith. reflexivity.
    destruct (IHl H) as [n [Hn Hl]]. apply lt_n_S in Hn. exists (S n). now split.
Qed.
(*
Lemma In_split_first : forall (x : A) l, In x l -> exists l1, exists l2, ~List.In x l1 /\ l = l1 ++ x :: l2.
Proof.
intros x l. induction l as [| a l]; intro Hin.
  now elim (List.in_nil Hin).
  destruct Hin.
    subst. exists nil. exists l. intuition.
    destruct (IHl H) as [l1 [l2 [Hnin Heq]]].
    exists (a :: l1). exists l2. subst. intuition.
Abort. (* require decidability of equality *)
*)
Lemma Permutation_in_inside : forall (x : A) l l',
  Permutation l l' -> In x l -> exists l1 l2, l' = l1 ++ x :: l2.
Proof.
intros x l l' Hperm Hin. rewrite Hperm in Hin.
destruct (in_split _ _ Hin) as [l1 [l2 Heq]]. exists l1. exists l2. now subst l'.
Qed.

Corollary Permutation_cons_inside : forall (x : A) l l',
  Permutation (x :: l) l' -> exists l1 l2, Permutation l (l1 ++ l2) /\ l' = l1 ++ x :: l2.
Proof.
intros x l l' Hperm. destruct (Permutation_in_inside x Hperm) as [l1 [l2 Heql]]. now left.
exists l1. exists l2. split.
- apply Permutation_cons_inv with x. transitivity l'. assumption. subst. symmetry. apply Permutation_middle.
- assumption.
Qed.

Lemma Permutation_NoDup : forall (l l' : list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
intros l l' Hperm. induction Hperm; intro Hdup.
+ trivial.
+ inversion_clear Hdup. constructor.
    intro Habs. apply H. now rewrite Hperm.
    auto.
+ inversion_clear Hdup. inversion_clear H0. constructor.
    intros [Habs | Habs]. subst. apply H. now left. contradiction.
    constructor. intro Habs. apply H. now right. assumption.
+ auto.
Qed.

Instance Permutation_NoDup_compat : Proper (@Permutation A ==> iff) (@NoDup A).
Proof. repeat intro. now split; apply Permutation_NoDup. Qed.

Lemma remove_in_out eq_dec : forall (x y : A) l, y <> x -> (In x (remove eq_dec y l) <-> In x l).
Proof.
intros x y l Hxy. induction l. reflexivity.
simpl. destruct (eq_dec y a).
  subst. rewrite IHl. split; intro H. now right. now destruct H.
  simpl. now rewrite IHl.
Qed.
Global Arguments remove_in_out eq_dec [x] y l _.

Theorem remove_in_iff eq_dec : forall (x y : A) l, In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
intros x y l. induction l as [| a l].
+ split; intro Habs. inversion Habs. destruct Habs as [Habs _]. inversion Habs.
+ simpl. destruct (eq_dec y a). 
  - subst a. rewrite IHl. intuition. now elim H3.
  - simpl. rewrite IHl. split; intro Hin.
      now destruct Hin; try subst a; intuition.
      intuition.
Qed.

Lemma remove_alls eq_dec : forall x n, remove eq_dec x (alls x n) = nil.
Proof.
intros x n. induction n.
  reflexivity.
  simpl. destruct (eq_dec x x) as [_ | Hneq]; assumption || now elim Hneq.
Qed.

Lemma remove_alls' eq_dec : forall x y n, x <> y -> remove eq_dec x (alls y n) = alls y n.
Proof.
intros x y n Hxy. induction n.
  reflexivity.
  simpl. destruct (eq_dec x y) as [Heq | _]; contradiction || now rewrite IHn.
Qed.

Lemma remove_nil eq_dec : forall x l, remove eq_dec x l = nil <-> l = alls x (length l).
Proof.
intros x l. split; intro Hl.
+ induction l; simpl in *.
  - reflexivity.
  - destruct (eq_dec x a).
      subst. now rewrite <- IHl.
      discriminate Hl.
+ rewrite Hl. apply remove_alls.
Qed.

Instance remove_Perm_proper eq_dec : Proper (eq ==> @Permutation A ==> @Permutation A) (@remove A eq_dec).
Proof.
intros x y ? l1 l2 Hl. subst. induction Hl.
- apply Permutation_refl.
- simpl. destruct (eq_dec y x). assumption. now constructor.
- simpl. destruct (eq_dec y y0), (eq_dec y x); apply Permutation_refl || now constructor.
- now constructor 4 with (remove eq_dec y l').
Qed.

Lemma remove_app eq_dec : forall (x : A) l1 l2,
  remove eq_dec x (l1 ++ l2) = remove eq_dec x l1 ++ remove eq_dec x l2.
Proof.
intros x l1 l2. induction l1. reflexivity. simpl.
destruct (eq_dec x a). apply IHl1. simpl. f_equal. apply IHl1.
Qed.

Corollary remove_inside_in eq_dec :
  forall (x : A) l1 l2, remove eq_dec x (l1 ++ x :: l2) = remove eq_dec x l1 ++ remove eq_dec x l2.
Proof. intros x ? ?. rewrite remove_app. simpl. destruct (eq_dec x x) as [| Hneq]. reflexivity. now elim Hneq. Qed.

Corollary remove_inside_out eq_dec : forall (x y : A) l1 l2,
  x <> y -> remove eq_dec x (l1 ++ y :: l2) = remove eq_dec x l1 ++ y :: remove eq_dec x l2.
Proof. intros x y ? ? ?. rewrite remove_app. simpl. destruct (eq_dec x y). contradiction. reflexivity. Qed.

Lemma remove_idempotent eq_dec : forall (x : A) l, remove eq_dec x (remove eq_dec x l) = remove eq_dec x l.
Proof.
intros x l. induction l.
  reflexivity.
  simpl. destruct (eq_dec x a) eqn:Hx.
    assumption.
    simpl. rewrite Hx. now rewrite IHl.
Qed.

Lemma remove_comm eq_dec : forall (x y : A) l,
  remove eq_dec x (remove eq_dec y l) = remove eq_dec y (remove eq_dec x l).
Proof.
intros x y l. induction l.
  reflexivity.
  simpl. destruct (eq_dec y a) eqn:Hy, (eq_dec x a) eqn:Hx; simpl;
  try rewrite Hx; try rewrite Hy; simpl; now rewrite IHl.
Qed.

Lemma remove_length_le eq_dec : forall l (x : A), length (remove eq_dec x l) <= length l.
Proof.
intros l x. induction l; simpl.
  reflexivity.
  destruct (eq_dec x a); simpl; omega.
Qed.

Instance InA_impl_compat : Proper (subrelation ==> eq ==> eq ==> impl) (@InA A).
Proof.
intros R1 R2 HR x y Hxy l l2 Hl Hin. subst y l2. induction l.
  now inversion Hin.
  inversion_clear Hin.
    constructor. now apply HR.
    constructor 2. now apply IHl.
Qed.

Lemma PermutationA_nil : forall l, PermutationA eqA nil l -> l = nil.
Proof.
intros l Hl. destruct l.
  reflexivity.
  exfalso. rewrite <- InA_nil. rewrite (PermutationA_equivlistA HeqA).
    now left.
    eassumption.
Qed.

Instance InA_compat : Proper (eqA ==> equivlistA eqA ==> iff) (InA eqA).
Proof.
intros x y Hxy l1 l2 Hl. split; intro H; eapply InA_eqA; try eassumption.
  now rewrite <- Hl.
  symmetry. eassumption.
  now rewrite Hl.
Qed.

Instance InA_perm_compat : Proper (eqA ==> PermutationA eqA ==> iff) (InA eqA).
Proof. intros x y Hxy l1 l2 Hl. now apply InA_compat; try apply PermutationA_equivlistA. Qed.

Lemma PermutationA_InA_inside : forall (x : A) l l',
  PermutationA eqA l l' -> InA eqA x l -> exists l1 y l2, eqA x y /\ l' = l1 ++ y :: l2.
Proof. intros x l l' Hperm Hin. rewrite Hperm in Hin. apply (InA_split Hin). Qed.

Lemma PermutationA_cons_split : forall (x : A) l l',
  PermutationA eqA (x :: l) l' -> exists l'', PermutationA eqA l' (x :: l'').
Proof.
intros x l l' Hperm. assert (Hin : InA eqA x l'). { rewrite <- Hperm. now left. }
symmetry in Hperm. destruct (PermutationA_InA_inside Hperm Hin) as [l1 [y [l2 [Heq Hll]]]].
exists (l1 ++ l2). rewrite Hperm, Hll. etransitivity. symmetry. apply (PermutationA_middle _).
constructor. now symmetry. reflexivity.
Qed.

Theorem PermutationA_ind_bis :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x₁ x₂ l l', eqA x₁ x₂ -> PermutationA eqA l l' -> P l l' -> P (x₁ :: l) (x₂ :: l')) ->
   (forall x y l l', PermutationA eqA l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', PermutationA eqA l l' -> P l l' -> PermutationA eqA l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationA eqA l l' -> P l l'.
Proof.
  intros P Hnil Hskip Hswap Htrans.
  induction 1; auto.
    apply Hswap; auto.
      reflexivity.
      induction l; auto. now apply Hskip.
    now apply Htrans with l₂.
Qed.

Ltac break_list l x l' H := destruct l as [| x l']; inversion H; subst; simpl in *.

Theorem PermutationA_app_inv : forall (l1 l2 l3 l4:list A) a,
  PermutationA eqA (l1++a::l2) (l3++a::l4) -> PermutationA eqA (l1++l2) (l3 ++ l4).
Proof.
  set (P l l' :=
         forall a b l1 l2 l3 l4, eqA a b -> l=l1++a::l2 -> l'=l3++b::l4 -> PermutationA eqA (l1++l2) (l3++l4)).
  cut (forall l l', PermutationA eqA l l' -> P l l').
  intros; apply (H _ _ H0 a a); auto. reflexivity.
  intros; apply (PermutationA_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto.
+ (* nil *)
  intros; destruct l1; simpl in *; discriminate.
+ (* skip *)
  intros x x' l l' Heq H IH; intros.
  break_list l1 c l1' H1; break_list l3 d l3' H2.
  - now auto. 
  - rewrite H. symmetry. etransitivity.
      constructor 2. transitivity a. symmetry. apply Heq. apply H0. reflexivity.
      now apply PermutationA_middle.
  - rewrite <- H. etransitivity.
      constructor 2. transitivity b. apply Heq. symmetry. apply H0. reflexivity.
      now apply PermutationA_middle.
  - rewrite (IH a _ _ _ _ _ H0 eq_refl eq_refl). now constructor 2.
+ (* contradict *)
  intros x y l l' Hp IH; intros.
  break_list l1 c l1' H0; break_list l3 d l3' H1.
  - now constructor 2.
  - break_list l3' c l3'' H4.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp. now rewrite Hp, H. refine _. 
  - break_list l1' d l1'' H0.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp. now rewrite <- H, Hp. refine _. 
  - break_list l3' e l3'' H1; break_list l1' g l1'' H4.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp. rewrite permA_swap, <- H. now constructor 2. refine _.
      rewrite permA_swap, PermutationA_middle, H. now constructor 2. refine _.
      now rewrite permA_swap, (IH a _ _ _ _ _ H eq_refl eq_refl).
+ (*trans*)
  intros.
  destruct (@InA_split _ eqA l' a) as [l'1 [y [l'2 [H7 H6]]]].
  - rewrite <- H. subst l. rewrite InA_app_iff. now right; left.
  - apply permA_trans with (l'1++l'2).
      apply (H0 _ _ _ _ _ _ H7 H4 H6).
      rewrite H7 in H3. apply (H2 _ _ _ _ _ _ H3 H6 H5).
Qed.

Theorem PermutationA_cons_inv :
   forall l l' (a : A), PermutationA eqA (a::l) (a::l') -> PermutationA eqA l l'.
Proof. intros; exact (PermutationA_app_inv nil l nil l' a H). Qed.

Instance PermutationA_length : Proper (PermutationA eqA ==> Logic.eq) (@length A).
Proof.
intro l. induction l; intros l' Hperm.
  apply PermutationA_nil in Hperm. now subst.
  assert (Hp := @PermutationA_InA_inside a _ _ Hperm).
  destruct Hp as [l1 [y [l2 [Heq1 Heq2]]]]. now left. subst l'.
  rewrite app_length. simpl. rewrite <- plus_n_Sm. f_equal. rewrite <- app_length.
  apply IHl. apply PermutationA_cons_inv with a.
  transitivity (l1 ++ y :: l2). assumption. etransitivity. symmetry. apply PermutationA_middle. assumption.
  constructor. now symmetry. reflexivity.
Qed.

Lemma PermutationA_NoDupA : forall (l l' : list A), PermutationA eqA l l' -> NoDupA eqA l -> NoDupA eqA l'.
Proof.
intros l l' Hperm. induction Hperm; intro Hdup.
+ trivial.
+ inversion_clear Hdup. constructor.
    intro Habs. apply H0. now rewrite Hperm, H.
    now apply IHHperm.
+ inversion_clear Hdup. inversion_clear H0. constructor.
    intros Habs. inversion_clear Habs. apply H. now left. contradiction.
    constructor. intro Habs. apply H. now right. assumption.
+ auto.
Qed.

Instance PermutationA_NoDupA_compat : Proper (PermutationA eqA ==> iff) (NoDupA eqA).
Proof. now repeat intro; split; apply PermutationA_NoDupA. Qed.

Lemma PermutationA_length1 : forall x l, PermutationA eqA l (x :: nil) -> exists y, eqA x y /\ l = y :: nil.
Proof.
intros x l Hperm. destruct l as [| a [| b l]].
- apply PermutationA_nil in Hperm. discriminate Hperm.
- exists a. assert (Hlength := PermutationA_length Hperm).
  apply PermutationA_InA_inside with a _ _ in Hperm.
    destruct Hperm as [l1 [y [l2 [Heq Hl]]]].
    rewrite Hl in Hlength. rewrite app_length in Hlength. simpl in Hlength.
    assert (Hl1 : length l1 = 0) by omega. assert (Hl2 : length l2 = 0) by omega. clear Hlength.
    destruct l1, l2.
      inversion Hl. now split.
      now inversion Hl.
      discriminate Hl1.
      discriminate Hl2.
    now left.
- apply PermutationA_length in Hperm. simpl in Hperm. omega.
Qed.

Lemma PermutationA_1 : forall x x', PermutationA eqA (x :: nil) (x' :: nil) <-> eqA x x'.
Proof.
intros. split; intro Hperm.
+ apply PermutationA_length1 in Hperm. destruct Hperm as [y [Heq Hperm]]. inversion_clear Hperm. now symmetry.
+ rewrite Hperm. reflexivity.
Qed.

Lemma PermutationA_2 : forall x y x' y', PermutationA eqA (x :: y :: nil) (x' :: y' :: nil) <->
  eqA x x' /\ eqA y y' \/ eqA x y' /\ eqA y x'.
Proof.
intros. split.
+ generalize (eq_refl (x :: y :: nil)). generalize (x :: y :: nil) at -2. intros l1 Hl1.
  generalize (eq_refl (x' :: y' :: nil)). generalize (x' :: y' :: nil) at -2. intros l2 Hl2 perm.
  revert x y x' y' Hl1 Hl2. induction perm.
  - intros * Hl1 Hl2. inversion Hl1.
  - intros x x' y y' Hl1 Hl2. inversion Hl1. inversion Hl2. subst.
    rewrite PermutationA_1 in perm. auto.
  - intros x' x'' y' y'' Hl1 Hl2. inversion Hl1. inversion Hl2. do 2 subst. right; split; reflexivity.
  - intros x x' y y' Hl1 Hl2. subst.
    assert (Hlength : length l₂ = length (y :: y' :: nil)) by now rewrite perm2.
    destruct l₂ as [| x'' [| y'' [| ? ?]]]; discriminate Hlength || clear Hlength.
    destruct (IHperm1 _ _ _ _ $(reflexivity)$ $(reflexivity)$) as [[H11 H12] | [H11 H12]],
             (IHperm2 _ _ _ _ $(reflexivity)$ $(reflexivity)$) as [[H21 H22] | [H21 H22]];
    rewrite H11, H12, <- H21, <- H22; intuition.
+ intros [[Heq1 Heq2] | [Heq1 Heq2]]; rewrite Heq1, Heq2. reflexivity. now constructor 3.
Qed.

Lemma PermutationA_3 : forall x y z x' y' z',
  PermutationA eqA (x :: y :: z :: nil) (x' :: y' :: z' :: nil) <->
  eqA x x' /\ eqA y y' /\ eqA z z' \/ eqA x x' /\ eqA y z' /\ eqA z y' \/
  eqA x y' /\ eqA y x' /\ eqA z z' \/ eqA x y' /\ eqA y z' /\ eqA z x' \/
  eqA x z' /\ eqA y y' /\ eqA z x' \/ eqA x z' /\ eqA y x' /\ eqA z y'.
Proof.
intros. split.
+ generalize (eq_refl (x :: y :: z :: nil)). generalize (x :: y :: z :: nil) at -2. intros l1 Hl1.
  generalize (eq_refl (x' :: y' :: z' :: nil)). generalize (x' :: y' :: z' :: nil) at -2. intros l2 Hl2 perm.
  revert x y z x' y' z' Hl1 Hl2. induction perm; intros.
  - discriminate Hl1.
  - inversion Hl1. inversion Hl2. subst. rewrite PermutationA_2 in perm. intuition.
  - inversion Hl1. inversion Hl2. do 2 subst. inversion H5. intuition.
  - subst. assert (Hlength : length l₂ = length (x' :: y' :: z' :: nil)) by now rewrite perm2.
    destruct l₂ as [| x'' [| y'' [| z'' [| ? ?]]]]; discriminate Hlength || clear Hlength.
    specialize (IHperm1 _ _ _ _ _ _ $(reflexivity)$ $(reflexivity)$).
    specialize (IHperm2 _ _ _ _ _ _ $(reflexivity)$ $(reflexivity)$).
    repeat destruct IHperm1 as [IHperm1 | IHperm1]; destruct IHperm1 as [H11 [H12 H13]];
    repeat destruct IHperm2 as [IHperm2 | IHperm2]; destruct IHperm2 as [H21 [H22 H23]];
    rewrite H11, H12, H13, <- H21, <- H22, <-H23; intuition.
+ intro Hperm. repeat destruct Hperm as [Hperm | Hperm]; destruct Hperm as [Heq1 [Heq2 Heq3]].
  - repeat apply PermutationA_cons; trivial. constructor.
  - apply PermutationA_cons; trivial. rewrite PermutationA_2. intuition.
  - etransitivity; [constructor 3 |].
    repeat apply PermutationA_cons; trivial. constructor.
  - etransitivity; [| constructor 3].
    apply PermutationA_cons; trivial. rewrite Heq2, Heq3. constructor 3.
  - etransitivity; [constructor 3 |]. etransitivity; [| constructor 3].
    apply PermutationA_cons; trivial. rewrite Heq1, Heq3. constructor 3.
  - etransitivity; [constructor 3 |].
    apply PermutationA_cons; trivial. rewrite Heq1, Heq3. constructor 3.
Qed.

Lemma NoDupA_strengthen : forall l, subrelation eqA eqA' -> NoDupA eqA' l -> NoDupA eqA l.
Proof.
intros l HAB Hl. induction l.
  constructor.
  inversion_clear Hl. constructor.
    intro Habs. apply H. clear -Habs HAB. induction Habs.
      left. now apply (HAB a y).
      now right.
    now apply IHl.
Qed.

Instance fold_left_start : forall f, Proper (eqB ==> eqA ==> eqB) f ->
  forall l, Proper (eqB ==> eqB) (fold_left f l).
Proof.
intros f Hf l. induction l; intros i1 i2 Hi; simpl.
  assumption.
  rewrite IHl. reflexivity. now rewrite Hi.
Qed.

Instance fold_left_symmetry_PermutationA : forall (f : B -> A -> B),
  Proper (eqB ==> eqA ==> eqB) f -> (forall x y z, eqB (f (f z x) y) (f (f z y) x)) ->
  Proper (PermutationA eqA ==> eqB ==> eqB) (fold_left f).
Proof.
intros f Hfcomm Hf l1 l2 perm. induction perm; simpl.
- now repeat intro.
- intros ? ? Heq. rewrite H, Heq. now apply IHperm.
- intros ? ? Heq. now rewrite Hf, Heq.
- repeat intro. etransitivity. now apply IHperm1. now apply IHperm2.
Qed.

Instance PermutationA_map : forall f, Proper (eqA ==> eqB) f ->
  Proper (PermutationA eqA ==> PermutationA eqB) (map f).
Proof.
intros f Hf l l' perm. induction perm; simpl.
  reflexivity.
  constructor 2. now rewrite H. now apply IHperm.
  now constructor 3.
  now transitivity (map f l₂).
Qed.

Lemma HdRel_app : forall l1 l2 R (a : A), HdRel R a l1 -> HdRel R a l2 -> HdRel R a (l1++l2).
Proof. induction l1; simpl; auto. intros. inversion_clear H. now constructor. Qed.

Lemma sort_app : forall R,
  forall l1 l2 : list A, sort R l1 -> sort R l2 -> (forall x y, In x l1 -> In y l2 -> R x y) -> sort R (l1 ++ l2).
Proof.
induction l1; simpl in *; intuition. constructor.
+ apply IHl1.
  - now inversion_clear H.
  - assumption.
  - intros. apply H1. now right. assumption.
+ apply HdRel_app.
  - now inversion H.
  - destruct l2; constructor. apply H1; now left.
Qed.

Lemma NoDupA_dec : (forall x y : A, {eqA x y} + {~eqA x y}) -> forall l : list A, {NoDupA eqA l} + {~NoDupA eqA l}.
Proof.
intros eq_dec l. induction l. now left; constructor.
destruct IHl as [Hbad | Hok].
  destruct (InA_dec eq_dec a l).
    right. intro Habs. inversion_clear Habs. contradiction.
    left. now constructor.
  right. intro Habs. inversion_clear Habs. contradiction.
Qed.

Lemma PermutationA_split : forall x l, InA eqA x l -> exists l', PermutationA eqA l (x :: l').
Proof.
intros x l Hin. induction l; inversion_clear Hin.
  exists l. now rewrite H.
  apply IHl in H. destruct H as [l' Hperm]. exists (a :: l'). transitivity (a :: x :: l').
    now rewrite <- Hperm.
    constructor 3.
Qed.

Lemma not_NoDupA : (forall x y, {eqA x y} + {~eqA x y} ) ->
 forall l, ~NoDupA eqA l <-> exists (x : A) l', PermutationA eqA l (x :: x :: l').
Proof.
intros eq_dec l. split; intro Hl.
+ induction l.
    elim Hl. now constructor.
    destruct (InA_dec eq_dec a l) as [Hin | Hnin].
      exists a. apply PermutationA_split in Hin. destruct Hin as [l' Hperm]. exists l'. now rewrite Hperm.
      destruct IHl as [x [l' Hperm]].
        intro Habs. apply Hl. now constructor.
        exists x. exists (a :: l'). rewrite Hperm. transitivity (x :: a :: x :: l').
          now constructor 3.
          apply PermutationA_cons. reflexivity. constructor 3.
+ destruct Hl as [x [l' Hperm]]. rewrite Hperm. intro Habs. inversion_clear Habs. apply H. now left.
Qed.

Lemma app_last : forall (d : A) l1 l2, l2 <> nil -> last (l1 ++ l2) d = last l2 d.
Proof.
intros d l1 l2 Hl2. induction l1; simpl.
  reflexivity.
  assert (l1 ++ l2 <> nil). { intro Habs. apply Hl2. now destruct (app_eq_nil _ _ Habs). }
  destruct (l1 ++ l2). now elim H. assumption.
Qed.

Theorem PermutationA_rev : forall l, PermutationA eqA l (rev l).
Proof. intro. apply Permutation_PermutationA_weak. apply Permutation_rev. Qed.

Lemma last_rev_hd : forall (d : A) l, last (rev l) d = hd d l.
Proof. intros d l. destruct l; simpl. reflexivity. rewrite app_last. reflexivity. discriminate. Qed.

Corollary hd_rev_last : forall (d : A) l, hd d (rev l) = last l d.
Proof. intros d l. rewrite <- (rev_involutive l) at 2. now rewrite last_rev_hd. Qed.

Definition nat_ind2 P P0 P1 PSS :=
  fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
      | 0 => P0
      | S 0 => P1
      | S (S m) => PSS m (F m)
    end.

Lemma odd_middle : forall l (d : A), Nat.Odd (length l) ->
  nth (div2 (length l)) (rev l) d = nth (div2 (length l)) l d.
Proof.
intros l d. generalize (eq_refl (length l)). generalize (length l) at 2 3 4 5. intro n. revert l.
induction n using nat_ind2; intros l Hl [m Hm].
+ omega.
+ destruct l as [| a [| b l]]; try discriminate Hl. reflexivity.
+ simpl. destruct l as [| a [| b l]]; try reflexivity.
  assert (Hnil : b :: l <> nil) by discriminate. revert Hl Hnil. generalize (b :: l). clear l.
  intros l Hlen Hnil. destruct (exists_last Hnil) as [l' [z Heq]]. subst l. simpl.
  rewrite rev_app_distr. simpl in *. apply eq_add_S in Hlen.
  rewrite app_length, plus_comm in Hlen. simpl in Hlen. apply eq_add_S in Hlen. clear Hnil.
  destruct n as [| n].
  - clear -Hm. omega.
  - assert (div2 (S n) < length l'). { rewrite Hlen. apply lt_div2. omega. }
    repeat rewrite app_nth1; trivial. apply IHn.
      assumption.
      destruct m as [| m]. omega. exists m. omega.
      now rewrite rev_length.
Qed.

Lemma length_0 : forall l : list A, length l = 0 -> l = nil.
Proof. intros [|] H; reflexivity || discriminate H. Qed.

Theorem partition_filter : forall (f : A -> bool) l, partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
intros f l. induction l as [| a l]; simpl.
  reflexivity.
  rewrite IHl. now destruct (f a).
Qed.

Corollary partition_fst_In : forall (x : A) f l, In x (fst (partition f l)) <-> In x l /\ f x = true.
Proof. intros. rewrite partition_filter. apply filter_In. Qed.

Corollary partition_snd_In : forall (x : A) f l, In x (snd (partition f l)) <-> In x l /\ f x = false.
Proof. intros. rewrite partition_filter. rewrite <- negb_true_iff. apply filter_In. Qed.

Theorem partition_Permutation : forall f (l : list A),
  Permutation (fst (partition f l) ++ snd (partition f l)) l.
Proof.
intros f l. induction l as [| x l].
+ reflexivity.
+ simpl. destruct (partition f l) as [lg ld] eqn:Hpart. destruct (f x); simpl in *.
  - now rewrite IHl.
  - now rewrite <- Permutation_middle, IHl.
Qed.

Corollary partition_length : forall f (l : list A),
  length (fst (partition f l)) + length (snd (partition f l)) = length l.
Proof. intros. now rewrite <- app_length, partition_Permutation. Qed.

Corollary filter_length : forall f (l : list A),
  length (filter f l) = length l - length (filter (fun x => negb (f x)) l).
Proof. intros. apply plus_minus. rewrite <- (partition_length f), partition_filter. simpl. apply plus_comm. Qed.

Lemma map_cond_Permutation : forall (f : A -> bool) (g₁ g₂ : A -> B) l,
  Permutation (map (fun x => if f x then g₁ x else g₂ x) l)
              (map g₁ (filter f l) ++ map g₂ (filter (fun x => negb (f x)) l)).
Proof.
intros f ? ? l. induction l; simpl.
+ reflexivity.
+ destruct (f a); simpl.
  - apply Permutation_cons; trivial.
  - rewrite IHl. apply Permutation_middle.
Qed.

Lemma map_cst : forall x (l : list B), map (fun y => x) l = alls x (length l).
Proof. intros x l. now induction l; simpl; try f_equal. Qed.

Theorem Forall_dec : forall P (Pdec : forall x : A, {P x} + {~P x}), forall l, {Forall P l} + {~Forall P l}.
Proof.
intros P Pdec l. induction l; simpl.
+ left. constructor.
+ destruct (Pdec a) as [Ha | Ha].
  - destruct IHl as [Hok | Hko].
      left. now constructor.
      right. intros Habs. inversion_clear Habs. contradiction.
  - right. intros Habs. inversion_clear Habs. contradiction.
Qed.

Section CountA.

Variable eq_dec : forall x y : A, {eqA x y} + {~eqA x y}.

Fixpoint countA_occ (x : A) l :=
  match l with
    | Datatypes.nil => 0
    | y :: l' => let n := countA_occ x l' in if eq_dec y x then S n else n
  end.

Lemma countA_occ_app : forall l1 l2 (x : A),
  countA_occ x (l1 ++ l2) = (countA_occ x l1 + countA_occ x l2)%nat.
Proof.
intros l1. induction l1; intros l2 x; simpl.
- reflexivity.
- destruct (eq_dec a x); now rewrite IHl1.
Qed.

Instance count_occ_proper : Proper (eq ==> PermutationA eqA ==> eq) (countA_occ).
Proof.
intros a b Hab l. induction l as [| x l]; intros [| x' l'] Hl; subst.
+ reflexivity.
+ apply PermutationA_nil in Hl. discriminate Hl.
+ symmetry in Hl. apply PermutationA_nil in Hl. discriminate Hl.
+ assert (Hperm := @PermutationA_InA_inside x _ _ Hl). destruct Hperm as [l1 [y [l2 [Hxy Heql]]]]; try now left.
  rewrite Heql in *. rewrite Hxy, <- (PermutationA_middle _) in Hl. apply PermutationA_cons_inv in Hl.
  apply IHl in Hl. simpl. rewrite Hl. repeat rewrite countA_occ_app. simpl.
  destruct (eq_dec x b) as [Hx | Hx], (eq_dec y b) as [Hy | Hy]; try omega.
  - elim Hy. rewrite <- Hxy. assumption.
  - elim Hx. rewrite Hxy. assumption.
Qed.
(*
Lemma countA_occ_remove_in eq_dec : forall (x : A) l, count_occ eq_dec (remove eq_dec x l) x = 0%nat.
Proof.
intros x l. induction l. reflexivity. simpl.
destruct (eq_dec x a) as [| Hneq]. assumption. simpl.
destruct (eq_dec a x). now elim Hneq. assumption. 
Qed.

Lemma count_occ_remove_out eq_dec :
  forall (x y : A) l, x <> y -> count_occ eq_dec (remove eq_dec x l) y = count_occ eq_dec l y.
Proof.
intros x y l Hxy. induction l. reflexivity. simpl.
destruct (eq_dec x a); simpl; destruct (eq_dec a y).
  subst. now elim Hxy.
  assumption.
  now f_equal.
  assumption.
Qed.
Global Arguments count_occ_remove_out [eq_dec] x [y] [l] _.
*)
Lemma countA_occ_alls_in : forall x n, countA_occ x (alls x n) = n.
Proof.
intros x n. induction n; simpl.
  reflexivity.
  destruct (eq_dec x x) as [| Hneq]. now rewrite IHn. now elim Hneq. 
Qed.

Lemma countA_occ_alls_out : forall x y n, ~eqA x y -> countA_occ y (alls x n) = 0%nat.
Proof. intros x y n Hxy. induction n; simpl; trivial; now destruct (eq_dec x y). Qed.

Lemma countA_occ_pos : forall x l, countA_occ x l > 0 <-> InA eqA x l.
Proof.
intros x l. induction l as [| a l]; simpl.
+ split; intro Habs.
  - omega.
  - rewrite InA_nil in Habs. elim Habs.
+ destruct (eq_dec a x) as [Heq | Heq].
  - split; intro; omega || now left.
  - rewrite IHl. split; intro Hin; try now right; [].
    inversion_clear Hin; trivial. now elim Heq.
Qed.

(*
Theorem remove_count_occ_restore eq_dec : forall x l,
  Permutation l (alls x (count_occ eq_dec l x) ++ (remove eq_dec x l)).
Proof.
intros x l. induction l.
+ reflexivity.
+ simpl. destruct (eq_dec a x) as [| Hneq]. subst.
  - simpl. apply Permutation_cons. destruct (eq_dec x x) as [| Hneq]. assumption. now elim Hneq.
  - destruct (eq_dec x a). subst. now elim Hneq. etransitivity.
      now apply Permutation_cons, IHl.
      now apply Permutation_cons_app.
Qed.
*)
Lemma countA_occ_length_le : forall l (x : A), countA_occ x l <= length l.
Proof.
intros l x. induction l; simpl.
  reflexivity.
  destruct (eq_dec a x); omega.
Qed.
(*
Lemma remove_count_occ_length eq_dec : forall (x : A) l,
  length (remove eq_dec x l) + count_occ eq_dec l x = length l.
Proof.
intros x l. induction l; simpl.
+ reflexivity.
+ destruct (eq_dec x a); simpl.
  - subst. destruct (eq_dec a a) as [_ | Habs]. rewrite <- plus_n_Sm, IHl. reflexivity. now elim Habs.
  - destruct (eq_dec a x) as [Heq | Habs].
      symmetry in Heq. contradiction.
      now rewrite IHl.
Qed.

Corollary count_occ_length eq_dec : forall (x : A) l, count_occ eq_dec l x = length l - length (remove eq_dec x l).
Proof. intros. apply plus_minus. symmetry. apply remove_count_occ_length. Qed.

Corollary remove_length eq_dec : forall (x : A) l, length (remove eq_dec x l) = length l - count_occ eq_dec l x.
Proof. intros. apply plus_minus. symmetry. rewrite plus_comm. apply remove_count_occ_length. Qed.
*)

Lemma countA_occ_partition : forall f, Proper (eqA ==> eq) f ->
  forall l x, countA_occ x l = countA_occ x (fst (partition f l)) + countA_occ x (snd (partition f l)).
Proof.
intros f Hf l. induction l as [| a l].
* intro. reflexivity.
* intro x. destruct (f a) eqn:Hfa.
  + apply (partition_cons1 f a l (surjective_pairing (partition f l))) in Hfa. rewrite Hfa. simpl.
    destruct (eq_dec a x) as [Heq | Heq].
    - rewrite IHl. omega.
    - apply IHl.
  + apply (partition_cons2 f a l (surjective_pairing (partition f l))) in Hfa. rewrite Hfa. simpl.
    destruct (eq_dec a x) as [Heq | Heq].
    - rewrite IHl. omega.
    - apply IHl.
Qed.

End CountA.

Theorem Exists_dec : forall P, (forall x : A, {P x} + {~P x}) -> forall l, {Exists P l} + {~Exists P l}.
Proof.
intros P Pdec l. induction l as [| x l].
* right. intro Habs. inversion Habs.
* destruct IHl.
  + left. now constructor 2.
  + destruct (Pdec x).
    - left. now constructor.
    - right. intro Habs. inversion_clear Habs; contradiction.
Qed.

Global Instance forallb_compat : Proper ((eq ==> eq) ==> eq ==> eq) (@forallb A).
Proof.
intros f f' Hf l l' Hl. subst l'. induction l.
- reflexivity.
- simpl. destruct (f a) eqn:Hfa; rewrite <- (Hf a), <- IHl, Hfa; reflexivity.
Qed.

Global Instance existsb_compat : Proper ((eq ==> eq) ==> eq ==> eq) (@existsb A).
Proof.
intros f f' Hf l l' Hl. subst l'. induction l.
- reflexivity.
- simpl. destruct (f a) eqn:Hfa; rewrite <- (Hf a), <- IHl, Hfa; reflexivity.
Qed.

Theorem existsb_forallb : forall (f : A -> bool) l,
  negb (forallb f l) = existsb (fun x => negb (f x)) l.
Proof.
intros f l. induction l as [| x l].
+ reflexivity.
+ simpl. destruct (f x) eqn:Hfx; simpl.
  - simpl. apply IHl.
  - reflexivity.
Qed.

Lemma forallb_existsb : forall (f : A -> bool) l,
  negb (existsb f l) = forallb (fun x : A => negb (f x)) l.
Proof.
intros. rewrite <- negb_involutive, existsb_forallb. f_equal. f_equiv.
repeat intro. subst. now rewrite negb_involutive.
Qed.

Global Instance inclA_compat : Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (inclA eqA).
Proof. intros ? ? Hl1 ? ? Hl2. unfold inclA. setoid_rewrite Hl1. setoid_rewrite Hl2. reflexivity. Qed.

Lemma inclA_cons_inv : forall x l1 l2, ~InA eqA x l1 ->
  inclA eqA (x :: l1) (x :: l2) -> inclA eqA l1 l2.
Proof.
intros x l1 l2 Hx Hincl y Hin1.
assert (Hin2 : InA eqA y (x :: l2)). { apply Hincl. now right. }
inversion_clear Hin2; trivial. rewrite <- H in Hx. contradiction.
Qed.

Lemma NoDupA_inclA_length : forall l1 l2 : list A, NoDupA eqA l1 -> inclA eqA l1 l2 -> length l1 <= length l2.
Proof.
intro l1. induction l1 as [| a l1]; intros l2 Hnodup Hincl.
+ simpl. omega.
+ assert (Hin : InA eqA a l2). { apply Hincl. now left. }
  apply PermutationA_split in Hin. destruct Hin as [l2' Heql2]. 
  rewrite Heql2 in *. inversion_clear Hnodup.
  apply inclA_cons_inv in Hincl; trivial. simpl. apply le_n_S. now apply IHl1.
Qed.

Lemma NoDupA_inclA_length_PermutationA : forall l1 l2,
  NoDupA eqA l1 -> NoDupA eqA l2 -> inclA eqA l1 l2 -> length l1 = length l2 -> PermutationA eqA l1 l2.
Proof.
intro l1. induction l1 as [| x l1]; intros l2 Hnodup1 Hnodup2 Hincl Hlen.
+ destruct l2. reflexivity. discriminate Hlen.
+ assert (Hin : InA eqA x l2). { apply Hincl. now left. }
  apply PermutationA_split in Hin. destruct Hin as [l2' Heql2]. 
  rewrite Heql2 in *. constructor; try reflexivity.
  inversion_clear Hnodup1. inversion_clear Hnodup2.
  apply inclA_cons_inv in Hincl; trivial. apply IHl1; auto.
Qed.

End List_results.

Corollary NoDup_dec {A} : (forall x y : A, {x = y} + {~x = y}) -> forall l : list A, {NoDup l} + {~NoDup l}.
Proof. intros eq_dec l. destruct (NoDupA_dec _ eq_dec l); rewrite NoDupA_Leibniz in *; auto. Qed.


(* ******************************* *)
(** *  The same for real numbers. **)
(* ******************************* *)


Lemma Rdec : forall x y : R, {x = y} + {x <> y}.
Proof.
intros x y. destruct (Rle_dec x y). destruct (Rle_dec y x).
  left. now apply Rle_antisym.
  right; intro; subst. contradiction.
  right; intro; subst. pose (Rle_refl y). contradiction.
Qed.

Definition Rdec_bool x y := match Rdec x y with left _ => true | right _ => false end.

Global Instance Rdec_bool_compat : Proper (eq ==> eq ==> eq) Rdec_bool.
Proof. repeat intro. subst. reflexivity. Qed.

Lemma Rdec_bool_true_iff : forall x y, Rdec_bool x y = true <-> x = y.
Proof. intros. unfold Rdec_bool. destruct (Rdec x y); now split. Qed.

Lemma Rdec_bool_false_iff : forall x y, Rdec_bool x y = false <-> x <> y.
Proof. intros. unfold Rdec_bool. destruct (Rdec x y); now split. Qed.

Lemma if_Rdec : forall A x y (l r : A), (if Rdec x y then l else r) = if Rdec_bool x y then l else r.
Proof. intros. unfold Rdec_bool. now destruct Rdec. Qed.

Definition Rle_bool x y :=
  match Rle_dec x y with
    | left _ => true
    | right _ => false
  end.

Lemma Rle_bool_spec : forall x y, Rle_bool x y = true <-> Rle x y.
Proof. intros x y. unfold Rle_bool. destruct (Rle_dec x y); intuition discriminate. Qed.

(*Definition count_occ_properR := count_occ_proper Rdec.*)
Definition remove_Perm_properR := remove_Perm_proper Rdec.
Existing Instance Permutation_length_compat.
Existing Instance Permutation_NoDup_compat.
(*Existing Instance count_occ_properR.*)
Existing Instance remove_Perm_properR.
Existing Instance In_perm_compat.
Existing Instance InA_impl_compat.
Existing Instance InA_compat.
Existing Instance InA_perm_compat.
Existing Instance PermutationA_length.
Existing Instance fold_left_start.
Existing Instance fold_left_symmetry_PermutationA.
Existing Instance PermutationA_map.


Lemma le_neq_lt : forall m n : nat, n <= m -> n <> m -> n < m.
Proof. intros n m Hle Hneq. now destruct (le_lt_or_eq _ _ Hle). Qed.

Local Open Scope R_scope.

Lemma Rle_neq_lt : forall x y : R, x <= y -> x <> y -> x < y.
Proof. intros ? ? Hle ?. now destruct (Rle_lt_or_eq_dec _ _ Hle). Qed.

Lemma Rdiv_reg : forall x y z, z <> 0 -> x / z = y / z -> x = y.
Proof.
intros x y z Hneq Heq. setoid_rewrite <- Rmult_1_r. rewrite <- Rinv_r with z.
setoid_rewrite <- Rmult_comm at 2 4. do 2 rewrite <- Rmult_assoc.
unfold Rdiv in Heq. now rewrite Heq. assumption.
Qed.

Lemma local_invert : forall k t x y, k <> 0 -> (k * (x - t) = k * (y - t) <-> x = y).
Proof.
intros. split; intro.
  apply Rplus_eq_reg_l with (- t). setoid_rewrite Rplus_comm. now apply Rmult_eq_reg_l with k.
  now subst.
Qed.

Unset Implicit Arguments.
Lemma succ_neq : forall x, x <> x+1.
Proof.
intros x Habs. assert (Heq : x = x + 0) by ring. rewrite Heq in Habs at 1. clear Heq.
apply Rplus_eq_reg_l in Habs. symmetry in Habs. revert Habs. exact R1_neq_R0.
Qed.
