(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)


Require Import Arith.Div2.
Require Import Omega.
Require Import Reals.
Require Import List SetoidList.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Equalities.
Require Import Sorting.Permutation.
Require Import Psatz.
Require Import SetoidList.
Require Export SetoidPermutation.
Require Import Bool.


Set Implicit Arguments.


Ltac autoclass := eauto with typeclass_instances.
Ltac inv H := inversion H; subst; clear H.

(** A tactic simplifying coinduction proofs. *)
Global Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

(** Destruct matches from innermost to outermost, with or without keeping the associated equality. *)
Ltac destr_match_eq name A :=
  match A with | context[match ?x with | _ => _ end] =>
    destr_match_eq name x (* recursive call *)
    || let H := fresh name in destruct x eqn:H (* if innermost match, destruct it *)
  end.

Ltac destruct_match_eq name := match goal with | |- ?A => destr_match_eq name A end.

Ltac destr_match A :=
  match A with | context[match ?x with | _ => _ end] =>
    destr_match x (* recursive call *)
    || destruct x (* if innermost match, destruct it *)
  end.

Ltac destruct_match := match goal with | |- ?A => destr_match A end.

(** Tactics to revert hypotheses based on their head symbol *)
Ltac get_head_symbol term :=
  match term with
    | ?f _ => get_head_symbol f
    | _ => term
  end.

(* Revert one hypothesis whose head symbol is [sym]. *)
Ltac revert_one sym :=
  match goal with
    | H : ?A |- _ => let f := get_head_symbol A in let g := get_head_symbol sym in unify f g; revert H
    | |- _ => fail "Symbol" sym "not found"
  end.

(* Revert all hypotheses with the same head symbol as the goal. *)
Ltac revert_all :=
  match goal with
    | |- ?B => repeat revert_one B
  end.


Lemma nat_compare_Eq_comm : forall n m, nat_compare n m = Eq <-> nat_compare m n = Eq.
Proof. intros n m. do 2 rewrite nat_compare_eq_iff. now split. Qed.

Lemma nat_compare_Lt_Gt : forall n m, nat_compare n m = Lt <-> nat_compare m n = Gt.
Proof. intros n m. rewrite <- nat_compare_lt, <- nat_compare_gt. now split. Qed.

Definition nat_ind2 P P0 P1 PSS :=
  fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
      | 0 => P0
      | S 0 => P1
      | S (S m) => PSS m (F m)
    end.

Lemma div2_le_compat : Proper (le ==> le) div2.
Proof.
intro n. induction n using ind_0_1_SS; intros m Heq; auto with arith.
destruct m as [| [| m]]; try now inversion Heq.
simpl. do 2 apply le_S_n in Heq. apply IHn in Heq. omega.
Qed.

Lemma even_div2 : forall n, Nat.Even n -> Nat.div2 n + Nat.div2 n = n.
Proof.
intros n Hn. replace (Nat.div2 n + Nat.div2 n) with (2 * Nat.div2 n) by lia.
rewrite <- Nat.double_twice. symmetry. apply even_double. now rewrite Even.even_equiv.
Qed.

Definition injective {A B : Type} eqA eqB (f : A -> B) := (forall x y, eqB (f x) (f y) -> eqA x y).

Definition monotonic {A B : Type} (RA : relation A) (RB : relation B) (f : A -> B) :=
  Proper (RA ==> RB) f \/ Proper (RA --> RB) f.

Definition full_relation {A : Type} := fun _ _ : A => True.

Global Hint Extern 0 (full_relation _ _) => exact I.

Global Instance relation_equivalence_subrelation {A} :
  forall R R' : relation A, relation_equivalence R R' -> subrelation R R'.
Proof. intros R R' Heq x y Hxy. now apply Heq. Qed.

Global Hint Extern 3 (relation_equivalence _ _) => symmetry.


(******************************)
(** *  Some results on Lists  *)
(******************************)

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

Lemma InA_Leibniz : forall (x : A) l, InA Logic.eq x l <-> In x l.
Proof.
intros x l. split; intro Hl; induction l; inversion_clear Hl; (subst; now left) || (right; now apply IHl).
Qed.

Lemma nil_or_In_dec : forall l : list A, {l = nil} + {exists x, In x l}.
Proof. intros [| x l]; auto. right. exists x. now left. Qed.

Lemma not_nil_In : forall l : list A, l <> nil -> exists x, In x l.
Proof.
intros [| x l] Hl.
- now elim Hl.
- exists x. now left.
Qed.

Lemma not_nil_last : forall l, l <> nil -> exists (a : A) l', l = l' ++ a :: nil.
Proof.
intros l Hl. induction l.
+ now elim Hl.
+ destruct l.
  - exists a, nil. reflexivity.
  - destruct (IHl ltac:(discriminate)) as [b [l'' Hl'']].
    exists b, (a :: l''). now rewrite Hl''.
Qed.

Lemma length_0 : forall l : list A, length l = 0 -> l = nil.
Proof. intros [|] H; reflexivity || discriminate H. Qed.

Lemma In_nth : forall d x (l : list A), In x l -> exists n, (n < length l)%nat /\ nth n l d = x.
Proof.
intros x d l Hin. induction l.
+ inversion Hin.
+ destruct Hin.
  - subst. exists 0%nat. split. simpl. now auto with arith. reflexivity.
  - destruct (IHl H) as [n [Hn Hl]]. apply lt_n_S in Hn. exists (S n). now split.
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

(** If the list argument is not empty, [hd] and [last] return an element of the list,
    independent from the default value provided. *)
Lemma hd_indep : forall l (d d' : A), l <> nil -> hd d l = hd d' l.
Proof.
intros [| x l] d d' Hl.
- now elim Hl.
- reflexivity.
Qed.

Lemma last_indep : forall l (d d' : A), l <> nil -> last l d = last l d'.
Proof.
induction l as [| x l]; intros d d' Hl.
- now elim Hl.
- destruct l; trivial. apply IHl. discriminate.
Qed.

Lemma hd_In : forall (d : A) l, l <> nil -> In (hd d l) l.
Proof.
intros d [| x l] Hl.
- now elim Hl.
- now left.
Qed.

Lemma last_In : forall l (d : A), l <> List.nil -> List.In (List.last l d) l.
Proof.
induction l as [| x l]; intros d Hl.
- now elim Hl.
- destruct l; try now left. right. apply IHl. discriminate.
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

Lemma app_last : forall (d : A) l1 l2, l2 <> nil -> last (l1 ++ l2) d = last l2 d.
Proof.
intros d l1 l2 Hl2. induction l1; simpl.
  reflexivity.
  assert (l1 ++ l2 <> nil). { intro Habs. apply Hl2. now destruct (app_eq_nil _ _ Habs). }
  destruct (l1 ++ l2). now elim H. assumption.
Qed.

Lemma rev_nil : forall l : list A, rev l = nil <-> l = nil.
Proof.
intros [| x l].
+ reflexivity.
+ simpl. split; intro Habs.
  - assert (Hlen : length (rev l ++ x :: nil) = length (@nil A)) by now rewrite Habs.
    rewrite app_length in Hlen. simpl in Hlen. omega.
  - discriminate.
Qed.

Lemma last_rev_hd : forall (d : A) l, last (rev l) d = hd d l.
Proof. intros d l. destruct l; simpl. reflexivity. rewrite app_last. reflexivity. discriminate. Qed.

Corollary hd_rev_last : forall (d : A) l, hd d (rev l) = last l d.
Proof. intros d l. rewrite <- (rev_involutive l) at 2. now rewrite last_rev_hd. Qed.

Lemma eqlistA_Leibniz : forall l1 l2 : list A, eqlistA eq l1 l2 <-> l1 = l2.
Proof.
intro l1. induction l1 as [| e1 l1]; intro l2.
+ now destruct l2.
+ destruct l2 as [| e2 l2]; try now intuition.
  split; intro Heq.
  - inversion_clear Heq as [| ? ? ? ? He Hl]. rewrite IHl1 in Hl. now f_equal.
  - rewrite Heq. reflexivity.
Qed.

Lemma eqlistA_Leibniz_equiv : relation_equivalence (@eqlistA A eq) eq.
Proof. repeat intro. apply eqlistA_Leibniz. Qed.

Global Instance InA_impl_compat : Proper (subrelation ==> eq ==> eq ==> impl) (@InA A).
Proof.
intros R1 R2 HR x y Hxy l l2 Hl Hin. subst y l2. induction l.
  now inversion Hin.
  inversion_clear Hin.
    constructor. now apply HR.
    constructor 2. now apply IHl.
Qed.

Global Instance InA_compat : Proper (eqA ==> equivlistA eqA ==> iff) (InA eqA).
Proof.
intros x y Hxy l1 l2 Hl. split; intro H; eapply InA_eqA; try eassumption.
  now rewrite <- Hl.
  symmetry. eassumption.
  now rewrite Hl.
Qed.

(** ***  Results about [map]  **)

Global Instance map_extensionalityA_compat : Proper ((eqA ==> eqB) ==> eqlistA eqA ==> eqlistA eqB) (@map A B).
Proof.
intros f g Hfg l. induction l as [| e l]; intros l' Hl.
- destruct l'; reflexivity || inversion Hl.
- destruct l' as [| e' l']; try now inversion Hl.
  inversion_clear Hl as [| ? ? ? ? He Hl'].
  simpl. constructor; auto.
Qed.

Global Instance map_extensionality_compat : Proper ((eq ==> eq) ==> eq ==> eq) (@map A B).
Proof.
intros f g Hfg l. induction l as [| e l]; intros l' Hl.
- destruct l'; reflexivity || inversion Hl.
- subst. simpl. f_equal; auto.
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

Theorem map_injective_NoDupA : forall f, Proper (eqA ==> eqB) f -> injective eqA eqB f ->
  forall l, NoDupA eqA l -> NoDupA eqB (map f l).
Proof.
intros f Hf Hinj l Hnodup. induction Hnodup.
+ constructor.
+ simpl. constructor.
  - rewrite InA_map_iff; trivial. intros [y [Heq Hin]].
    apply Hinj in Heq. rewrite Heq in Hin. contradiction.
  - assumption.
Qed.

Lemma filter_map : forall f (g : A -> B) l, filter f (map g l) = map g (filter (fun x => f (g x)) l).
Proof.
intros f g l. induction l as [| e l]; simpl in *.
+ reflexivity.
+ destruct (f (g e)); simpl.
  - f_equal. apply IHl.
  - apply IHl.
Qed.

Global Instance PermutationA_map : forall f, Proper (eqA ==> eqB) f ->
  Proper (PermutationA eqA ==> PermutationA eqB) (map f).
Proof.
intros f Hf l l' perm. induction perm; simpl.
  reflexivity.
  constructor 2. now rewrite H. now apply IHperm.
  now constructor 3.
  now transitivity (map f l₂).
Qed.

(** ***  Function [alls x n] creating a list of size [n] containing only [x]  **)

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
+ induction l. reflexivity. simpl. f_equal.
  - apply H. now left.
  - apply IHl. intros y Hy. apply H. now right.
+ rewrite H. intro. apply alls_In.
Qed.

Lemma alls_caracA : forall x l, (forall y, InA eqA y l -> eqA y x) <-> eqlistA eqA l (alls x (length l)).
Proof.
intros x l. split; intro H.
+ induction l. reflexivity. simpl. constructor.
  - apply H. now left.
  - apply IHl. intros y Hy. apply H. now right.
+ intro. rewrite H, InA_alt. intros [y' [Heq Hin]]. apply alls_In in Hin. now subst.
Qed.

Lemma Permutation_alls : forall (x : A) n l,
  Permutation l (alls x n) <-> l = alls x n.
Proof.
intros x n l. split.
* revert l. induction n; intros l Hl.
  + simpl in *. apply Permutation_nil. now symmetry.
  + destruct l.
    - apply Permutation_nil in Hl. discriminate Hl.
    - assert (a = x). { apply alls_In with (S n). simpl alls. rewrite <- Hl. now left. }
      subst. simpl in *. f_equal. apply IHn. apply (Permutation_cons_inv Hl).
* intro Hl. now rewrite Hl.
Qed.

Lemma map_alls : forall f pt n, map f (alls pt n) = alls (f pt) n.
Proof. intros f pt n. induction n. reflexivity. simpl. now rewrite IHn. Qed.

Lemma map_cst : forall x l, map (fun _ : B => x) l = alls x (length l).
Proof. intros x l. now induction l; simpl; try f_equal. Qed.

(** ***  Boolean properties over a list  **)

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

(** ***  Results about [PermutationA]  **)

Global Instance InA_perm_compat : Proper (eqA ==> PermutationA eqA ==> iff) (InA eqA).
Proof. intros x y Hxy l1 l2 Hl. now apply InA_compat; try apply PermutationA_equivlistA. Qed.

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

Lemma PermutationA_Leibniz_equiv : relation_equivalence (@PermutationA A eq) (@Permutation A).
Proof. repeat intro. apply PermutationA_Leibniz. Qed.

Lemma PermutationA_subrelation_compat : Proper (subrelation ==> eq ==> eq ==> impl) (@PermutationA A).
Proof.
intros eqA1 eqA2 Hrel l1 l2 H12 l3 l4 H34 Hperm. subst. induction Hperm.
- constructor.
- constructor. now apply Hrel. assumption.
- constructor 3.
- now constructor 4 with l₂.
Qed.

Global Instance eqlistA_PermutationA_subrelation : subrelation (eqlistA eqA) (PermutationA eqA).
Proof. intros ? ? Heq. induction Heq; constructor; auto. Qed.

Global Instance PermutationA_equivlistA_subrelation : subrelation (PermutationA eqA) (equivlistA eqA).
Proof. intros l1 l2 Heq x. now rewrite Heq. Qed.

Global Instance PermutationA_eq_compat : Proper ((eq ==> eq ==> iff) ==> eq ==> eq ==> iff) (@PermutationA A).
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

Global Instance Permutation_length_compat : Proper (@Permutation A ==> eq) (@length A).
Proof. now intros ? ? ?; apply Permutation_length. Qed.

(* Already exists as Permutation.Permutation_in' *)
Global Instance In_perm_compat : Proper (eq ==> @Permutation A ==> iff) (@In A).
Proof. intros x y ? l l' Hl. subst. split; apply Permutation_in; assumption || now symmetry. Qed.

Global Instance In_permA_compat : Proper (eq ==> @PermutationA A eq ==> iff) (@In A).
Proof. repeat intro. rewrite PermutationA_Leibniz in *. now apply In_perm_compat. Qed.

Lemma Forall_Perm_trans : forall (l1 l2 : list A) (P Q : A -> Prop),
  (eq ==> iff)%signature P Q -> Permutation l1 l2 -> List.Forall P l1 -> List.Forall Q l2.
Proof.
intros l1 l2 P Q HPQ Hperm Hfor. 
rewrite List.Forall_forall in *. intros. rewrite <- (HPQ _ _ eq_refl). 
apply Hfor. revert H. apply Permutation_in. now symmetry.
Qed.

Global Instance Forall_Permutation_compat : Proper ((eq ==> iff) ==> @Permutation A ==> iff) (@List.Forall A).
Proof. repeat intro. split; apply Forall_Perm_trans; easy || (repeat intro; symmetry; auto). Qed.

Corollary Permutation_cons_inside : forall (x : A) l l',
  Permutation (x :: l) l' -> exists l1 l2, Permutation l (l1 ++ l2) /\ l' = l1 ++ x :: l2.
Proof.
intros x l l' Hperm. destruct (Permutation_in_inside x Hperm) as [l1 [l2 Heql]]. now left.
exists l1. exists l2. split.
- apply Permutation_cons_inv with x. transitivity l'. assumption. subst. symmetry. apply Permutation_middle.
- assumption.
Qed.

Lemma PermutationA_nil : forall l, PermutationA eqA nil l -> l = nil.
Proof.
intros l Hl. destruct l.
  reflexivity.
  exfalso. rewrite <- InA_nil. rewrite (PermutationA_equivlistA HeqA).
    now left.
    eassumption.
Qed.

Lemma PermutationA_InA_inside : forall (x : A) l l',
  PermutationA eqA l l' -> InA eqA x l -> exists l1 y l2, eqA x y /\ l' = l1 ++ y :: l2.
Proof. intros x l l' Hperm Hin. rewrite Hperm in Hin. apply (InA_split Hin). Qed.

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
      rewrite <- PermutationA_middle in Hp; autoclass. now rewrite Hp, H.
  - break_list l1' d l1'' H0.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp; autoclass. now rewrite <- H, Hp.
  - break_list l3' e l3'' H1; break_list l1' g l1'' H4.
      now constructor 2.
      rewrite <- PermutationA_middle in Hp; autoclass. rewrite permA_swap, <- H. now constructor 2.
      rewrite permA_swap, PermutationA_middle, H; autoclass. now constructor 2.
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

Global Instance PermutationA_length : Proper (PermutationA eqA ==> Logic.eq) (@length A).
Proof. clear. intros l1 l2 perm. induction perm; simpl; omega. Qed.

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
    destruct (IHperm1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)) as [[H11 H12] | [H11 H12]],
             (IHperm2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)) as [[H21 H22] | [H21 H22]];
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
    specialize (IHperm1 _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
    specialize (IHperm2 _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
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

Lemma PermutationA_split : forall x l, InA eqA x l -> exists l', PermutationA eqA l (x :: l').
Proof.
intros x l Hin. induction l; inversion_clear Hin.
  exists l. now rewrite H.
  apply IHl in H. destruct H as [l' Hperm]. exists (a :: l'). transitivity (a :: x :: l').
    now rewrite <- Hperm.
    constructor 3.
Qed.

End List_results.

Global Hint Immediate eqlistA_Leibniz_equiv PermutationA_Leibniz_equiv.


(** ***  Results about [NoDupA]  **)

Section NoDupA_results.
Context (A B : Type).
Context (eqA eqA' : relation A) (eqB : relation B).
Context (HeqA : Equivalence eqA) (HeqB : Equivalence eqB).

Lemma NoDupA_Leibniz : forall l : list A, NoDupA Logic.eq l <-> NoDup l.
Proof.
intro l. split; intro Hl; induction l; inversion_clear Hl; constructor;
(now rewrite <- InA_Leibniz in *) || now apply IHl.
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

Global Instance PermutationA_NoDupA_compat : Proper (PermutationA eqA ==> iff) (NoDupA eqA).
Proof. now repeat intro; split; apply PermutationA_NoDupA. Qed.

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

Lemma NoDupA_app_iff : forall l1 l2, NoDupA eqA (l1 ++ l2) <->
  NoDupA eqA l1 /\ NoDupA eqA l2 /\ (forall x, InA eqA x l1 -> InA eqA x l2 -> False).
Proof.
intros. split; intro Hnodup.
* induction l1 as [| x l1]; simpl in *.
  + repeat split; try setoid_rewrite InA_nil; auto.
  + inversion_clear Hnodup as [| ? ? Hin Hdup].
    apply IHl1 in Hdup. destruct Hdup as [Hl1 [Hl2 Hboth]]. clear IHl1. rewrite InA_app_iff in Hin.
    repeat split; auto.
    intros y Hinl1 Hinl2. inversion_clear Hinl1 as [? ? Heq | ? ? Hin' H].
    - rewrite Heq in Hinl2. auto.
    - now apply (Hboth y).
* decompose [and] Hnodup. now apply NoDupA_app.
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

Lemma not_NoDupA : (forall x y, {eqA x y} + {~eqA x y} ) ->
 forall l, ~NoDupA eqA l <-> exists (x : A) l', PermutationA eqA l (x :: x :: l').
Proof.
intros eq_dec l. split; intro Hl.
* induction l.
  + elim Hl. now constructor.
  + destruct (InA_dec eq_dec a l) as [Hin | Hnin].
    - exists a. apply (PermutationA_split _) in Hin. destruct Hin as [l' Hperm]. exists l'. now rewrite Hperm.
    - destruct IHl as [x [l' Hperm]].
      ++ intro Habs. apply Hl. now constructor.
      ++ exists x. exists (a :: l'). rewrite Hperm. transitivity (x :: a :: x :: l').
         -- now constructor.
         -- apply PermutationA_cons. reflexivity. now constructor.
* destruct Hl as [x [l' Hperm]]. rewrite Hperm. intro Habs. inversion_clear Habs. apply H. now left.
Qed.

End NoDupA_results.

Lemma Permutation_NoDup {A : Type} : forall (l l' : list A), Permutation l l' -> NoDup l -> NoDup l'.
Proof.
intros ? ?. rewrite <- PermutationA_Leibniz. do 2 rewrite <- NoDupA_Leibniz.
apply PermutationA_NoDupA; autoclass.
Qed.

(* Already exists as [Permutation.Permutation_NoDup'] *)
Global Instance Permutation_NoDup_compat {A : Type} : Proper (@Permutation A ==> iff) (@NoDup A).
Proof. repeat intro. now split; apply Permutation_NoDup. Qed.

(** ***  Results about [remove]  **)

Section Remove_results.
Context (A : Type).
Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

Lemma remove_in_out : forall (x y : A) l, y <> x -> (In x (remove eq_dec y l) <-> In x l).
Proof.
intros x y l Hxy. induction l. reflexivity.
simpl. destruct (eq_dec y a).
- subst. rewrite IHl. split; intro H. now right. now destruct H.
- simpl. now rewrite IHl.
Qed.
Global Arguments remove_in_out [x] y l _.

Theorem remove_in_iff : forall (x y : A) l, In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
intros x y l. induction l as [| a l].
+ split; intro Habs. inversion Habs. destruct Habs as [Habs _]. inversion Habs.
+ simpl. destruct (eq_dec y a). 
  - subst a. rewrite IHl. intuition. now elim H3.
  - simpl. rewrite IHl. split; intro Hin.
      now destruct Hin; try subst a; intuition.
      intuition.
Qed.

Lemma remove_alls : forall x n, remove eq_dec x (alls x n) = nil.
Proof.
intros x n. induction n.
  reflexivity.
  simpl. destruct (eq_dec x x) as [_ | Hneq]; assumption || now elim Hneq.
Qed.

Lemma remove_alls' : forall x y n, x <> y -> remove eq_dec x (alls y n) = alls y n.
Proof.
intros x y n Hxy. induction n.
  reflexivity.
  simpl. destruct (eq_dec x y) as [Heq | _]; contradiction || now rewrite IHn.
Qed.

Lemma remove_nil : forall x l, remove eq_dec x l = nil <-> l = alls x (length l).
Proof.
intros x l. split; intro Hl.
+ induction l; simpl in *.
  - reflexivity.
  - destruct (eq_dec x a).
      subst. now rewrite <- IHl.
      discriminate Hl.
+ rewrite Hl. apply remove_alls.
Qed.

Global Instance remove_Perm_proper : Proper (eq ==> @Permutation A ==> @Permutation A) (@remove A eq_dec).
Proof.
intros x y ? l1 l2 Hl. subst. induction Hl.
- apply Permutation_refl.
- simpl. destruct (eq_dec y x). assumption. now constructor.
- simpl. destruct (eq_dec y y0), (eq_dec y x); apply Permutation_refl || now constructor.
- now constructor 4 with (remove eq_dec y l').
Qed.

Lemma remove_app : forall (x : A) l1 l2,
  remove eq_dec x (l1 ++ l2) = remove eq_dec x l1 ++ remove eq_dec x l2.
Proof.
intros x l1 l2. induction l1. reflexivity. simpl.
destruct (eq_dec x a). apply IHl1. simpl. f_equal. apply IHl1.
Qed.

Corollary remove_inside_in :
  forall (x : A) l1 l2, remove eq_dec x (l1 ++ x :: l2) = remove eq_dec x l1 ++ remove eq_dec x l2.
Proof. intros x ? ?. rewrite remove_app. simpl. destruct (eq_dec x x) as [| Hneq]. reflexivity. now elim Hneq. Qed.

Corollary remove_inside_out : forall (x y : A) l1 l2,
  x <> y -> remove eq_dec x (l1 ++ y :: l2) = remove eq_dec x l1 ++ y :: remove eq_dec x l2.
Proof. intros x y ? ? ?. rewrite remove_app. simpl. destruct (eq_dec x y). contradiction. reflexivity. Qed.

Lemma remove_idempotent : forall (x : A) l, remove eq_dec x (remove eq_dec x l) = remove eq_dec x l.
Proof.
intros x l. induction l.
  reflexivity.
  simpl. destruct (eq_dec x a) eqn:Hx.
    assumption.
    simpl. rewrite Hx. now rewrite IHl.
Qed.

Lemma remove_comm : forall (x y : A) l,
  remove eq_dec x (remove eq_dec y l) = remove eq_dec y (remove eq_dec x l).
Proof.
intros x y l. induction l.
  reflexivity.
  simpl. destruct (eq_dec y a) eqn:Hy, (eq_dec x a) eqn:Hx; simpl;
  try rewrite Hx; try rewrite Hy; simpl; now rewrite IHl.
Qed.

Lemma remove_length_le : forall l (x : A), length (remove eq_dec x l) <= length l.
Proof.
intros l x. induction l; simpl.
  reflexivity.
  destruct (eq_dec x a); simpl; omega.
Qed.

End Remove_results.

(** ***  Results about [inclA]  **)

Section inclA_results.
Context (A B : Type).
Context (eqA : relation A).
Context (HeqA : Equivalence eqA).
Context (eq_dec : forall x y : A, {eqA x y} + {~eqA x y}).

Lemma inclA_Leibniz : forall l1 l2 : list A, inclA Logic.eq l1 l2 <-> incl l1 l2.
Proof. intros. unfold inclA, incl. setoid_rewrite InA_Leibniz. reflexivity. Qed.

Global Instance inclA_compat : Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (inclA eqA).
Proof. intros ? ? Hl1 ? ? Hl2. unfold inclA. setoid_rewrite Hl1. setoid_rewrite Hl2. reflexivity. Qed.

Lemma inclA_nil : forall l, inclA eqA l nil -> l = nil.
Proof. intros [| x l] Hin; trivial. specialize (Hin x ltac:(now left)). inversion Hin. Qed.

Lemma inclA_cons_inv : forall x l1 l2, ~InA eqA x l1 ->
  inclA eqA (x :: l1) (x :: l2) -> inclA eqA l1 l2.
Proof.
intros x l1 l2 Hx Hincl y Hin1.
assert (Hin2 : InA eqA y (x :: l2)). { apply Hincl. now right. }
inversion_clear Hin2; trivial. rewrite <- H in Hx. contradiction.
Qed.

Lemma inclA_skip: forall (x : A) (l1 l2 : list A), ~ InA eqA x l1 -> inclA eqA l1 (x :: l2) -> inclA eqA l1 l2.
Proof.
intros x l1 l2 Hout Hincl y Hin.
specialize (Hincl y Hin).
inversion_clear Hincl as [? ? Heq |]; subst.
- now rewrite Heq in Hin.
- assumption.
Qed.

Lemma inclA_dec : forall l1 l2, {inclA eqA l1 l2} + {~inclA eqA l1 l2}.
Proof.
induction l1 as [| x1 l1 Hrec]; intro l2.
* left. abstract (intros x Habs; rewrite InA_nil in Habs; elim Habs).
* refine (match InA_dec eq_dec x1 l2 with
            | left in_x => match Hrec l2 with
                             | left in_l => left _
                             | right out_l => right _
                           end
            | right out_x => right _
          end).
  + abstract (intros x Hin; inversion_clear Hin; now rewrite H || apply in_l).
  + abstract (intro Habs; apply out_l; intros x Hin; apply Habs; now right).
  + abstract (intro Habs; apply out_x; apply Habs; now left).
Defined.

Global Instance inclA_preorder: PreOrder (inclA eqA).
Proof.
  unfold inclA.
  split;auto.
Qed.

Lemma inclA_cons_InA : forall (x : A) (l1 l2 : list A),
  InA eqA x l2 -> inclA eqA l1 (x::l2) -> inclA eqA l1 l2.
Proof.
  intros x l1 l2 Hin Hincl.
  unfold inclA in *.
  intros x' Hin'.
  apply Hincl in Hin'.
  inversion_clear Hin'.
  + now rewrite H.
  + assumption.
Qed.

Lemma not_inclA : forall l1 l2, ~inclA eqA l1 l2 <-> exists x, InA eqA x l1 /\ ~InA eqA x l2.
Proof.
intros l1 l2. split; intro H.
* induction l1 as [| e l1].
  + elim H. intro. now rewrite InA_nil.
  + destruct (InA_dec eq_dec e l2).
    - assert (Hincl : ~ inclA eqA l1 l2).
      { intro Hincl. apply H. intros x Hin. inversion_clear Hin.
        - now rewrite H0.
        - now apply Hincl. }
      apply IHl1 in Hincl. destruct Hincl as [x [Hin Hin']].
      exists x. intuition.
    - exists e. intuition.
* destruct H as [x [Hin Hin']].
  intro Hincl. now apply Hincl in Hin.
Qed.

(** A boolean decision procedure *)
Definition inclA_bool l1 l2 := if inclA_dec l1 l2 then true else false.

Lemma inclA_bool_true_iff : forall l1 l2, inclA_bool l1 l2 = true <-> inclA eqA l1 l2.
Proof. intros l1 l2. unfold inclA_bool. destruct (inclA_dec l1 l2); intuition discriminate. Qed.

Lemma inclA_bool_false_iff : forall l1 l2, inclA_bool l1 l2 = false <-> ~inclA eqA l1 l2.
Proof. intros l1 l2. unfold inclA_bool. destruct (inclA_dec l1 l2); intuition discriminate. Qed.

Global Instance inclA_bool_compat : Proper (PermutationA eqA ==> PermutationA eqA ==> eq) (inclA_bool).
Proof.
intros l1 l1' Hl1 l2 l2' Hl2. unfold inclA_bool.
destruct (inclA_dec l1 l2), (inclA_dec l1' l2'); trivial; rewrite ?Hl1, ?Hl2 in *; contradiction.
Qed.

Lemma NoDupA_inclA_length : forall l1 l2 : list A, NoDupA eqA l1 -> inclA eqA l1 l2 -> length l1 <= length l2.
Proof.
intro l1. induction l1 as [| a l1]; intros l2 Hnodup Hincl.
+ simpl. omega.
+ assert (Hin : InA eqA a l2). { apply Hincl. now left. }
  apply (PermutationA_split _) in Hin. destruct Hin as [l2' Heql2]. 
  rewrite Heql2 in *. inversion_clear Hnodup.
  apply inclA_cons_inv in Hincl; trivial. simpl. apply le_n_S. now apply IHl1.
Qed.

Lemma NoDupA_inclA_length_PermutationA : forall l1 l2,
  NoDupA eqA l1 -> NoDupA eqA l2 -> inclA eqA l1 l2 -> length l2 <= length l1 -> PermutationA eqA l1 l2.
Proof.
intro l1. induction l1 as [| x l1]; intros l2 Hnodup1 Hnodup2 Hincl Hlen.
+ destruct l2; try reflexivity. cbn in *. omega.
+ assert (Hin : InA eqA x l2). { apply Hincl. now left. }
  apply (PermutationA_split _) in Hin. destruct Hin as [l2' Heql2]. 
  rewrite Heql2 in *. constructor; try reflexivity.
  inversion_clear Hnodup1. inversion_clear Hnodup2.
  apply inclA_cons_inv in Hincl; trivial. apply IHl1; auto. cbn in *. omega.
Qed.

End inclA_results.

(** ***  Counting occurences in a list modulo some setoid equality  **)

Section CountA.
Context (A : Type).
Context (eqA : relation A).
Context (HeqA : Equivalence eqA).
Hypothesis eq_dec : forall x y : A, {eqA x y} + {~eqA x y}.

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

Global Instance count_occ_proper : Proper (eq ==> PermutationA eqA ==> eq) (countA_occ).
Proof.
intros a b Hab l. induction l as [| x l]; intros [| x' l'] Hl; subst.
+ reflexivity.
+ apply (PermutationA_nil _) in Hl. discriminate Hl.
+ symmetry in Hl. apply (PermutationA_nil _) in Hl. discriminate Hl.
+ assert (Hperm := @PermutationA_InA_inside _ _ _ x _ _ Hl).
  destruct Hperm as [l1 [y [l2 [Hxy Heql]]]]; try now left.
  rewrite Heql in *. rewrite Hxy, <- (PermutationA_middle _) in Hl. apply (PermutationA_cons_inv _) in Hl.
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
intros x n. induction n; simpl; trivial.
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

(** ***  Results about [firstn] and [skipn]  **)

Section List_halves.
Variable A : Type.

Lemma skipn_nil : forall k, skipn k (@nil A) = nil.
Proof. now intros []. Qed.

Theorem skipn_length : forall (l : list A) n, length (skipn n l) = length l - n.
Proof.
induction l.
- now intros [| n].
- intros [| n]; trivial. simpl. apply IHl.
Qed.

Lemma firstn_In : forall (l : list A) n, incl (firstn n l) l.
Proof.
induction l; intros n x Hin.
+ destruct n; elim Hin.
+ destruct n; try now elim Hin. simpl in Hin. destruct Hin.
  - subst. now left.
  - right. now apply IHl in H.
Qed.

Lemma firstn_add_hd : forall n l (a : A), firstn (S n) (a :: l) =  a :: firstn n l.
Proof. reflexivity. Qed.

Lemma firstn_add_tl_In : forall n l (x a : A), In x (firstn n l) -> In x (firstn n (l ++ a :: nil)).
Proof.
induction n; intros l x a Hin; simpl in *.
- assumption.
- destruct l as [| b l]; simpl in *; solve [elim Hin | intuition].
Qed.

Lemma firstn_add_tl : forall l n (a : A), n <= length l -> firstn n (l ++ a :: nil) = firstn n l.
Proof.
intro l. induction l as [| e l]; intros n a Hle.
+ now inversion_clear Hle.
+ destruct n; simpl in *.
  - reflexivity.
  - f_equal. apply IHl. omega.
Qed.

Lemma firstn_NoDup : forall (l : list A) n, NoDup l -> NoDup (firstn n l).
Proof.
intros l. induction l as [| e l]; intros n Hnodup.
+ now destruct n; compute.
+ destruct n; try now constructor. simpl.
  inversion_clear Hnodup as [| ? ? Helt Hnodup']. constructor.
  - intro Hin. apply Helt. apply (firstn_In l n e Hin).
  - auto.
Qed.

Lemma skipn_In : forall (l : list A) n, incl (skipn n l) l.
Proof.
induction l; intros n x Hin.
+ destruct n; elim Hin.
+ destruct n; try now elim Hin. simpl in Hin. apply IHl in Hin. now right.
Qed.

Lemma In_skipn : forall l l' (pt : A) n, n <= length l -> In pt (skipn n (l ++ pt :: l')).
Proof.
intros l l' pt. generalize (le_refl (length l)). generalize l at -2. induction l; simpl.
* intros [| x l] Hl [| n] ?; simpl in *; try tauto || omega.
* intros [| x l''] Hl'' n Hn; simpl in *; try tauto.
  + destruct n; simpl; tauto || omega.
  + destruct n; simpl.
    - right. change (In pt (skipn 0 (l'' ++ pt :: l'))). apply IHl; omega.
    - apply IHl; omega.
Qed.

Lemma skipn_add_hd : forall n l (a : A), skipn (S n) (a :: l) = skipn n l.
Proof. reflexivity. Qed.

Lemma skipn_add_tl_In : forall n l (x a : A), In x (skipn n l) -> In x (skipn n (l ++ a :: nil)).
Proof.
induction n; intros l x a Hin; simpl in *.
- rewrite in_app_iff. now left.
- destruct l as [| b l]; simpl in *; solve [elim Hin | auto].
Qed.

Lemma In_skipn_add : forall l (pt : A), In pt (skipn (Nat.div2 (length l)) (l ++ pt :: nil)).
Proof. intros. apply In_skipn. apply Nat.div2_decr. omega. Qed.

Lemma skipn_add_tl : forall l n (a : A), n <= length l -> skipn n (l ++ a :: nil) = skipn n l ++ a :: nil.
Proof.
intro l. induction l as [| e l]; intros n a Hle; simpl in *.
+ now inversion_clear Hle.
+ destruct n; simpl in *.
  - reflexivity.
  - apply IHl. omega.
Qed.

Lemma skipn_NoDup : forall (l : list A) n, NoDup l -> NoDup (skipn n l).
Proof.
intro l. induction l as [| e l]; intros n Hnodup.
- destruct n; constructor.
- destruct n; auto. simpl. apply IHl. now inversion_clear Hnodup.
Qed.

Lemma firstn_skipn_nodup_exclusive : forall l : list A, NoDup l ->
  forall n e, In e (firstn n l) -> In e (skipn n l) -> False.
Proof.
intros l Hnodup n. rewrite <- (firstn_skipn n) in Hnodup.
rewrite <- NoDupA_Leibniz, NoDupA_app_iff in Hnodup; autoclass.
destruct Hnodup as [Hleft [Hright Hboth]]. now setoid_rewrite InA_Leibniz in Hboth.
Qed.

Lemma firstn_map_swap : forall {B} (f : A -> B) k l, firstn k (map f l) = map f (firstn k l).
Proof. intros B f k. induction k; intros [| x l]; simpl; now try rewrite IHk. Qed.

Lemma skipn_map_swap : forall {B} (f : A -> B) k l, skipn k (map f l) = map f (skipn k l).
Proof. intros B f k. induction k; intros [| x l]; simpl; now try rewrite IHk. Qed.

(** ***  Cutting a list in two halves: [half1] and [half2]  **)

Definition half1 (l : list A) := firstn (Nat.div2 (length l)) l.
Definition half2 (l : list A) := skipn  (Nat.div2 (length l)) l.

Lemma half1_length : forall l : list A, length (half1 l) = div2 (length l).
Proof.
  intros.
  unfold half1.
  rewrite firstn_length.
  rewrite min_l;auto.
  apply Nat.div2_decr.
  omega.
Qed.

Corollary half2_length : forall l : list A, length (half2 l) = length l - div2 (length l).
Proof. intros. unfold half2. now rewrite skipn_length. Qed.

Corollary half2_even_length : forall l : list A, Nat.Even (length l) -> length (half2 l) = div2 (length l).
Proof. intros l H. unfold half2. rewrite skipn_length. apply even_div2 in H. omega. Qed.

Lemma merge_halves : forall l : list A, half1 l ++ half2 l = l.
Proof. intro. apply firstn_skipn. Qed.

Lemma half1_incl : forall l : list A, incl (half1 l) l.
Proof. intros ? ? ?. rewrite <- merge_halves. apply in_app_iff. tauto. Qed.

Lemma half2_incl : forall l : list A, incl (half2 l) l.
Proof. intros ? ? ?. rewrite <- merge_halves. apply in_app_iff. tauto. Qed.

Lemma half1_cons2 : forall (e e' : A) l, half1 (e :: l ++ e' :: nil) = e :: half1 l.
Proof.
intros e e' l. unfold half1 at 1. simpl. rewrite app_length, plus_comm. simpl.
f_equal. apply firstn_add_tl. apply Nat.div2_decr. omega.
Qed.

Lemma half2_cons2 : forall (e e' : A) l, half2 (e :: l ++ e' :: nil) = half2 l ++ e' :: nil.
Proof.
intros e e' l. unfold half2 at 1. simpl. rewrite app_length, plus_comm. simpl.
apply skipn_add_tl. apply Nat.div2_decr. omega.
Qed.

Lemma half1_dec : (forall x y : A, {x = y} + {x <> y}) ->
  forall (e : A) l, {In e (half1 l)} + {~In e (half1 l)}.
Proof. intros. now apply List.In_dec. Qed.

Lemma half2_dec : (forall x y : A, {x = y} + {x <> y}) ->
  forall (e : A) l, {In e (half2 l)} + {~In e (half2 l)}.
Proof. intros. now apply List.In_dec. Qed.

Theorem half_dec : (forall x y : A, {x = y} + {x <> y}) ->
  forall l e, In e l -> {In e (half1 l)} + {In e (half2 l)}.
Proof.
intros HeqA l e Hin. destruct (half1_dec HeqA e l) as [? | Hg].
+ left. assumption.
+ right. abstract (rewrite <- merge_halves in Hin; apply List.in_app_or in Hin; tauto).
Defined.

Corollary incl_nil : forall (l : list A), incl l nil -> l = nil.
Proof. intros l. rewrite <- inclA_Leibniz. apply (inclA_nil _). Qed.

Corollary NoDup_dec : (forall x y : A, {x = y} + {~x = y}) -> forall l : list A, {NoDup l} + {~NoDup l}.
Proof. intros eq_dec l. destruct (NoDupA_dec _ eq_dec l); rewrite NoDupA_Leibniz in *; auto. Qed.

(** Induction on first and last elements of a list. *)

Lemma first_last_ind_aux : forall P : list A -> Prop, P nil -> (forall x, P (x :: nil)) ->
  (forall x y l, P l -> P ((x :: l) ++ (y :: nil))) -> forall l l' : list A, length l' <= length l -> P l'.
Proof.
intros P Pnil Pone Prec l. induction l as [| x l]; intros l' Hlength.
* destruct l'. apply Pnil. simpl in Hlength. omega.
* destruct l as [| x' l].
  + destruct l' as [| ? [| ? ?]]; apply Pnil || apply Pone || simpl in Hlength; omega.
  + destruct l' as [| ? [| ? ?]]; try apply Pnil || apply Pone.
    destruct (@exists_last _ (a0 :: l0)) as [l2 [ y Hy]]; try discriminate.
    rewrite Hy. apply Prec. apply IHl. transitivity (length (l2 ++ y :: nil)).
    - rewrite app_length. omega.
    - rewrite Hy in Hlength. simpl in *. omega.
Qed.

Theorem first_last_ind : forall P : list A -> Prop, P nil -> (forall x, P (x :: nil)) ->
  (forall x y l, P l -> P ((x :: l) ++ (y :: nil))) -> forall l : list A, P l.
Proof. intros P Pnil Pone Prec l. now apply first_last_ind_aux with l. Qed.

Corollary first_last_even_ind : forall P : list A -> Prop, P nil ->
  (forall x y l, Nat.Even (length l) -> P l -> P ((x :: l) ++ (y :: nil))) -> forall l, Nat.Even (length l) -> P l.
Proof.
intros P Pnil Prec l. pattern l. apply first_last_ind; clear l.
+ auto.
+ simpl. intros x Habs. inversion Habs. omega.
+ intros x y l Hrec Hlen. rewrite app_length, plus_comm in Hlen. simpl in Hlen. destruct Hlen as [n Hlen].
  apply Prec, Hrec; exists (pred n); omega.
Qed.

End List_halves.

(** ***  To sort out  **)

Section ToSortOut_results.
Context (A B : Type).
Context (eqA eqA' : relation A) (eqB : relation B).
Context (HeqA : Equivalence eqA) (HeqB : Equivalence eqB).

Global Instance fold_left_start : forall f, Proper (eqB ==> eqA ==> eqB) f ->
  forall l, Proper (eqB ==> eqB) (fold_left f l).
Proof.
intros f Hf l. induction l; intros i1 i2 Hi; simpl.
  assumption.
  rewrite IHl. reflexivity. now rewrite Hi.
Qed.

Global Instance fold_left_symmetry_PermutationA : forall (f : B -> A -> B),
  Proper (eqB ==> eqA ==> eqB) f -> (forall x y z, eqB (f (f z x) y) (f (f z y) x)) ->
  Proper (PermutationA eqA ==> eqB ==> eqB) (fold_left f).
Proof.
intros f Hfcomm Hf l1 l2 perm. induction perm; simpl.
- now repeat intro.
- intros ? ? Heq. rewrite H, Heq. now apply IHperm.
- intros ? ? Heq. now rewrite Hf, Heq.
- repeat intro. etransitivity. now apply IHperm1. now apply IHperm2.
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

Theorem PermutationA_rev : forall l, PermutationA eqA l (rev l).
Proof. intro. apply (Permutation_PermutationA_weak _). apply Permutation_rev. Qed.

(* A boolean version of membership *)
Definition mem eq_dec (x : A) l := if @InA_dec A eqA eq_dec x l then true else false.

Lemma mem_true_iff : forall eq_dec x l, mem eq_dec x l = true <-> InA eqA x l.
Proof. intros eq_dec x l. unfold mem. destruct (InA_dec eq_dec x l); intuition discriminate. Qed.

Lemma mem_false_iff : forall eq_dec x l, mem eq_dec x l = false <-> ~InA eqA x l.
Proof. intros eq_dec x l. unfold mem. destruct (InA_dec eq_dec x l); intuition discriminate. Qed.

Global Instance mem_compat : forall eq_dec, Proper (eqA ==> equivlistA eqA ==> eq) (mem eq_dec).
Proof.
intros eq_dec x y Hxy l1 l2 Hl. unfold mem.
destruct (InA_dec eq_dec x l1), (InA_dec eq_dec y l2); trivial; rewrite Hl, Hxy in *; contradiction.
Qed.

Lemma mem_map : forall eq_dec f, Proper (eqA ==> eqA) f ->
  forall x l, mem eq_dec x l = true -> mem eq_dec (f x) (map f l) = true.
Proof.
intros eq_dec f Hf x l Hin.
rewrite mem_true_iff in *. rewrite (InA_map_iff _); trivial.
exists x. now split.
Qed.

Lemma mem_injective_map : forall eq_dec f, Proper (eqA ==> eqA) f -> injective eqA eqA f ->
  forall x l, mem eq_dec (f x) (map f l) = mem eq_dec x l.
Proof.
intros eq_dec f Hf Hinj x l.
destruct (mem eq_dec x l) eqn:Hmem.
- now apply mem_map.
- rewrite mem_false_iff in *. intro Hin. apply Hmem. rewrite (InA_map_iff _ _ _) in Hin.
  destruct Hin as [x' [Heq Hin]]. apply Hinj in Heq. now rewrite <- Heq.
Qed.

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

Global Instance filter_PermutationA_compat : forall f, Proper (eqA ==> eq) f ->
  Proper (PermutationA eqA ==> PermutationA eqA) (@filter A f).
Proof.
intros f Hf l1 l2 Hperm. pattern l1, l2.
apply (PermutationA_ind_bis _); easy || simpl; clear l1 l2 Hperm.
+ intros x y l1 l2 Hxy Hperm Hrec. destruct (f x) eqn:Hfx;
  rewrite (Hf _ _ Hxy) in Hfx; now rewrite Hfx, ?Hxy, Hrec.
+ intros x y l1 l2 Hperm Hrec. destruct (f x), (f y); rewrite Hrec; easy || now constructor; auto.
+ intros l1 l2 l3 Hperm12 Hrec12 Hperm23 Hrec23. now rewrite Hrec12.
Qed.

Global Instance filter_extensionality_compat : Proper ((eq ==> eq) ==> eq ==> eq) (@filter A).
Proof.
intros f g Hfg ? l ?; subst. induction l as [| x l]; simpl.
+ trivial.
+ destruct (f x) eqn:Hfx; rewrite (Hfg _ _ (reflexivity _)) in Hfx; now rewrite Hfx, IHl.
Qed.

Lemma filter_twice : forall f (l : list A), filter f (filter f l) = filter f l.
Proof.
intros f l. induction l as [| e l]; simpl; auto.
destruct (f e) eqn:Hfe; simpl; try rewrite Hfe; rewrite IHl; auto.
Qed.

Lemma filter_inclA : forall f, Proper (eqA ==> eq) f -> forall l, inclA eqA (filter f l) l.
Proof. intros f Hf l x Hin. now rewrite filter_InA in Hin. Qed.

Lemma filter_incl : forall f (l : list A), incl (filter f l) l.
Proof. intros f l x Hin. now rewrite filter_In in Hin. Qed.

Lemma filter_app : forall f (l1 l2 : list A), filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
intros f l1 l2. induction l1 as [| x l1]; simpl.
+ reflexivity.
+ destruct (f x); now rewrite IHl1.
Qed.

Lemma eqlistA_dec (eqA_dec : forall x y, {eqA x y} + {~eqA x y}) :
  forall l1 l2, {eqlistA eqA l1 l2} + {~eqlistA eqA l1 l2}.
Proof.
intros l. induction l as [| x l1]; intros [| y l2].
+ now left.
+ now right.
+ now right.
+ destruct (eqA_dec x y) as [Hxy | Hxy]; [destruct (IHl1 l2) as [Hrec | Hrec] |].
  - auto.
  - right. intro Habs. inv Habs. contradiction.
  - right. intro Habs. inv Habs. contradiction.
Qed.

Lemma eqlistA_app_split : forall l1 l2 l1' l2',
  eqlistA eqA (l1 ++ l2) (l1' ++ l2') -> length l1 = length l1' -> eqlistA eqA l1 l1' /\ eqlistA eqA l2 l2'.

Proof.
intro l. induction l as [| x l1];
intros l2 [| y l1'] l2' Heq Hlen; simpl in *; auto; try omega; [].
inv Heq. edestruct IHl1; eauto.
Qed.

Lemma singleton_characterization: forall (Aeq_dec: forall (a b: A), {a=b} + {a<>b}) (l: list A) (a: A),
    NoDup l ->
    In a l ->
    (forall b, ~ a = b -> ~ In b l) ->
    l = a :: nil.
Proof.
  intros Aeq_dec l a Hnodup Hin Hnotin.
  destruct l.
  + inversion Hin.
  + destruct (Aeq_dec a a0).
    - subst. f_equal.
      destruct l.
      * reflexivity.
      * exfalso. apply (Hnotin a).
        -- inversion Hnodup.
           intro Heq.
           apply H1. now left.
        -- intuition.
    - exfalso.
      apply (Hnotin a0); intuition.
Qed.

End ToSortOut_results.

Global Arguments mem [A] [eqA] eq_dec x l.


(* ******************************* *)
(** *  The same for real numbers. **)
(* ******************************* *)


Open Scope R_scope.

(* Should be in Reals from the the std lib! *)
Global Instance Rle_preorder : PreOrder Rle.
Proof. split.
- intro. apply Rle_refl.
- intro. apply Rle_trans.
Qed.

Global Instance Rle_partialorder : PartialOrder eq Rle.
Proof.
intros x y. unfold flip. cbn. split; intro Hxy.
- now subst.
- destruct Hxy. now apply Rle_antisym.
Qed.

Lemma Rdec : forall x y : R, {x = y} + {x <> y}.
Proof.
intros x y. destruct (Rle_dec x y). destruct (Rle_dec y x).
  left. now apply Rle_antisym.
  right; intro; subst. contradiction.
  right; intro; subst. pose (Rle_refl y). contradiction.
Qed.

Lemma Rdiv_le_0_compat : forall a b, 0 <= a -> 0 < b -> 0 <= a / b.
Proof. intros a b ? ?. now apply Fourier_util.Rle_mult_inv_pos. Qed.

(* Lemma Rdiv_le_compat : forall a b c, (0 <= a -> a <= b -> 0 < c -> a / c <= b / c)%R.
Proof.
intros a b c ? ? ?. unfold Rdiv. apply Rmult_le_compat; try lra.
rewrite <- Rmult_1_l. apply Fourier_util.Rle_mult_inv_pos; lra.
Qed. *)

Lemma Zup_lt : forall x y, x <= y - 1 -> (up x < up y)%Z.
Proof.
intros x y Hle. apply lt_IZR. apply Rle_lt_trans with (x + 1).
- generalize (proj2 (archimed x)). lra.
- apply Rle_lt_trans with (y - 1 + 1); try lra; [].
  generalize (proj1 (archimed y)). lra.
Qed.

Lemma up_le_0_compat : forall x, 0 <= x -> (0 <= up x)%Z.
Proof. intros x ?. apply le_0_IZR, Rlt_le, Rle_lt_trans with x; trivial; []. now destruct (archimed x). Qed.

(** A boolean equality test. *)
Definition Rdec_bool x y := match Rdec x y with left _ => true | right _ => false end.

Global Instance Rdec_bool_compat : Proper (eq ==> eq ==> eq) Rdec_bool.
Proof. repeat intro. subst. reflexivity. Qed.

Lemma Rdec_bool_true_iff : forall x y, Rdec_bool x y = true <-> x = y.
Proof. intros. unfold Rdec_bool. destruct (Rdec x y); now split. Qed.

Lemma Rdec_bool_false_iff : forall x y, Rdec_bool x y = false <-> x <> y.
Proof. intros. unfold Rdec_bool. destruct (Rdec x y); now split. Qed.

Lemma if_Rdec : forall A x y (l r : A), (if Rdec x y then l else r) = if Rdec_bool x y then l else r.
Proof. intros. unfold Rdec_bool. now destruct Rdec. Qed.

Lemma Rdec_bool_plus_l : forall k r r', Rdec_bool (k + r) (k + r') = Rdec_bool r r'.
Proof.
intros k r r'.
destruct (Rdec_bool (k + r) (k + r')) eqn:Heq1, (Rdec_bool r r') eqn:Heq2; trivial;
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *.
- elim Heq2. eapply Rplus_eq_reg_l; eassumption.
- subst. auto.
Qed.

Lemma Rdec_bool_mult_l : forall k r r', (k <> 0)%R -> Rdec_bool (k * r) (k * r') = Rdec_bool r r'.
Proof.
intros k r r' Hk.
destruct (Rdec_bool r r') eqn:Heq1, (Rdec_bool (k * r) (k * r')) eqn:Heq2; trivial;
rewrite ?Rdec_bool_true_iff, ?Rdec_bool_false_iff in *.
- subst. auto.
- elim Heq1. eapply Rmult_eq_reg_l; eassumption.
Qed.

Corollary Rdec_bool_plus_r : forall k r r', Rdec_bool (r + k) (r' + k) = Rdec_bool r r'.
Proof. intros. setoid_rewrite Rplus_comm. apply Rdec_bool_plus_l. Qed.

Corollary Rdec_bool_mult_r : forall k r r', (k <> 0)%R -> Rdec_bool (r * k) (r' * k) = Rdec_bool r r'.
Proof. intros. setoid_rewrite Rmult_comm. now apply Rdec_bool_mult_l. Qed.

(** A boolean inequality test. *)
Definition Rle_bool x y :=
  match Rle_dec x y with
    | left _ => true
    | right _ => false
  end.

Lemma Rle_bool_true_iff : forall x y, Rle_bool x y = true <-> Rle x y.
Proof. intros x y. unfold Rle_bool. destruct (Rle_dec x y); intuition discriminate. Qed.

Lemma Rle_bool_false_iff : forall x y, Rle_bool x y = false <-> ~Rle x y.
Proof. intros x y. unfold Rle_bool. destruct (Rle_dec x y); intuition discriminate. Qed.

Lemma Rle_bool_mult_l : forall k x y, (0 < k)%R -> Rle_bool (k * x) (k * y) = Rle_bool x y.
Proof.
intros k x y Hk. destruct (Rle_bool x y) eqn:Hle.
- rewrite Rle_bool_true_iff in *. now apply Rmult_le_compat_l; trivial; apply Rlt_le.
- rewrite Rle_bool_false_iff in *. intro Habs. apply Hle. eapply Rmult_le_reg_l; eassumption.
Qed.

Lemma Rle_bool_plus_l : forall k x y, Rle_bool (k + x) (k + y) = Rle_bool x y.
Proof.
intros k x y. destruct (Rle_bool x y) eqn:Hle.
- rewrite Rle_bool_true_iff in *. now apply Rplus_le_compat_l.
- rewrite Rle_bool_false_iff in *. intro Habs. apply Hle. eapply Rplus_le_reg_l; eassumption.
Qed.

Corollary Rle_bool_plus_r : forall k r r', Rle_bool (r + k) (r' + k) = Rle_bool r r'.
Proof. intros. setoid_rewrite Rplus_comm. apply Rle_bool_plus_l. Qed.

Corollary Rle_bool_mult_r : forall k r r', (0 < k)%R -> Rle_bool (r * k) (r' * k) = Rle_bool r r'.
Proof. intros. setoid_rewrite Rmult_comm. now apply Rle_bool_mult_l. Qed.


Definition remove_Perm_properR := remove_Perm_proper Rdec.
Existing Instance Permutation_length_compat.
Existing Instance Permutation_NoDup_compat.
Existing Instance remove_Perm_properR.
Existing Instance In_perm_compat.
Existing Instance InA_impl_compat.
Existing Instance InA_compat.
Existing Instance InA_perm_compat.
Existing Instance PermutationA_length.
Existing Instance fold_left_start.
Existing Instance fold_left_symmetry_PermutationA.
Existing Instance PermutationA_map.


Close Scope R_scope.

Lemma le_neq_lt : forall m n : nat, n <= m -> n <> m -> n < m.
Proof. intros n m Hle Hneq. now destruct (le_lt_or_eq _ _ Hle). Qed.

Local Open Scope R_scope.

Lemma Rle_neq_lt : forall x y : R, x <= y -> x <> y -> x < y.
Proof. intros ? ? Hle ?. now destruct (Rle_lt_or_eq_dec _ _ Hle). Qed.

Unset Implicit Arguments.
Lemma succ_neq : forall x, x <> x+1.
Proof.
intros x Habs. assert (Heq : x = x + 0) by ring. rewrite Heq in Habs at 1. clear Heq.
apply Rplus_eq_reg_l in Habs. symmetry in Habs. revert Habs. exact R1_neq_R0.
Qed.

(** Lifting an equivalence relation to an option type. *)
Definition opt_eq {T} (eqT : T -> T -> Prop) (xo yo : option T) :=
  match xo, yo with
    | None, None => True
    | None, Some _ | Some _, None => False
    | Some x, Some y => eqT x y
  end.

Instance opt_eq_refl : forall T (R : relation T), Reflexive R -> Reflexive (opt_eq R).
Proof. intros T R HR [x |]; simpl; auto. Qed.

Instance opt_eq_sym : forall T (R : relation T), Symmetric R -> Symmetric (opt_eq R).
Proof. intros T R HR [x |] [y |]; simpl; auto. Qed.

Instance opt_eq_trans : forall T (R : relation T), Transitive R -> Transitive (opt_eq R).
Proof. intros T R HR [x |] [y |] [z |]; simpl; intros; eauto; contradiction. Qed.

Instance opt_equiv T eqT (HeqT : @Equivalence T eqT) : Equivalence (opt_eq eqT).
Proof. split; auto with typeclass_instances. Qed.


(** *  The same for integers. **)

Open Scope Z.

Lemma Zincr_mod : forall k n, 0 < n -> (k + 1) mod n = k mod n + 1 \/ (k + 1) mod n = 0 /\ k mod n = n - 1.
Proof.
intros k n Hn.
destruct (Z.eq_dec (k mod n) (n - 1)) as [Heq | Heq].
+ right. rewrite <- Zdiv.Zplus_mod_idemp_l, Heq.
  ring_simplify (n - 1 + 1). split; trivial; []. apply Z.mod_same. omega.
+ left. rewrite <- Zdiv.Zplus_mod_idemp_l. apply Z.mod_small.
  assert (Hle := Z.mod_pos_bound k n Hn). omega.
Qed.

Lemma Zopp_mod : forall k n, 0 <= k < n -> (-k) mod n = (n - (k mod n)) mod n.
Proof.
intros k n Hn. destruct (Z.eq_dec k 0).
- subst. rewrite 2 Z.mod_0_l, Z.sub_0_r, Z.mod_same; omega.
- rewrite Z.mod_opp_l_nz, Z.mod_small; try rewrite Z.mod_small; omega.
Qed.

Close Scope Z.
