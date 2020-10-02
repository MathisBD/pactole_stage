
(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     P. Courtieu, L. Rieg, X. Urbain                                        
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence       
                                                                          *)
(**************************************************************************)


Require Import List SetoidList.
Require Export SetoidPermutation.
Require Import Sorting.Permutation.
Require Import Bool.
Require Import Arith.Div2 Lia PeanoNat.
Require Import Psatz.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Import Pactole.Util.NumberComplements.


Set Implicit Arguments.
Arguments PermutationA {A}%type eqA%signature l1%list l2%list.


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
Proof using .
intros x l. split; intro Hl; induction l; inversion_clear Hl;
(subst; now left) || (right; now apply IHl).
Qed.

Lemma nil_or_In_dec : forall l : list A, {l = nil} + {exists x, In x l}.
Proof using . intros [| x l]; auto. right. exists x. now left. Qed.

Lemma not_nil_In : forall l : list A, l <> nil -> exists x, In x l.
Proof using .
intros [| x l] Hl.
- now elim Hl.
- exists x. now left.
Qed.

Lemma not_nil_last : forall l, l <> nil -> exists (a : A) l', l = l' ++ a :: nil.
Proof using .
intros l Hl. induction l.
+ now elim Hl.
+ destruct l.
  - exists a, nil. reflexivity.
  - destruct (IHl ltac:(discriminate)) as [b [l'' Hl'']].
    exists b, (a :: l''). now rewrite Hl''.
Qed.

Lemma length_0 : forall l : list A, length l = 0 -> l = nil.
Proof using . intros [|] H; reflexivity || discriminate H. Qed.

(* Require Import Omega. *)

Lemma InA_nth : forall d x (l : list A), InA eqA x l ->
  exists n y, (n < length l)%nat /\ eqA x y /\ nth n l d = y.
Proof using .
intros d x l Hin. induction l as [| e l].
+ inversion Hin.
+ inversion_clear Hin.
  - exists 0, e. repeat split; trivial; simpl; lia.
  - destruct IHl as [n [y [Hn [Hy Hl]]]]; trivial; [].
    apply Lt.lt_n_S in Hn. exists (S n), y. now repeat split.
Qed.

(* Already exists as [List.In_nth] but with a reversed argument order
Lemma In_nth : forall d x (l : list A), In x l -> exists n, (n < length l)%nat /\ nth n l d = x.
Proof.
intros x d l Hin. induction l.
+ inversion Hin.
+ destruct Hin.
  - subst. exists 0%nat. split. simpl. now auto with arith. reflexivity.
  - destruct (IHl H) as [n [Hn Hl]]. apply lt_n_S in Hn. exists (S n). now split.
Qed. *)

(* Lemma In_split_first : forall (x : A) l, In x l ->
  exists l1, exists l2, ~List.In x l1 /\ l = l1 ++ x :: l2.
Proof.
intros x l. induction l as [| a l]; intro Hin.
  now elim (List.in_nil Hin).
  destruct Hin.
    subst. exists nil. exists l. intuition.
    destruct (IHl H) as [l1 [l2 [Hnin Heq]]].
    exists (a :: l1). exists l2. subst. intuition.
Abort. (* require decidability of equality *) *)

Lemma Permutation_in_inside : forall (x : A) l l',
  Permutation l l' -> In x l -> exists l1 l2, l' = l1 ++ x :: l2.
Proof using .
intros x l l' Hperm Hin. rewrite Hperm in Hin.
destruct (in_split _ _ Hin) as [l1 [l2 Heq]]. exists l1. exists l2. now subst l'.
Qed.

(** If the list argument is not empty, [hd] and [last] return an element of the list,
    independent from the default value provided. *)
Lemma hd_indep : forall l (d d' : A), l <> nil -> hd d l = hd d' l.
Proof using .
intros [| x l] d d' Hl.
- now elim Hl.
- reflexivity.
Qed.

Lemma last_indep : forall l (d d' : A), l <> nil -> last l d = last l d'.
Proof using .
induction l as [| x l]; intros d d' Hl.
- now elim Hl.
- destruct l; trivial. apply IHl. discriminate.
Qed.

Lemma hd_In : forall (d : A) l, l <> nil -> In (hd d l) l.
Proof using .
intros d [| x l] Hl.
- now elim Hl.
- now left.
Qed.

Lemma last_In : forall l (d : A), l <> List.nil -> List.In (List.last l d) l.
Proof using .
induction l as [| x l]; intros d Hl.
- now elim Hl.
- destruct l; try now left. right. apply IHl. discriminate.
Qed.

Lemma hd_last_diff : forall l d d', length l > 1 -> NoDupA eqA l ->
  ~eqA (hd d l) (last l d').
Proof using HeqA.
intros l d d' Hl Hnodup Heq.
destruct l as [| x [| y l]]; simpl in Hl; try lia.
inversion_clear Hnodup. change (eqA x (last (y :: l) d')) in Heq.
apply H. rewrite Heq. rewrite InA_alt. eexists; split; try reflexivity.
apply last_In. discriminate.
Qed.

Lemma app_last : forall (d : A) l1 l2, l2 <> nil -> last (l1 ++ l2) d = last l2 d.
Proof using .
intros d l1 l2 Hl2. induction l1; simpl.
  reflexivity.
  assert (l1 ++ l2 <> nil). { intro Habs. apply Hl2. now destruct (app_eq_nil _ _ Habs). }
  destruct (l1 ++ l2). now elim H. assumption.
Qed.

Lemma rev_nil : forall l : list A, rev l = nil <-> l = nil.
Proof using .
intros [| x l].
+ reflexivity.
+ simpl. split; intro Habs.
  - assert (Hlen : length (rev l ++ x :: nil) = length (@nil A)) by now rewrite Habs.
    rewrite app_length in Hlen. simpl in Hlen. lia.
  - discriminate.
Qed.

Lemma last_rev_hd : forall (d : A) l, last (rev l) d = hd d l.
Proof using . intros d l. destruct l; simpl; trivial; []. now rewrite app_last. Qed.

Corollary hd_rev_last : forall (d : A) l, hd d (rev l) = last l d.
Proof using . intros d l. rewrite <- (rev_involutive l) at 2. now rewrite last_rev_hd. Qed.

Lemma eqlistA_Leibniz : forall l1 l2 : list A, eqlistA eq l1 l2 <-> l1 = l2.
Proof using .
intro l1. induction l1 as [| e1 l1]; intro l2.
+ now destruct l2.
+ destruct l2 as [| e2 l2]; try now intuition.
  split; intro Heq.
  - inversion_clear Heq as [| ? ? ? ? He Hl]. rewrite IHl1 in Hl. now f_equal.
  - rewrite Heq. reflexivity.
Qed.

Lemma eqlistA_Leibniz_equiv : relation_equivalence (@eqlistA A eq) eq.
Proof using . repeat intro. apply eqlistA_Leibniz. Qed.

Global Instance InA_impl_compat : Proper (subrelation ==> eq ==> eq ==> impl) (@InA A).
Proof using .
intros R1 R2 HR x y Hxy l l2 Hl Hin. subst y l2. induction l.
  now inversion Hin.
  inversion_clear Hin.
    constructor. now apply HR.
    constructor 2. now apply IHl.
Qed.

Global Instance InA_compat : Proper (eqA ==> equivlistA eqA ==> iff) (InA eqA).
Proof using HeqA.
intros x y Hxy l1 l2 Hl. split; intro H; eapply InA_eqA; try eassumption.
  now rewrite <- Hl.
  symmetry. eassumption.
  now rewrite Hl.
Qed.

(** ***  Results about [map]  **)

Lemma map_id : forall (l : list A), map Datatypes.id l = l.
Proof using . induction l; simpl; now try rewrite IHl. Qed.

Global Instance map_extensionalityA_compat
  : Proper ((eqA ==> eqB) ==> eqlistA eqA ==> eqlistA eqB) (@map A B).
Proof using HeqB.
intros f g Hfg l. induction l as [| e l]; intros l' Hl.
- destruct l'; reflexivity || inversion Hl.
- destruct l' as [| e' l']; try now inversion Hl.
  inversion_clear Hl as [| ? ? ? ? He Hl'].
  simpl. constructor; auto.
Qed.

Global Instance map_eqlistA_compat f : Proper (eqA ==> eqB) f ->
  Proper (eqlistA eqA ==> eqlistA eqB) (map f).
Proof using HeqB. intro Hf. apply map_extensionalityA_compat. apply Hf. Qed.

Global Instance map_extensionality_compat : Proper ((eq ==> eq) ==> eq ==> eq) (@map A B).
Proof using .
intros f g Hfg l. induction l as [| e l]; intros l' Hl.
- destruct l'; reflexivity || inversion Hl.
- subst. simpl. f_equal; auto.
Qed.

Lemma map_singleton :
  forall (f : A -> B) l x, map f l = x :: nil <-> exists y, l = y :: nil /\ x = f y.
Proof using .
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
Proof using . intros f l d. now destruct l. Qed.

Lemma map_last : forall (f : A -> B) l d, last (map f l) (f d) = f (last l d).
Proof using .
intros f l d. induction l; simpl.
  reflexivity.
  destruct l. simpl. reflexivity. apply IHl.
Qed.

Theorem InA_map_iff : forall f, Proper (eqA ==> eqB) f ->
  forall l y, InA eqB y (map f l) <-> exists x, eqB (f x) y /\ InA eqA x l.
Proof using HeqA HeqB.
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
Proof using HeqA HeqB.
intros f Hf Hinj l Hnodup. induction Hnodup.
+ constructor.
+ simpl. constructor.
  - rewrite InA_map_iff; trivial. intros [y [Heq Hin]].
    apply Hinj in Heq. rewrite Heq in Hin. contradiction.
  - assumption.
Qed.

Lemma map_NoDupA_inv : forall f, Proper (eqA ==> eqB) f ->
  forall l, NoDupA eqB (map f l) -> NoDupA eqA l.
Proof using HeqA HeqB.
intros f Hf l Hfl.
induction l as [| e l].
+ constructor.
+ simpl map in Hfl. inversion_clear Hfl.
  constructor; auto; [].
  intro Habs. rewrite InA_map_iff in *; trivial; []. firstorder.
Qed.

Lemma map_NoDupA_eq : (forall x y, {eqA x y} + {~eqA x y}) ->
  forall f, Proper (eqA ==> eqB) f ->
  forall l, NoDupA eqB (map f l) ->
  forall x y, InA eqA x l -> InA eqA y l -> eqB (f x) (f y) -> eqA x y.
Proof using HeqA HeqB.
intros eqA_dec f Hf l Hfl x y Hx Hy Hxy.
destruct (eqA_dec x y); try tauto; [].
induction l.
+ now rewrite InA_nil in *.
+ inversion_clear Hfl.
  rewrite InA_cons in *. destruct Hx as [Hx | Hx], Hy as [Hy | Hy].
  - now rewrite Hx, Hy.
  - match goal with H : ~ InA _ _ _ |- _ => elim H end.
    rewrite <- Hx, Hxy, InA_map_iff; firstorder.
  - match goal with H : ~ InA _ _ _ |- _ => elim H end.
    rewrite <- Hy, <- Hxy, InA_map_iff; firstorder.
  - auto.
Qed.

Lemma filter_map : forall f (g : A -> B) l,
  filter f (map g l) = map g (filter (fun x => f (g x)) l).
Proof using .
intros f g l. induction l as [| e l]; simpl in *.
+ reflexivity.
+ destruct (f (g e)); simpl.
  - f_equal. apply IHl.
  - apply IHl.
Qed.

Global Instance PermutationA_map : forall f, Proper (eqA ==> eqB) f ->
  Proper (PermutationA eqA ==> PermutationA eqB) (map f).
Proof using HeqB.
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

Global Instance alls_compat : Proper (eqA ==> Logic.eq ==> eqlistA eqA) alls.
Proof using . intros x y Hxy ? n ?. subst. now induction n; simpl; constructor. Qed.

Lemma alls_length : forall (x : A) n, length (alls x n) = n.
Proof using . intros x n. induction n; simpl; auto. Qed.

Lemma alls_In : forall x y n, In y (alls x n) -> y = x.
Proof using . intros x y n Hin. induction n; inversion Hin. auto. now apply IHn. Qed.

Lemma alls_In_iff : forall (x y : A) n, n > 0 -> (In y (alls x n) <-> y = x).
Proof using .
intros x y n Hn. split; intro H.
+ eapply alls_In; eassumption.
+ induction n. now inversion Hn. left; auto.
Qed.

Corollary alls_not_In : forall (x y : A) n, x <> y -> ~In y (alls x n).
Proof using .
intros x y n Hxy Habs. apply Hxy. symmetry.
destruct n. now inversion Habs. rewrite alls_In_iff in Habs; assumption || lia.
Qed.

Lemma alls_InA : forall x y n, InA eqA y (alls x n) -> eqA y x.
Proof using . intros x y n Hin. induction n; inversion Hin. auto. now apply IHn. Qed.

Lemma alls_InA_iff : forall (x y : A) n, n > 0 -> (InA eqA y (alls x n) <-> eqA y x).
Proof using .
intros x y n Hn. split; intro H.
+ eapply alls_InA; eassumption.
+ induction n. now inversion Hn. left; auto.
Qed.

Corollary alls_notA_In : forall (x y : A) n, ~eqA x y -> ~InA eqA y (alls x n).
Proof using HeqA.
intros x y n Hxy Habs. apply Hxy. symmetry.
destruct n. now inversion Habs. rewrite alls_InA_iff in Habs; assumption || lia.
Qed.

Lemma alls_inj1 : forall x1 x2 n1 n2, alls x1 (S n1) = alls x2 n2 -> x1 = x2.
Proof using . intros x1 x2 n1 [] Heq; simpl in *. discriminate Heq. now inversion Heq. Qed.

Lemma alls_inj2 : forall x1 x2 n1 n2, alls x1 n1 = alls x2 n2 -> n1 = n2.
Proof using .
intros x1 x2 n1. induction n1; intros [] Heq; try reflexivity || discriminate Heq.
f_equal. apply IHn1. now inversion Heq.
Qed.

Lemma alls_app : forall x n1 n2, alls x n1 ++ alls x n2 = alls x (n1 + n2).
Proof using .
intros x n1 n2. induction n1; simpl.
+ reflexivity.
+ f_equal. assumption.
Qed.

Lemma alls_carac : forall x l, (forall y, In y l -> y = x) <-> l = alls x (length l).
Proof using .
intros x l. split; intro H.
+ induction l. reflexivity. simpl. f_equal.
  - apply H. now left.
  - apply IHl. intros y Hy. apply H. now right.
+ rewrite H. intro. apply alls_In.
Qed.

Lemma alls_caracA : forall x l,
  (forall y, InA eqA y l -> eqA y x) <-> eqlistA eqA l (alls x (length l)).
Proof using HeqA.
intros x l. split; intro H.
+ induction l. reflexivity. simpl. constructor.
  - apply H. now left.
  - apply IHl. intros y Hy. apply H. now right.
+ intro. rewrite H, InA_alt. intros [y' [Heq Hin]]. apply alls_In in Hin. now subst.
Qed.

Lemma Permutation_alls : forall (x : A) n l,
  Permutation l (alls x n) <-> l = alls x n.
Proof using .
intros x n l. split.
* revert l. induction n; intros l Hl.
  + simpl in *. apply Permutation_nil. now symmetry.
  + destruct l.
    - apply Permutation_nil in Hl. discriminate Hl.
    - assert (a = x). { apply alls_In with (S n). simpl alls. rewrite <- Hl. now left. }
      subst. simpl in *. f_equal. apply IHn. apply (Permutation_cons_inv Hl).
* intro Hl. now rewrite Hl.
Qed.

Lemma map_cst : forall x l, map (fun _ : B => x) l = alls x (length l).
Proof using . intros x l. now induction l; simpl; try f_equal. Qed.

(** ***  Boolean properties over a list  **)

Theorem Forall_dec : forall P,  (forall x : A, {P x} + {~P x}) ->
  forall l, {Forall P l} + {~Forall P l}.
Proof using .
intros P Pdec l. induction l; simpl.
+ left. constructor.
+ destruct (Pdec a) as [Ha | Ha].
  - destruct IHl as [Hok | Hko].
      left. now constructor.
      right. intros Habs. inversion_clear Habs. contradiction.
  - right. intros Habs. inversion_clear Habs. contradiction.
Qed.

Theorem Exists_dec : forall P, (forall x : A, {P x} + {~P x}) ->
  forall l, {Exists P l} + {~Exists P l}.
Proof using .
intros P Pdec l. induction l as [| x l].
* right. intro Habs. inversion Habs.
* destruct IHl.
  + left. now constructor 2.
  + destruct (Pdec x).
    - left. now constructor.
    - right. intro Habs. inversion_clear Habs; contradiction.
Qed.

Global Instance forallb_compat : Proper ((eq ==> eq) ==> eq ==> eq) (@forallb A).
Proof using .
intros f f' Hf l l' Hl. subst l'. induction l.
- reflexivity.
- simpl. destruct (f a) eqn:Hfa; rewrite <- (Hf a), <- IHl, Hfa; reflexivity.
Qed.

Global Instance existsb_compat (equivA : A -> A -> Prop) : Proper ((equivA ==> equiv) ==> (eqlistA equivA) ==> eq) (@existsb A).
Proof using .
intros f f' Hf l l' Hl. simpl in Hl.
  unfold existsb. 
  induction Hl.
  - reflexivity.
  - rewrite (Hf x x'). case (f' x'). now simpl.
    case ((fix existsb (l0 : list A) : bool :=
        match l0 with
        | nil => false
        | a :: l1 => f a || existsb l1
        end) l) eqn : Hcase;
    rewrite <- IHHl;
    auto.
    auto. 
Qed.

Theorem existsb_forallb : forall (f : A -> bool) l,
  negb (forallb f l) = existsb (fun x => negb (f x)) l.
Proof using .
intros f l. induction l as [| x l].
+ reflexivity.
+ simpl. destruct (f x) eqn:Hfx; simpl.
  - simpl. apply IHl.
  - reflexivity.
Qed.

Lemma forallb_existsb : forall (f : A -> bool) l,
  negb (existsb f l) = forallb (fun x : A => negb (f x)) l.
Proof using .
intros. rewrite <- negb_involutive, existsb_forallb. f_equal.
  induction l as [| x l].
+ reflexivity.
+ simpl. destruct (f x) eqn:Hfx; simpl.
  - reflexivity.
  - simpl. apply IHl.
Qed.

(** ***  Results about [PermutationA]  **)

Global Instance InA_perm_compat : Proper (eqA ==> PermutationA eqA ==> iff) (InA eqA).
Proof using HeqA. intros x y Hxy l1 l2 Hl. now apply InA_compat; try apply PermutationA_equivlistA. Qed.

Lemma Permutation_PermutationA_weak : forall l1 l2, Permutation l1 l2 -> PermutationA eqA l1 l2.
Proof using HeqA. intros ? ? Heq. induction Heq; try now constructor. now transitivity l'. Qed.

Global Instance PermutationA_compat :
  Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (PermutationA eqA).
Proof using HeqA. intros l1 l2 Hl12 l3 l4 Hl34. now rewrite Hl12, Hl34. Qed.

Lemma PermutationA_Leibniz : forall l1 l2 : list A, PermutationA eq l1 l2 <-> Permutation l1 l2.
Proof using .
intros l1 l2. split; intro Hl.
  induction Hl; try now constructor.
    subst. now constructor.
    now transitivity l₂.
  induction Hl; try now constructor. now transitivity l'.
Qed.

Lemma PermutationA_Leibniz_equiv : relation_equivalence (@PermutationA A eq) (@Permutation A).
Proof using . repeat intro. apply PermutationA_Leibniz. Qed.

Lemma PermutationA_subrelation_compat :
  Proper (subrelation ==> eq ==> eq ==> impl) (@PermutationA A).
Proof using .
intros eqA1 eqA2 Hrel l1 l2 H12 l3 l4 H34 Hperm. subst. induction Hperm.
- constructor.
- constructor. now apply Hrel. assumption.
- constructor 3.
- now constructor 4 with l₂.
Qed.

Global Instance eqlistA_PermutationA_subrelation : subrelation (eqlistA eqA) (PermutationA eqA).
Proof using . intros ? ? Heq. induction Heq; constructor; auto. Qed.

Global Instance PermutationA_equivlistA_subrelation :
  subrelation (PermutationA eqA) (equivlistA eqA).
Proof using HeqA. intros l1 l2 Heq x. now rewrite Heq. Qed.

Global Instance PermutationA_eq_compat :
  Proper ((eq ==> eq ==> iff) ==> eq ==> eq ==> iff) (@PermutationA A).
Proof using .
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
Proof using . now intros ? ? ?; apply Permutation_length. Qed.

(* Already exists as Permutation.Permutation_in' *)
Global Instance In_perm_compat : Proper (eq ==> @Permutation A ==> iff) (@In A).
Proof using . intros x y ? l l' Hl. subst. split; apply Permutation_in; assumption || now symmetry. Qed.

Global Instance In_permA_compat : Proper (eq ==> @PermutationA A eq ==> iff) (@In A).
Proof using . repeat intro. rewrite PermutationA_Leibniz in *. now apply In_perm_compat. Qed.

Lemma Forall_Perm_trans : forall (l1 l2 : list A) (P Q : A -> Prop),
  (eq ==> iff)%signature P Q -> Permutation l1 l2 -> List.Forall P l1 -> List.Forall Q l2.
Proof using .
intros l1 l2 P Q HPQ Hperm Hfor. 
rewrite List.Forall_forall in *. intros. rewrite <- (HPQ _ _ eq_refl). 
apply Hfor. revert H. apply Permutation_in. now symmetry.
Qed.

Global Instance Forall_Permutation_compat :
  Proper ((eq ==> iff) ==> @Permutation A ==> iff) (@List.Forall A).
Proof using . repeat intro. split; apply Forall_Perm_trans; easy || (repeat intro; symmetry; auto). Qed.

Corollary Permutation_cons_inside : forall (x : A) l l',
  Permutation (x :: l) l' -> exists l1 l2, Permutation l (l1 ++ l2) /\ l' = l1 ++ x :: l2.
Proof using .
intros x l l' Hperm. destruct (Permutation_in_inside x Hperm) as [l1 [l2 Heql]]. now left.
exists l1. exists l2. split.
- apply Permutation_cons_inv with x. transitivity l'; trivial; [].
  subst. symmetry. apply Permutation_middle.
- assumption.
Qed.

Lemma PermutationA_nil : forall l, PermutationA eqA nil l -> l = nil.
Proof using HeqA.
intros l Hl. destruct l.
  reflexivity.
  exfalso. rewrite <- InA_nil. rewrite (PermutationA_equivlistA HeqA).
    now left.
    eassumption.
Qed.

Lemma PermutationA_InA_inside : forall (x : A) l l',
  PermutationA eqA l l' -> InA eqA x l -> exists l1 y l2, eqA x y /\ l' = l1 ++ y :: l2.
Proof using HeqA. intros x l l' Hperm Hin. rewrite Hperm in Hin. apply (InA_split Hin). Qed.

Theorem PermutationA_ind_bis :
 forall P : list A -> list A -> Prop,
   P nil nil ->
   (forall x₁ x₂ l l', eqA x₁ x₂ -> PermutationA eqA l l' -> P l l' -> P (x₁ :: l) (x₂ :: l')) ->
   (forall x y l l', PermutationA eqA l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', PermutationA eqA l l' -> P l l' ->
                     PermutationA eqA l' l'' -> P l' l'' -> P l l'') ->
   forall l l', PermutationA eqA l l' -> P l l'.
Proof using HeqA.
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
Proof using HeqA.
  set (P l l' := forall a b l1 l2 l3 l4,
                 eqA a b -> l=l1++a::l2 -> l'=l3++b::l4 -> PermutationA eqA (l1++l2) (l3++l4)).
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
Proof using HeqA. intros; exact (PermutationA_app_inv nil l nil l' a H). Qed.

Global Instance PermutationA_length : Proper (PermutationA eqA ==> Logic.eq) (@length A).
Proof using . clear. intros l1 l2 perm. induction perm; simpl; lia. Qed.

Lemma PermutationA_length1 : forall x l,
  PermutationA eqA l (x :: nil) -> exists y, eqA x y /\ l = y :: nil.
Proof using HeqA.
intros x l Hperm. destruct l as [| a [| b l]].
- apply PermutationA_nil in Hperm. discriminate Hperm.
- exists a. assert (Hlength := PermutationA_length Hperm).
  apply PermutationA_InA_inside with a _ _ in Hperm.
    destruct Hperm as [l1 [y [l2 [Heq Hl]]]].
    rewrite Hl in Hlength. rewrite app_length in Hlength. simpl in Hlength.
    assert (Hl1 : length l1 = 0) by lia. assert (Hl2 : length l2 = 0) by lia. clear Hlength.
    destruct l1, l2.
      inversion Hl. now split.
      now inversion Hl.
      discriminate Hl1.
      discriminate Hl2.
    now left.
- apply PermutationA_length in Hperm. simpl in Hperm. lia.
Qed.

Lemma PermutationA_1 : forall x x', PermutationA eqA (x :: nil) (x' :: nil) <-> eqA x x'.
Proof using HeqA.
intros. split; intro Hx.
+ apply PermutationA_length1 in Hx. destruct Hx as [y [Heq Hx]]. inversion_clear Hx. now symmetry.
+ rewrite Hx. reflexivity.
Qed.

Lemma PermutationA_2 : forall x y x' y', PermutationA eqA (x :: y :: nil) (x' :: y' :: nil) <->
  eqA x x' /\ eqA y y' \/ eqA x y' /\ eqA y x'.
Proof using HeqA.
intros. split.
+ generalize (eq_refl (x :: y :: nil)). generalize (x :: y :: nil) at -2. intros l1 Hl1.
  generalize (eq_refl (x' :: y' :: nil)). generalize (x' :: y' :: nil) at -2. intros l2 Hl2 perm.
  revert x y x' y' Hl1 Hl2. induction perm.
  - intros * Hl1 Hl2. inversion Hl1.
  - intros x x' y y' Hl1 Hl2. inv Hl1. inv Hl2.
    rewrite PermutationA_1 in perm. auto.
  - intros x' x'' y' y'' Hl1 Hl2. inv Hl1. inv Hl2. right; split; reflexivity.
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
Proof using eqA HeqA.
intros. split.
+ generalize (eq_refl (x :: y :: z :: nil)).
  generalize (x :: y :: z :: nil) at -2. intros l1 Hl1.
  generalize (eq_refl (x' :: y' :: z' :: nil)).
  generalize (x' :: y' :: z' :: nil) at -2. intros l2 Hl2 perm.
  revert x y z x' y' z' Hl1 Hl2. induction perm; intros.
  - discriminate Hl1.
  - inversion Hl1. inversion Hl2. subst. rewrite PermutationA_2 in perm. intuition.
  - inversion Hl1. inversion Hl2. do 2 subst. inversion H5. intuition.
  - subst. assert (Hlength : length l₂ = length (x' :: y' :: z' :: nil)) by now rewrite perm2.
    destruct l₂ as [| x'' [| y'' [| z'' [| ? ?]]]]; discriminate Hlength || clear Hlength.
    specialize (IHperm1 _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
    specialize (IHperm2 _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
    repeat destruct IHperm2 as [IHperm2 | IHperm2]; destruct IHperm2 as [H21 [H22 H23]];
    rewrite <- H21, <- H22, <- H23; clear perm1 perm2; intuition.
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
Proof using HeqA.
intros x l Hin. induction l; inversion_clear Hin.
+ exists l. now rewrite H.
+ apply IHl in H. destruct H as [l' Hperm]. exists (a :: l'). transitivity (a :: x :: l').
  - now rewrite <- Hperm.
  - constructor 3.
Qed.

Lemma PermutationA_split_dec (eqdec : forall x y : A, {eqA x y} + {~eqA x y}) :
  forall x l, InA eqA x l -> {l' | PermutationA eqA l (x :: l')}.
Proof using HeqA.
intros x l Hin. induction l as [| e l].
* exfalso. now rewrite InA_nil in Hin.
* destruct (eqdec x e).
  + exists l. now constructor.
  + assert (Hl : InA eqA x l). { now inversion_clear Hin. }
    apply IHl in Hl. destruct Hl as [l' Hperm].
    exists (e :: l'). transitivity (e :: x :: l').
    now rewrite <- Hperm.
    constructor 3.
Qed.

Lemma PermutationA_dec (eqdec : forall x y : A, {eqA x y} + {~eqA x y}) :
  forall l1 l2 : list A, {PermutationA eqA l1 l2} + {~PermutationA eqA l1 l2}.
Proof.
intro l1. induction l1 as [| e l1]; intro l2.
* destruct l2.
  + left. constructor.
  + right. abstract (intro Habs; apply PermutationA_nil in Habs; discriminate).
* destruct (InA_dec eqdec e l2) as [He | He].
  + destruct (PermutationA_split_dec eqdec He) as [l' Hl'].
    destruct (IHl1 l') as [Hrec | Hrec].
    - left. abstract (now rewrite Hl'; constructor).
    - right. intro Habs. apply Hrec.
      abstract (rewrite Hl' in Habs; apply (PermutationA_cons_inv Habs)).
  + right. abstract (intro Habs; apply He; rewrite <- Habs; now left).
Defined.

End List_results.

Lemma map_alls {A B} : forall (f : A -> B) pt n, map f (alls pt n) = alls (f pt) n.
Proof using . intros f pt n. induction n. reflexivity. simpl. now rewrite IHn. Qed.

Global Hint Immediate eqlistA_Leibniz_equiv PermutationA_Leibniz_equiv : core.


(** ***  Results about [NoDupA]  **)

Section NoDupA_results.
Context (A B : Type).
Context (eqA eqA' : relation A) (eqB : relation B).
Context (HeqA : Equivalence eqA) (HeqB : Equivalence eqB).

Lemma NoDupA_Leibniz : forall l : list A, NoDupA Logic.eq l <-> NoDup l.
Proof using .
intro l. split; intro Hl; induction l; inversion_clear Hl; constructor;
(now rewrite <- InA_Leibniz in *) || now apply IHl.
Qed.

Lemma NoDupA_2 : forall x y, ~eqA x y -> NoDupA eqA (x :: y :: nil).
Proof using .
intros x y Hdiff. constructor.
  intro Habs. inversion_clear Habs.
    now elim Hdiff.
    inversion H.
  apply NoDupA_singleton.
Qed.

Lemma NoDupA_3 : forall x y z, ~eqA x y -> ~eqA y z -> ~eqA x z -> NoDupA eqA (x :: y :: z :: nil).
Proof using .
intros x y z Hxy Hyz Hxz. constructor.
- intro Habs. rewrite 2 InA_cons, InA_nil in Habs. tauto.
- now apply NoDupA_2.
Qed.

Lemma PermutationA_NoDupA : forall l l', PermutationA eqA l l' -> NoDupA eqA l -> NoDupA eqA l'.
Proof using HeqA.
intros l l' Hperm. induction Hperm; intro Hdup.
+ trivial.
+ inversion_clear Hdup. constructor.
  - intro Habs. apply H0. now rewrite Hperm, H.
  - now apply IHHperm.
+ inversion_clear Hdup. inversion_clear H0. constructor.
  - intros Habs. inversion_clear Habs. apply H. now left. contradiction.
  - constructor. intro Habs. apply H. now right. assumption.
+ auto.
Qed.

Global Instance PermutationA_NoDupA_compat : Proper (PermutationA eqA ==> iff) (NoDupA eqA).
Proof using HeqA. now repeat intro; split; apply PermutationA_NoDupA. Qed.

Lemma NoDupA_strengthen : forall l, subrelation eqA eqA' -> NoDupA eqA' l -> NoDupA eqA l.
Proof using .
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
Proof using HeqA.
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

Lemma NoDupA_dec : (forall x y : A, {eqA x y} + {~eqA x y}) ->
  forall l, {NoDupA eqA l} + {~NoDupA eqA l}.
Proof using .
intros eq_dec l. induction l. now left; constructor.
destruct IHl as [Hbad | Hok].
  destruct (InA_dec eq_dec a l).
    right. intro Habs. inversion_clear Habs. contradiction.
    left. now constructor.
  right. intro Habs. inversion_clear Habs. contradiction.
Qed.

Lemma not_NoDupA : (forall x y, {eqA x y} + {~eqA x y} ) ->
 forall l, ~NoDupA eqA l <-> exists (x : A) l', PermutationA eqA l (x :: x :: l').
Proof using HeqA.
intros eq_dec l. split; intro Hl.
* induction l.
  + elim Hl. now constructor.
  + destruct (InA_dec eq_dec a l) as [Hin | Hnin].
    - exists a. apply (PermutationA_split _) in Hin.
      destruct Hin as [l' Hperm]. exists l'. now rewrite Hperm.
    - destruct IHl as [x [l' Hperm]].
      ++ intro Habs. apply Hl. now constructor.
      ++ exists x. exists (a :: l'). rewrite Hperm. transitivity (x :: a :: x :: l').
         -- now constructor.
         -- apply PermutationA_cons. reflexivity. now constructor.
* destruct Hl as [x [l' Hperm]]. rewrite Hperm. intro Habs. inv Habs. apply H1. now left.
Qed.

End NoDupA_results.

Lemma Permutation_NoDup {A : Type} : forall l l', @Permutation A l l' -> NoDup l -> NoDup l'.
Proof using .
intros ? ?. rewrite <- PermutationA_Leibniz. do 2 rewrite <- NoDupA_Leibniz.
apply PermutationA_NoDupA; autoclass.
Qed.

(* Already exists as [Permutation.Permutation_NoDup'] *)
Global Instance Permutation_NoDup_compat {A : Type} : Proper (@Permutation A ==> iff) (@NoDup A).
Proof using . repeat intro. now split; apply Permutation_NoDup. Qed.

(** ***  Results about [filter]  **)

Section Filter_results.
Context {A : Type}.
Context {eqA : relation A}.
Context {HeqA : Equivalence eqA}.

Global Instance filter_PermutationA_compat : forall f, Proper (eqA ==> eq) f ->
  Proper (PermutationA eqA ==> PermutationA eqA) (@filter A f).
Proof using HeqA.
intros f Hf l1 l2 Hperm. pattern l1, l2.
apply (PermutationA_ind_bis _); easy || simpl; clear l1 l2 Hperm.
+ intros x y l1 l2 Hxy Hperm Hrec. destruct (f x) eqn:Hfx;
  rewrite (Hf _ _ Hxy) in Hfx; now rewrite Hfx, ?Hxy, Hrec.
+ intros x y l1 l2 Hperm Hrec. destruct (f x), (f y); rewrite Hrec; easy || now constructor; auto.
+ intros l1 l2 l3 Hperm12 Hrec12 Hperm23 Hrec23. now rewrite Hrec12.
Qed.

Global Instance filter_extensionality_compat : Proper ((eq ==> eq) ==> eq ==> eq) (@filter A).
Proof using .
intros f g Hfg ? l ?; subst. induction l as [| x l]; simpl.
+ trivial.
+ destruct (f x) eqn:Hfx; rewrite (Hfg _ _ (reflexivity _)) in Hfx; now rewrite Hfx, IHl.
Qed.

Global Instance filter_extensionalityA_compat :
  Proper ((eqA ==> Logic.eq) ==> eqlistA eqA ==> eqlistA eqA) (@filter A).
Proof using HeqA.
intros f g Hfg l1. induction l1 as [| x l1]; intros l2 Hl; simpl.
+ inv Hl. reflexivity.
+ destruct l2 as [| y l2]; inv Hl; [].
  match goal with H : eqA x y |- _ => specialize (Hfg _ _ H) end. rewrite Hfg.
  simpl. destruct (g y); try constructor; auto.
Qed.

Lemma filter_twice : forall f (l : list A), filter f (filter f l) = filter f l.
Proof using .
intros f l. induction l as [| e l]; simpl; auto.
destruct (f e) eqn:Hfe; simpl; try rewrite Hfe; rewrite IHl; auto.
Qed.

Lemma filter_comm : forall f g (l : list A), filter f (filter g l) = filter g (filter f l).
Proof using .
intros f g l. induction l as [| x l]; simpl.
+ reflexivity.
+ destruct (f x) eqn:Hfx, (g x) eqn:Hgx; simpl; rewrite ?Hfx, ?Hgx, IHl; reflexivity.
Qed.

Lemma filter_weakened : forall f g (l : list A),
  (forall x, List.In x l -> f x = true -> g x = true) ->
  filter g (filter f l) = filter f l.
Proof using .
intros f g l Hfg. induction l as [| x l].
+ reflexivity.
+ simpl. destruct (f x) eqn:Hfx.
  - simpl. rewrite Hfg; trivial; try (now left); [].
    f_equal. apply IHl. intros. apply Hfg; trivial; now right.
  - apply IHl. intros. apply Hfg; trivial; now right.
Qed.

Corollary filter_weakenedA : forall f g l,
  (forall x, InA eqA x l -> f x = true -> g x = true) ->
  filter g (filter f l) = filter f l.
Proof using HeqA. intros * Hin. apply filter_weakened. intros. apply Hin; trivial; []. now apply In_InA. Qed.

Lemma filter_inclA : forall f, Proper (eqA ==> eq) f -> forall l, inclA eqA (filter f l) l.
Proof using . intros f Hf l x Hin. now rewrite filter_InA in Hin. Qed.

Lemma filter_incl : forall f (l : list A), incl (filter f l) l.
Proof using . intros f l x Hin. now rewrite filter_In in Hin. Qed.

Lemma filter_app : forall f (l1 l2 : list A), filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof using .
intros f l1 l2. induction l1 as [| x l1]; simpl.
+ reflexivity.
+ destruct (f x); now rewrite IHl1.
Qed.

Lemma NoDupA_filter_compat : forall f, Proper (eqA ==> eq) f ->
  forall l, NoDupA eqA l -> NoDupA eqA (filter f l).
Proof using .
intros f Hf l Hnodup. induction Hnodup; simpl.
- constructor.
- destruct (f x) eqn:Hfx; trivial. constructor; trivial. rewrite filter_InA; intuition.
Qed.

Lemma filter_andb : forall f g (l : list A),
  filter (fun x => f x && g x) l = filter f (filter g l).
Proof using .
intros f g l. induction l as [| x l]; simpl.
+ reflexivity.
+ destruct (f x) eqn:Hfx, (g x) eqn:Hgx; simpl; rewrite ?Hfx, ?Hgx, IHl; reflexivity.
Qed.

End Filter_results.


(** ***  Results about [inclA]  **)

Section inclA_results.
Context (A B : Type).
Context (eqA : relation A).
Context (HeqA : Equivalence eqA).
Context (eq_dec : forall x y : A, {eqA x y} + {~eqA x y}).

Lemma inclA_Leibniz : forall l1 l2 : list A, inclA Logic.eq l1 l2 <-> incl l1 l2.
Proof using . intros. unfold inclA, incl. setoid_rewrite InA_Leibniz. reflexivity. Qed.

Global Instance inclA_compat : Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (inclA eqA).
Proof using HeqA. intros ? ? Hl1 ? ? Hl2. unfold inclA. setoid_rewrite Hl1. now setoid_rewrite Hl2. Qed.

Lemma inclA_nil : forall l, inclA eqA l nil -> l = nil.
Proof using HeqA. intros [| x l] Hin; trivial. specialize (Hin x ltac:(now left)). inversion Hin. Qed.

Lemma inclA_cons_inv : forall x l1 l2, ~InA eqA x l1 ->
  inclA eqA (x :: l1) (x :: l2) -> inclA eqA l1 l2.
Proof using HeqA.
intros x l1 l2 Hx Hincl y Hin1.
assert (Hin2 : InA eqA y (x :: l2)). { apply Hincl. now right. }
inversion_clear Hin2; trivial. rewrite <- H in Hx. contradiction.
Qed.

Lemma inclA_skip: forall (x : A) (l1 l2 : list A),
  ~ InA eqA x l1 -> inclA eqA l1 (x :: l2) -> inclA eqA l1 l2.
Proof using HeqA.
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
Proof using .
  unfold inclA.
  split;auto.
Qed.

Lemma inclA_cons_InA : forall (x : A) (l1 l2 : list A),
  InA eqA x l2 -> inclA eqA l1 (x::l2) -> inclA eqA l1 l2.
Proof using HeqA.
  intros x l1 l2 Hin Hincl.
  unfold inclA in *.
  intros x' Hin'.
  apply Hincl in Hin'.
  inversion_clear Hin'.
  + now rewrite H.
  + assumption.
Qed.

Lemma not_inclA : forall l1 l2, ~inclA eqA l1 l2 <-> exists x, InA eqA x l1 /\ ~InA eqA x l2.
Proof using HeqA eq_dec.
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
Proof using . intros l1 l2. unfold inclA_bool. destruct (inclA_dec l1 l2); intuition discriminate. Qed.

Lemma inclA_bool_false_iff : forall l1 l2, inclA_bool l1 l2 = false <-> ~inclA eqA l1 l2.
Proof using . intros l1 l2. unfold inclA_bool. destruct (inclA_dec l1 l2); intuition discriminate. Qed.

Global Instance inclA_bool_compat :
  Proper (PermutationA eqA ==> PermutationA eqA ==> eq) (inclA_bool).
Proof using .
intros l1 l1' Hl1 l2 l2' Hl2. unfold inclA_bool.
destruct (inclA_dec l1 l2), (inclA_dec l1' l2'); trivial; rewrite ?Hl1, ?Hl2 in *; contradiction.
Qed.

Lemma NoDupA_inclA_length : forall l1 l2,
  NoDupA eqA l1 -> inclA eqA l1 l2 -> length l1 <= length l2.
Proof using HeqA.
intro l1. induction l1 as [| a l1]; intros l2 Hnodup Hincl.
+ simpl. lia.
+ assert (Hin : InA eqA a l2). { apply Hincl. now left. }
  apply (PermutationA_split _) in Hin. destruct Hin as [l2' Heql2]. 
  rewrite Heql2 in *. inversion_clear Hnodup.
  apply inclA_cons_inv in Hincl; trivial. simpl. apply le_n_S. now apply IHl1.
Qed.

Lemma NoDupA_inclA_length_PermutationA : forall l1 l2, NoDupA eqA l1 -> NoDupA eqA l2 ->
  inclA eqA l1 l2 -> length l2 <= length l1 -> PermutationA eqA l1 l2.
Proof using HeqA.
intro l1. induction l1 as [| x l1]; intros l2 Hnodup1 Hnodup2 Hincl Hlen.
+ destruct l2; try reflexivity. cbn in *. lia.
+ assert (Hin : InA eqA x l2). { apply Hincl. now left. }
  apply (PermutationA_split _) in Hin. destruct Hin as [l2' Heql2]. 
  rewrite Heql2 in *. constructor; try reflexivity.
  inversion_clear Hnodup1. inversion_clear Hnodup2.
  apply inclA_cons_inv in Hincl; trivial. apply IHl1; auto. cbn in *. lia.
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
Proof using .
intros l1. induction l1; intros l2 x; simpl.
- reflexivity.
- destruct (eq_dec a x); now rewrite IHl1.
Qed.

Global Instance countA_occ_compat : Proper (eqA ==> PermutationA eqA ==> eq) (countA_occ).
Proof using HeqA.
intros a b Hab l. induction l as [| x l]; intros [| x' l'] Hl.
+ reflexivity.
+ apply (PermutationA_nil _) in Hl. discriminate Hl.
+ symmetry in Hl. apply (PermutationA_nil _) in Hl. discriminate Hl.
+ assert (Hperm := @PermutationA_InA_inside _ _ _ x _ _ Hl).
  destruct Hperm as [l1 [y [l2 [Hxy Heql]]]]; try now left.
  rewrite Heql in *. rewrite Hxy, <- (PermutationA_middle _) in Hl.
  apply (PermutationA_cons_inv _), IHl in Hl. simpl.
  rewrite Hl. repeat rewrite countA_occ_app. simpl.
  destruct (eq_dec x a) as [Hx | Hx], (eq_dec y b) as [Hy | Hy]; try lia.
  - elim Hy. now rewrite <- Hxy, <- Hab.
  - elim Hx. now rewrite Hxy, Hab.
Qed.

Lemma countA_occ_alls_in : forall x n, countA_occ x (alls x n) = n.
Proof using HeqA.
intros x n. induction n; simpl; trivial.
destruct (eq_dec x x) as [| Hneq]. now rewrite IHn. now elim Hneq.
Qed.

Lemma countA_occ_alls_out : forall x y n, ~eqA x y -> countA_occ y (alls x n) = 0%nat.
Proof using . intros x y n Hxy. induction n; simpl; trivial; now destruct (eq_dec x y). Qed.

Lemma countA_occ_pos : forall x l, countA_occ x l > 0 <-> InA eqA x l.
Proof using HeqA.
intros x l. induction l as [| a l]; simpl.
+ split; intro Habs.
  - lia.
  - rewrite InA_nil in Habs. elim Habs.
+ destruct (eq_dec a x) as [Heq | Heq].
  - split; intro; lia || now left.
  - rewrite IHl. split; intro Hin; try now right; [].
    inversion_clear Hin; trivial. now elim Heq.
Qed.

Lemma countA_occ_length_le : forall l (x : A), countA_occ x l <= length l.
Proof using .
intros l x. induction l; simpl.
  reflexivity.
  destruct (eq_dec a x); lia.
Qed.

Lemma countA_occ_partition : forall f, Proper (eqA ==> eq) f -> forall l x,
  countA_occ x l = countA_occ x (fst (partition f l)) + countA_occ x (snd (partition f l)).
Proof using .
intros f Hf l. induction l as [| a l].
* intro. reflexivity.
* intro x. destruct (f a) eqn:Hfa.
  + apply (partition_cons1 f a l (surjective_pairing (partition f l))) in Hfa. rewrite Hfa. simpl.
    destruct (eq_dec a x) as [Heq | Heq].
    - rewrite IHl. lia.
    - apply IHl.
  + apply (partition_cons2 f a l (surjective_pairing (partition f l))) in Hfa. rewrite Hfa. simpl.
    destruct (eq_dec a x) as [Heq | Heq].
    - rewrite IHl. lia.
    - apply IHl.
Qed.

Lemma countA_occ_filter : forall f, Proper (eqA ==> eq) f ->
  forall l x, countA_occ x (filter f l) = if f x then countA_occ x l else 0.
Proof using .
intros f Hf l x. induction l as [| y l]; simpl.
+ now destruct_match.
+ destruct (f x) eqn:Hfx, (f y) eqn:Hfy; simpl;
  destruct (eq_dec y x) as [Heq | Heq]; rewrite IHl;
  reflexivity || apply Hf in Heq; congruence.
Qed.

Theorem countA_occ_spec : forall x l n,
  countA_occ x l = n <-> PermutationA eqA l (alls x n ++ removeA eq_dec x l).
Proof using HeqA.
intros x l. induction l as [| a l]; intro n; simpl.
* rewrite app_nil_r. split; intro Heq.
  + subst. simpl. reflexivity.
  + apply PermutationA_nil in Heq; autoclass; now destruct n.
* destruct (eq_dec a x) as [Heq | Heq].
  + split; intro Hn.
    - destruct n as [| n]; try lia; [].
      apply eq_add_S in Hn. rewrite IHl in Hn.
      simpl. constructor; trivial; [].
      destruct_match; auto; now symmetry in Heq.
    - destruct (eq_dec x a); try (now symmetry in Heq); [].
      assert (n <> 0).
      { intro. subst. simpl in Hn. assert (Hin : InA eqA a (a :: l)) by now left.
        rewrite Hn, removeA_InA in Hin; autoclass; tauto. }
      destruct n as [| n]; try lia; [].
      f_equal. rewrite IHl. simpl in Hn. rewrite <- Heq in Hn at 1.
      apply PermutationA_cons_inv in Hn; autoclass.
  + rewrite IHl. destruct (eq_dec x a); try (now elim Heq); [].
    rewrite <- PermutationA_middle; autoclass; [].
    split; intro Hperm.
    - now constructor.
    - now apply PermutationA_cons_inv in Hperm.
Qed.

Corollary PermutationA_count_split : forall x l,
  PermutationA eqA l (alls x (countA_occ x l) ++ removeA eq_dec x l).
Proof using HeqA. intros. now rewrite <- countA_occ_spec. Qed.

End CountA.

Lemma countA_occ_map {A B} (eqA : relation A) (eqB : relation B) Aeq_dec Beq_dec :
  forall (f : A -> B), Proper (eqA ==> eqB) f -> injective eqA eqB f ->
  forall x l, countA_occ eqB Beq_dec (f x) (map f l) = countA_occ eqA Aeq_dec x l.
Proof using .
intros f Hf Hinj x l. induction l as [| y l].
+ reflexivity.
+ simpl. do 2 destruct_match; simpl; rewrite IHl; intuition.
Qed.

(** ***  Results about [firstn] and [skipn]  **)

Section List_halves.
Variable A : Type.

Lemma skipn_nil : forall k, skipn k (@nil A) = nil.
Proof using . now intros []. Qed.

Theorem skipn_length : forall (l : list A) n, length (skipn n l) = length l - n.
Proof using .
induction l.
- now intros [| n].
- intros [| n]; trivial. simpl. apply IHl.
Qed.

Lemma firstn_In : forall (l : list A) n, incl (firstn n l) l.
Proof using .
induction l; intros n x Hin.
+ destruct n; elim Hin.
+ destruct n; try now elim Hin. simpl in Hin. destruct Hin.
  - subst. now left.
  - right. now apply IHl in H.
Qed.

Lemma firstn_add_hd : forall n l (a : A), firstn (S n) (a :: l) =  a :: firstn n l.
Proof using . reflexivity. Qed.

Lemma firstn_add_tl_In : forall n l (x a : A),
  In x (firstn n l) -> In x (firstn n (l ++ a :: nil)).
Proof using .
induction n; intros l x a Hin; simpl in *.
- assumption.
- destruct l as [| b l]; simpl in *; solve [elim Hin | intuition].
Qed.

Lemma firstn_add_tl : forall l n (a : A), n <= length l -> firstn n (l ++ a :: nil) = firstn n l.
Proof using .
intro l. induction l as [| e l]; intros n a Hle.
+ now inversion_clear Hle.
+ destruct n; simpl in *.
  - reflexivity.
  - f_equal. apply IHl. lia.
Qed.

Lemma firstn_NoDup : forall (l : list A) n, NoDup l -> NoDup (firstn n l).
Proof using .
intros l. induction l as [| e l]; intros n Hnodup.
+ now destruct n; compute.
+ destruct n; try now constructor. simpl.
  inversion_clear Hnodup as [| ? ? Helt Hnodup']. constructor.
  - intro Hin. apply Helt. apply (firstn_In l n e Hin).
  - auto.
Qed.

Lemma skipn_In : forall (l : list A) n, incl (skipn n l) l.
Proof using .
induction l; intros n x Hin.
+ destruct n; elim Hin.
+ destruct n; try now elim Hin. simpl in Hin. apply IHl in Hin. now right.
Qed.

Lemma In_skipn : forall l l' (pt : A) n, n <= length l -> In pt (skipn n (l ++ pt :: l')).
Proof using .
intros l l' pt. generalize (Nat.le_refl (length l)). generalize l at -2. induction l; simpl.
* intros [| x l] Hl [| n] ?; simpl in *; try tauto || lia.
* intros [| x l''] Hl'' n Hn; simpl in *; try tauto.
  + destruct n; simpl; tauto || lia.
  + destruct n; simpl.
    - right. change (In pt (skipn 0 (l'' ++ pt :: l'))). apply IHl; lia.
    - apply IHl; lia.
Qed.

Lemma skipn_add_hd : forall n l (a : A), skipn (S n) (a :: l) = skipn n l.
Proof using . reflexivity. Qed.

Lemma skipn_add_tl_In : forall n l (x a : A), In x (skipn n l) -> In x (skipn n (l ++ a :: nil)).
Proof using .
induction n; intros l x a Hin; simpl in *.
- rewrite in_app_iff. now left.
- destruct l as [| b l]; simpl in *; solve [elim Hin | auto].
Qed.

Lemma In_skipn_add : forall l (pt : A), In pt (skipn (Nat.div2 (length l)) (l ++ pt :: nil)).
Proof using . intros. apply In_skipn. apply Nat.div2_decr. lia. Qed.

Lemma skipn_add_tl : forall l n (a : A), n <= length l ->
  skipn n (l ++ a :: nil) = skipn n l ++ a :: nil.
Proof using .
intro l. induction l as [| e l]; intros n a Hle; simpl in *.
+ now inversion_clear Hle.
+ destruct n; simpl in *.
  - reflexivity.
  - apply IHl. lia.
Qed.

Lemma skipn_NoDup : forall (l : list A) n, NoDup l -> NoDup (skipn n l).
Proof using .
intro l. induction l as [| e l]; intros n Hnodup.
- destruct n; constructor.
- destruct n; auto. simpl. apply IHl. now inversion_clear Hnodup.
Qed.

Lemma firstn_skipn_nodup_exclusive : forall l : list A, NoDup l ->
  forall n e, In e (firstn n l) -> In e (skipn n l) -> False.
Proof using .
intros l Hnodup n. rewrite <- (firstn_skipn n) in Hnodup.
rewrite <- NoDupA_Leibniz, NoDupA_app_iff in Hnodup; autoclass.
destruct Hnodup as [Hleft [Hright Hboth]]. now setoid_rewrite InA_Leibniz in Hboth.
Qed.

Lemma firstn_map_swap : forall {B} (f : A -> B) k l, firstn k (map f l) = map f (firstn k l).
Proof using . intros B f k. induction k; intros [| x l]; simpl; now try rewrite IHk. Qed.

Lemma skipn_map_swap : forall {B} (f : A -> B) k l, skipn k (map f l) = map f (skipn k l).
Proof using . intros B f k. induction k; intros [| x l]; simpl; now try rewrite IHk. Qed.

(** ***  Cutting a list in two halves: [half1] and [half2]  **)

Definition half1 (l : list A) := firstn (Nat.div2 (length l)) l.
Definition half2 (l : list A) := skipn  (Nat.div2 (length l)) l.

Lemma half1_length : forall l : list A, length (half1 l) = div2 (length l).
Proof using .
  intros.
  unfold half1.
  rewrite firstn_length.
  rewrite min_l;auto.
  apply Nat.div2_decr.
  lia.
Qed.

Corollary half2_length : forall l, length (half2 l) = length l - div2 (length l).
Proof using . intros. unfold half2. now rewrite skipn_length. Qed.

Corollary half2_even_length : forall l, Nat.Even (length l) -> length (half2 l) = div2 (length l).
Proof using . intros l H. unfold half2. rewrite skipn_length. apply even_div2 in H. lia. Qed.

Lemma merge_halves : forall l : list A, half1 l ++ half2 l = l.
Proof using . intro. apply firstn_skipn. Qed.

Lemma half1_incl : forall l : list A, incl (half1 l) l.
Proof using . intros ? ? ?. rewrite <- merge_halves. apply in_app_iff. tauto. Qed.

Lemma half2_incl : forall l : list A, incl (half2 l) l.
Proof using . intros ? ? ?. rewrite <- merge_halves. apply in_app_iff. tauto. Qed.

Lemma half1_cons2 : forall (e e' : A) l, half1 (e :: l ++ e' :: nil) = e :: half1 l.
Proof using .
intros e e' l. unfold half1 at 1. simpl. rewrite app_length, Nat.add_comm. simpl.
f_equal. apply firstn_add_tl. apply Nat.div2_decr. lia.
Qed.

Lemma half2_cons2 : forall (e e' : A) l, half2 (e :: l ++ e' :: nil) = half2 l ++ e' :: nil.
Proof using .
intros e e' l. unfold half2 at 1. simpl. rewrite app_length, Nat.add_comm. simpl.
apply skipn_add_tl. apply Nat.div2_decr. lia.
Qed.

Lemma half1_dec : (forall x y : A, {x = y} + {x <> y}) ->
  forall (e : A) l, {In e (half1 l)} + {~In e (half1 l)}.
Proof using . intros. now apply List.In_dec. Qed.

Lemma half2_dec : (forall x y : A, {x = y} + {x <> y}) ->
  forall (e : A) l, {In e (half2 l)} + {~In e (half2 l)}.
Proof using . intros. now apply List.In_dec. Qed.

Theorem half_dec : (forall x y : A, {x = y} + {x <> y}) ->
  forall l e, In e l -> {In e (half1 l)} + {In e (half2 l)}.
Proof.
intros HeqA l e Hin. destruct (half1_dec HeqA e l) as [? | Hg].
+ left. assumption.
+ right. abstract (rewrite <- merge_halves in Hin; apply List.in_app_or in Hin; tauto).
Defined.

Corollary incl_nil : forall (l : list A), incl l nil -> l = nil.
Proof using . intros l. rewrite <- inclA_Leibniz. apply (inclA_nil _). Qed.

Corollary NoDup_dec : (forall x y : A, {x = y} + {~x = y}) ->
  forall l : list A, {NoDup l} + {~NoDup l}.
Proof using . intros eq_dec l. destruct (NoDupA_dec _ eq_dec l); rewrite NoDupA_Leibniz in *; auto. Qed.

(** Induction on first and last elements of a list. *)

Lemma first_last_ind_aux : forall P : list A -> Prop,
  P nil ->
  (forall x, P (x :: nil)) ->
  (forall x y l, P l -> P ((x :: l) ++ (y :: nil))) ->
  forall l l' : list A, length l' <= length l -> P l'.
Proof using .
intros P Pnil Pone Prec l. induction l as [| x l]; intros l' Hlength.
* destruct l'. apply Pnil. simpl in Hlength. lia.
* destruct l as [| x' l].
  + destruct l' as [| ? [| ? ?]]; apply Pnil || apply Pone || simpl in Hlength; lia.
  + destruct l' as [| ? [| ? ?]]; try apply Pnil || apply Pone.
    destruct (@exists_last _ (a0 :: l0)) as [l2 [ y Hy]]; try discriminate.
    rewrite Hy. apply Prec. apply IHl. transitivity (length (l2 ++ y :: nil)).
    - rewrite app_length. lia.
    - rewrite Hy in Hlength. simpl in *. lia.
Qed.

Theorem first_last_ind : forall P : list A -> Prop, P nil -> (forall x, P (x :: nil)) ->
  (forall x y l, P l -> P ((x :: l) ++ (y :: nil))) -> forall l : list A, P l.
Proof using . intros P Pnil Pone Prec l. now apply first_last_ind_aux with l. Qed.

Corollary first_last_even_ind : forall P : list A -> Prop, P nil ->
  (forall x y l, Nat.Even (length l) -> P l -> P ((x :: l) ++ (y :: nil))) ->
  forall l, Nat.Even (length l) -> P l.
Proof using .
intros P Pnil Prec l. pattern l. apply first_last_ind; clear l.
+ auto.
+ simpl. intros x Habs. inversion Habs. lia.
+ intros x y l Hrec Hlen. rewrite app_length, Nat.add_comm in Hlen.
  simpl in Hlen. destruct Hlen as [n Hlen].
  apply Prec, Hrec; exists (pred n); lia.
Qed.

End List_halves.

(** ***  Computing the max value of a real-valued function on a list  **)

Require Import Rbase Rbasic_fun.
Open Scope R_scope.

Section FoldRight.
Context {A B : Type}.
Context {eqA : relation A} {eqB : relation B}.
Context {HeqA : Equivalence eqA} {HeqB : Equivalence eqB}.

Global Instance fold_right_compat :
  Proper ((eqA ==> eqB ==> eqB) ==> eqB ==> eqlistA eqA ==> eqB) (@fold_right B A).
Proof using .
intros f1 f2 Hf i1 i2 Hi l1 l2 Hl. revert i1 i2 Hi.
induction Hl; intros i1 i2 Hi; simpl.
+ assumption.
+ now apply Hf, IHHl.
Qed.

Global Instance fold_right_symmetry_PermutationA : forall (f : A -> B -> B),
  Proper (eqA ==> eqB ==> eqB) f -> (forall x y z, eqB (f y (f x z)) (f x (f y z))) ->
  Proper (eqB ==> PermutationA eqA ==> eqB) (fold_right f).
Proof using HeqA HeqB.
intros f Hf Hfcomm i1 i2 Hi l1 l2 perm. revert i1 i2 Hi.
induction perm; intros i1 i2 Hi; simpl.
- assumption.
- now apply Hf, IHperm.
- now rewrite Hfcomm, Hi.
- etransitivity. now apply IHperm1. now apply IHperm2.
Qed.
End FoldRight.

Section FunMaxList.
Context {A : Type}.
Context `{EqDec A}.

Definition max_list f (l : list A) : R :=
  fold_right (fun pt max => Rmax (f pt) max) 0%R l.

Lemma max_list_aux_min : forall (f : A -> R) l r,
  (r <= fold_right (fun pt max => Rmax (f pt) max) r l)%R.
Proof using .
intros f l. induction l; intro r; simpl.
+ reflexivity.
+ rewrite Rmax_Rle. now right.
Qed.

Corollary max_list_nonneg : forall f l, 0 <= max_list f l.
Proof using . intros. now apply max_list_aux_min. Qed.

Corollary max_list_aux_eq : forall f l r, 0 <= r ->
  fold_right (fun pt max => Rmax (f pt) max) r l = Rmax r (max_list f l).
Proof using .
intros f l r Hr. induction l; simpl.
+ symmetry. now apply Rmax_left.
+ setoid_rewrite IHl. now rewrite Rmax_assoc, (Rmax_comm _ r), Rmax_assoc.
Qed.

Lemma max_list_app : forall f l1 l2, max_list f (l1 ++ l2) = Rmax (max_list f l1) (max_list f l2).
Proof using .
intros f l1 l2.
unfold max_list. rewrite fold_right_app, max_list_aux_eq.
+ apply Rmax_comm.
+ apply max_list_aux_min.
Qed.

Lemma max_list_alls : forall f pt n, n <> 0%nat -> max_list f (alls pt n) = Rmax (f pt) 0.
Proof using .
intros f pt n Hn. induction n as [| n]; try tauto; [].
destruct (Nat.eq_dec n 0) as [Heq | Heq].
+ subst. simpl. reflexivity.
+ specialize (IHn Heq). simpl. setoid_rewrite IHn.
  rewrite Rmax_assoc, (Rmax_left (f pt)); auto; reflexivity.
Qed.

Instance max_list_compat_aux : Proper ((equiv ==> eq) ==> PermutationA equiv ==> eq) max_list.
Proof using .
intros f g Hfg l1 l2 Hl. unfold max_list.
assert (Heq : (equiv ==> eq ==> eq)%signature (fun pt max => Rmax (f pt) max)
                                              (fun pt max => Rmax (g pt) max)).
{ intros i1 i2 Hi m1 m2 Hm. subst. f_equal. now apply Hfg. }
assert (Hg : Proper (equiv ==> eq) g).
{ intros x y Hxy. transitivity (f x).
  - symmetry. now apply Hfg.
  - now apply Hfg. }
rewrite (fold_right_compat Heq 0 0 (reflexivity 0) (reflexivity l1)).
clear f Hfg Heq. revert l2 Hl.
apply fold_right_symmetry_PermutationA.
+ intros ? ? Heq ? ? ?. subst. f_equal. now rewrite Heq.
+ intros. now rewrite 2 Rmax_assoc, (Rmax_comm _ (g _)).
+ reflexivity.
Qed.

Instance max_list_compat : Proper ((equiv ==> eq) ==> equivlistA equiv ==> eq) max_list.
Proof using H.
intros f g Hfg l1.
assert (Hf : Proper (equiv ==> eq) f).
{ intros x y Hxy. transitivity (g y).
  - now apply Hfg.
  - symmetry. now apply Hfg. }
assert (Hg : Proper (equiv ==> eq) g).
{ intros x y Hxy. transitivity (f x).
  - symmetry. now apply Hfg.
  - now apply Hfg. }
revert g Hg Hfg. induction l1 as [| e1 l1]; intros g Hg Hfg l2 Hl.
* assert (l2 = nil). { symmetry in Hl. apply (equivlistA_nil_eq _ _ Hl). }
  subst. simpl. reflexivity.
* assert (l2 <> nil). { intro. subst. apply equivlistA_cons_nil in Hl; autoclass. }
  assert (Hin : InA equiv e1 l2). { rewrite <- Hl. now left. }
  destruct (InA_dec equiv_dec e1 l1) as [Hagain | Hagain].
  + assert (Hequiv : equivlistA equiv l1 l2).
    { intro r. rewrite <- Hl. split; intro Hr.
      - now right.
      - inv Hr; trivial; []. revert_one equiv. intro Heq. now rewrite Heq. }
    rewrite <- (IHl1 _ Hg Hfg _ Hequiv). symmetry. apply (IHl1 _ Hf Hf).
    intro r. split; intro Hr.
    - now right.
    - inv Hr; trivial; []. revert_one equiv. intro Heq. now rewrite Heq.
  + assert (Hl2 := PermutationA_count_split _ equiv_dec e1 l2).
    assert (Hequiv := removeA_equivlistA _ equiv_dec Hagain Hl).
    rewrite (max_list_compat_aux Hg Hl2).
    rewrite max_list_app, max_list_alls.
    - rewrite <- (IHl1 _ Hg Hfg _ Hequiv). simpl.
      rewrite <- Rmax_assoc, (Rmax_right 0); try apply max_list_nonneg; [].
      f_equal. apply Hfg. reflexivity.
    - rewrite <- (countA_occ_pos _ equiv_dec) in Hin; autoclass. lia.
Qed.

Lemma max_list_le : forall f, Proper (equiv ==> eq) f ->
  forall l pt, InA equiv pt l -> f pt <= max_list f l.
Proof using .
intros f Hf l pt Hin.
induction l as [| e l].
+ now rewrite InA_nil in *.
+ simpl. inv Hin.
  - match goal with H : _ == _ |- _ => rewrite H end.
    apply Rmax_l.
  - unfold max_list in *. simpl.
    eapply Rle_trans; [now apply IHl | apply Rmax_r].
Qed.

Lemma max_list_ex : forall f l, l <> nil ->
  exists pt, InA equiv pt l /\ max_list f l = Rmax (f pt) 0.
Proof using .
intros f l Hl. induction l as [| pt l].
* now elim Hl.
* destruct (nil_or_In_dec l) as [? | Hin].
  + subst l. exists pt. split; eauto; now left.
  + assert (Hnil : l <> nil). { intro. subst. destruct Hin as [? []]. }
    destruct (IHl Hnil) as [pt' [Hin' Heq]].
    simpl. rewrite Heq. clear Heq.
    destruct (Rle_dec (f pt') (f pt)) as [Hle | Hle].
    - exists pt. split; try (now left); [].
      now rewrite Rmax_assoc, (Rmax_left _ (f pt')).
    - exists pt'. split; auto; [].
      rewrite Rmax_assoc, (Rmax_right _ (f pt')); lra.
Qed.

Lemma max_list_eq_0 : forall f, Proper (equiv ==> eq) f -> (forall x, 0 <= f x) ->
  forall l, max_list f l = 0%R <-> forall x, InA equiv x l -> f x = 0.
Proof using .
intros f Hf Hfle l. destruct l as [| pt l].
* cbn. setoid_rewrite InA_nil. tauto.
* split; intro Hprop.
  + intros x Hin. assert (Hle := max_list_le Hf Hin).
    rewrite Hprop in Hle. symmetry. now apply antisymmetry.
  + destruct (@max_list_ex f (pt :: l) ltac:(discriminate)) as [? [Hin Heq]].
    apply Hprop in Hin. rewrite Heq, Hin, Rmax_left; reflexivity.
Qed.

End FunMaxList.
Close Scope R_scope.

(** ***  To sort out  **)

Section ToSortOut_results.
Context {A B : Type}.
Context {eqA eqA' : relation A} {eqB : relation B}.
Context {HeqA : Equivalence eqA} {HeqB : Equivalence eqB}.

Global Instance fold_left_compat :
  Proper ((eqB ==> eqA ==> eqB) ==> eqlistA eqA ==> eqB ==> eqB) (@fold_left B A).
Proof using .
intros f1 f2 Hf l1 l2 Hl.
induction Hl; intros i1 i2 Hi; simpl.
+ assumption.
+ now apply IHHl, Hf.
Qed.

Global Instance fold_left_start : forall f, Proper (eqB ==> eqA ==> eqB) f ->
  forall l, Proper (eqB ==> eqB) (fold_left f l).
Proof using HeqA. intros. now apply fold_left_compat. Qed.

Global Instance fold_left_symmetry_PermutationA : forall (f : B -> A -> B),
  Proper (eqB ==> eqA ==> eqB) f -> (forall x y z, eqB (f (f z x) y) (f (f z y) x)) ->
  Proper (PermutationA eqA ==> eqB ==> eqB) (fold_left f).
Proof using HeqA HeqB.
intros f Hf Hfcomm l1 l2 perm. induction perm; intros i1 i2 Hi; simpl.
- assumption.
- now apply IHperm, Hf.
- now rewrite Hfcomm, Hi.
- etransitivity. now apply IHperm1. now apply IHperm2.
Qed.

Lemma HdRel_app : forall l1 l2 R (a : A), HdRel R a l1 -> HdRel R a l2 -> HdRel R a (l1++l2).
Proof using . induction l1; simpl; auto. intros. inversion_clear H. now constructor. Qed.

Lemma sort_app : forall R (l1 l2 : list A),
  sort R l1 -> sort R l2 -> (forall x y, In x l1 -> In y l2 -> R x y) -> sort R (l1 ++ l2).
Proof using .
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
Proof using HeqA. intro. apply (Permutation_PermutationA_weak _). apply Permutation_rev. Qed.

Lemma fold_symmetric : forall (f : B -> A -> B),
  Proper (eqB ==> eqA ==> eqB) f -> (forall x y z, eqB (f (f z x) y) (f (f z y) x)) ->
  forall l i, eqB (fold_left f l i) (fold_right (flip f) i l).
Proof using HeqA HeqB.
intros f Hf Hf2 l i.
rewrite <- (rev_involutive l) at 2. rewrite fold_left_rev_right.
eapply fold_left_symmetry_PermutationA; reflexivity || autoclass; [].
apply PermutationA_rev; autoclass.
Qed.

(* A boolean version of membership *)
Definition mem eq_dec (x : A) l := if @InA_dec A eqA eq_dec x l then true else false.

Lemma mem_true_iff : forall eq_dec x l, mem eq_dec x l = true <-> InA eqA x l.
Proof using . intros eq_dec x l. unfold mem. destruct (InA_dec eq_dec x l); intuition discriminate. Qed.

Lemma mem_false_iff : forall eq_dec x l, mem eq_dec x l = false <-> ~InA eqA x l.
Proof using . intros eq_dec x l. unfold mem. destruct (InA_dec eq_dec x l); intuition discriminate. Qed.

Global Instance mem_compat : forall eq_dec, Proper (eqA ==> equivlistA eqA ==> eq) (mem eq_dec).
Proof using HeqA.
intros eq_dec x y Hxy l1 l2 Hl. unfold mem.
destruct (InA_dec eq_dec x l1), (InA_dec eq_dec y l2);
trivial; rewrite Hl, Hxy in *; contradiction.
Qed.

Lemma mem_map : forall eq_dec f, Proper (eqA ==> eqA) f ->
  forall x l, mem eq_dec x l = true -> mem eq_dec (f x) (map f l) = true.
Proof using HeqA.
intros eq_dec f Hf x l Hin.
rewrite mem_true_iff in *. rewrite (InA_map_iff _); trivial.
exists x. now split.
Qed.

Lemma mem_injective_map : forall eq_dec f, Proper (eqA ==> eqA) f -> injective eqA eqA f ->
  forall x l, mem eq_dec (f x) (map f l) = mem eq_dec x l.
Proof using HeqA.
intros eq_dec f Hf Hinj x l.
destruct (mem eq_dec x l) eqn:Hmem.
- now apply mem_map.
- rewrite mem_false_iff in *. intro Hin. apply Hmem. rewrite (InA_map_iff _ _ _) in Hin.
  destruct Hin as [x' [Heq Hin]]. apply Hinj in Heq. now rewrite <- Heq.
Qed.

Lemma odd_middle : forall l (d : A), Nat.Odd (length l) ->
  nth (div2 (length l)) (rev l) d = nth (div2 (length l)) l d.
Proof using .
intros l d. generalize (eq_refl (length l)). generalize (length l) at 2 3 4 5. intro n. revert l.
induction n using nat_ind2; intros l Hl [m Hm].
+ lia.
+ destruct l as [| a [| b l]]; try discriminate Hl. reflexivity.
+ simpl. destruct l as [| a [| b l]]; try reflexivity.
  assert (Hnil : b :: l <> nil) by discriminate. revert Hl Hnil. generalize (b :: l). clear l.
  intros l Hlen Hnil. destruct (exists_last Hnil) as [l' [z Heq]]. subst l. simpl.
  rewrite rev_app_distr. simpl in *. apply eq_add_S in Hlen.
  rewrite app_length, Nat.add_comm in Hlen. simpl in Hlen. apply eq_add_S in Hlen. clear Hnil.
  destruct n as [| n].
  - clear -Hm. lia.
  - assert (div2 (S n) < length l'). { rewrite Hlen. apply Nat.lt_div2. lia. }
    repeat rewrite app_nth1; trivial. apply IHn.
      assumption.
      destruct m as [| m]. lia. exists m. lia.
      now rewrite rev_length.
Qed.

Theorem partition_filter : forall (f : A -> bool) l,
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof using .
intros f l. induction l as [| a l]; simpl.
  reflexivity.
  rewrite IHl. now destruct (f a).
Qed.

Corollary partition_fst_In : forall (x : A) f l,
  In x (fst (partition f l)) <-> In x l /\ f x = true.
Proof using . intros. rewrite partition_filter. apply filter_In. Qed.

Corollary partition_snd_In : forall (x : A) f l,
  In x (snd (partition f l)) <-> In x l /\ f x = false.
Proof using . intros. rewrite partition_filter. rewrite <- negb_true_iff. apply filter_In. Qed.

Theorem partition_PermutationA : forall f l,
  PermutationA eqA (fst (partition f l) ++ snd (partition f l)) l.
Proof using HeqA.
intros f l. induction l as [| x l].
+ reflexivity.
+ simpl. destruct (partition f l) as [lg ld] eqn:Hpart. destruct (f x); simpl in *.
  - now rewrite IHl.
  - now rewrite <- PermutationA_middle, IHl.
Qed.

Lemma map_cond_Permutation : forall (f : A -> bool) (g₁ g₂ : A -> B) l,
  Permutation (map (fun x => if f x then g₁ x else g₂ x) l)
              (map g₁ (filter f l) ++ map g₂ (filter (fun x => negb (f x)) l)).
Proof using .
intros f ? ? l. induction l; simpl.
+ reflexivity.
+ destruct (f a); simpl.
  - apply Permutation_cons; trivial.
  - rewrite IHl. apply Permutation_middle.
Qed.

Lemma eqlistA_dec (eqA_dec : forall x y, {eqA x y} + {~eqA x y}) :
  forall l1 l2, {eqlistA eqA l1 l2} + {~eqlistA eqA l1 l2}.
Proof using .
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
  eqlistA eqA (l1 ++ l2) (l1' ++ l2') -> length l1 = length l1' ->
  eqlistA eqA l1 l1' /\ eqlistA eqA l2 l2'.

Proof using .
intro l. induction l as [| x l1];
intros l2 [| y l1'] l2' Heq Hlen; simpl in *; auto; try lia; [].
inv Heq. edestruct IHl1; eauto.
Qed.

Lemma singleton_characterization :
  forall (Aeq_dec : forall (a b : A), {a = b} + {a <> b}) (l : list A) (a : A),
         NoDup l ->
         In a l ->
         (forall b, ~ a = b -> ~ In b l) ->
         l = a :: nil.
Proof using .
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

Corollary partition_Permutation : forall {A} f (l : list A),
  Permutation (fst (partition f l) ++ snd (partition f l)) l.
Proof using . intros. rewrite <- PermutationA_Leibniz. apply partition_PermutationA; autoclass. Qed.

Corollary partition_length : forall {A} f (l : list A),
  length (fst (partition f l)) + length (snd (partition f l)) = length l.
Proof using . intros. now rewrite <- app_length, partition_Permutation. Qed.

Corollary filter_length : forall {A} f (l : list A),
  length (filter f l) = length l - length (filter (fun x => negb (f x)) l).
Proof using .
intros. apply plus_minus.
rewrite <- (partition_length f), partition_filter.
simpl. apply Nat.add_comm.
Qed.

(* Definition remove_Perm_properR := remove_Perm_proper Rdec. *)
Existing Instance Permutation_length_compat.
Existing Instance Permutation_NoDup_compat.
(* Existing Instance remove_Perm_properR. *)
Existing Instance In_perm_compat.
Existing Instance InA_impl_compat.
Existing Instance InA_compat.
Existing Instance InA_perm_compat.
Existing Instance PermutationA_length.
Existing Instance fold_left_start.
Existing Instance fold_left_symmetry_PermutationA.
Existing Instance PermutationA_map.
