
(**************************************************************************)
(**  Mechanised Framework for Local Interactions & Distributed Algorithms   
                                                                            
     T. Balabonski, P. Courtieu, L. Rieg, X. Urbain                         
                                                                            
     PACTOLE project                                                        
                                                                            
     This file is distributed under the terms of the CeCILL-C licence     *)
(**************************************************************************)


(**************************************************************************)
(* Author : Mathis Bouverot-Dupuis (June 2022). *)
(**************************************************************************)


Require Import Bool.
Require Import Arith.Div2.
Require Import Lia Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import FunInd.
Require Import FMapFacts.
Require Import SetoidDec.

(* Helping typeclass resolution avoid infinite loops. *)
Typeclasses eauto := (bfs).

Require Import Pactole.Util.Coqlib.
Require Import Pactole.Util.Ratio.
Require Import Pactole.Spaces.R2.
Require Import Pactole.Observations.MultisetObservation.
Require Import Pactole.Core.Identifiers.
Require Import Pactole.Spaces.Similarity.

Set Implicit Arguments.

Close Scope R_scope.

Local Existing Instance R2_VS.
Local Existing Instance R2_ES.


(* Change the left hand side of a setoid-equality with a convertible term. *)
Ltac change_LHS E := 
  match goal with 
  | [ |- ?LHS == ?RHS ] => change (E == RHS)
  end.

(* Change the right hand side of a setoid-equality with a convertible term. *)
Ltac change_RHS E := 
  match goal with 
  | [ |- ?LHS == ?RHS ] => change (LHS == E)
  end.

(* This tactic feeds the precondition of an implication in order to derive the conclusion
  (taken from http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/7013).
  Usage: feed H.
  H: P -> Q  ==becomes==>  H: P
                          ____
                          Q
  After completing this proof, Q becomes a hypothesis in the context. *)
  Ltac feed H :=
  match type of H with
  | ?foo -> _ =>
    let FOO := fresh in
    assert foo as FOO; [|specialize (H FOO); clear FOO]
  end.

(* Generalization of feed for multiple hypotheses.
  feed_n is useful for accessing conclusions of long implications.
  Usage: feed_n 3 H.
    H: P1 -> P2 -> P3 -> Q.
  We'll be asked to prove P1, P2 and P3, so that Q can be inferred. *)
Ltac feed_n n H := match constr:(n) with
  | O => idtac
  | (S ?m) => feed H ; [| feed_n m H]
  end.

(* Simplify a goal involving calculations in R2 by expanding everything. 
 * This is rarely useful. *)
Ltac simplifyR2 :=
unfold Rminus ; 
repeat (try rewrite mul_distr_add ;
        try rewrite <-add_morph ;
        try rewrite mul_0 ;
        try rewrite mul_1 ; 
        try rewrite add_origin_l ; 
        try rewrite add_origin_r ; 
        try rewrite mul_opp ; 
        try rewrite minus_morph ;
        try rewrite opp_opp ; 
        try rewrite opp_origin ;
        try rewrite R2_opp_dist ; 
        try rewrite add_opp).

Lemma contra (P Q : Prop) : (Q -> P) -> (~P -> ~Q).
Proof. intuition. Qed.

(* This inductive type inspired by mathcomp allows elegant destruction 
 * of if-statements (more than the 'destruct_match' tactic).
 * Usage : [case ifP_sumbool] will destuct the first if-statement 
 * with a sumbool condition in the goal. *)
Section IfSpecSumbool.
Variables (P Q : Prop) (T : Type).
Implicit Types (u v : T).

Inductive if_spec_sumbool u v : {P} + {Q} -> T -> Prop := 
  | if_spec_sumbool_true (p : P) : if_spec_sumbool u v (left p) u 
  | if_spec_sumbool_false (q : Q) : if_spec_sumbool u v (right q) v.

Lemma ifP_sumbool (c : {P} + {Q}) u v : if_spec_sumbool u v c (if c then u else v).
Proof using . case c ; constructor. Qed.

End IfSpecSumbool.

(* Usage : [case ifP_sumbool] will destuct the first if-statement 
 * with a boolean condition in the goal. *)
Section IfSpecBool.
Variables (T : Type) (u v : T).

Inductive if_spec_bool (B NB : Prop) : bool -> T -> Prop := 
  | if_spec_bool_true : B -> if_spec_bool B NB true u 
  | if_spec_bool_false : NB -> if_spec_bool B NB false v.

Lemma ifP_bool b : if_spec_bool (b = true) (b = false) b (if b then u else v).
Proof using . case b ; constructor ; reflexivity. Qed.

End IfSpecBool.

(* Lemma ifP_bool_test b : b = negb b -> (if b then b || b else false) = false.
Proof. case ifP_bool. ... *)


Section ForallTriplets.
Variable (A B C : Type).
Implicit Types (R : A -> B -> C -> Prop).

(* The proposition R holds for every triplet in the cartesian product (l1 * l2 * l3). *)
Definition ForallTriplets R l1 l2 l3 : Prop :=
  Forall (fun x => Forall (fun y => Forall (fun z => R x y z) l3) l2) l1.

Local Instance Forall_PermutationA_compat_strong {T : Type} `{Setoid T} : 
  Proper ((equiv ==> iff) ==> PermutationA equiv ==> iff) (@Forall T).
Proof using . 
intros P P' HP l l' Hl. elim Hl.
+ intuition.
+ intros x x' t t' Hx Ht IH. repeat rewrite Forall_cons_iff. now f_equiv ; [apply HP|].
+ intros x y t. repeat rewrite Forall_cons_iff. repeat rewrite <-and_assoc. f_equiv.
  - rewrite and_comm. now f_equiv ; auto.
  - f_equiv. intros ? ? ->. now apply HP.
+ intros t1 t2 t3 _ IH1 _ IH2. rewrite IH1, <-IH2.
  f_equiv. intros ? ? ->. symmetry. now apply HP.
Qed.

Local Instance ForallTriplets_PermutationA_compat  `{Setoid A} `{Setoid B} `{Setoid C} : 
  Proper ((equiv ==> equiv ==> equiv ==> iff) ==> 
    PermutationA equiv ==> PermutationA equiv ==> PermutationA equiv ==> iff) ForallTriplets.
Proof using . 
intros R R' HR l1 l1' Hl1 l2 l2' Hl2 l3 l3' Hl3. unfold ForallTriplets.
repeat (f_equiv ; auto ; intros ? ? ?). now apply HR.
Qed.

(* As with Forall, ForallTriplets is decidable (provided R is decidable). *)
Lemma ForallTriplets_dec R l1 l2 l3 : 
  (forall x y z, {R x y z} + {~ R x y z}) ->
  {ForallTriplets R l1 l2 l3} + {~ ForallTriplets R l1 l2 l3}.
Proof using . intros Rdec. unfold ForallTriplets. repeat (apply Forall_dec ; intros ?). now apply Rdec. Qed.

(* The equivalence between ForallTriplets and regular forall. *)
Lemma ForallTriplets_forall R l1 l2 l3 : 
  (ForallTriplets R l1 l2 l3) <-> forall x y z, List.In x l1 -> List.In y l2 -> List.In z l3 -> R x y z.
Proof using . 
unfold ForallTriplets. split.
+ intros H x y z Hinx Hiny Hinz.
  rewrite Forall_forall in H. specialize (H x Hinx).
  rewrite Forall_forall in H. specialize (H y Hiny).
  rewrite Forall_forall in H. specialize (H z Hinz).
  exact H.
+ intros H. 
  rewrite Forall_forall. intros x Hinx.
  rewrite Forall_forall. intros y Hiny.
  rewrite Forall_forall. intros z Hinz.
  auto.
Qed.

End ForallTriplets.

Global Instance flat_map_compat_eq {A B} `{Setoid A} `{Setoid B} : 
Proper ((equiv ==> PermutationA equiv) ==> eqlistA equiv ==> PermutationA equiv) (@flat_map A B).
Proof using . 
intros f f' Hff' l l' Hll'. elim Hll'.
+ cbn. now reflexivity.
+ intros x x' t t' Hxx' Htt' IH. cbn. now f_equiv ; auto.
Qed.

Global Instance flat_map_compat_perm {A B} `{Setoid A} `{Setoid B} : 
Proper ((equiv ==> PermutationA equiv) ==> PermutationA equiv ==> PermutationA equiv) (@flat_map A B).
Proof using . 
intros f f' Hff' l l' Hll'. elim Hll'.
+ simpl. now reflexivity.
+ intros x x' t t' Hxx' Htt' IH. cbn. rewrite <-IH. f_equiv. now apply Hff'.
+ intros x y t. cbn. repeat rewrite app_assoc. f_equiv.
- rewrite PermutationA_app_comm. f_equiv ; now apply Hff'. now apply setoid_equiv.
- now f_equiv.
+ intros t t' t'' _ IH1 _ IH2. rewrite IH1, <-IH2. f_equiv. 
intros x x' Hxx'. symmetry. now apply Hff'.
Qed.

Global Instance countA_occ_compat_setoid {A : Type} `{eq_dec : EqDec A} : 
  Proper (equiv ==> PermutationA equiv ==> equiv) (countA_occ equiv eq_dec).
Proof using . intros x x' Hx l l' Hl. now apply countA_occ_compat ; autoclass. Qed.

Lemma countA_occ_removeA_same {A : Type} `{eq_dec : EqDec A} x l :
  countA_occ equiv eq_dec x (removeA eq_dec x l) = 0%nat.
Proof using . 
induction l as [|y l IH].
+ reflexivity.
+ cbn. destruct_match.
  - now rewrite IH.
  - cbn. destruct_match ; [intuition | now rewrite IH].
Qed.    

Lemma countA_occ_removeA_other {A : Type} `{eq_dec : EqDec A} x y l :
  x =/= y -> countA_occ equiv eq_dec x (removeA eq_dec y l) = countA_occ equiv eq_dec x l.
Proof using .
intros Hxy. induction l as [|z l IH].
+ reflexivity.
+ cbn. repeat destruct_match.
  - rewrite <-e in e0. symmetry in e0. intuition.
  - now rewrite IH.
  - rewrite e. cbn. destruct_match ; [|intuition]. now rewrite IH.
  - cbn. destruct_match ; [intuition|]. now rewrite IH.
Qed.

Lemma PermutationA_countA_occ {A : Type} `{eq_dec : EqDec A} l l' :
  PermutationA equiv l l' <-> 
  forall x, countA_occ equiv eq_dec x l == countA_occ equiv eq_dec x l'.
Proof using . 
split.
+ intros Hperm x. elim Hperm.
  - now reflexivity.
  - intros x1 x2 l1 l2 Hx Hl IH. cbn. 
    repeat destruct_match ; try (now rewrite IH) ;
      rewrite <-e, Hx in c ; unfold complement in c ; now intuition.
  - intros a b t. cbn. repeat destruct_match ; reflexivity.
  - intros l1 l2 l3 _ H1 _ H2. now rewrite H1, <-H2.
+ intros Hcount. remember (length l) as m. generalize l l' Heqm Hcount.
  pattern m. apply (well_founded_ind lt_wf). clear m l l' Heqm Hcount.
  intros m IH [|x l] l' Hm Hcount.
  -  cbn in *. destruct l' as [|y tl'] ; [now apply permA_nil|].
    specialize (Hcount y). revert Hcount ; cbn. destruct_match ; [|intuition]. discriminate.
  - rewrite (PermutationA_count_split _ eq_dec x l).
    rewrite (PermutationA_count_split _ eq_dec x l').
    rewrite app_comm_cons. f_equiv.
    * apply eqlistA_PermutationA. rewrite <-Hcount. cbn. destruct_match ; [|intuition].
      cbn. reflexivity.
    * eapply IH ; [|reflexivity|].
      ++apply (Nat.le_lt_trans _ (length l)) ; [apply Preliminary.removeA_length_le|].
        rewrite Hm. cbn. apply Nat.lt_succ_diag_r.
      ++intros y. case (x =?= y) as [Hxy|Hxy]. 
        rewrite <-Hxy. repeat rewrite countA_occ_removeA_same. reflexivity.
        repeat rewrite countA_occ_removeA_other by (symmetry ; auto).
        rewrite <-Hcount. cbn. destruct_match ; [intuition|reflexivity].
Qed.


Lemma countA_occ_le {A : Type} `{eq_dec : EqDec A} w ps ps' :
  Forall2 (fun x x' => x' == x \/ x' == w) ps ps' -> 
    countA_occ equiv eq_dec w ps <= countA_occ equiv eq_dec w ps'.
Proof using . 
intros HF. induction HF as [| x x' l l' Hxx' Hll' IH] ; [auto|].
cbn -[equiv]. repeat destruct_match ; intuition.
rewrite H, e in c. intuition.
Qed.

Lemma countA_occ_lt {A : Type} `{eq_dec : EqDec A} w ps ps' : 
  Forall2 (fun x x' => x' == x \/ x' == w) ps ps' -> 
  List.Exists (fun '(x, x') => x' =/= x) (combine ps ps') ->
    countA_occ equiv eq_dec w ps < countA_occ equiv eq_dec w ps'.
Proof using .
intros HF HE. induction HF as [| x x' l l' Hxx' Hll' IH].
+ rewrite Exists_exists in HE. destruct HE as [x [In_nil _]]. now apply in_nil in In_nil.
+ cbn -[complement equiv] in HE. rewrite Exists_cons in HE.
  destruct HE as [Dxx' | HE].
  - destruct Hxx' as [Exx' | Ex'w] ; intuition.
    rewrite Ex'w in Dxx' |- *. cbn -[equiv].
    repeat destruct_match ; intuition. apply le_lt_n_Sm. now apply countA_occ_le.
  - destruct Hxx' as [Exx' | Ex'w] ; cbn -[equiv] ; repeat destruct_match ; intuition.
    rewrite Exx', e in c. intuition.
Qed.

Lemma nth_enum i m d :
  forall Him : i < m, nth i (enum m) d = exist (fun x => x < m) i Him.
Proof.
intros Him. apply eq_proj1, Nat.le_antisymm ; cbn.
+ apply lt_n_Sm_le, firstn_enum_spec. rewrite <-(firstn_skipn (S i)) at 1.
  rewrite app_nth1 ; [apply nth_In|] ; rewrite firstn_length_le ; try rewrite enum_length ; lia. 
+ apply skipn_enum_spec. rewrite <-(firstn_skipn i) at 1.
  rewrite app_nth2 ; [apply nth_In|] ; rewrite firstn_length_le by (rewrite enum_length ; lia) ; auto.
  rewrite Nat.sub_diag, skipn_length, enum_length. lia.
Qed.

Lemma combine_nil_iff {A B : Type} (l : list A) (l' : list B) :
  combine l l' = nil <-> (l = nil \/ l' = nil).
Proof. 
split.
+ intros Hcom. destruct l as [|x l] ; destruct l' as [|x' l'] ; intuition.
  discriminate Hcom.
+ intros [-> | ->] ; [|rewrite combine_nil] ; reflexivity.
Qed.

Lemma combine_map {A B C : Type} l l' (f : A -> C) (f' : B -> C) : 
  combine (List.map f l) (List.map f' l') = List.map (fun '(x, x') => (f x, f' x')) (combine l l').
Proof.
generalize l'. clear l'. induction l as [| x l IH] ; intros [|x' l'] ; cbn ; try reflexivity.
f_equal. apply IH.
Qed.


Lemma Forall2_Forall {A B : Type} (R : A -> B -> Prop) l l' : length l = length l' -> 
  (Forall2 R l l' <-> Forall (fun '(x, y) => R x y) (combine l l')).
Proof. 
intros Hlen. split.
+ intros Hforall2. induction Hforall2 as [|x x' l l' Hx Hl IH] ; constructor ; auto.
+ intros Hforall. remember (combine l l') as c.
  generalize dependent l'. generalize dependent l. generalize dependent c.
  induction c as [|a c IH] ; intros Hforall l l' Hlen Hcom.
  - symmetry in Hcom. rewrite combine_nil_iff in Hcom. 
    destruct Hcom as [-> | ->] ; cbn in Hlen ; [symmetry in Hlen|] ; 
      apply length_0 in Hlen ; rewrite Hlen ; constructor.
  - destruct a as [y y']. 
    destruct l as [|x l] ; [discriminate|]. 
    destruct l' as [|x' l'] ; [discriminate|].
    cbn in Hcom. inv Hcom. rewrite Forall_cons_iff in Hforall. constructor ; intuition.
Qed.

Lemma mul_eq0_iff (k : R) (x : R2) : (k * x == 0)%VS <-> (k == 0)%R \/ (x == 0)%VS.
Proof.
split ; intros H.
+ case (k =?= 0%R) as [Hk | Hk] ; [now left | right].
  apply mul_reg_l with k ; [intuition|].
  rewrite mul_origin. exact H.
+ destruct H as [Hk | Hx].
  - now rewrite Hk, mul_0.
  - now rewrite Hx, mul_origin.
Qed.

Lemma nth_InA {A : Type} {eqA : relation A} i l d :
  Reflexive eqA -> 
  i < length l -> InA eqA (nth i l d) l.
Proof.
intros Hrefl Hi. induction l using rev_ind. 
+ cbn in Hi. lia.
+ rewrite app_length in Hi. cbn in Hi.
  case (lt_dec i (length l)) as [Hi_lt | Hi_ge].
  - rewrite InA_app_iff ; left.
    rewrite app_nth1 by auto. now apply IHl.
  - assert (Hi_eq : i = length l) by lia.
    rewrite Hi_eq, nth_middle, InA_app_iff ; right.
    now apply InA_cons_hd.
Qed.

Lemma list_all_eq_or_perm {A : Type} `{Setoid A} `{EqDec A} (x0 : A) l : 
  (forall x, InA equiv x l -> x == x0) \/ (exists x1 l1, PermutationA equiv l (x1 :: l1) /\ x1 =/= x0).
Proof.
case (Forall_dec (equiv x0) (equiv_dec x0) l) as [Hall_eq | HNall_eq].
+ left. intros x Hin. rewrite Forall_forall in Hall_eq.
  rewrite InA_alt in Hin. destruct Hin as [y [Hxy Hin]].
  rewrite Hxy. symmetry. now apply Hall_eq.
+ right. apply neg_Forall_Exists_neg in HNall_eq ; [|apply equiv_dec].
  rewrite Exists_exists in HNall_eq. destruct HNall_eq as [x1 [Hin Hx1]].
  apply (@In_InA _ equiv) in Hin ; autoclass.
  apply PermutationA_split in Hin ; autoclass.
  destruct Hin as [l1 Hperm].
  exists x1. exists l1. split ; [exact Hperm | symmetry ; exact Hx1].
Qed.

Lemma add_sub {A : Type} `{R : RealVectorSpace A} (x y : A) :
  (x + (y - x) == y)%VS.
Proof. now rewrite (RealVectorSpace.add_comm y), RealVectorSpace.add_assoc, add_opp, add_origin_l. Qed. 

Lemma straight_path_0 p p' : straight_path p p' ratio_0 == p. 
Proof. cbn -[equiv mul opp RealVectorSpace.add]. now rewrite mul_0, add_origin_r. Qed. 

Lemma straight_path_same p r : straight_path p p r == p.
Proof. cbn -[equiv mul opp RealVectorSpace.add]. now rewrite add_opp, mul_origin, add_origin_r. Qed. 

Lemma straight_path_end s d r : 
  straight_path s d r == d <-> (s == d \/ proj_ratio r == 1%R).
Proof.
split. 
+ intros Hend. cbn -[mul opp RealVectorSpace.add] in Hend.
  assert (H : ((r - 1) * (d - s) == 0)%VS).
  {
    unfold Rminus. rewrite <-add_morph, minus_morph, mul_1, opp_distr_add, opp_opp.
    rewrite (RealVectorSpace.add_comm _ s), RealVectorSpace.add_assoc, (RealVectorSpace.add_comm _ s).
    now rewrite Hend, add_opp.
  }  
  rewrite mul_eq0_iff in H. case H as [H1 | H2].
  - right. cbn in H1 |- *. lra.
  - left. now rewrite R2sub_origin in H2.
+ intros [H1 | H2].
  - now rewrite H1, straight_path_same.
  - cbn -[mul opp RealVectorSpace.add equiv]. rewrite H2, mul_1.
    now rewrite add_sub. 
Qed.



Lemma straight_path_similarity (f : similarity R2) x y r :
  straight_path (f x) (f y) r == f (straight_path x y r).
Proof using .
cbn -[mul opp RealVectorSpace.add]. 
rewrite sim_add, <-RealVectorSpace.add_assoc. f_equal.
rewrite sim_mul. unfold Rminus. rewrite <-add_morph, mul_1.
rewrite (RealVectorSpace.add_comm (f 0%VS) _), <-2 RealVectorSpace.add_assoc.
rewrite add_opp, add_origin_r. 
rewrite minus_morph, <-mul_opp, <-mul_distr_add. f_equal.
rewrite sim_add, sim_opp, <-2 RealVectorSpace.add_assoc. f_equal.
change 2%R with (1 + 1)%R. rewrite <-add_morph, mul_1. 
rewrite RealVectorSpace.add_comm, 2 RealVectorSpace.add_assoc. 
rewrite <-add_origin_l. f_equal.
+ rewrite <-(RealVectorSpace.add_assoc (- f 0)%VS _), (RealVectorSpace.add_comm (- f 0)%VS (f 0)%VS), add_opp.
  rewrite add_origin_r, RealVectorSpace.add_comm, add_opp.
  reflexivity.
+ rewrite add_origin_l. reflexivity. 
Qed.

Lemma straight_path_dist_start (s d : R2) (r : ratio) : 
  dist s (straight_path s d r) == (r * dist s d)%R.
Proof. 
rewrite 2 norm_dist. cbn -[norm mul opp RealVectorSpace.add equiv].
rewrite opp_distr_add, RealVectorSpace.add_assoc, add_opp, add_origin_l.
rewrite <-mul_opp, opp_distr_add, opp_opp, RealVectorSpace.add_comm.
rewrite norm_mul, Rabs_pos_eq ; [reflexivity | apply ratio_bounds].
Qed.

Lemma straight_path_dist_end (s d : R2) (r : ratio) : 
  dist d (straight_path s d r) == ((1 - r) * dist s d)%R.
Proof.  
rewrite 2 norm_dist. cbn -[norm mul opp RealVectorSpace.add equiv].
assert (H : (d - (s + r * (d - s)) == (r - 1) * (s - d))%VS).
{
  unfold Rminus. rewrite <-add_morph, minus_morph, mul_1, 2 opp_distr_add, opp_opp.
  rewrite (RealVectorSpace.add_comm _ (-s + d)%VS), RealVectorSpace.add_assoc.
  f_equiv.
  + now rewrite RealVectorSpace.add_comm.
  + rewrite <-mul_opp. f_equiv. now rewrite opp_distr_add, opp_opp, RealVectorSpace.add_comm.  
}
rewrite H, norm_mul. f_equiv. rewrite Rabs_left1.
+ now rewrite Ropp_minus_distr.
+ generalize (ratio_bounds r). lra.
Qed. 

Lemma add_ratio_ge_left (r1 r2 : ratio) : (r1 <= add_ratio r1 r2)%R. 
Proof.
unfold add_ratio. destruct_match.
+ apply ratio_bounds.
+ cbn. generalize (ratio_bounds r2). lra.
Qed.

Lemma add_ratio_ge_right (r1 r2 : ratio) : (r2 <= add_ratio r1 r2)%R. 
Proof.
unfold add_ratio. destruct_match.
+ apply ratio_bounds.
+ cbn. generalize (ratio_bounds r1). lra.
Qed. 

Lemma colinear_exists_mul u v : 
  ~ u == 0%VS -> colinear u v -> exists t, v == (t * u)%VS. 
Proof.
intros Hu_n0 Hcol. destruct (colinear_decompose Hu_n0 Hcol) as [Hdecomp | Hdecomp].
+ exists (norm v / norm u)%R. rewrite Hdecomp at 1. unfold Rdiv, unitary.
  now rewrite mul_morph.
+ exists ((- norm v) / norm u)%R. rewrite Hdecomp at 1. unfold Rdiv, unitary.
  now rewrite mul_morph.
Qed.   