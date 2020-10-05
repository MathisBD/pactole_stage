(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms  
      T. Balabonski, P. Courtieu, R. Pelle, L. Rieg, X. Urbain              
                                                                            
      PACTOLE project                                                       
                                                                            
      This file is distributed under the terms of the CeCILL-C licence      
                                                                          *)
(**************************************************************************)


Require Import Lia Psatz SetoidDec Rbase.
Require Import Pactole.Util.Coqlib.
Require Import Pactole.Core.Identifiers.
Require Export Pactole.Spaces.Graph.
Require Import Pactole.Spaces.Isomorphism.


Typeclasses eauto := (bfs).
Remove Hints eq_setoid : typeclass_instances.

(** ** A ring  **)

(** What we need to define a ring. *)
Class RingSpec := {
  ring_size : nat;
  ring_size_spec : 1 < ring_size }.
Coercion ring_size_spec : RingSpec >-> lt.

Section Ring.
Context {RR : RingSpec}.

Notation ring_node := (finite_node ring_size).

Inductive direction := Forward | Backward | SelfLoop.
Definition ring_edge := (ring_node * direction)%type.

Global Instance direction_Setoid : Setoid direction.
simple refine {|
  equiv := fun d1 d2 => if (Nat.eq_dec ring_size 2)
                        then match d1, d2 with
                               | SelfLoop, SelfLoop => True
                               | SelfLoop, _ | _, SelfLoop  => False
                               | _, _ => True
                             end
                        else d1 = d2 |}; trivial; [].
Proof. split.
+ intro. repeat destruct_match; reflexivity.
+ intros ? ? ?. repeat destruct_match; auto; now symmetry.
+ intros ? ? ?. repeat destruct_match; auto; congruence.
Defined.

Global Instance ring_edge_Setoid : Setoid ring_edge := prod_Setoid _ _.

Lemma direction_eq_dec : forall d d': direction, {d = d'} + {d <> d'}.
Proof. decide equality. Defined.

Global Instance direction_EqDec : EqDec direction_Setoid.
  refine (fun d1 d2 => if (Nat.eq_dec ring_size 2)
                       then match d1, d2 with
                              | SelfLoop, SelfLoop => left _
                              | SelfLoop, _ | _, SelfLoop  => right _
                              | _, _ => left _
                            end
                       else _); simpl; try rewrite e; simpl; try tauto.
Proof.
abstract (repeat destruct_match; tauto || apply direction_eq_dec).
Defined.

Global Instance ring_edge_EqDec : EqDec ring_edge_Setoid := prod_EqDec _ _.

(* the following lemmas are used to easily prove that 
         (Z.to_nat (l mod Z.of_nat n)) = (l mod Z.of_nat n) *)
Lemma to_Z_sup_0 : forall l : Z, (0 <= l mod Z.of_nat ring_size)%Z.
Proof using . intros. apply Zdiv.Z_mod_lt. destruct RR. simpl. lia. Qed.

Lemma to_Z_inf_n (x : Z): Z.to_nat (x mod Z.of_nat ring_size)%Z < ring_size.
Proof using .
intros. rewrite <- Nat2Z.id, <- Z2Nat.inj_lt;
try apply Zdiv.Z_mod_lt; destruct RR; simpl; lia.
Qed.

Definition to_Z (v : ring_node) : Z := Z.of_nat (proj1_sig v).
Definition of_Z (x : Z) : ring_node :=
  exist _ (Z.to_nat (x mod Z.of_nat ring_size)) (to_Z_inf_n x).

Global Instance to_Z_compat : Proper (equiv ==> Z.eq) to_Z.
Proof using . repeat intro. hnf in *. now f_equal. Qed.

Global Instance of_Z_compat : Proper (Z.eq ==> equiv) of_Z.
Proof using . intros ? ? Heq. now rewrite Heq. Qed.

Lemma to_Z_injective : Preliminary.injective equiv Logic.eq to_Z.
Proof using .
intros [x Hx] [y Hy] Heq.
unfold to_Z in Heq. hnf in Heq |- *. simpl in Heq.
apply Nat2Z.inj in Heq. subst. f_equal. apply le_unique.
Qed.

Lemma to_Z_small : forall v, (0 <= to_Z v < Z.of_nat ring_size)%Z.
Proof using . intro. unfold to_Z. split; try lia; []. apply Nat2Z.inj_lt. apply proj2_sig. Qed.

Lemma Z2Z : forall l, (to_Z (of_Z l) = l mod Z.of_nat ring_size)%Z.
Proof using .
intros. unfold to_Z, of_Z. simpl.
rewrite Z2Nat.id; trivial; [].
apply Z.mod_pos_bound. destruct RR. simpl. lia.
Qed.

Lemma V2V : forall v, of_Z (to_Z v) == v.
Proof using .
intros [k Hk]. hnf. unfold to_Z, of_Z. apply eq_proj1. simpl.
rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; lia.
Qed.

(** From a node, if we move in one direction, get get to another node. *)
Definition move_along (v : ring_node) (dir : direction) :=
  match dir with 
    | SelfLoop => v
    | Forward  => of_Z (to_Z v + 1)
    | Backward => of_Z (to_Z v - 1)
  end.

Global Instance move_along_compat : Proper (equiv ==> equiv ==> equiv) move_along.
Proof using .
intros v1 v2 Hv e1 e2. simpl in *. unfold move_along. subst.
destruct (Nat.eq_dec ring_size 2) as [Hsize | Hsize];
repeat destruct_match; try tauto || discriminate; [|];
intros _; unfold of_Z; apply eq_proj1; simpl; rewrite Hsize; simpl;
assert (Hv2 := proj2_sig v2);
destruct v2 as [[| [| [| v]]] ?]; simpl in *; lia.
Qed.

Definition Ring (thd : ring_edge -> R)
                (thd_pos : forall e, (0 < thd e < 1)%R)
                (thd_compat : Proper (equiv ==> Logic.eq) thd)
  : FiniteGraph ring_size (ring_edge).
Proof.
refine ({|
  src := fst;
  tgt := fun e => move_along (fst e) (snd e);
  threshold := thd;
  find_edge := fun v1 v2 => if v1 =?= of_Z (to_Z v2 + 1) then Some (v1, Backward) else
                            if of_Z (to_Z v1 + 1) =?= v2 then Some (v1, Forward)  else
                            if v1 =?= v2 then Some (v1, SelfLoop) else None;
  V_EqDec := @finite_node_EqDec ring_size;
  E_EqDec := ring_edge_EqDec |}).
* exact thd_pos.
* (* src_compat *)
  intros e1 e2 He. apply He.
* (* tgt_compat *)
  intros e1 e2 [Ht Hd]. apply eq_proj1.
  repeat rewrite Ht. clear Ht. revert Hd.
  simpl. repeat destruct_match; simpl; intro;
  try tauto || discriminate; [| |];
  try (destruct (fst e2) as [k ?]; unfold to_Z; simpl;
       match goal with H : ring_size = 2 |- _ => try rewrite H in *; clear H end;
       destruct k as [| [| k]]; simpl; lia); [].
  rewrite move_along_compat; trivial; try rewrite Hd; reflexivity.
(* * (* find_edge_compat *)
  intros v1 v2 Hv12 v3 v4 Hv34. hnf in *. subst.
  repeat destruct_match; hnf in *; simpl in *; try easy || congruence; [| |];
  (split; trivial; []); now destruct_match. *)
Open Scope Z_scope.
* (* find_edge_None *)
  assert (Hsize := ring_size_spec).
  unfold move_along.
  intros a b; split; unfold find_edge;
  destruct (a =?= of_Z (to_Z b + 1)) as [Heq_a | Hneq_a].
  + tauto.
  + destruct (of_Z (to_Z a + 1) =?= b) as [Heq_b | Hneq_b], (a =?= b); try tauto; [].
    intros _ e [Hsrc Htgt].
    destruct (snd e); rewrite Hsrc in Htgt.
    - hnf in *. subst b. intuition.
    - elim Hneq_a. rewrite <- Htgt. rewrite Z2Z. apply eq_proj1.
      unfold of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
      ring_simplify (to_Z a - 1 + 1).
      unfold to_Z. rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; try lia; [].
      apply proj2_sig.
    - contradiction.
  + intros Hedge. elim (Hedge (a, Backward)).
    split; simpl; try reflexivity; [].
    rewrite Heq_a, Z2Z. apply eq_proj1.
    unfold Z.sub, of_Z. simpl. rewrite Zdiv.Zplus_mod_idemp_l.
    ring_simplify (to_Z b + 1 + -1).
    unfold to_Z. rewrite <- Zdiv.mod_Zmod, Nat2Z.id, Nat.mod_small; lia || apply proj2_sig.
  + intro Hedge. destruct (of_Z (to_Z a + 1) =?= b) as [Heq_b | Hneq_b].
    - elim (Hedge (a, Forward)).
      split; simpl; try reflexivity; []. now rewrite <- Heq_b.
    - destruct (a =?= b) as [Heq |]; try reflexivity; [].
      elim (Hedge (a, SelfLoop)).
      split; simpl; try reflexivity; []. apply Heq.
* (* find_edge_Some *)
  assert (Hsize_pos := ring_size_spec).
  unfold move_along.
  clear dependent thd.
  intros v1 v2 e.
  simpl in *. repeat (destruct_match; simpl in *); subst;
  match goal with
    | H : ring_size = 2%nat |- _ => rename H into Hsize
    | H : ring_size <> 2%nat |- _ => rename H into Hsize
  end;
  destruct e as [v dir]; simpl in *; split; intros []; subst;
  try split; try tauto || discriminate.
  + apply eq_proj1. unfold of_Z, to_Z. simpl.
    destruct v2 as [[| [| ?]] ?]; simpl; rewrite Hsize; simpl; lia.
  + apply eq_proj1. unfold of_Z, to_Z. simpl.
    destruct v2 as [[| [| ?]] ?]; simpl; rewrite Hsize; simpl; lia.
  + unfold of_Z, to_Z in *. destruct v2 as [v2 ?]; simpl in *; rewrite Hsize in *; simpl in *.
    match goal with H : exist _ _ _ = _ |- _ => rename H into Heq end.
    apply (f_equal (@proj1_sig _ _)) in Heq. simpl in Heq. rewrite Hsize in *.
    destruct v2 as [| [| ?]]; simpl in *; lia.
  + apply eq_proj1. destruct v as [v Hv]. unfold of_Z, to_Z. simpl. rewrite Hsize in *.
    destruct v as [| [| ?]]; simpl; lia.
  + match goal with H : _ = v |- _ => rename H into Heq end.
    apply (f_equal (@proj1_sig _ _)) in Heq.
    unfold to_Z, of_Z in Heq. destruct v as [v Hv]. simpl in Heq.
    rewrite Hsize in *. destruct v as [| [| ?]]; simpl in *; lia || lia.
  + match goal with H : v = _ |- _ => rename H into Heq end.
    apply (f_equal (@proj1_sig _ _)) in Heq.
    unfold to_Z, of_Z in Heq. destruct v as [v Hv]. simpl in Heq.
    rewrite Hsize in *. destruct v as [| [| ?]]; simpl in *; lia || lia.
  + match goal with H : of_Z (to_Z v + 1) = of_Z (to_Z v - 1) -> False |- _ => apply H end.
    apply eq_proj1. unfold of_Z, to_Z. simpl.
    rewrite <- (Zdiv.Z_mod_plus_full (_ - 1) 1 (Z.of_nat ring_size)).
    do 2 f_equal. destruct v as [v ?]; simpl; rewrite Hsize; simpl. ring.
  + exfalso. match goal with H : _ = _ |- _ => rename H into Heq end.
    apply (f_equal to_Z) in Heq. symmetry in Heq. revert Heq.
    rewrite 2 Z2Z. destruct v2 as [v2 ?]. unfold of_Z, to_Z. simpl.
    rewrite Zdiv.Zplus_mod_idemp_l.
    rewrite <- (Z.mod_small (Z.of_nat v2) (Z.of_nat ring_size)) at 2; try lia; [].
    replace (Z.of_nat v2 + 1 + 1) with (Z.of_nat v2 + 2) by ring.
    apply Zadd_small_mod_non_conf. lia.
  + rewrite Z2Z. apply eq_proj1. destruct v2 as [v2 Hv2]. unfold to_Z, of_Z; simpl.
    rewrite Zdiv.Zminus_mod_idemp_l.
    ring_simplify (Z.of_nat v2 + 1 - 1). rewrite Z.mod_small, Nat2Z.id; lia.
  + exfalso. match goal with H : _ = _ |- _ => rename H into Heq end.
    apply (f_equal to_Z)in Heq. rewrite Z2Z in Heq. destruct v2 as [v2 ?].
    unfold to_Z, of_Z in Heq. simpl in Heq. symmetry in Heq. revert Heq.
    rewrite <- (Z.mod_small (Z.of_nat v2) (Z.of_nat ring_size)) at 2; try lia; [].
    apply Zadd_small_mod_non_conf. lia.
  + exfalso. match goal with H : _ = _ |- _ => rename H into Heq end.
    apply (f_equal to_Z) in Heq. revert Heq.
    rewrite 2 Z2Z. replace (to_Z v + 1) with (to_Z v - 1 + 2) by ring.
    apply Zadd_small_mod_non_conf. lia.
  + exfalso. match goal with H : _ = _ |- _ => rename H into Heq end.
    apply (f_equal to_Z) in Heq. revert Heq.
    rewrite Z2Z. rewrite <- (Z.mod_small _ _ (to_Z_small v)) at 2.
    apply Zadd_small_mod_non_conf. lia.
  + exfalso. match goal with H : _ = _ |- _ => rename H into Heq end.
    apply (f_equal to_Z) in Heq. revert Heq.
    rewrite Z2Z. rewrite <- (Z.mod_small _ _ (to_Z_small v)) at 1.
    replace (to_Z v) with (to_Z v - 1 + 1) at 1 by ring.
    apply Zadd_small_mod_non_conf. lia.
  + match goal with H : _ = of_Z (_ + 1) -> False |- _ => apply H end.
    apply to_Z_injective. rewrite 2 Z2Z, Zdiv.Zplus_mod_idemp_l.
    ring_simplify (to_Z v - 1 + 1). symmetry. apply Z.mod_small, to_Z_small.
Defined.

(** If we do not care about threshold values, we just take 1/2 everywhere. *)
Definition nothresholdRing : FiniteGraph ring_size (ring_edge) :=
  Ring (fun _ => 1/2)%R
       ltac:(abstract (intro; lra))
       (fun _ _ _ => eq_refl).
End Ring.


(** **  Ring operations **)

Section RingTranslation.
Context {RR : RingSpec}.
Local Instance localRing : FiniteGraph ring_size ring_edge := nothresholdRing.
Notation ring_node := (finite_node ring_size).

(** ***  Translation along a ring  **)

(* TODO: generalize the definition of translation to thresholds. *)
Lemma bij_trans_V_proof : forall c x y,
  of_Z (to_Z x - c) == y <-> of_Z (to_Z y + c) == x.
Proof using .
intros c [x ?] [y ?]. unfold of_Z, to_Z.
split; intro Heq; apply (f_equal (@proj1_sig _ _)) in Heq;
simpl in *; subst; apply eq_proj1; simpl;
rewrite Z2Nat.id; auto using to_Z_sup_0.
- rewrite Z.add_mod_idemp_l; try lia; [].
  ring_simplify (Z.of_nat x - c + c)%Z.
  rewrite Z.mod_small, Nat2Z.id; lia.
- rewrite Zdiv.Zminus_mod_idemp_l.
  ring_simplify (Z.of_nat y + c - c)%Z.
  rewrite Z.mod_small, Nat2Z.id; lia.
Qed.

Definition bij_trans_V (c : Z) : @Bijection.bijection ring_node (@V_Setoid _ _ localRing) := {|
  Bijection.section := fun x => of_Z (to_Z x - c);
  Bijection.retraction := fun x => of_Z (to_Z x + c);
  Bijection.Inversion := bij_trans_V_proof c |}.

Definition bij_trans_E (c : Z) : @Bijection.bijection ring_edge (@E_Setoid _ _ localRing).
refine {|
  Bijection.section := fun x => (of_Z (to_Z (fst x) - c), snd x);
  Bijection.retraction := fun x => (of_Z (to_Z (fst x) + c), snd x) |}.
Proof.
+ abstract (intros ? ? Heq; hnf in *; simpl; destruct Heq as [Heq ?]; now rewrite Heq).
+ abstract (intros [x dx] [y dy]; split; intros [Hxy Hd];
            split; try (now apply bij_trans_V_proof); [|];
            destruct (Nat.eq_dec ring_size 2);
            solve [simpl in *; destruct dx, dy; tauto | symmetry; apply Hd]).
Defined.

Definition trans (c : Z) : isomorphism localRing.
refine {|
  iso_V := bij_trans_V c;
  iso_E := bij_trans_E c;
  iso_T := @Bijection.id _ R_Setoid |}.
Proof.
* (* iso_morphism *)
  intro e. split.
  + simpl. reflexivity.
  + apply to_Z_injective.
    unfold tgt. simpl. unfold move_along.
    destruct (snd e) eqn:Hsnd; repeat rewrite Z2Z.
    - repeat rewrite ?Zdiv.Zplus_mod_idemp_l, ?Zdiv.Zminus_mod_idemp_l. f_equal. ring.
    - rewrite 2 Zdiv.Zminus_mod_idemp_l. f_equal. ring.
    - reflexivity.
* (* iso_threshold *)
  intro. simpl. reflexivity.
* (* iso_incr *)
  intro. simpl. tauto.
* (* iso_bound_T *)
  intro. simpl. tauto.
Defined. (* TODO: abstract the proofs *)

Instance trans_compat : Proper (equiv ==> @equiv _ isomorphism_Setoid) trans.
Proof using .
intros c1 c2 Hc. simpl in *. subst.
repeat split; try reflexivity; [].
repeat destruct_match; tauto.
Qed.

Lemma trans_origin : @equiv _ isomorphism_Setoid (trans 0) Isomorphism.id.
Proof using .
split; [| split; [| reflexivity]].
+ intro x. apply eq_proj1. cbn -[of_Z]. now rewrite Z.sub_0_r, V2V.
+ intros [x d]. cbn -[equiv]. now rewrite Z.sub_0_r, V2V.
Qed.

Lemma trans_same : forall k, Bijection.section (trans (to_Z k)) k == of_Z 0.
Proof using . intro k. simpl. f_equal. ring. Qed.

(** ***  Symmetry of a ring w.r.t. a point [c]  **)

Definition swap_direction dir :=
  match dir with
    | Forward => Backward
    | Backward => Forward
    | SelfLoop => SelfLoop
  end.

Lemma bij_sym_V_proof : forall c x y, of_Z (c - to_Z x) == y <-> of_Z (c - to_Z y) == x.
Proof using .
intros c x y. simpl. split; intro; subst; rewrite Z2Z; apply eq_proj1;
unfold of_Z; simpl proj1_sig; rewrite Zdiv.Zminus_mod_idemp_r;
match goal with x : ring_node |- _ =>
  ring_simplify (c - (c - to_Z x))%Z; destruct x as [m Hm] end;
unfold to_Z; simpl; rewrite Z.mod_small, Nat2Z.id; lia.
Qed.

Definition bij_sym_V (c : Z) : @Bijection.bijection ring_node (@V_Setoid _ _ localRing) := {|
  Bijection.section := fun x => of_Z (c - to_Z x);
  Bijection.retraction := fun x => of_Z (c - to_Z x);
  Bijection.Inversion := bij_sym_V_proof c |}.

Definition bij_sym_E (c : Z) : @Bijection.bijection ring_edge (@E_Setoid _ _ localRing).
refine {|
  Bijection.section := fun x => (of_Z (c - to_Z (fst x)), swap_direction (snd x));
  Bijection.retraction := fun x => (of_Z (c - to_Z (fst x)), swap_direction (snd x)) |}.
Proof.
+ abstract (intros x y [Heq ?]; hnf in *; simpl; rewrite Heq;
     destruct (Nat.eq_dec ring_size 2), (snd x), (snd y); simpl in *; tauto || discriminate).
+ abstract (intros [x dx] [y dy]; split; intros [Hxy Hd];
            split; try (now apply bij_sym_V_proof); [|]; simpl in *;
            destruct (Nat.eq_dec ring_size 2), dx, dy; simpl in *; tauto || discriminate).
Defined.

Definition sym (c : Z) : isomorphism localRing.
refine {|
  iso_V := bij_sym_V c;
  iso_E := bij_sym_E c;
  iso_T := @Bijection.id _ R_Setoid |}.
Proof.
* (* iso_morphism *)
  intro e. split.
  + simpl. reflexivity.
  + apply eq_proj1.
    unfold tgt. simpl. unfold move_along.
    destruct (snd e) eqn:Hsnd; simpl; repeat rewrite Z2Z.
    - rewrite Zdiv.Zminus_mod_idemp_r, Zdiv.Zminus_mod_idemp_l. do 2 f_equal. ring.
    - rewrite Zdiv.Zplus_mod_idemp_l, Zdiv.Zminus_mod_idemp_r. do 2 f_equal. ring.
    - reflexivity.
* (* iso_threshold *)
  intro. simpl. reflexivity.
* (* iso_incr *)
  intro. simpl. tauto.
* (* iso_bound_T *)
  intro. simpl. tauto.
Defined. (* TODO: abstract the proofs *)

Instance sym_compat : Proper (equiv ==> @equiv _ isomorphism_Setoid) sym.
Proof using .
intros c1 c2 Hc. simpl in *. subst.
repeat split; try reflexivity; [].
repeat destruct_match; tauto.
Qed.

Lemma sym_involutive : forall c,
  @equiv _ isomorphism_Setoid (@compose _ _ IsoComposition (sym c) (sym c)) Isomorphism.id.
Proof using .
intro c. split; [| split; [| simpl; reflexivity]].
+ intro x. apply eq_proj1. cbn -[of_Z]. rewrite Z2Z. unfold of_Z. simpl.
  rewrite Zdiv.Zminus_mod_idemp_r. ring_simplify (c - (c - to_Z x))%Z.
  unfold to_Z. rewrite Z.mod_small, Nat2Z.id; trivial; []. assert (Hx := proj2_sig x).
  simpl in Hx.
  lia.
+ intro x. split.
  - (* TODO: same proof as above, factor it? *)
    apply eq_proj1. cbn -[of_Z]. rewrite Z2Z. unfold of_Z. simpl.
    rewrite Zdiv.Zminus_mod_idemp_r. ring_simplify (c - (c - to_Z (fst x)))%Z.
    unfold to_Z. rewrite Z.mod_small, Nat2Z.id; trivial; [].
    assert (Hx := proj2_sig (fst x)).
    simpl in Hx.
    lia.
  - simpl. destruct (snd x); simpl; now destruct_match.
Qed.

End RingTranslation.
