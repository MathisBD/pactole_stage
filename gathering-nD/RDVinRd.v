Require Import Utf8_core.
Require Import Bool.
Require Import Arith.Div2.
Require Import Rbase.
Require Import SetoidList.
Require Import FMultisetFacts.
Require Import FMultisetMap.
Require Import Preliminary.
Require Import ConvergentFormalismRd.
Require Import EqualitiesRd.
Require Import Morphisms.
Require Import Psatz.
Import Permutation.
Import Datatypes. (* to overshadow Rlist and its constructors [nil] and [cons] *)
Require FMapWeakList. (* to build an actual implementation of multisets *)

Set Implicit Arguments.
Close Scope R_scope.

(**  [Location] can be any decidable metric space where we can recognize spheres *)

(** **  Spectra are multisets  **)

Module Type GatheringLocation <: MetricSpace.
  Include MetricSpace.
  
  (** Required geometric primitives *)
  Parameter smallest_enclosing_sphere : list t -> t * R.
  Parameter smallest_enclosing_sphere_spec : forall l, 
    let (c, R) := smallest_enclosing_sphere l in
    (forall x, InA eq x l -> (dist c x <= R)%R) /\ exists x, InA eq x l /\ dist x c = R.
End GatheringLocation.

Module Multiset(Location : GatheringLocation)(N : Size) <: Spectrum (Location)(N).
  Module Names := Names(N).
  
  Module Mraw : FMultisetsOn Location := FMultisets FMapWeakList.Make Location.
  Module M := FMultisetFacts.Make Location Mraw.
  Include M.
  
  Notation "m1  [=]  m2" := (eq m1 m2) (at level 70).
  Notation "m1  [<=]  m2" := (M.Subset m1 m2) (at level 70).
  
  Definition position := Names.ident -> Location.t.
  Definition PosEq (pos₁ pos₂ : position) : Prop := forall id, Location.eq (pos₁ id) (pos₂ id).
  
  Definition from_pos pos : t := fold_left (fun acc x => M.add x 1 acc)
                                           (Names.fin_map (fun g => pos (Names.Good g)))
                                           M.empty.
  Instance from_pos_compat : Proper (PosEq ==> eq) from_pos.
  Proof. Admitted.
(*
Lemma multiset_nil : multiset nil [=] M.empty.
Proof. reflexivity. Qed.

Lemma multiset_cons_aux : forall s x m,
  List.fold_left (fun acc y => M.add y 1 acc) (x :: s) m [=]
  M.add x 1 (List.fold_left (fun acc x => M.add x 1 acc) s m).
Proof.
intro s. induction s; intros x m.
  reflexivity.
  simpl. intro.
  assert (Hf : Proper (M.eq ==> eq ==> M.eq) (fun (acc : M.t) (y : M.elt) => M.add y 1 acc)).
  { clear. intros s1 s2 Hs x y Hxy. now rewrite Hxy, Hs. }
  rewrite (@fold_left_start _ _ Logic.eq M.eq _ _ _ Hf s _ (M.add x 1 (M.add a 1 m)) (M.add_comm _ _ _ _ _)).
  apply IHs.
Qed.

Lemma multiset_cons : forall x s, multiset (x :: s) [=] M.add x 1 (multiset s).
Proof. intros x s y. unfold multiset. now rewrite multiset_cons_aux. Qed.

Lemma multiset_empty : forall l, multiset l [=] M.empty <-> l = nil.
Proof.
intro l. split; intro H.
  destruct l. reflexivity. rewrite multiset_cons in H.
  specialize (H r). rewrite M.add_spec, M.empty_spec in H. omega.
  subst l. apply multiset_nil.
Qed.

Lemma multiset_app : forall s s', multiset (s ++ s') [=] M.union (multiset s) (multiset s').
Proof.
induction s; intros s'; simpl.
  now rewrite M.union_empty_l.
  do 2 rewrite multiset_cons. intro x. destruct (Rdec x a).
    subst a. rewrite M.add_spec. rewrite IHs. repeat rewrite M.union_spec. rewrite M.add_spec. omega.
    rewrite M.add_spec'. rewrite IHs. repeat rewrite M.union_spec. rewrite M.add_spec'. reflexivity. auto. auto.
Qed.

Instance multiset_compat : Proper (@Permutation R ==> M.eq) multiset.
Proof.
intro s1. induction s1 as [| x s1]; intros s2 Hperm.
  apply Permutation_nil in Hperm. now subst.
  assert (Hx := Permutation_in_inside x Hperm). destruct Hx as [l1 [l2 Heq]]. now left. subst s2.
  intro y. rewrite multiset_app, M.union_spec. do 2 rewrite multiset_cons.
  destruct (Rdec x y) as [Heq | Hneq].
    subst y. repeat rewrite M.add_spec. rewrite plus_assoc. f_equal. rewrite <- M.union_spec, <- multiset_app.
    apply IHs1. now apply Permutation_cons_app_inv with x.
    repeat rewrite M.add_spec'; trivial. rewrite <- M.union_spec, <- multiset_app.
    apply IHs1. now apply Permutation_cons_app_inv with x.
Qed.

Lemma multiset_Permutation :
  forall x l n, M.multiplicity x (multiset l) = n -> exists l', ~In x l' /\ Permutation l (alls x n ++ l').
Proof.
intros x l. induction l; intros n Hin.
  exists nil. split. now auto. rewrite multiset_nil, M.empty_spec in Hin. subst n. simpl. reflexivity.
  rewrite multiset_cons in Hin. destruct (Rdec a x).
  - subst a. rewrite M.add_spec in Hin. destruct n. omega.
    rewrite plus_comm in Hin. simpl in Hin. apply eq_add_S in Hin. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
    exists l'. split. assumption. simpl. now constructor.
  - rewrite M.add_spec' in Hin; trivial. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
    exists (a :: l'). split. intros [|]; contradiction.
    transitivity (a :: alls x n ++ l'); now constructor || apply Permutation_middle.
Qed.

Lemma multiset_alls : forall x n, multiset (alls x n) [=] M.singleton x n.
Proof.
intros x n. induction n; simpl.
+ now rewrite M.singleton_0, multiset_nil.
+ rewrite multiset_cons. rewrite IHn. intro y. rewrite M.singleton_spec. Rdec_full.
    subst y. rewrite M.add_spec, M.singleton_spec. Rdec. omega.
    rewrite M.add_spec'. rewrite M.singleton_spec. now Rdec_full. auto.
Qed.

Corollary multiset_In : forall x l, M.multiplicity x (multiset l) > 0 <-> In x l.
Proof.
intros x l. split; intro Hl.
- destruct (multiset_Permutation _ (eq_refl (M.multiplicity x (multiset l)))) as [l' [Hl' Hperm]].
  rewrite Hperm. rewrite in_app_iff. left. destruct (M.multiplicity x (multiset l)). omega. now left.
- induction l. now inversion Hl. rewrite multiset_cons. destruct (Rdec a x).
    subst a. rewrite M.add_spec. omega.
    rewrite M.add_spec'; trivial. apply IHl. now inversion_clear Hl.
Qed.

Theorem multiset_map : forall f, injective eq eq f -> forall l, multiset (map f l) [=] M.map f (multiset l).
Proof.
intros f Hf l.
assert (Hf2 : Proper (eq ==> eq) f) by now repeat intro; subst.
induction l; simpl.
   rewrite (@M.map_compat f Hf2 (multiset nil)), multiset_nil. now rewrite M.map_empty. now apply multiset_nil.
   do 2 rewrite multiset_cons. now rewrite M.map_add, IHl.
Qed.

Theorem multiset_spec : forall x l, M.multiplicity x (multiset l) = count_occ Rdec l x.
Proof.
intros x l. induction l; simpl.
  rewrite multiset_nil. now apply M.empty_spec.
  rewrite multiset_cons. destruct (Rdec a x).
    subst a. rewrite M.add_spec. rewrite IHl. omega.
    rewrite M.add_spec'. now apply IHl. assumption.
Qed.

Theorem cardinal_multiset : forall l, M.cardinal (multiset l) = length l.
Proof.
induction l; simpl.
+ now rewrite multiset_nil, M.cardinal_empty.
+ rewrite multiset_cons, M.cardinal_add. apply f_equal, IHl.
Qed.

Lemma multiset_remove : forall x l,
  multiset (remove Rdec x l) [=] M.remove x (M.multiplicity x (multiset l)) (multiset l).
Proof.
intros x l y. induction l as[| a l]; simpl.
+ rewrite multiset_nil. do 2 rewrite M.empty_spec. now rewrite M.remove_0, M.empty_spec.
+ rewrite multiset_cons. destruct (Rdec y x). 
  - subst y. Rdec_full.
      subst a. rewrite IHl. rewrite M.add_spec. do 2 rewrite M.remove_spec. rewrite M.add_spec. omega.
      rewrite multiset_cons. rewrite M.add_spec'; auto. rewrite IHl. do 2 rewrite M.remove_spec. omega.
  - Rdec_full.
      subst a. rewrite IHl. rewrite M.add_spec. repeat rewrite M.remove_spec'; auto. rewrite M.add_spec'; auto.
      rewrite multiset_cons. rewrite M.remove_spec'; auto. destruct (Rdec a y).
        subst a. do 2 rewrite M.add_spec. rewrite IHl. now rewrite M.remove_spec'.
        repeat rewrite M.add_spec'; trivial. rewrite IHl. rewrite M.remove_spec'; auto.
Qed.

Existing Instance In_permA_compat.

Lemma multiset_support : forall x l, In x (M.support (multiset l)) <-> In x l.
Proof.
intros x l. split; intro Hl.
* induction l.
  + cut (M.support (multiset nil) = nil).
      intro Heq. unfold M.elt in *. now rewrite <- Heq.
      apply Permutation_nil. now rewrite <- PermutationA_Leibniz, multiset_nil, M.support_empty.
  + rewrite multiset_cons in Hl. rewrite M.support_add in Hl; try omega. unfold Rdecidable.eq_dec in Hl.
    destruct ( InA_dec Rdec a (M.support (multiset l))).
    - right. now apply IHl.
    - destruct Hl. now left. right. now apply IHl.    
* induction l.
  + inversion Hl.
  + rewrite <- InA_Leibniz. rewrite M.support_spec. unfold M.In. rewrite multiset_cons. destruct (Rdec a x).
    - subst a. rewrite M.add_spec. omega.
    - rewrite M.add_spec'. change (M.In x (multiset l)). rewrite <- M.support_spec, InA_Leibniz. apply IHl.
      now inversion_clear Hl. assumption.
Qed.
*)  
  Definition is_ok s pos := eq s (from_pos pos).
  
  Instance smallest_enclosing_sphere_uniq :
    Proper (PermutationA Location.eq ==> (Location.eq * Logic.eq)) Location.smallest_enclosing_sphere.
  Proof. Admitted.
End Multiset.

(** *  The Gathering Problem  **)

(** Vocabulary: we call a [location] the coordinate of a robot. We
    call a [position] a function from robots to position. An
    [execution] is an infinite (coinductive) stream of [position]s. A
    [demon] is an infinite stream of [demonic_action]s. *)

(** ** Some general properties related to the gathering problem *)

Module GeneralGathering (Location : GatheringLocation) (N : Size).

(** The spectrum is a multiset of positions *)
Module Spec := Multiset(Location)(N).

(* Importing the previous results *)
Module Export Eq := Equalities(Location)(N)(Spec).
Definition position := Spec.position.

(** [gathered_at pos pt] means that in position [pos] all good robots
    are at the same location [pt] (exactly). *)
Definition gathered_at (pt : Location.t) (pos : position) := forall g : Names.G, pos (Names.Good g) = pt.

(** [Gather pt e] means that at all rounds of (infinite) execution
    [e], robots are gathered at the same position [pt]. *)
CoInductive Gather (pt: Location.t) (e : execution) : Prop :=
  Gathering : gathered_at pt (execution_head e) -> Gather pt (execution_tail e) -> Gather pt e.

(** [WillGather pt e] means that (infinite) execution [e] is *eventually* [Gather]ed. *)
Inductive WillGather (pt : Location.t) (e : execution) : Prop :=
  | Now : Gather pt e -> WillGather pt e
  | Later : WillGather pt (execution_tail e) -> WillGather pt e.

(** When all robots are on two towers of the same height,
    there is no solution to the gathering problem.
    Therefore, we define these positions as [forbidden]. *)
Definition forbidden (pos : position) :=
  let m := Spec.from_pos(pos) in
  exists p1 p2, ~Location.eq p1 p2 /\ Spec.multiplicity p1 m = N.nG /\ Spec.multiplicity p2 m = N.nG.

Instance forbidden_invariant : Proper (PosEq ==> iff) forbidden.
Proof.
intros ? ? Heq. split; intros [pt1 [pt2 [Hneq Hpt]]];
exists pt1; exists pt2; split; try rewrite Heq in *; trivial.
Qed.

(** [solGathering r d] means that any possible (infinite)
    execution, generated by demon [d] and robogram [r] and any intial
    position not [forbidden], will *eventually* be [Gather]ed. *)
Definition solGathering (r : robogram) (d : demon) :=
  forall pos, ~forbidden pos -> exists pt : Location.t, WillGather pt (execute r d pos).

End GeneralGathering.

(** * Framework of the impossibility proof: a finite set with at leasts two elements.  **)

Parameter nG : nat.
Axiom size_G : nG >= 2.

Module N : Size with Definition nG := nG.
  Definition nG := nG.
  Definition nB := 0.
End N.

Module GatheringinRd(Location : GatheringLocation).

Module Import Gathering := GeneralGathering(Location)(N).

Close Scope R_scope.

Corollary half_size_pos : (div2 nG > 0)%nat.
Proof. apply Exp_prop.div2_not_R0. apply size_G. Qed.

Definition g1 : Spec.Names.G.
unfold Spec.Names.G, N.nG. destruct nG eqn:HnG. generalize size_G. abstract omega.
apply (@Fin.F1 n).
Defined.

Definition g2 : Spec.Names.G.
unfold Spec.Names.G, N.nG. destruct nG as [| [| n]] eqn:HnG; try (abstract (generalize size_G; omega)).
apply (Fin.FS Fin.F1).
Defined.

Lemma g1_g2 : g1 <> g2.
Proof. Admitted.


(** *  Gathering robogram  **)

(** The robogram follows the following four steps:
    1) If a tower is strictly bigger than all others, every robot moves toward it.
    Otherwise, 2) Compute the smallest enclosing sphere and its center [c].
               3) Move every robot that is neither on this sphere nor at [c] toward [c].
               4) Move every robot that is on this sphere toward [c].

    In the FSYNC case, these steps take exactly one tick.
    In the SSYNC case, they make take several ticks and only fairness ensures that they terminate.
    **)

Definition max_mult s := Spec.fold (fun _=> max) s 0.
Definition max s := Spec.filter (fun _ => beq_nat (max_mult s)) s.

Definition on_sphere c R x :=
  if Rdec_bool (Location.dist c x) R then true else
  if Rdec_bool (Location.dist c x) 0 then true else false.

Definition all_on_sphere c R := forallb (fun x => on_sphere c R x).

Definition robogram_pgm (s : Spec.t) : Location.t :=
  match Spec.support (max s) with
    | nil => Location.origin (* only happen with no robots *)
    | pt :: nil => pt (* case 1: one majority stack *)
    | _ => (* several majority stacks *)
      let '(c, R) := Location.smallest_enclosing_sphere (Spec.support s) in
      if all_on_sphere c R (Spec.support s) then (* case 4 *) c else (* case 3 *)
      if Rdec_bool (Location.dist c Location.origin) 0 then Location.origin else
      if Rdec_bool (Location.dist c Location.origin) R then Location.origin else c
  end.

Print Assumptions robogram_pgm.

(** **  The robogram is well-defined on spectra **)

Instance max_mult_compat : Proper (Spec.eq ==> eq) max_mult.
Proof.
intros s1 s2 Heq. unfold max_mult. apply Spec.fold_compat; auto; refine _.
+ repeat intro. auto.
+ repeat intro. rewrite Max.max_assoc. setoid_rewrite Max.max_comm at 2. rewrite <- Max.max_assoc. reflexivity.
Qed.

Instance max_compat : Proper (Spec.eq ==> Spec.eq) max.
Proof.
intros s1 s2 Heq x. unfold max. rewrite Spec.filter_extensionality_compat.
+ apply Spec.filter_compat; try assumption. repeat intro. auto.
+ repeat intro. auto.
+ intros. simpl. rewrite Heq. reflexivity.
Qed.

Lemma support_max_nil : forall s s', Spec.eq s s' -> Spec.support (max s) = nil -> Spec.support (max s') = nil.
Proof. intros s s' Hs Hnil. apply (@PermutationA_nil _ Location.eq _). rewrite <- Hs, Hnil. reflexivity. Qed.

Lemma support_max_singleton : forall s s' x, Spec.eq s s' ->
  Spec.support (max s) = x :: nil -> exists y, Location.eq x y /\ Spec.support (max s') = y :: nil.
Proof. intros s s' x Heq Hs. apply (PermutationA_length1 _). rewrite <- Heq, Hs. reflexivity. Qed.

Instance on_sphere_compat : Proper (Location.eq ==> eq ==> Location.eq ==> eq) on_sphere.
Proof.
intros c1 c2 Hc R1 R2 HR x1 x2 Hx. unfold on_sphere.
rewrite Hc, Hx, HR. destruct (Rdec_bool (Location.dist c2 x2) R2); trivial.
rewrite Hc, Hx. destruct (Rdec_bool (Location.dist c2 x2) 0); trivial.
Qed.

Instance forallb_compat {A} {eqA} `{Equivalence A eqA} (f : A -> bool) :
  Proper (eqA ==> eq) f ->  Proper (PermutationA eqA ==> eq) (forallb f).
Proof.
intros Hf l. revert l. apply (PermutationA_ind_bis _).
+ reflexivity.
+ intros x y l1 l2 Hxy Hl IHl. simpl. rewrite IHl, Hxy. reflexivity.
+ intros x y l1 l2 Hl IHl. simpl. rewrite IHl, andb_assoc, andb_assoc. now setoid_rewrite andb_comm at 4. 
+ intros l1 l2 l3 Hl12 IHl12 Hl23 IHl23. rewrite IHl12, IHl23. reflexivity.
Qed.

Instance all_on_sphere_compat : Proper (Location.eq ==> eq ==> PermutationA Location.eq ==> eq) all_on_sphere.
Proof.
intros c1 c2 Hc ? R ? l. subst. revert l. apply (PermutationA_ind_bis _).
+ reflexivity.
+ intros x y l1 l2 Hxy Hl IHl. simpl. rewrite IHl, Hc, Hxy. reflexivity.
+ intros x y l1 l2 Hl IHl. simpl. rewrite IHl, Hc, andb_assoc, andb_assoc. now setoid_rewrite andb_comm at 4. 
+ intros l1 l2 l3 Hl12 IHl12 Hl23 IHl23. rewrite IHl12. unfold all_on_sphere.
  rewrite (forallb_compat _ (on_sphere_compat (reflexivity _) (reflexivity _)) _ _ Hl23). reflexivity.
Qed.

Instance robogram_compat : Proper (Spec.eq ==> Location.eq) robogram_pgm.
Proof.
unfold robogram_pgm. intros s s' Heq.
destruct (Spec.support (max s)) as [| pt [| ? l]] eqn:Hs.
+ rewrite (support_max_nil Heq Hs). reflexivity.
+ assert (Hs' := support_max_singleton Heq Hs). destruct Hs' as [y [Hxy Hs']]. rewrite Hs'. assumption.
+ destruct (Spec.support (max s')) as [| pt' [| ? l']] eqn:Hs'.
  - rewrite (support_max_nil (symmetry Heq) Hs') in Hs. discriminate Hs.
  - apply (support_max_singleton (symmetry Heq)) in Hs'.
    destruct Hs' as [? [_ Hs']]. rewrite Hs' in Hs. discriminate Hs.
  - destruct (Location.smallest_enclosing_sphere (Spec.support s)) as [c1 R1] eqn:Heq1,
              (Location.smallest_enclosing_sphere (Spec.support s')) as [c2 R2] eqn:Heq2.
    assert (Hsphere : (Location.eq * eq)%signature (c1, R1) (c2, R2)).
    { rewrite <- Heq1, <- Heq2. rewrite Heq. reflexivity. }
    destruct Hsphere as [Hc HR]. hnf in Hc, HR; simpl in Hc, HR. rewrite Hc, HR, Heq.
    destruct (all_on_sphere c2 R2 (Spec.support s')); trivial. rewrite Hc.
    destruct (Rdec_bool (Location.dist c2 Location.origin) 0); try reflexivity. rewrite Hc.
    destruct (Rdec_bool (Location.dist c2 Location.origin) R2); trivial; reflexivity.
Qed.
Print Assumptions robogram_compat.

Definition GatheringRobogram := Build_robogram robogram_pgm robogram_compat.

(*
Instance PermutationA_compat A eqA (HeqA : @Equivalence A eqA) :
  Proper (PermutationA eqA ==> PermutationA eqA ==> iff) (PermutationA eqA).
Proof. intros l1 l2 Hl12 l3 l4 Hl34. now rewrite Hl12, Hl34. Qed.
*)

(** **  General simplification lemmas for [round robogram da _] and [nominal_spectrum (round robogram da _)] **)
Locate Byz.
Lemma round_simplify : forall (da : demonic_action) pos,
  PosEq (round GatheringRobogram da pos)
        (fun id => match da.(step) id with
                     | Off => pos id
                     | On f _ =>
                       match id with
                         | Names.Byz b => relocate_byz da b
                         | Names.Good g =>
                           match Spec.support (max (Spec.from_pos pos)) with
                             | nil => Location.origin (* only happen with no robots *)
                             | pt :: nil => pt (* case 1: one majority stack *)
                             | _ => (* several majority stacks *)
                               let '(c, R) := Location.smallest_enclosing_sphere
                                                (Spec.support (Spec.from_pos pos)) in
                               if all_on_sphere c R (Spec.support (Spec.from_pos pos)) then c else
                               if Rdec_bool (Location.dist c Location.origin) 0 then Location.origin else
                               if Rdec_bool (Location.dist c Location.origin) R then Location.origin else c
                           end
                       end
                   end).
Proof.
intros da pos id. unfold round. destruct (step da id) as [| obs Hobs]. reflexivity.
destruct id as [g | b]; try reflexivity.
rewrite (spectrum_ok da). rewrite robogram_homothecy_invariant; trivial. field_simplify; trivial. clear Hframe.
unfold robogram.
rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
destruct (majority_stack (nominal_spectrum pos)) eqn:Hmaj.
+ rewrite majority_stack_NoResult_spec in Hmaj. elim (nominal_spectrum_nil _ Hmaj).
+ rewrite <- majority_stack_Valid_similarity in Hmaj; try exact R1_neq_R0. rewrite Hmaj. field.
+ rewrite <- majority_stack_Invalid_similarity in Hmaj; try exact R1_neq_R0. rewrite Hmaj.
  rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
  assert (Hinj : injective eq eq (fun x => 1 * (x - gp pos g))) by (apply similarity_injective; lra).
  assert (Proper (eq ==> eq) (fun x => 1 * (x - gp pos g))) by now repeat intro; subst.
  rewrite nominal_spectrum_similarity, multiset_map, M.map_support, map_length; trivial.
  assert (H0 : 1 * (gp pos g - gp pos g) = 0) by ring.
  unfold M.elt.
  destruct (beq_nat (@length R (M.support (multiset (nominal_spectrum pos)))) 3) eqn:H3.
  - rewrite nominal_spectrum_similarity, multiset_map, M.map_support; trivial.
    rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
    rewrite sort_map_increasing; try now apply similarity_increasing; lra.
    rewrite <- H0 at 1. rewrite (map_nth (fun x => 1 * (x - gp pos g))). field_simplify.
    rewrite (nth_indep _ _ 0). reflexivity. rewrite beq_nat_true_iff in H3.
    rewrite <- Permuted_sort. unfold M.elt in H3. rewrite H3. omega.
  - rewrite <- H0 at 1. rewrite is_extremal_similarity_invariant; try exact R1_neq_R0.
    rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. rewrite <- lift_gp_equiv.
    destruct (is_extremal (gp pos g) (nominal_spectrum pos)). field.
    rewrite extreme_center_similarity_invariant; try exact R1_neq_R0. field_simplify.
    rewrite (lift_gp_equiv {| gp := gp pos; bp := locate_byz da |}). simpl. now rewrite <- lift_gp_equiv.
Qed.
Print Assumptions round_simplify.

(* Definitions of two subsets of robots: active and idle ones. *)
Definition idle nG (da : demonic_action nG 0) := filter (fun x => Rdec_bool (frame da x) 0) (Gnames nG).
Definition active nG (da : demonic_action nG 0) := filter (fun x => negb (Rdec_bool (frame da x) 0)) (Gnames nG).

Theorem nominal_spectrum_simplify : forall (da : demonic_action nG 0) pos,
  Permutation (nominal_spectrum pos) (map (gp pos) (idle da) ++ map (gp pos) (active da)).
Proof.
intros da pos.
rewrite (lift_gp_equiv pos), <- (if_ExtEq (fun g => Rdec_bool (frame da g) 0) (gp pos)) at 1.
unfold lift_gp. rewrite (nominal_spectrum_combineG (fun g => Rdec_bool (frame da g) 0)).
rewrite partition_filter, app_nil_r. reflexivity.
Qed.

Theorem nominal_spectrum_round_simplify : forall (da : demonic_action nG 0) pos,
  Permutation
    (nominal_spectrum (lift_gp (round robogram da (gp pos))))
    (* robots that are not activated this turn *)
    (map (gp pos) (idle da)
    (* robots that are activated this turn *)
    ++ map (fun g => match majority_stack (nominal_spectrum pos) with
                       | NoResult => 0
                       | Valid pt n => pt
                       | Invalid n => if beq_nat (length (M.support (multiset (nominal_spectrum pos)))) 3
                                      then List.nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0
                                      else if is_extremal (gp pos g) (nominal_spectrum pos) then gp pos g
                                           else extreme_center (nominal_spectrum pos)
                     end)
           (active da)).
Proof.
intros da pos. rewrite round_simplify. unfold lift_gp. rewrite (if_Rdec_ExtEq 0 (frame da)).
rewrite nominal_spectrum_combineG. simpl. rewrite app_nil_r, partition_filter. reflexivity.
Qed.

(** ** Simplification of the global position in the three cases of the robogram **)

(** When there is a majority stack, it grows and all other stacks wither. **)
Theorem Stack_at_grow :  forall pt pos (da : demonic_action nG 0),
  Stack_at pt pos -> (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
                     >= M.multiplicity pt (multiset (nominal_spectrum pos)))%nat.
Proof.
intros pt pos da Hstack.
(* we first simplify the lhs *)
rewrite <- majority_stack_spec in Hstack. destruct Hstack as [m Hstack].
rewrite nominal_spectrum_round_simplify, Hstack. rewrite multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec. rewrite <- (map_length (gp pos)), <- cardinal_multiset. apply M.cardinal_lower.
Qed.
Print Assumptions Stack_at_grow.

(* This proof follows the exact same structure.
   It is simpler because among robots that are activated, none goes to pt' <> pt *)
Theorem Stack_at_wither : forall pt pt' pos (da : demonic_action nG 0), pt <> pt' ->
  Stack_at pt pos -> (M.multiplicity pt' (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
                     <= M.multiplicity pt' (multiset (nominal_spectrum pos)))%nat.
Proof.
intros pt pt' pos da Hdiff Hstack.
(* we first simplify the lhs *)
rewrite <- majority_stack_spec in Hstack. destruct Hstack as [m Hstack].
rewrite nominal_spectrum_round_simplify, Hstack. repeat rewrite multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* No activated robot goes to pt' as pt' <> pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec_full. now symmetry in Heq. omega.
Qed.

(** As a consequence, whenever there is a majority stack, it remains forever so. **)
Theorem Stack_at_forever : forall pt pos (da : demonic_action nG 0),
  Stack_at pt pos -> Stack_at pt (lift_gp (round robogram da (gp pos))).
Proof.
intros pt pos da Hstack. assert (Hs := Hstack). destruct Hs as [n [? Hpos]].
eexists. split. reflexivity. intros pt' Hdiff.
eapply le_lt_trans. apply Stack_at_wither with pt; trivial.
eapply lt_le_trans. apply Hpos. assumption.
subst n. apply Stack_at_grow. assumption.
Qed.


Existing Instance range_compat.
Existing Instance nominal_spectrum_compat.
Existing Instance lift_gp_compat.


(** If we have three stacks, everyone goes to the middle one. **)
Lemma round_simplify_Three : forall (da : demonic_action nG 0) pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  ExtEq (round robogram da (gp pos))
        (fun g => if Rdec (frame da g) 0 then gp pos g
                  else nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0).
Proof.
intros da pos n Hmaj H3.
rewrite round_simplify; trivial. intro g. Rdec_full. reflexivity.
rewrite Hmaj, H3. rewrite <- beq_nat_refl.
apply nth_indep. unfold M.elt in H3. rewrite <- (Permutation_length (Permuted_sort _)), H3. omega.
Qed.

Lemma nominal_spectrum_3_stacks : forall pos, length (M.support (multiset (nominal_spectrum pos))) = 3%nat <->
  exists pt1 pt2 pt3, exists n1 n2 n3, pt1 <> pt2 /\ pt2 <> pt3 /\ pt1 <> pt3 /\
    (0 < n1)%nat /\ (0 < n2)%nat /\ (0 < n3)%nat /\
    Permutation (nominal_spectrum pos) (alls pt1 n1 ++ alls pt2 n2 ++ alls pt3 n3).
Proof.
intro pos. split; intro H.
+ assert (Hl : exists pt1 pt2 pt3, M.support (multiset (nominal_spectrum pos)) =  pt1 :: pt2 :: pt3 :: nil).
  { destruct (M.support (multiset (nominal_spectrum pos))) as [| a [| b [| c [| d l]]]]; inversion H.
    exists a. exists b. exists c. reflexivity. } clear H.
  destruct Hl as [pt1 [pt2 [pt3 Hl]]]. exists pt1. exists pt2. exists pt3.
  exists (M.multiplicity pt1 (multiset (nominal_spectrum pos))).
  exists (M.multiplicity pt2 (multiset (nominal_spectrum pos))).
  exists (M.multiplicity pt3 (multiset (nominal_spectrum pos))).
  assert (Hdup := M.support_NoDupA (multiset (nominal_spectrum pos))).
  rewrite Hl in Hdup. inversion_clear Hdup. inversion_clear H0. clear H2.
  assert (H12 : pt1 <> pt2). { intro Habs. apply H. now left. }
  assert (H13 : pt1 <> pt3). { intro Habs. apply H. now right; left. }
  assert (H23 : pt2 <> pt3). { intro Habs. apply H1. now left. }
  clear H H1. repeat split; trivial.
  - change (M.In pt1 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now left.
  - change (M.In pt2 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now right; left.
  - change (M.In pt3 (multiset (nominal_spectrum pos))). rewrite <- M.support_spec, Hl. now do 2 right; left.
  - do 3 rewrite multiset_spec. etransitivity. apply (remove_count_occ_restore Rdec pt1).
    apply Permutation_app. reflexivity. etransitivity. apply (remove_count_occ_restore Rdec pt2).
    apply Permutation_app. now rewrite count_occ_remove_out.
    assert (Hin : forall x, In x (nominal_spectrum pos) -> x = pt1 \/ x = pt2 \/ x = pt3).
    { intros x Hin. cut (In x (M.support (multiset (nominal_spectrum pos)))).
        rewrite Hl. intros [| [| [|]]]; intuition. now inversion H. now apply multiset_support. }
    assert (Hrem : forall x, In x (remove Rdec pt2 (remove Rdec pt1 (nominal_spectrum pos))) -> x = pt3).
    { intros x H'. rewrite (remove_in_iff _ _) in H'. destruct H' as [H' ?].
      rewrite (remove_in_iff _ _) in H'. destruct H' as [H' ?]. apply Hin in H'. intuition. }
    rewrite alls_carac in Hrem. rewrite Hrem. f_equiv.
    clear Hrem Hl. induction (nominal_spectrum pos).
      reflexivity.
      simpl. repeat Rdec_full; try subst a.
        contradiction.
        apply IHs. intros x Hx. apply Hin. now right.
        simpl. Rdec_full. contradiction. simpl. f_equal. apply IHs. intros x Hx. apply Hin. now right.
        simpl. Rdec_full.
          subst a. apply IHs. intros x Hx. apply Hin. now right.
          exfalso. assert (Ha : In a (a :: s)) by now left. apply Hin in Ha. destruct Ha as [ | [|]]; auto.
+ destruct H as [pt1 [pt2 [pt3 [n1 [n2 [n3 [H12 [H23 [H13 [Hn1 [Hn2 [Hn3 Hperm]]]]]]]]]]]].
  rewrite Hperm. do 2 rewrite multiset_app. do 3 rewrite multiset_alls.
  do 2 rewrite M.add_union_singleton. rewrite M.support_add; trivial. unfold Rdecidable.eq_dec.
  destruct (InA_dec Rdec pt1 (M.support (M.add pt2 n2 (M.singleton pt3 n3)))) as [Hin | Hin].
  - rewrite M.support_add in Hin; trivial. unfold Rdecidable.eq_dec in Hin.
    destruct (InA_dec (eqA:=eq) Rdec pt2 (M.support (M.singleton pt3 n3))) as [Hin2 | Hin2].
      rewrite M.support_singleton in Hin; try omega. inversion_clear Hin. contradiction. now inversion H.
      inversion_clear Hin. contradiction. rewrite M.support_singleton in H; try omega.
      inversion_clear H. contradiction. now inversion H0.
  - simpl. f_equal. clear Hin. rewrite M.support_add; trivial. unfold Rdecidable.eq_dec.
    destruct (InA_dec Rdec pt2 (M.support (M.singleton pt3 n3))) as [Hin | Hin].
      rewrite M.support_singleton in Hin; try omega. inversion_clear Hin. contradiction. now inversion H.
      simpl. f_equal. rewrite M.support_singleton; simpl; omega.
Qed.


Ltac Rabs :=
  match goal with
    | Hx : ?x <> ?x |- _ => now elim Hx
    | Heq : ?x = ?y, Hneq : ?y <> ?x |- _ => symmetry in Heq; contradiction
    | _ => contradiction
  end.

Corollary nominal_spectrum_Three : forall pos n, 
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  exists pt1 pt2 pt3, exists m, pt1 <> pt2 /\ pt2 <> pt3 /\ pt1 <> pt3 /\ (0 < m <= n)%nat /\
    Permutation (nominal_spectrum pos) (alls pt1 n ++ alls pt2 n ++ alls pt3 m).
Proof.
intros pos n Hmaj H3. rewrite nominal_spectrum_3_stacks in H3.
destruct H3 as [pt1 [pt2 [pt3 [n1 [n2 [n3 [H12 [H23 [H13 [Hn1 [Hn2 [Hn3 Hperm]]]]]]]]]]]].
rewrite Hperm in Hmaj. rewrite majority_stack_Invalid_spec in Hmaj.
destruct Hmaj as [Hn [x [y [Hx [Hy [Hxy Hother]]]]]].
assert (Heqx : x = pt1 \/ x = pt2 \/ x = pt3).
{ rewrite <- Hx in Hn. change (M.In x (multiset (alls pt1 n1 ++ alls pt2 n2 ++ alls pt3 n3))) in Hn.
  rewrite <- M.support_spec, InA_Leibniz, multiset_support in Hn.
  do 2 rewrite in_app_iff in Hn. now destruct Hn as [Hn | [Hn | Hn]]; apply alls_In in Hn; auto. }
assert (Heqy : y = pt1 \/ y = pt2 \/ y = pt3).
{ rewrite <- Hy in Hn. change (M.In y (multiset (alls pt1 n1 ++ alls pt2 n2 ++ alls pt3 n3))) in Hn.
  rewrite <- M.support_spec, InA_Leibniz, multiset_support in Hn.
  do 2 rewrite in_app_iff in Hn. now destruct Hn as [Hn | [Hn | Hn]]; apply alls_In in Hn; auto. }
(* We consider the 6 possible permutations. *)
destruct Heqx as [ | [ | ]]; destruct Heqy as [ | [ | ]]; subst x y; try now elim Hxy.
+ (* x = pt1 & y = pt2 *)
  exists pt1. exists pt2. exists pt3. exists n3. specialize (Hother pt3).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. do 2 Rdec_full; try now symmetry in Heq; contradiction. simpl. intro Hother.
  now repeat split.
+ (* x = pt1 & y = pt3 *)
  exists pt1. exists pt3. exists pt2. exists n2. specialize (Hother pt2).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. apply Permutation_app. reflexivity. apply Permutation_app_comm.
+ (* x = pt2 & y = pt1 *)
  exists pt1. exists pt2. exists pt3. exists n3. specialize (Hother pt3).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. do 2 Rdec_full; try now symmetry in Heq; contradiction. simpl. intro Hother.
  now repeat split.
+ (* x = pt2 & y = pt3 *)
  exists pt2. exists pt3. exists pt1. exists n1. specialize (Hother pt1).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec. repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. now rewrite Permutation_app_comm, app_assoc.
+ (* x = pt3 & y = pt1 *)
  exists pt1. exists pt3. exists pt2. exists n2. specialize (Hother pt2).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec; repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. apply Permutation_app. reflexivity. apply Permutation_app_comm.
+ (* x = pt3 & y = pt2 *)
  exists pt2. exists pt3. exists pt1. exists n1. specialize (Hother pt1).
  repeat rewrite multiset_app, M.union_spec in *. repeat rewrite multiset_alls, M.singleton_spec in *.
  revert Hx Hy; repeat Rdec. repeat Rdec_full; try Rabs; simpl; repeat rewrite plus_0_r; intros; subst.
  revert Hother. Rdec. repeat Rdec_full; try now symmetry in Heq; contradiction. rewrite plus_0_r. intro Hother.
  repeat split; trivial. rewrite Hperm. now rewrite Permutation_app_comm, app_assoc.
Qed.

Theorem Three_grow : forall (da : demonic_action nG 0) pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  let pt := nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0 in
  (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
   >= M.multiplicity pt (multiset (nominal_spectrum pos)))%nat.
Proof.
intros da pos n Hmaj H3. hnf.
pose (pt := nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0%R). fold pt.
(* We simplify the lhs *)
rewrite nominal_spectrum_round_simplify, Hmaj, H3, <- beq_nat_refl.
rewrite multiset_app, M.union_spec.
(* We split the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec. unfold pt.
Rdec. rewrite <- (map_length (gp pos)), <- cardinal_multiset. apply M.cardinal_lower.
Qed.

Theorem Three_wither : forall (da : demonic_action nG 0) pos n,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  length (M.support (multiset (nominal_spectrum pos))) = 3%nat ->
  forall pt, pt <> nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0 ->
  (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
   <= M.multiplicity pt (multiset (nominal_spectrum pos)))%nat.
Proof.
intros da pos n Hmaj H3 pt Hdiff.
(* we first simplify the lhs *)
rewrite nominal_spectrum_round_simplify, Hmaj, H3, <- beq_nat_refl.
rewrite multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* No activated robot goes to pt' as pt' <> pt *)
rewrite map_cst, multiset_alls, M.singleton_spec.
Rdec_full. contradiction. omega.
Qed.

(** If we do not have a majority stack and have more than three stacks,
    then all activated robots except the ones on the extreme positions [x] and [t] go to [(x + t) / 2]. **)
Lemma Generic_min : forall l n x t,
  majority_stack l = Invalid n -> range x t l -> In x l -> In t l -> forall d, hd d (sort l) = x.
Proof.
intros l n x t Hmaj Hrange Hx Ht d. destruct (sort l) eqn:Hl.
- rewrite Permuted_sort, Hl in Hmaj. rewrite majority_stack_nil in Hmaj. discriminate Hmaj.
- apply Rle_antisym.
    rewrite <- Hl. now apply sort_min.
    rewrite range_split in Hrange. destruct Hrange as [Hrange _]. rewrite Forall_forall in Hrange.
    apply Hrange. apply (Permutation_in _ (symmetry (Permuted_sort _))). rewrite Hl. now left.
Qed.

Lemma Generic_max : forall l n x t,
  majority_stack l = Invalid n -> range x t l -> In x l -> In t l -> forall d, last (sort l) d = t.
Proof.
intros l n x t Hmaj Hrange Hx Ht d. destruct (sort l) eqn:Hl.
+ rewrite Permuted_sort, Hl in Hmaj. rewrite majority_stack_nil in Hmaj. discriminate Hmaj.
+ apply Rle_antisym.
  - rewrite range_split, Forall_forall, Forall_forall in Hrange.
    destruct Hrange as [_ Hrange]. apply Hrange. apply (Permutation_in _ (symmetry (Permuted_sort _))).
    rewrite Hl. apply last_In. discriminate.
  - rewrite <- Hl. now apply sort_max.
Qed.

Lemma extreme_center_simplify : forall l n x t,
  majority_stack l = Invalid n -> range x t l -> In x l -> In t l -> extreme_center l = (x + t) / 2.
Proof.
intros l n x t Hmaj Hrange Hx Ht. unfold extreme_center.
erewrite Generic_max, Generic_min; reflexivity || eassumption.
Qed.

Lemma round_simplify_Generic : forall (da : demonic_action nG 0) pos n x t,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  range x t (nominal_spectrum pos) -> In x (nominal_spectrum pos) -> In t (nominal_spectrum pos) ->
  length (M.support (multiset (nominal_spectrum pos))) <> 3%nat ->
  ExtEq (round robogram da (gp pos))
        (fun g => if Rdec (frame da g) 0 then gp pos g else
                  if Rdec (gp pos g) x then x else if Rdec (gp pos g) t then t else (x + t) / 2).
Proof.
intros da pos n min max Hmaj Hrange Hmin Hmax H3.
rewrite round_simplify; trivial. intro g. Rdec_full. reflexivity.
rewrite Hmaj. rewrite <- beq_nat_false_iff in H3. rewrite H3.
assert (Hextreme : forall pt, is_extremal pt (nominal_spectrum pos) = true <-> pt = min \/ pt = max).
{ intro pt. unfold is_extremal. repeat Rdec_full; split; intro H; try reflexivity || discriminate H.
  + clear H. left. rewrite Heq. now apply (@Generic_min (nominal_spectrum pos) n min max).
  + clear H. right. rewrite Heq. now apply (@Generic_max (nominal_spectrum pos) n min max).
  + exfalso. destruct H.
    - apply Hneq0. subst pt. symmetry. now apply (@Generic_min (nominal_spectrum pos) n min max).
    - apply Hneq1. subst pt. symmetry. now apply (@Generic_max (nominal_spectrum pos) n min max). }
destruct (is_extremal (gp pos g) (nominal_spectrum pos)) eqn:Hext.
  rewrite Hextreme in Hext. destruct Hext; repeat Rdec_full; assumption || contradiction.
  repeat Rdec_full.
  - apply (@or_introl _ (gp pos g = max)) in Heq. rewrite <- Hextreme in Heq.
    rewrite Heq in Hext. discriminate Hext.
  - apply (@or_intror (gp pos g = min)) in Heq. rewrite <- Hextreme in Heq.
    rewrite Heq in Hext. discriminate Hext.
  - apply (extreme_center_simplify Hmaj Hrange Hmin Hmax).
Qed.

(** If we have no majority stack (hence more than one stack), then the extreme locations are different. **)
Lemma min_max_diff :
  forall l n x t, majority_stack l = Invalid n -> range x t l -> In x l -> In t l -> x <> t.
Proof.
intros l n x t Hl Hrange Hx Ht Heq. subst t.
rewrite range_split in Hrange. destruct Hrange as [Hrange1 Hrange2]. rewrite Forall_forall in Hrange1, Hrange2.
assert (l = alls x (length l)).
{ rewrite <- (alls_carac x l). intros y Hy. now apply Rle_antisym; apply Hrange1 || apply Hrange2. }
rewrite H, majority_stack_alls in Hl. discriminate Hl.
intro Habs. apply length_0 in Habs. subst l. simpl in Hl. rewrite majority_stack_nil in Hl. discriminate Hl.
Qed.

Lemma map_ExtEq_compat A B : Proper (ExtEq ==> @Permutation A ==> @Permutation B) (@map A B).
Proof.
intros f g Hfg l. induction l; intros l' Hl; simpl.
- apply Permutation_nil in Hl. subst l'. reflexivity.
- assert (Hin : InA eq a l'). { rewrite <- PermutationA_Leibniz in Hl. rewrite <- Hl. now left. }
  apply (PermutationA_split _) in Hin. destruct Hin as [l'' Hl']. rewrite PermutationA_Leibniz in Hl'.
  rewrite Hl'. simpl. f_equal. rewrite Hfg. constructor.
  apply IHl. apply Permutation_cons_inv with a. now transitivity l'.
Qed.

Theorem Generic_grow : forall (da : demonic_action nG 0) pos n x t,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  range x t (nominal_spectrum pos) -> In x (nominal_spectrum pos) -> In t (nominal_spectrum pos) ->
  length (M.support (multiset (nominal_spectrum pos))) <> 3%nat ->
  (M.multiplicity ((x + t) / 2) (multiset (nominal_spectrum pos))
   <= M.multiplicity ((x + t) / 2) (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos))))))%nat.
Proof.
intros da pos n x t Hmaj Hrange Hx Ht H3. hnf.
pose (pt := nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0%R). fold pt.
(* We simplify the lhs *)
rewrite <- beq_nat_false_iff in H3.
rewrite nominal_spectrum_round_simplify, Hmaj, H3, multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Extremal robots are in the same locations in both positions so we can simplify them out *)
(*
SearchAbout Proper M.multiplicity M.eq.
SearchAbout Proper multiset.
SearchAbout Proper map Permutation.
Check (if_ExtEq (fun g => is_extremal (gp pos g) (nominal_spectrum pos)) (gp pos)). (* BUG rewrite? *)
*)
rewrite <- (map_ExtEq_compat (if_ExtEq (fun g => is_extremal (gp pos g) (nominal_spectrum pos)) (gp pos))
                             (reflexivity (active da))).
do 2 rewrite map_cond_Permutation, multiset_app, M.union_spec.
apply plus_le_compat. reflexivity.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec, (extreme_center_simplify Hmaj Hrange Hx Ht).
Rdec. rewrite <- (map_length (gp pos)), <- cardinal_multiset. apply M.cardinal_lower.
Qed.

Theorem Generic_wither : forall (da : demonic_action nG 0) pos n x t,
  majority_stack (nominal_spectrum pos) = Invalid n ->
  range x t (nominal_spectrum pos) -> In x (nominal_spectrum pos) -> In t (nominal_spectrum pos) ->
  length (M.support (multiset (nominal_spectrum pos))) <> 3%nat ->
  forall pt, pt <> ((x + t ) / 2) ->
  (M.multiplicity pt (multiset (nominal_spectrum (lift_gp (round robogram da (gp pos)))))
   <= M.multiplicity pt (multiset (nominal_spectrum pos)))%nat.
Proof.
intros da pos n x t Hmaj Hrange Hx Ht H3 pt Hdiff.
(* We simplify the lhs *)
rewrite <- beq_nat_false_iff in H3.
rewrite nominal_spectrum_round_simplify, Hmaj, H3, multiset_app, M.union_spec.
(* Same thing for the rhs *)
rewrite (nominal_spectrum_simplify da), multiset_app, M.union_spec.
(* Non activated robots are in the same locations in both positions so we can simplify them out *)
apply plus_le_compat. reflexivity.
(* Extremal robots are in the same locations in both positions so we can simplify them out *)
(*
SearchAbout Proper M.multiplicity M.eq.
SearchAbout Proper multiset.
SearchAbout Proper map Permutation.
Check (if_ExtEq (fun g => is_extremal (gp pos g) (nominal_spectrum pos)) (gp pos)). (* BUG rewrite? *)
*)
rewrite <- (map_ExtEq_compat (if_ExtEq (fun g => is_extremal (gp pos g) (nominal_spectrum pos)) (gp pos))
                             (reflexivity (active da))).
do 2 rewrite map_cond_Permutation, multiset_app, M.union_spec.
apply plus_le_compat. reflexivity.
(* Among those that are activated, at most all can be at position pt *)
rewrite map_cst, multiset_alls, M.singleton_spec, (extreme_center_simplify Hmaj Hrange Hx Ht).
Rdec_full. contradiction. omega.
Qed.

Theorem Stack_at_meeting : forall pos pt (d : demon nG 0) k,
  kFair k d -> Stack_at pt pos -> WillGather pt (execute robogram d (gp pos)).
Proof.
Admitted.

Theorem gathered_at_forever : forall pt gp (da : demonic_action nG 0),
  gathered_at pt gp -> gathered_at pt (round robogram da gp).
Proof.
intros pt gp [] Hgather. unfold round. simpl.
intro g. destruct (Rdec (frame g) 0). now apply Hgather.
rewrite Hgather. rewrite <- Rplus_0_r. f_equal. rewrite <- (Rmult_0_r (/ frame g)). f_equal.
unfold similarity. simpl. rewrite (spectrum_exteq g _ (lift_gp (fun _ => 0))). unfold robogram.
assert (spectrum_of g (lift_gp (fun _ => 0)) = alls 0 nG) as Heq.
{ apply Permutation_alls.
  transitivity (nominal_spectrum (lift_gp (fun _ : G nG => 0))).
    now apply spectrum_ok.
    now rewrite nominal_spectrum_alls. }
rewrite Heq. unfold majority_stack.
rewrite multiset_alls, M.fold_singleton; simpl; try omega.
  reflexivity.
  generalize size_G. omega.
  now repeat intro; subst.
  split; (now intros []) || intro x; simpl.
    rewrite Hgather, Rminus_diag_eq. now rewrite Rmult_0_r.
    reflexivity.
    now apply Fin.case0.
Qed.

Lemma Permutation_eq_pair_equiv : forall l1 l2, Permutation l1 l2 <-> PermutationA M.eq_pair l1 l2.
Proof.
assert (HeqA : (eq ==> eq ==> iff)%signature Logic.eq M.eq_pair).
{ intros [? ?] ? ? [? ?] ? ?. subst. now split; intro H; inversion H; reflexivity || hnf in *; simpl in *; subst. }
intros l1 l2. rewrite <- PermutationA_Leibniz. now apply (PermutationA_eq_compat HeqA).
Qed.

Lemma forbidden_elements_perm : forall pos,
  forbidden pos <-> exists pt1 pt2, pt1 <> pt2 /\ Permutation (M.elements (multiset (nominal_spectrum pos)))
                                                              ((pt1, div2 nG) :: (pt2, div2 nG) :: nil).
Proof.
intro pos. split; intros [pt1 [pt2 [Hneq Hpos]]]; exists pt1; exists pt2; split; trivial.
+ rewrite Permutation_eq_pair_equiv, Hpos, multiset_app, multiset_alls, multiset_alls, M.add_union_singleton.
  apply (NoDupA_equivlistA_PermutationA _).
  - apply (NoDupA_strengthen _ (M.elements_NoDupA _)).
  - apply NoDupA_2. intros [Habs _]. apply Hneq. apply Habs.
  - intros [x n]. rewrite M.elements_add. simpl. split; intro H.
      destruct H as [[? [? H]] | [_ H]].
        subst. rewrite M.singleton_spec. Rdec_full. contradiction. rewrite plus_0_r. now left.
        right. rewrite M.elements_spec in H. destruct H as [H Hn]. simpl in H. rewrite M.singleton_spec in H.
        revert H. Rdec_full; intro H. subst. now left. simpl in Hn. omega.
      rewrite M.singleton_spec. inversion_clear H.
        left. destruct H0. hnf in *; simpl in *. subst. repeat split.
          Rdec_full. contradiction. symmetry. now apply plus_0_r.
          now apply half_size_pos.
        right. inversion_clear H0.
          split.
            destruct H as [H _]. hnf in H. simpl in H. subst. now auto.
            rewrite M.elements_singleton. now left. now apply half_size_pos.
          inversion H.
+ assert (Hin : forall xn, InA M.eq_pair xn (M.elements (multiset (nominal_spectrum pos)))
                           <-> (fst xn = pt1 \/ fst xn = pt2) /\ snd xn = div2 nG).
  { intros [x n]. rewrite Permutation_eq_pair_equiv in Hpos. rewrite Hpos.
    split; intro H.
    + inversion H.
      - destruct H1. hnf in *; simpl in *. subst. auto.
      - inversion H1.
          destruct H4. hnf in *; simpl in *. subst. auto.
          inversion H4.
    + simpl in H. destruct H as [[? | ? ] ?]; subst.
        now left.
        now right; left. }
  (* If (x, n) belongs to elements l, then Permutation l alls x n ++ l' for some l' not containg x.
     Let do this twice to remove all elements of elements l. *)
  assert (Hmul1 : M.multiplicity pt1 (multiset (nominal_spectrum pos)) = div2 nG).
  { apply proj1 with (div2 nG > 0)%nat. rewrite <- (M.elements_spec (pt1, div2 nG)).
    rewrite Hin. now split; try left. }
  assert (Hmul2 : M.multiplicity pt2 (multiset (nominal_spectrum pos)) = div2 nG).
  { apply proj1 with (div2 nG > 0)%nat. rewrite <- (M.elements_spec (pt2, div2 nG)).
    rewrite Hin. now split; try right. }
  apply multiset_Permutation in Hmul1. destruct Hmul1 as [l [Hl Hperm]].
  rewrite Hperm. apply Permutation_app. reflexivity.
  rewrite Hperm, multiset_app, M.union_spec, multiset_alls, M.singleton_spec in Hmul2.
  revert Hmul2. Rdec_full. symmetry in Heq. contradiction. clear Hneq0. simpl. intro Hmul2.
  apply multiset_Permutation in Hmul2. destruct Hmul2 as [l' [Hl' Hperm']].
  rewrite <- app_nil_r, Hperm'. apply Permutation_app. reflexivity.
  (* Now we must prove that there is no other element in the spectrum because there is none in its multiset. *)
  destruct l'. reflexivity. exfalso. cut (e = pt1 \/ e = pt2).
  - intros [? | ?]; subst e.
      apply Hl. rewrite Hperm'. apply in_app_iff. now right; left.
      apply Hl'. now left.
  - apply proj1 with (M.multiplicity e (multiset l) = div2 nG).
    rewrite <- (Hin (e, M.multiplicity e (multiset l))). rewrite Hperm.
    rewrite multiset_app, multiset_alls, M.elements_union. simpl. unfold M.In.
    rewrite M.singleton_spec. Rdec_full.
      elim Hl. subst e. rewrite Hperm'. rewrite in_app_iff. now right; left.
      split.
        right. rewrite Hperm', multiset_app, multiset_alls, multiset_cons, M.union_spec, M.add_spec. simpl. omega.
        reflexivity.
Qed.

Corollary forbidden_elements : forall pos,
  forbidden pos <-> exists pt1 pt2, pt1 <> pt2
                    /\ M.elements (multiset (nominal_spectrum pos)) = (pt1, div2 nG) :: (pt2, div2 nG) :: nil.
Proof.
intro pos. rewrite forbidden_elements_perm. split; intros [pt1 [pt2 [Hdiff H]]].
+ symmetry in H. apply Permutation_length_2_inv in H. destruct H as [H | H].
  - exists pt1. exists pt2. auto.
  - exists pt2. exists pt1. auto.
+ exists pt1. exists pt2. rewrite H. auto.
Qed.

Corollary forbidden_multiplicity : forall pos,
  forbidden pos <-> exists pt1 pt2, pt1 <> pt2
              /\ M.multiplicity pt1 (multiset (nominal_spectrum pos)) = div2 nG
              /\ M.multiplicity pt2 (multiset (nominal_spectrum pos)) = div2 nG
              /\ forall pt, pt <> pt1 -> pt <> pt2 -> M.multiplicity pt (multiset (nominal_spectrum pos)) = 0%nat.
Proof.
intro pos. split; intros [pt1 [pt2 [Hdiff H]]].
+ exists pt1. exists pt2. repeat split.
  - assumption.
  - apply proj1 with (div2 nG > 0)%nat. rewrite H, multiset_app, M.union_spec.
    do 2 rewrite multiset_alls, M.singleton_spec. Rdec. Rdec_full. contradiction. split.
      now apply plus_0_r.
      now apply half_size_pos.
  - apply proj1 with (div2 nG > 0)%nat. rewrite H, multiset_app, M.union_spec.
    do 2 rewrite multiset_alls, M.singleton_spec. Rdec. Rdec_full. symmetry in Heq. contradiction. split.
      reflexivity.
      now apply half_size_pos.
  - intros pt Hdiff1 Hdiff2. rewrite H, multiset_app, M.union_spec.
    do 2 rewrite multiset_alls, M.singleton_spec. now do 2 Rdec_full.
+ rewrite forbidden_elements_perm. exists pt1. exists pt2. split; trivial.
  apply Permutation_eq_pair_equiv. apply (NoDupA_equivlistA_PermutationA _).
  - apply (NoDupA_strengthen _ (M.elements_NoDupA _)).
  - apply NoDupA_2. intros [Habs _]. apply Hdiff. apply Habs.
  - intros [x n]. destruct H as [Hin1 [Hin2 Hin]]. destruct (Rdec x pt1).
      subst. rewrite M.elements_spec. simpl. rewrite Hin1. split; intro H.
        now left.
        inversion_clear H.
          destruct H0 as [_ H]. hnf in H; simpl in H. subst n. split. reflexivity. now apply half_size_pos.
          inversion_clear H0. destruct H as [Habs _]. elim Hdiff. now apply Habs. now inversion H.
      destruct (Rdec x pt2).
        subst. rewrite M.elements_spec. simpl. rewrite Hin2. split; intro H.
          now right; left.
          inversion_clear H.
            destruct H0 as [Habs _]. elim Hdiff. symmetry. now apply Habs.
            inversion_clear H0.
              destruct H as [_ H]. hnf in H; simpl in H. subst n. split. reflexivity. now apply half_size_pos.
              now inversion H.
        split; intro H.
          rewrite M.elements_spec in H. rewrite Hin in H; try assumption. simpl in H. omega.
          inversion_clear H.
            destruct H0 as [H _]. hnf in H; simpl in H. contradiction.
            inversion_clear H0.
              destruct H as [H _]. hnf in H; simpl in H. contradiction.
              now inversion H.
Qed.

Lemma forbidden_even : forall pos, forbidden pos -> NPeano.Even nG.
Proof.
intros pos [pt1 [pt2 [Hdiff Hperm]]]. exists (div2 nG).
rewrite <- plus_0_r at 1. rewrite <- (nominal_spectrum_length pos).
rewrite Hperm, app_length, alls_length, alls_length. omega.
Qed.

Lemma Stack_at_forbidden : forall pt pos, Stack_at pt pos -> ~forbidden pos.
Proof.
intros pt pos [n [Hstack Hother]] [pt1 [pt2 [Hdiff Habs]]]. revert Hstack Hother.
setoid_rewrite Habs.
setoid_rewrite multiset_app. setoid_rewrite M.union_spec.
setoid_rewrite multiset_alls. setoid_rewrite M.singleton_spec.
do 2 Rdec_full; try subst pt.
- contradiction.
- rewrite plus_0_r. intro. subst. intro H. specialize (H pt2 Hdiff). revert H. Rdec. intro. omega.
- simpl. intro. subst. intro H. specialize (H pt1 Hneq). revert H. Rdec. intro. omega.
- simpl. intro. subst. intro H. specialize (H pt1 Hneq). revert H. Rdec. intro. omega.
Qed.


Theorem never_forbidden : forall (da : demonic_action nG 0) pos,
  ~forbidden pos -> ~forbidden (lift_gp (round robogram da pos.(gp))).
Proof.
intros da pos Hok.
(* Three cases for the robogram *)
destruct (majority_stack (nominal_spectrum pos)) eqn:Hs.
+ (* Absurd case: no robot *)
  rewrite majority_stack_NoResult_spec in Hs. elim (nominal_spectrum_nil _ Hs).
+ (* 1) There is a majority stack *)
  apply Stack_at_forbidden with l. apply Stack_at_forever. rewrite <- majority_stack_spec. now exists n.
+ (* We express more directly the position after one round *)
  destruct (beq_nat (length (M.support (multiset (nominal_spectrum pos)))) 3) eqn:Hn.
  - (* 2) There are exactly three stacks *)
    rewrite round_simplify, Hs, Hn. rewrite beq_nat_true_iff in Hn.
    destruct (nominal_spectrum_Three _ Hs Hn) as [pt1 [pt2 [pt3 [m [H12 [H23 [H13 [[Hlt Hle] Hperm]]]]]]]].
    assert (Hsup : Permutation (M.support (multiset ((nominal_spectrum pos)))) (pt1 :: pt2 :: pt3 :: nil)).
    { rewrite <- PermutationA_Leibniz. apply (NoDupA_equivlistA_PermutationA _).
      - apply (NoDupA_strengthen _ (M.support_NoDupA _)).
      - now apply NoDupA_3.
      - intro x. do 2 rewrite InA_Leibniz. rewrite multiset_support, Hperm.
        do 2 rewrite in_app_iff. repeat rewrite alls_In_iff; try omega.
        split; intros [? | [? | ?]];  try (now left) || (now right; left) || (now do 2 right) || idtac.
        now do 2 right; left. destruct H. now do 2 right. inversion H. }
    assert (Hext : ExtEq (fun g => if Rdec (frame da g) 0 then gp pos g
                                   else nth 1 (sort (M.support (multiset (nominal_spectrum pos)))) 0)
                         (fun g => if Rdec (frame da g) 0 then gp pos g
                                   else nth 1 (sort (pt1 :: pt2 :: pt3 :: nil)) 0)).
    { intro g. Rdec_full. reflexivity. now rewrite Hsup. }
    rewrite Hext. clear Hext.
    intros [x [y [Hxy Hperm']]].
  - (* 3) We are in the Generic case *)
Qed.

Theorem Will_stack : forall da pos, ~forbidden pos -> (forall pt, ~Stack_at pt pos) ->
  Stack_at (lift_gp (round robogram da pos.(gp))).
Proof.
intros da pos Hok Hyet.
rewrite <- majority_stack_spec in Hyet.
assert (exists n, majority_stack (nominal_spectrum pos) = Invalid n).
{ destruct (majority_stack (nominal_spectrum pos)) eqn:Hpos.
  - rewrite majority_stack_NoResult_spec in Hpos. rewrite nominal_spectrum4 in Hpos. discriminate Hpos.
  - elim Hyet. exists l. exists n. reflexivity.
  - exists n. reflexivity. }
destruct H as [n Hn]. clear Hyet.
(* We express more directly the position after one round *)
assert (Heq : ExtEq (round robogram da (gp pos))
             (fun g => if is_extremal (gp pos g) (nominal_spectrum pos)
                       then gp pos g else extreme_center (nominal_spectrum pos))).
{ etransitivity. apply round_simplify. assumption.
  intro g. destruct (Rdec (frame da g) 0) as [| Hframe]. now elim (active da g).
  now rewrite Hn. }
assert (Hl : length (sort (nominal_spectrum pos)) = 4%nat).
{ rewrite (Permutation_length (symmetry (Permuted_sort _))). now rewrite nominal_spectrum4. }
assert (Hperm := Permuted_sort (nominal_spectrum pos)).
assert (Hsort := Sorted_sort (nominal_spectrum pos)).
destruct (sort (nominal_spectrum pos)) as [| x [| y [| z [| t [| ]]]]] eqn:Hs; try discriminate Hl. clear Hl.
inversion_clear Hsort. inversion_clear H. inversion_clear H1. clear H. unfold is_true in *. rewrite Rleb_spec in *.
assert (Hd := Invalid_spectrum_simplify Hok Hn).
rewrite Hperm in Hd. inversion_clear Hd. inversion_clear H1. inversion_clear H5.
assert (Hxy : x < y). { apply Rle_neq_lt. assumption. intro. subst y. apply H. now left. }
assert (Hyz : y < z). { apply Rle_neq_lt. assumption. intro. subst y. apply H4. now left. }
assert (Hzt : z < t). { apply Rle_neq_lt. assumption. intro. subst z. apply H1. now left. }
clear H H0 H1 H2 H3 H4 H6.
assert (x <> t) by lra. assert (x <> (x + t) / 2) by lra. assert (t <> (x + t) / 2) by lra.
assert (Hperm2 : Permutation (nominal_spectrum (lift_gp (round robogram da (gp pos))))
                             (x :: (x + t) / 2 :: (x + t) / 2 :: t :: nil)).
{ apply (@nominal_spectrum_simplify da pos n x t Hok Hn).
  - rewrite range_split. do 2 rewrite Forall_forall. split; intros a Hin.
      change x with (hd 0 (x :: y :: z :: t :: nil)). rewrite <- Hs. now apply sort_min.
      change t with (last (x :: y :: z :: t :: nil) 0). rewrite <- Hs. now apply sort_max.
  - rewrite Hperm. now left.
  - rewrite Hperm. now do 3 right; left. }
exists (extreme_center (nominal_spectrum pos)). exists 2%nat. split.
+ unfold is_extremal, extreme_center. rewrite Hs, Hperm2. simpl.
  repeat rewrite multiset_cons.
  now rewrite M.add_spec', M.add_spec, M.add_spec, M.add_spec', multiset_nil, M.empty_spec.
+ unfold is_extremal, extreme_center. intro pt. rewrite Hs, Hperm2. simpl. repeat rewrite multiset_cons.
  intro Hy. destruct (Rdec x pt).
    subst pt. now rewrite M.add_spec, M.add_spec', M.add_spec', M.add_spec', multiset_nil, M.empty_spec; auto.
    destruct (Rdec t pt).
      subst pt. now rewrite M.add_spec', M.add_spec', M.add_spec', M.add_spec, multiset_nil, M.empty_spec; auto.
      now rewrite M.add_spec', M.add_spec', M.add_spec', M.add_spec', multiset_nil, M.empty_spec; auto.
Qed.


Lemma gathered_at_PosEq : forall (gp : Four -> R) pt, gathered_at gp pt -> ExtEq gp (fun _ => pt).
Proof. intros gp pt Hgather. intro n. apply Hgather. Qed.

Lemma gathered_at_Gather : forall pt (d : demon Four Zero) gp, gathered_at gp pt ->
  Gather pt (execute robogram d gp).
Proof.
intro pt. cofix gather. intros d gp Hgather. constructor. apply Hgather.
rewrite execute_tail. apply gather. now apply gathered_at_forever.
Qed.

Theorem stack_gathered_at : forall (da : demonic_action Four Zero) gp pt n, ~forbidden (lift_gp gp) ->
  majority_stack (nominal_spectrum (lift_gp gp)) = Valid pt n ->
  gathered_at (round robogram da gp) pt.
Proof.
intros da gp pt n Hok Hstack g. unfold round.
pose (s := spectrum_of da g ((⟦frame da g, gp g⟧) {| gp := gp; bp := locate_byz da |})). fold s.
destruct (Rdec (frame da g) 0).
  now elim (active da g). (* Stalling case *)
  unfold robogram.
  assert (Hfor : is_forbidden s = false).
  { unfold s. rewrite spectrum_ok. rewrite is_forbidden_false. intro Habs. apply Hok.
    revert Habs. setoid_rewrite lift_gp_equiv at 2. simpl. apply forbidden_similarity_invariant. }
  rewrite Hfor. clear Hfor.
  assert (Hperm : Permutation s (nominal_spectrum (⟦frame da g, gp g⟧ {| gp := gp; bp := locate_byz da |})))
  by apply da.(spectrum_ok).
  rewrite <- is_forbidden_false in Hok. rewrite Hperm. setoid_rewrite lift_gp_equiv at 2.
  simpl. rewrite <- (majority_stack_Valid_similarity (gp g) _ _ _ (active da g)) in Hstack.
  rewrite Hstack. now field.
Qed.

Corollary stack_sol : forall k (d : demon Four Zero), kFair k d ->
  forall gp : Four -> R, ~forbidden (lift_gp gp) ->
  Stack (lift_gp gp) ->
  exists pt, WillGather pt (execute robogram d gp).
Proof.
intros k [da d] Hfair gp Hok Hstack.
assert (Hs := Hstack). rewrite <- majority_stack_spec in Hs. destruct Hs as [pt [n Hpt]].
exists pt. constructor 2. constructor 1.
rewrite execute_tail. cofix gathered. constructor. clear gathered. simpl. now apply stack_gathered_at with n.
(* back to coinduction *)
apply gathered. (* ill-formed recursive definition: we cannot use stack_gathered *)
Admitted.

Theorem meeting4 :
  forall d : demon Four Zero, forall k, kFair k d -> solGathering robogram d.
Proof.
intros d k Hfair gp Hok.
destruct (majority_stack (nominal_spectrum (lift_gp gp))) as [| r n | n] eqn:Hdup.
  (* there is no robot *)
  rewrite majority_stack_NoResult_spec in Hdup. rewrite nominal_spectrum4 in Hdup. discriminate Hdup.
  (* there is a stack *)
  apply (stack_sol Hfair Hok). rewrite <- majority_stack_spec. now exists r; exists n.
  (* there is no stack, it will be created at the next step *)
  inversion_clear Hfair as [_ Htfair].
  destruct (stack_sol Htfair (@never_forbidden (demon_head d) _ Hok)) as [pt Hpt].
    apply Will_stack. assumption. rewrite <- majority_stack_spec.
    intros [x [m Habs]]. rewrite Hdup in Habs. discriminate Habs.
    exists pt. constructor 2. rewrite execute_tail. exact Hpt.
Qed.
Print Assumptions meeting4.

