(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence.    *)
(*                                                                        *)
(**************************************************************************)

(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)

Require Import Utf8_core.
Require Import Omega.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Pactole.Util.Preliminary.
Require Export Pactole.Util.FSets.FSetInterface.
Require Export Pactole.Util.FSets.FSetFacts.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.RobotInfo.
Require Import Pactole.Spectra.Definition.


Section SetConstruction.

Context {loc : Type}.
Context `{EqDec loc}.

(* FIXME: remove once we have the implem in FSetList. *)
Context {FS : @FSet loc _ _}.
Context {FSSpec : @FSetSpecs loc _ _ FS}.
(* Existing Instance multiplicity_compat.
Existing Instance FMOps_WMap.
Existing Instance MakeFMultisetsFacts. *)

Ltac fsetdec := set_iff; tauto.

(* 
Lemma eq_refl_left : forall (e : loc) A (a b:A), (if equiv_dec e e then a else b) = a.
Proof.
intros e A a b.
destruct (equiv_dec e e) as [| Hneq].
- reflexivity.
- now elim Hneq.
Qed.
 *)
(* 
Notation "m1  ≡  m2" := (M.eq m1 m2) (at level 70).
Notation "m1  ⊆  m2" := (M.Subset m1 m2) (at level 70).
Notation "m1  [=]  m2" := (M.eq m1 m2) (at level 70, only parsing).
Notation "m1  [c=]  m2" := (M.Subset m1 m2) (at level 70, only parsing).
 *)

(** **  Building sets from lists  **)

Definition make_set l := fold_left (fun acc x => add x acc) l empty.

Lemma make_set_nil : make_set nil == empty.
Proof. reflexivity. Qed.

Lemma make_set_cons_aux : forall l x m,
  List.fold_left (fun acc y => add y acc) (x :: l) m ==
  add x (List.fold_left (fun acc x => add x acc) l m).
Proof.
intro l. induction l as [| e l]; intros x s.
+ reflexivity.
+ simpl fold_left.
  assert (Hf : Proper (equiv ==> equiv ==> equiv) (fun acc y => add y acc)).
  { clear x. intros s1 s2 Hs x y Hxy. now rewrite Hxy, Hs. }
  rewrite (@fold_left_start _ _ equiv equiv _ _ _ Hf l _ (add x (add e s))).
  apply IHl. intro. fsetdec.
Qed.

Lemma make_set_cons : forall x l, make_set (x :: l) == add x (make_set l).
Proof. intros x l. unfold make_set. now rewrite make_set_cons_aux. Qed.

Lemma make_set_empty : forall l, make_set l == empty <-> l = nil.
Proof.
intro l. split; intro Hl.
+ destruct l as [| x l]. reflexivity. rewrite make_set_cons in Hl.
  specialize (Hl x). rewrite add_spec, empty_spec in Hl. intuition.
+ subst l. apply make_set_nil.
Qed.

Lemma make_set_app : forall l l', make_set (l ++ l') == union (make_set l) (make_set l').
Proof.
induction l as [| e l]; intros l'.
+ rewrite make_set_nil. simpl. intro. fsetdec.
+ simpl List.app. rewrite 2 make_set_cons, IHl. intro. fsetdec.
Qed.

Instance make_set_compat : Proper (PermutationA equiv ==> equiv) make_set.
Proof.
intro l1. induction l1 as [| x l1]; intros l2 Hperm.
+ apply (PermutationA_nil _) in Hperm. now subst.
+ assert (Hx := @PermutationA_InA_inside _ _ _ x _ _ Hperm).
  destruct Hx as [l1' [y [l2' [Hxy Heq]]]]. now left. subst l2.
  intro z. rewrite make_set_app, union_spec, 2 make_set_cons.
  destruct (x =?= z) as [Heq | Hneq].
  - rewrite Heq in *. rewrite <- Hxy. repeat rewrite add_spec. intuition.
  - rewrite <- (PermutationA_middle _), Hxy in Hperm. apply (PermutationA_cons_inv _) in Hperm.
    repeat rewrite add_spec. rewrite (IHl1 _ Hperm). rewrite make_set_app, Hxy. fsetdec.
Qed.

Lemma make_set_PermutationA : forall x l,
  exists l' n, ~InA equiv x l' /\ PermutationA equiv l (alls x n ++ l').
Proof.
intros x l. induction l as [| e l].
* exists nil, 0. split. now auto. simpl. reflexivity.
* destruct IHl as [l' [n [Hin Hperm]]]. destruct (e =?= x) as [Heq | Heq].
  + exists l', (S n). split; trivial. simpl. apply PermutationA_cons; assumption.
  + exists (e :: l'), n. split.
    - intro Habs. inversion_clear Habs. elim Heq. now symmetry. contradiction.
    - rewrite Hperm. apply (PermutationA_middle _).
Qed.

Lemma make_set_alls : forall x n, 0 < n -> make_set (alls x n) == singleton x.
Proof.
intros x n Hn. induction n; simpl alls.
+ inversion Hn.
+ rewrite make_set_cons. destruct n.
  - simpl alls. rewrite make_set_nil. intro. fsetdec.
  - rewrite IHn. intro. fsetdec. omega.
Qed.

Theorem make_set_spec : forall x l, In x (make_set l) <-> InA equiv x l.
Proof.
intros x l. induction l.
+ rewrite make_set_nil, InA_nil. fsetdec.
+ rewrite make_set_cons, add_spec, IHl. intuition. inversion_clear H2; auto.
Qed.

Theorem cardinal_make_set : forall l, cardinal (make_set l) <= length l.
Proof.
induction l as [| x l]; simpl.
+ now rewrite make_set_nil, cardinal_empty.
+ transitivity (S (cardinal (make_set l))); try omega; [].
  rewrite make_set_cons, 2 cardinal_spec.
  change (S (length (elements (make_set l))))
    with (length (x :: elements (make_set l))).
  apply NoDupA_inclA_length with equiv.
  - autoclass.
  - apply elements_NoDupA.
  - apply elements_add_incl.
Qed.

Theorem cardinal_NoDupA_make_set : forall l, NoDupA equiv l -> cardinal (make_set l) = length l.
Proof.
intros l Hl. induction l as [| x l]; simpl.
- now rewrite make_set_nil, cardinal_empty.
- inv Hl. rewrite <- IHl; trivial; [].
  rewrite make_set_cons, cardinal_add; trivial; [].
  now rewrite make_set_spec.
Qed.

Instance fold_compat {A B} `{FSetSpecs A} `{Setoid B} :
  forall f : A -> B -> B, Proper (equiv ==> equiv ==> equiv) f -> transpose equiv f ->
  forall a, Proper (equiv ==> equiv) (fun x => fold f x a).
Proof.
intros f Hf Ht a m1 m2 Heq. do 2 rewrite fold_spec.
rewrite fold_left_symmetry_PermutationA; autoclass; [|].
- repeat intro. now apply Hf.
- now rewrite Heq.
Qed.

Lemma fold_left_add_acc {A B} `{FSet A} `{FSetSpecs B} : forall (f : A -> B), Proper (equiv ==> equiv) f ->
  forall x l acc, In x (fold_left (fun acc y => add (f y) acc) l acc)
                  <-> In x acc \/ exists y, InA equiv y l /\ x == f y.
Proof.
intros f Hf x l. induction l as [| e l]; intro acc; simpl.
+ intuition.
  match goal with H : exists _, InA _ _ nil /\ _ |- _ =>
    destruct H as [? [H _]]; now rewrite InA_nil in H end.
+ rewrite IHl. set_iff. split; intro Hin.
  - destruct Hin as [[? | ?] | [? [? ?]]]; try tauto; eauto.
  - destruct Hin as [Heq | [? [Hin Heq]]]; tauto || inv Hin; eauto.
    do 2 left. match goal with H : _ == e |- _ => now rewrite <- H end.
Qed.

(* Instance elements_compat : Proper (equiv ==> PermutationA equiv) elements := elements_compat. *)
Definition map {A B} `{FSet A} `{FSet B} (f : A -> B) m :=
  fold (fun x acc => add (f x) acc) m empty.

Instance map_compat : forall f, Proper (equiv ==> equiv) f ->
  Proper (equiv ==> equiv) (map f).
Proof.
intros f Hf m₁ m₂ Hm. unfold map. apply fold_compat; autoclass; [|].
- repeat intro. now repeat f_equiv.
- repeat intro. fsetdec.
Qed.

Lemma map_empty : forall f, map f empty == empty.
Proof. intro. unfold map. rewrite fold_spec, elements_empty. simpl. reflexivity. Qed.

(*
Lemma fold_add_out {A B} `{FSetSpecs A} `{Setoid B} :
  forall (f : A -> B -> B), Proper (equiv ==> equiv ==> equiv) f -> transpose2 equiv f ->
  forall x m acc, ~In x m -> fold f (add x m) acc == fold f m (f x acc).
Proof.
intros f Hf Hf2 x m acc Hx.
assert (Hf' : Proper (equiv ==> equiv ==> equiv) (fun x y => f y x)).
{ repeat intro. now apply Hf. }
assert (Hf2' : forall x y z, f y (f x z) == (f x (f y z))) by auto.
assert (Hperm : PermutationA equiv (elements {x; m}) (x :: elements m)).
{ apply NoDupA_equivlistA_PermutationA; autoclass.
  + apply elements_NoDupA.
  + constructor.
    - now rewrite elements_spec.
    - apply elements_NoDupA.
  + intro y. rewrite elements_spec. set_iff.
    split; intro Hin.
    - intuition.
    - inv Hin. now left. rewrite <- elements_spec; auto. }
rewrite 2 fold_spec.
rewrite (fold_left_symmetry_PermutationA _ _ Hf' Hf2');
try apply Hperm; simpl; reflexivity.
Qed.

Lemma fold_add_in {A B} `{FSetSpecs A} `{Setoid B} :
  forall (f : A -> B -> B), Proper (equiv ==> equiv ==> equiv) f -> transpose2 equiv f ->
  forall x m acc, In x m -> fold f (add x m) acc == fold f m acc.
Proof.
intros f Hf Hf2 x m acc Hx.
assert (Hf' : Proper (equiv ==> equiv ==> equiv) (fun x y => f y x)).
{ repeat intro. now apply Hf. }
assert (Hf2' : forall x y z, f y (f x z) == (f x (f y z))) by auto.
assert (Hperm : PermutationA equiv (elements {x; m}) (elements m)).
{ apply NoDupA_equivlistA_PermutationA; autoclass.
  + apply elements_NoDupA.
  + apply elements_NoDupA.
  + intro y. rewrite 2 elements_spec. set_iff. intuition. rewrite <- In_eq_iff; eauto. }
rewrite 2 fold_spec.
rewrite (fold_left_symmetry_PermutationA _ _ Hf' Hf2');
try apply Hperm; simpl; reflexivity.
Qed.

Lemma map_In {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall x m, In x m -> In (f x) (map f m).
Proof.
intros f Hf x m Hin.
unfold map. generalize empty.
setoid_rewrite fold_spec. rewrite <- elements_spec in Hin.
induction (elements m); intro acc.
+ now rewrite InA_nil in Hin.
+ inv Hin; simpl.
  - match goal with H : _ == _ |- _ => rewrite H end.
    rewrite fold_left_add_acc, add_spec; trivial; []. now do 2 left.
  - now apply IHl.
Qed.

Lemma map_add {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall x m, map f (add x m) == add (f x) (map f m).
Proof.
intros f Hf x m y.
assert (Proper (equiv ==> equiv ==> equiv) (fun x acc => add (f x) acc)).
{ intros ? ? Heq ? ? Heq' ?. rewrite Heq, Heq'. fsetdec. }
assert (transpose2 equiv (fun x acc => add (f x) acc)).
{ intros ? ? ? ? Heq ?. rewrite Heq. fsetdec. }
destruct (mem x m) eqn:Hin.
+ rewrite mem_spec in Hin. unfold map at 1.
  rewrite fold_add_in; autoclass; [].
  change (fold (fun x acc => add (f x) acc) m empty) with (map f m).
  set_iff. intuition.
  match goal with H : _ == _ |- _ => rewrite <- H end.
  now apply map_In.
+ rewrite mem_false in Hin. unfold map at 1.
  rewrite fold_add_out, fold_spec, fold_left_add_acc; autoclass; [].
  set_iff.
  split; intro Hy.
  - destruct Hy as [[|] | [? [Hy Heq]]]; try tauto; [].
    right. rewrite Heq. rewrite elements_spec in Hy. now apply map_In.
  - unfold map in Hy. rewrite fold_spec, fold_left_add_acc, empty_spec in Hy; trivial; [].
    destruct Hy as [? | [? | [? [Hy Heq]]]]; eauto.
Qed.
*)

Lemma map_spec {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall y s, In y (map f s) <-> exists x, In x s /\ y == (f x).
Proof.
intros f Hf y s. unfold map.
rewrite fold_spec, fold_left_add_acc, empty_spec; trivial; [].
setoid_rewrite elements_spec. intuition.
Qed.

Corollary map_In {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall x m, In x m -> In (f x) (map f m).
Proof. repeat intro. rewrite map_spec; eauto. Qed.

Corollary map_add {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f : A -> B, Proper (equiv ==> equiv) f ->
  forall x m, map f (add x m) == add (f x) (map f m).
Proof.
intros f Hf x m y. set_iff. rewrite 2 map_spec; trivial; [].
split; intro Hin.
+ destruct Hin as [? [Hin Hy]]. revert Hin. set_iff. intros [Hx | Hin].
  - rewrite Hy, Hx. now left.
  - right. eauto.
+ destruct Hin as [Hy | [? [Hin Hx]]]; eexists; set_iff; eauto.
Qed.

Lemma map_injective_elements {A B} `{FSetSpecs A} `{FSetSpecs B} : forall f,
  Proper (equiv ==> equiv) f ->
  injective equiv equiv f ->
  forall s, PermutationA equiv (elements (map f s)) (List.map f (elements s)).
Proof.
intros f Hf Hf2 s.
apply NoDupA_equivlistA_PermutationA; autoclass.
+ apply elements_NoDupA.
+ eapply map_injective_NoDupA, elements_NoDupA; autoclass.
+ intro y.
  rewrite elements_spec, map_spec, InA_map_iff; autoclass; [].
  split; intros [x [Hx1 Hx2]].
  - exists x. rewrite elements_spec. auto.
  - exists x. rewrite <- elements_spec. now symmetry in Hx1.
Qed.


Theorem make_set_map : forall f, Proper (equiv ==> equiv) f ->
  forall l, make_set (List.map f l) == map f (make_set l).
Proof.
intros f Hf l. induction l; simpl List.map.
+ now rewrite make_set_nil, map_empty.
+ do 2 rewrite make_set_cons. now rewrite map_add, IHl.
Qed.

End SetConstruction.

(** Building a spectrum from a configuration *)

Section SetSpectrum.

Context {loc info : Type}.
Context `{EqDec loc}.
Context `{EqDec info}.
Context {Loc : IsLocation loc info}.
Context `{Names}.

(* FIXME: remove once we have the implem in FSetList. *)
Context {FS : @FSet loc _ _}.
Context {FSSpec : @FSetSpecs loc _ _ FS}.

Notation configuration := (@configuration info _ _ _ _).
Notation map_config := (@map_config info _ _ _ _).
Notation config_list := (@config_list info _ _ _ _).

Implicit Type config : configuration.

Global Instance set_spectrum : Spectrum loc info := {
  spectrum := set loc;
  
  spect_from_config config pt := make_set (List.map get_location (config_list config));
  spect_is_ok s config pt :=
    forall l, In l s <-> InA equiv l (List.map get_location (config_list config)) }.
Proof.
+ repeat intro.
  apply make_set_compat, eqlistA_PermutationA_subrelation,
        (@map_eqlistA_compat _ _ equiv equiv _ get_location).
  - autoclass.
  - apply config_list_compat. assumption.
+ unfold spect_from_config, spect_is_ok. intros. apply make_set_spec.
Defined.

Notation spectrum := (@spectrum loc info _ _ _ _ _ _ _).
Notation spect_from_config := (@spect_from_config loc info _ _ _ _ _ _ set_spectrum).

Require Pactole.Spaces.RealMetricSpace.
Lemma spect_from_config_ignore_snd {RMS : RealMetricSpace.RealMetricSpace loc} : forall config pt,
  spect_from_config config pt == spect_from_config config RealMetricSpace.origin.
Proof. reflexivity. Qed.

Lemma spect_from_config_map : forall f, Proper (equiv ==> equiv) f ->
  forall config pt,
  map f (spect_from_config config pt) == spect_from_config (map_config (app f) config) (f pt).
Proof.
repeat intro. unfold spect_from_config, set_spectrum.
rewrite config_list_map, map_map, <- make_set_map, map_map.
+ apply make_set_compat, Preliminary.eqlistA_PermutationA_subrelation.
  assert (Hequiv : (equiv ==> equiv)%signature (fun x => f (get_location x)) (fun x => get_location (app f x))).
  { intros pt1 pt2 Heq. now rewrite get_location_app, Heq. }
  now apply (map_extensionalityA_compat _ Hequiv).
+ assumption.
+ now apply app_compat.
Qed.

Theorem cardinal_spect_from_config : forall config pt, cardinal (spect_from_config config pt) <= nG + nB.
Proof.
intros. unfold spect_from_config, set_spectrum.
etransitivity; try apply cardinal_make_set; [].
now rewrite map_length, config_list_length.
Qed.

Property pos_in_config : forall config pt id, In (get_location (config id)) (spect_from_config config pt).
Proof.
intros config pt id. unfold spect_from_config. simpl.
rewrite make_set_spec, InA_map_iff; autoclass; [].
eexists. split; auto; []. apply config_list_InA. now exists id.
Qed.

Property spect_from_config_In : forall config pt l,
  In l (spect_from_config config pt) <-> exists id, get_location (config id) == l.
Proof.
intros config pt l. split; intro Hin.
+ assert (Heq := spect_from_config_spec config pt).
  unfold spect_is_ok, spect_from_config, set_spectrum in *.
  rewrite Heq, config_list_spec, map_map, (InA_map_iff _ _) in Hin.
  - firstorder.
  - repeat intro. cbn in *. now subst.
+ destruct Hin as [id Hid]. rewrite <- Hid. apply pos_in_config.
Qed.

End SetSpectrum.
