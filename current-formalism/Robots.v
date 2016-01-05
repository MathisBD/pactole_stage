(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Utf8.
Require Import Morphisms.
Require Import Arith_base.
Require Import Omega.
Require Import SetoidList.
Require Import Pactole.Preliminary.
Open Scope list_scope.
Require Vector.

Set Implicit Arguments.


(* TODO: change the name: it is merely an equivalence *)
Class Bisimulation (T : Type) := {
  bisim : T -> T -> Prop;
  bisim_equiv : Equivalence bisim}.
Infix "≈" := bisim (at level 30).


(** *  Identification of robots  **)

(** The number of good and byzantine robots *)
Module Type Size.
  Parameter nG : nat.
  Parameter nB : nat.
End Size.

Inductive identifier {G} {B} : Type :=  Good : G → identifier | Byz : B → identifier.


Module Type RobotInternals(N : Size).
  Parameter Vfin_map : ∀ (n : nat) (A : Type), (Fin.t n → A) → Vector.t A n.
  Parameter fin_map : ∀ (n : nat) (A : Type), (Fin.t n → A) → list A.
  Parameter Vfin_fin_map : ∀ (n : nat) (A : Type) (f : Fin.t n → A),
    fin_map f = Vector.to_list (Vfin_map f).
  Parameter fin_map_compatA : ∀ (n : nat) (A : Type) (eqA : relation A),
    Proper ((eq ==> eqA) ==> eqlistA eqA) (@fin_map n A).
  Parameter eqlistA_Leibniz : ∀ (A : Type) (l1 l2 : list A), eqlistA eq l1 l2 ↔ l1 = l2.
  Parameter fin_map_compat : ∀ (n : nat) (A : Type), Proper ((eq ==> eq) ==> eq) (@fin_map n A).
  Parameter InA_fin_map : ∀ (n : nat) (A : Type) (eqA : relation A), Equivalence eqA →
    ∀ (g : Fin.t n) (f : Fin.t n → A), InA eqA (f g) (fin_map f).
  Parameter In_fin_map : ∀ (n : nat) (A : Type) (g : Fin.t n) (f : Fin.t n → A), In (f g) (fin_map f).
  Parameter fin_map_InA :
    ∀ (A : Type) (eqA : relation A), Equivalence eqA → (∀ x y : A, {eqA x y} + {¬eqA x y}) →
    ∀ (n : nat) (f : Fin.t n → A) (x : A), InA eqA x (fin_map f) ↔ (∃ id : Fin.t n, eqA x (f id)).
  Parameter fin_map_In : ∀ A : Type, (∀ x y : A, {x = y} + {x ≠ y}) →
    ∀ (n : nat) (f : Fin.t n → A) (x : A), In x (fin_map f) ↔ (∃ id : Fin.t n, x = f id).
  Parameter map_fin_map : ∀ (n : nat) (A B : Type) (f : A → B) (h : Fin.t n → A),
    fin_map (λ x : Fin.t n, f (h x)) = map f (fin_map h).
  Parameter fin_map_id : ∀ (n : nat) (A : Type) (f : Fin.t n → A), fin_map f = map f (fin_map (fun x => x)).
  Parameter fin_map_length : ∀ (n : nat) (A : Type) (f : Fin.t n → A), length (fin_map f) = n.
  Parameter fin_map_NoDup : forall n A (f : Fin.t n -> A),
    (forall x y : A, {x = y} + {x <> y}) -> injective eq eq f -> NoDup (fin_map f).
  Parameter Rinv : ∀ n m : nat, m ≠ 0 → Fin.t (n + m) → Fin.t m.
  Parameter Rinv_R : ∀ (n m : nat) (Hm : m ≠ 0) (x : Fin.t m), Rinv n Hm (Fin.R n x) = x.
  Parameter combine : ∀ (n m : nat) (A : Type), (Fin.t n → A) → (Fin.t m → A) → Fin.t (n + m) → A.
  Parameter combine_0_r : ∀ (n : nat) (A : Type) (f : Fin.t n → A) (g : Fin.t 0 → A),
    (eq ==> eq)%signature (combine f g) (λ x : Fin.t (n + 0), f (eq_rec (n + 0) Fin.t x n (plus_0_r n))).
  Parameter combine_0_l : ∀ (m : nat) (A : Type) (f : Fin.t 0 → A) (g : Fin.t m → A),
    (eq ==> eq)%signature (combine f g) g.
  Parameter combine_compat : ∀ (n m : nat) (A : Type),
    Proper ((eq ==> eq) ==> (eq ==> eq) ==> eq ==> eq) (@combine n m A).
  Parameter fin_map_app : ∀ (n m : nat) (A : Type) (f : Fin.t n → A) (g : Fin.t m → A),
    fin_map f ++ fin_map g = fin_map (combine f g).
  Definition G : Set := Fin.t N.nG.
  Definition B := Fin.t N.nB.
  Definition ident : Type := @identifier G B.
  Definition Gnames : list G := fin_map (fun x : G => x).
  Definition Bnames : list B := fin_map (fun x : B => x).
  Definition names : list ident := List.map Good Gnames ++ List.map Byz Bnames.
End RobotInternals.


Module Names (N : Size) : RobotInternals(N).

(** **  Finite sets of names  **)

Fixpoint Vfin_map n A (f : Fin.t n -> A) {struct n} : Vector.t A n :=
  match n as n' return n = n' -> Vector.t A n' with
    | 0 => fun _ => (Vector.nil _)
    | S m => fun Heq => Vector.cons A (f (eq_rec_r _ Fin.F1 Heq)) m
                                      (Vfin_map (fun x => f (eq_rec_r _ (Fin.FS x) Heq)))
  end (eq_refl n).

Fixpoint fin_map n A (f : Fin.t n -> A) {struct n} : list A :=
  match n as n' return n = n' -> list A with
    | 0 => fun _ => nil
    | S m => fun Heq => cons (f (eq_rec_r _ Fin.F1 Heq)) (fin_map (fun x => f (eq_rec_r _ (Fin.FS x) Heq)))
  end (eq_refl n).
(*
Fixpoint fin_map n A (f : Fin.t n -> A) {struct n} : list A :=
  match n as n' return n = n' -> list A with
    | 0 => fun _ => nil
    | S m => fun Heq => cons (f (eq_rec_r _ Fin.F1 Heq)) (fin_map (fun x => f (Fin.FS x)))
  end (eq_refl n).
*)
Lemma Vfin_fin_map : forall n A (f : Fin.t n -> A), fin_map f = Vector.to_list (Vfin_map f).
Proof.
induction n; intros A f; simpl; unfold Vector.to_list.
  reflexivity.
  f_equal. rewrite IHn. reflexivity.
Qed.

Instance fin_map_compatA n A eqA : Proper ((eq ==> eqA) ==> eqlistA eqA) (@fin_map n A).
Proof.
intros f g Hext. induction n; simpl.
+ constructor.
+ constructor.
  - apply Hext. reflexivity.
  - apply IHn. repeat intro. apply Hext. subst. reflexivity.
Qed.

Lemma eqlistA_Leibniz A : forall (l1 l2 : list A), eqlistA eq l1 l2 <-> l1 = l2.
Proof.
intro l1. induction l1 as [| x1 l1]; intros l2.
* destruct l2.
  + split; intro; reflexivity.
  + split; intro Habs; inversion Habs.
* destruct l2.
  + split; intro Habs; inversion Habs.
  + split; intro Heq; inversion_clear Heq.
    - subst. f_equal. rewrite <- IHl1. assumption.
    - reflexivity.
Qed.

Instance fin_map_compat n A : Proper ((eq ==> eq) ==> eq) (@fin_map n A).
Proof. intros f g Hext. rewrite <- eqlistA_Leibniz. apply fin_map_compatA. repeat intro. subst. now apply Hext. Qed.

Theorem InA_fin_map : forall n A eqA `(Equivalence A eqA) g (f : Fin.t n -> A), InA eqA (f g) (fin_map f).
Proof.
intros n A eqA HeqA g f. destruct n.
+ now apply Fin.case0.
+ revert n g f. apply (Fin.rectS (fun n g => ∀ f : Fin.t (S n) → A, InA eqA (f g) (fin_map f))).
  - intros n f. now left.
  - intros n g IHn f. right. apply (IHn (fun x => f (Fin.FS x))).
Qed.

Corollary In_fin_map : forall n A g (f : Fin.t n -> A), In (f g) (fin_map f).
Proof. intros. rewrite <- InA_Leibniz. apply (InA_fin_map _). Qed.

Theorem fin_map_InA : forall A eqA `(Equivalence A eqA) (eq_dec : forall x y : A, {eqA x y} + {~eqA x y}),
  forall n (f : Fin.t n -> A) x, InA eqA x (fin_map f) <-> exists id : Fin.t n, eqA x (f id).
Proof.
intros A eqA HeqA eq_dec n. induction n; intros f x.
* simpl. rewrite InA_nil. split; intro Habs; try elim Habs. destruct Habs. now apply Fin.case0.
* destruct (eq_dec x (f Fin.F1)) as [Heq | Heq].
  + subst. split; intro Hin. 
    - firstorder.
    - rewrite Heq. apply (InA_fin_map _).
  + simpl. unfold eq_rec_r. simpl. split; intro Hin.
    - inversion_clear Hin; try contradiction. rewrite (IHn (fun id => f (Fin.FS id)) x) in H.
      destruct H as [id Hin]; subst; try now elim Heq. now exists (Fin.FS id).
    - right. destruct Hin as [id Hin]. rewrite Hin in *. clear Hin.
      rewrite (IHn (fun id => f (Fin.FS id)) (f id)). revert f Heq.
      apply (Fin.caseS  (λ n (t : Fin.t (S n)), ∀ f : Fin.t (S n) → A,
                         ~eqA (f t) (f Fin.F1) → ∃ id0 : Fin.t n, eqA (f t) (f (Fin.FS id0)))).
        clear -HeqA. intros n f Hn. elim Hn. reflexivity.
        clear -HeqA. intros n id f Hn. exists id. reflexivity.
Qed.

Corollary fin_map_In : forall A (eq_dec : forall x y : A, {x =  y} + {x <> y}),
  forall n (f : Fin.t n -> A) x, In x (fin_map f) <-> exists id : Fin.t n, x = (f id).
Proof. intros. rewrite <- InA_Leibniz. rewrite (fin_map_InA _); trivial. reflexivity. Qed.

Theorem map_fin_map : forall n A B (f : A -> B) (h : Fin.t n -> A),
  fin_map (fun x => f (h x)) = List.map f (fin_map h).
Proof.
intros n A B f h. induction n.
  reflexivity.
  simpl. f_equal. now rewrite IHn.
Qed.

Corollary fin_map_id : forall n A (f : Fin.t n -> A), fin_map f = List.map f (fin_map (fun x => x)).
Proof. intros. apply map_fin_map. Qed.

Lemma fin_map_length : forall n A (f : Fin.t n -> A), length (fin_map f) = n.
Proof.
intros n A f. induction n.
  reflexivity.
  simpl. now rewrite IHn.
Qed.

Lemma fin_map_NoDup : forall n A (f : Fin.t n -> A),
  (forall x y : A, {x = y} + {x <> y}) -> injective eq eq f -> NoDup (fin_map f).
Proof.
intros n A f HeqA Hinj. induction n.
* assert (Heq : fin_map f = nil). { rewrite <- length_zero_iff_nil. apply fin_map_length. }
  rewrite Heq. constructor.
* simpl. constructor.
  + rewrite <- InA_Leibniz, (fin_map_InA _).
    - intros [id Heq]. apply Hinj in Heq. inversion Heq.
    - apply HeqA.
  + apply IHn. intros x y Heq. apply Hinj in Heq. compute in Heq. now apply Fin.FS_inj.
Qed.

Unset Implicit Arguments.

Fixpoint Rinv n m (Hm : m <> 0) (x : Fin.t (n + m)) : Fin.t m.
  refine (match n as n', x in Fin.t x' return n = n' -> x' = n + m -> Fin.t m with
            | 0, _ => fun Hn _ => _
            | S n', Fin.F1 => fun _ _ => _
            | S n', Fin.FS x' => fun Hn Heq => Rinv n' m Hm _
          end eq_refl eq_refl).
- subst n. exact x.
- destruct m. now elim Hm. now apply Fin.F1.
- rewrite Hn in Heq. simpl in Heq. apply eq_add_S in Heq. rewrite <- Heq. exact x'.
Defined.

Theorem Rinv_R : forall n m (Hm : m <> 0) x, Rinv n m Hm (Fin.R n x) = x.
Proof. now induction n. Qed.

(*
Fixpoint Linv n m (Hn : n <> 0) (x : Fin.t (n + m)) {struct n} : Fin.t n.
  refine (match n as n' return n = n' -> Fin.t n' with
    | 0 => fun Hn => _
    | 1 => fun Hn => Fin.F1
    | S (S n'' as rec) => fun Hn => 
      match x in Fin.t x' return x' = n + m -> Fin.t (S rec) with
        | Fin.F1 _ => fun Heq => Fin.F1
        | Fin.FS _ x' => fun Heq => Fin.FS (Linv rec m _ _)
      end eq_refl
  end eq_refl).
- apply False_rec. now apply Hn.
- abstract (unfold rec0 in *; omega).
- subst n. simpl in Heq. apply eq_add_S in Heq. rewrite Heq in x'. exact x'. (* bug *)
Defined.
*)
Set Implicit Arguments.

Definition combine n m A (f : Fin.t n -> A) (g : Fin.t m -> A) : Fin.t (n + m) -> A.
  unshelve refine (fun x =>
      if eq_nat_dec m 0 then f _ else
      if (lt_dec (proj1_sig (Fin.to_nat x)) n) then f (Fin.of_nat_lt _) else g (Rinv n m _ x)).
- exact (proj1_sig (Fin.to_nat x)).
- subst m. rewrite plus_0_r in x. exact x.
- assumption.
- assumption.
Defined.

Lemma combine_0_r : forall n A f g,
  (eq ==> eq)%signature (@combine n 0 A f g) (fun x => f (eq_rec (n+0) Fin.t x n (plus_0_r n))).
Proof. intros. intros x y ?. subst y. unfold combine. destruct (Fin.to_nat x) eqn:Hx. simpl. reflexivity. Qed.

Lemma combine_0_l : forall m A f g, (eq ==> eq)%signature (@combine 0 m A f g) g.
Proof.
intros m *. intros x y ?. subst y. unfold combine. destruct (eq_nat_dec m) as [Hm | Hm]; simpl.
- apply Fin.case0. now rewrite Hm in x.
- reflexivity.
Qed.

Instance combine_compat n m A : Proper ((eq ==> eq) ==> (eq ==> eq) ==> (eq ==> eq)) (@combine n m A).
Proof.
intros f₁ f₂ Hf g₁ g₂ Hg x y ?. subst y. unfold combine.
destruct (Fin.to_nat x). destruct m; simpl.
- now apply Hf.
- destruct (lt_dec x0 n). now apply Hf. now apply Hg.
Qed.

(* To illustrate
Example ex_f := fun x : Fin.t 2 => 10 + proj1_sig (Fin.to_nat x).
Example ex_g := fun x : Fin.t 3 => 20 + proj1_sig (Fin.to_nat x).

Eval compute in combine ex_f ex_g (Fin.F1).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.F1)).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.F1))).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
Fail Eval compute in combine ex_f ex_g (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.FS (Fin.F1))))).
*)

Theorem fin_map_app : forall n m A (f : Fin.t n -> A) (g : Fin.t m -> A),
  fin_map f ++ fin_map g = fin_map (combine f g).
Proof.
intros n m A f g. destruct m; simpl.
+ rewrite (combine_0_r f g). rewrite app_nil_r. now rewrite plus_0_r.
+ induction n; simpl.
  - reflexivity.
  - f_equal. rewrite IHn. apply fin_map_compat. intros x y ?. subst y. unfold eq_rec_r. simpl.
    unfold combine. simpl. destruct (Fin.to_nat x) as [x0 Hx0]. simpl.
    destruct (lt_dec x0 n) as [Hle | Hle], (lt_dec (S x0) (S n)) as [HleS | HleS]; try omega.
      now rewrite (le_unique _ _ (lt_S_n x0 n HleS) Hle).
      reflexivity.
Qed.


(** ** Byzantine Robots *)

(** We have finetely many robots. Some are good, other are evil. *)

Definition G : Set := Fin.t N.nG.
Definition B := Fin.t N.nB.

(** Disjoint union of both kinds of robots is obtained by a sum type. *)
(* TODO: replace this by (G ⊎ B). *)
Definition ident := @identifier G B.

(** Names of robots **)

Definition Gnames : list G := fin_map (fun x : G => x).
Definition Bnames : list B := fin_map (fun x : B => x).
Definition names : list ident := List.map Good Gnames ++ List.map Byz Bnames.

End Names.


Module Type Robots(N : Size).
  Declare Module Internals : RobotInternals(N).
(*    with Definition ident := identifier Internals.G Internals.B.*)
  
  Definition G := Internals.G.
  Definition B := Internals.B.
  
  (** Disjoint union of both kinds of robots is obtained by a sum type. *)
  (* TODO: replace this by (G ⊎ B). *)
  Definition ident := Internals.ident.
  
  (** Names of robots **)
  Definition Gnames := Internals.Gnames.
  Definition Bnames := Internals.Bnames.
  Definition names := Internals.names.
  
  Parameter In_Gnames : forall g : G, In g Gnames.
  Parameter In_Bnames : forall b : B, In b Bnames.
  Parameter In_names : forall r : ident, In r names.
  
  Parameter Gnames_NoDup : NoDup Gnames.
  Parameter Bnames_NoDup : NoDup Bnames.
  Parameter names_NoDup : NoDup names.
  
  Parameter Gnames_length : length Gnames = N.nG.
  Parameter Bnames_length : length Bnames = N.nB.
  Parameter names_length : length names = N.nG + N.nB.
End Robots.

Module Make(N : Size) <: Robots(N).
  Module Internals := Names(N).
  
  Definition G := Internals.G.
  Definition B := Internals.B.
  Definition ident := Internals.ident.
  Definition Gnames := Internals.Gnames.
  Definition Bnames := Internals.Bnames.
  Definition names := Internals.names.
  
  Lemma In_Gnames : forall g : G, In g Gnames.
  Proof. intro g. unfold Gnames. change g with (Datatypes.id g). apply Internals.In_fin_map. Qed.
  
  Lemma In_Bnames : forall b : B, In b Bnames.
  Proof. intro b. unfold Bnames. change b with (Datatypes.id b). apply Internals.In_fin_map. Qed.
  
  Lemma In_names : forall r : ident, In r names.
  Proof.
  intro r. unfold names, Internals.names. rewrite in_app_iff. destruct r as [g | b].
  - left. apply in_map, In_Gnames.
  - right. apply in_map, In_Bnames.
  Qed.
  
  Lemma Gnames_NoDup : NoDup Gnames.
  Proof.
  unfold Gnames. apply Internals.fin_map_NoDup.
  - apply Fin.eq_dec.
  - now intro.
  Qed.
  
  Lemma Bnames_NoDup : NoDup Bnames.
  Proof.
  unfold Bnames. apply Internals.fin_map_NoDup.
  - apply Fin.eq_dec.
  - now intro.
  Qed.
  
  Lemma names_NoDup : NoDup names.
  Proof.
  unfold names. rewrite <- NoDupA_Leibniz. apply (NoDupA_app _).
  + apply (map_injective_NoDupA _ _).
    - now repeat intro; subst.
    - intros ? ? H. now inversion H.
    - rewrite NoDupA_Leibniz. apply Gnames_NoDup.
  + apply (map_injective_NoDupA _ _).
    - now repeat intro; subst.
    - intros ? ? H. now inversion H.
    - rewrite NoDupA_Leibniz. apply Bnames_NoDup.
  + intros id HinA HinB. rewrite (InA_map_iff _ _) in HinA. rewrite (InA_map_iff _ _) in HinB.
    - destruct HinA as [? [? ?]], HinB as [? [? ?]]. subst. discriminate.
    - now repeat intro; subst.
    - now repeat intro; subst.
  Qed.
  
  Lemma Gnames_length : length Gnames = N.nG.
  Proof. unfold Gnames, Internals.Gnames. apply Internals.fin_map_length. Qed.
  
  Lemma Bnames_length : length Bnames = N.nB.
  Proof. unfold Bnames, Internals.Bnames. apply Internals.fin_map_length. Qed.
  
  Lemma names_length : length names = N.nG + N.nB.
  Proof.
  unfold names, Internals.names. rewrite app_length, map_length, map_length.
  fold Gnames Bnames. now rewrite Gnames_length, Bnames_length.
  Qed.
End Make.
