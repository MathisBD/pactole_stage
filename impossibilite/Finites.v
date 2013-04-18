Set Implicit Arguments.
Require Import ConvergentFormalism.
(** * All stuff about [finite] *)

(** Yet all that stuff is useless, it just give some insurance that this is
    really finite set. Later, we may need part of that stuff to reason
    on finiteness. *)

Definition Last (f : finite) (x : name f) : Prop := next f (Some x) = None.
Definition First (f : finite) (x : name f) : Prop := prev f (Some x) = None.

Inductive next_result (f : finite) (x : name f) :=
 | NextOne : forall y, NextRel f x y -> next_result f x
 | LastOne : Last f x -> next_result f x.
Inductive prev_result (f : finite) (x : name f) :=
 | PrevOne : forall y, PrevRel f x y -> prev_result f x
 | FirstOne : First f x -> prev_result f x.

Definition next2 (f : finite) (x : name f) : next_result f x :=
 match next f (Some x) as k return next f (Some x) = k -> next_result f x with
 | Some y => @NextOne f x y
 | None => @LastOne f x
 end (eq_refl _).
Definition prev2 (f : finite) (x : name f) : prev_result f x :=
 match prev f (Some x) as k return prev f (Some x) = k -> prev_result f x with
 | Some y => @PrevOne f x y
 | None => @FirstOne f x
 end (eq_refl _).

Lemma SurjToInj A B (f : A -> B) (g : B -> A)
: (forall x, f (g x) = x) -> (forall x y, g x = g y -> x = y).
Proof. intros H x y Heq. case (H x), (H y). case Heq. split. Qed.

Lemma NextSurj (f : finite) : forall x, next f (prev f x) = x.
Proof. exact (fun x => proj2 (NextPrev f (prev f x) x) (eq_refl _)). Qed.

Lemma PrevSurj (f : finite) : forall x, prev f (next f x) = x.
Proof. exact (fun x => proj1 (NextPrev f x (next f x)) (eq_refl _)). Qed.

Lemma NextInj (f : finite) : forall x y, next f x = next f y -> x = y.
Proof. apply SurjToInj with (prev f). apply PrevSurj. Qed.

Lemma PrevInj (f : finite) : forall x y, prev f x = prev f y -> x = y.
Proof. apply SurjToInj with (next f). apply NextSurj. Qed.

Definition index_aux (f : finite) : forall x, Acc (NextRel f) x -> nat :=
  fix index x (H : Acc (NextRel f) x) :=
  match prev2 f x with
  | FirstOne _ => O
  | PrevOne y Hy =>
    S (index y (let (rec) := H in rec y (proj2 (NextPrev f _ _) Hy)))
  end.

Definition index (f : finite) (x : option (name f)) : nat :=
 match x with
 | None => O
 | Some x => S (index_aux (RecNext f x))
 end.

Definition coindex (f : finite) : nat -> option (name f) :=
 fix coindex n :=
 match n with
 | O => None
 | S n => next f (coindex n)
 end.

Lemma CoindexSurj_aux (f : finite)
: forall n Hn, next f (coindex f (@index_aux f n Hn)) = Some n.
Proof.
 fix 2; intros n [Hind]; simpl.
 destruct (prev2 f n) as [m Hm|H]; simpl.
 + rewrite CoindexSurj_aux; unfold PrevRel in Hm; clear - Hm.
   now apply (proj2 (NextPrev f _ _)).
 + unfold First in H; clear - H.
   now apply (proj2 (NextPrev f _ _)).
Qed.

Lemma CoindexSurj (f : finite) : forall n, coindex f (index f n) = n.
Proof. unfold index; intros [n|]; simpl; auto; apply CoindexSurj_aux. Qed.

Lemma IndexInj_aux f x (Hx : Acc (NextRel f) x) y (Hy : Acc (NextRel f) y)
: index_aux Hx = index_aux Hy -> x = y.
Proof.
  intros H.
  change y with (match Some y with Some y => y | _ => y end).
  case (CoindexSurj_aux Hy).
  change x with (match Some x with Some y => y | _ => y end).
  case (CoindexSurj_aux Hx).
  case H; split.
Qed.

Lemma IndexInj (f : finite) : forall x y, index f x = index f y -> x = y.
Proof. apply SurjToInj with (coindex f). apply CoindexSurj. Qed.

Definition card (f : finite) : nat := index f (prev f None).

Lemma bounded (f : finite) : forall x, index f x <= card f.
Proof.
  unfold card, index; intros x.
  case_eq (prev f None).
  * intros n Hn; case x; clear x; [|apply Le.le_0_n].
    intros x; apply Le.le_n_S.
    generalize (RecNext f x); revert x.
    fix 2; intros x [rec]; simpl.
    generalize (fun x Hx => bounded x (rec x Hx)).
    clear bounded; simpl.
    destruct (prev2 f x); [|intros; apply Le.le_0_n].
    generalize (proj2 (NextPrev f (Some y) (Some x)) p).
    intros acc Hacc; generalize (rec y acc), (Hacc _ acc); clear - p acc Hn.
    unfold PrevRel in p; intros; simpl in *.
    generalize (IndexInj_aux a (RecNext f n)).
    destruct H as [|o Ho]; [|intros _; apply Le.le_n_S; auto].
    intros H; exfalso.
    revert Hn; case (H (eq_refl _)); case p; clear.
    intros H; generalize (PrevInj f None (Some x) H); clear.
    intros H; change (match Some x with None => True | _ => False end).
    destruct H; split.
  * destruct x; [|left].
    intros H; exfalso.
    generalize (RecNext f n); revert n.
    fix 2; intros x [rec].
    destruct (prev2 f x).
    + exact (bounded y (rec y (proj2 (NextPrev f (Some y) (Some x)) p))).
    + unfold First in f0; revert f0; destruct H; subst o; clear.
      intros K; generalize (PrevInj f (Some x) None K); clear.
      intros H; change (match @None (name f) with None => False |_ => True end).
      destruct H; split.
Qed.
