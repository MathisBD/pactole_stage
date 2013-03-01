Set Implicit Arguments.
Require Import byzance.
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

Lemma NextSurj (f : finite) : forall x, next f (prev f x) = x.
Proof. exact (fun x => proj2 (NextPrev f (prev f x) x) (eq_refl _)). Qed.

Lemma PrevSurj (f : finite) : forall x, prev f (next f x) = x.
Proof. exact (fun x => proj1 (NextPrev f x (next f x)) (eq_refl _)). Qed.

Lemma NextInj (f : finite) : forall x y, next f x = next f y -> x = y.
Proof. intros; case (PrevSurj f y); case H; symmetry; apply PrevSurj. Qed.

Lemma PrevInj (f : finite) : forall x y, prev f x = prev f y -> x = y.
Proof. intros; case (NextSurj f y); case H; symmetry; apply NextSurj. Qed.

Definition index_aux (f : finite) : forall x, Acc (NextRel f) x -> nat :=
  fix index x (H : Acc (NextRel f) x) :=
  match prev2 f x with
  | FirstOne _ => O
  | PrevOne y Hy =>
    S (index y (let (rec) := H in rec y (proj2 (NextPrev f _ _) Hy)))
  end.

Definition index (f : finite) (x : name f) : nat := index_aux (RecNext f x).

Definition coindex (f : finite) : nat -> option (name f) :=
 fix coindex n :=
 match n with
 | O => next f None
 | S n => match coindex n with
          | Some m => next f (Some m)
          | None => None
          end
 end.

Lemma nat_split (f : finite) : forall n, coindex f (index f n) = Some n.
Proof.
 unfold index.
 intros n; generalize (RecNext f n); revert n.
 fix 2; intros n [Hind]; simpl.
 destruct (prev2 f n) as [m Hm|H]; simpl.
 + rewrite nat_split; unfold PrevRel in Hm; clear - Hm.
   now apply (proj2 (NextPrev f _ _)).
 + unfold First in H; clear - H.
   now apply (proj2 (NextPrev f _ _)).
Qed.

Lemma nat_cosplit (f : finite)
: forall n, match coindex f n with
            | Some k => index f k = n
            | None => True
            end.
Proof.
 intros n; case_eq (coindex f n); auto.
 unfold index; intros n0; generalize (RecNext f n0); revert n0.
 induction n; intros m [rec]; simpl.
 + destruct (prev2 f m); auto.
   intros H; exfalso; revert p; unfold PrevRel; case H; clear.
   rewrite PrevSurj; discriminate.
 + destruct (coindex f n); try discriminate.
   destruct (prev2 f m); simpl.
   - generalize (rec y (proj2 (NextPrev f (Some y) (Some m)) p)); intros.
     f_equal; apply IHn.
     clear - H p.
     case (proj1 (NextPrev f (Some n0) (Some m)) H); auto.
   - unfold First in f0.
     case (proj2 (NextPrev f None (Some m)) f0); clear.
     intros H; generalize (NextInj f _ _ H); clear.
     discriminate.
Qed.
