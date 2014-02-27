Set Implicit Arguments.
Require Import ConvergentFormalismR.

Definition chain_aux_aux A B (ob : option B) : option (B + A) :=
  match ob with
  | Some b => Some (inl b)
  | None => None
  end.

Definition chain_aux A (oa : option A) B (ob : option B) : option (B + A) :=
  match oa with
  | Some a => Some (inr a)
  | None => chain_aux_aux A ob
  end.

Definition chain A (f : option A -> option A) B (g : option B -> option B)
: option (A + B) -> option (B + A)
:= fun x => match x with
            | None => chain_aux (f None) (g None)
            | Some (inl a) => chain_aux (f (Some a)) (g None)
            | Some (inr b) => chain_aux_aux A (g (Some b))
            end.

Definition flip A B (x : A + B) : B + A :=
  match x with inl a => inr a | inr b => inl b end.

Definition oflip A B (x : option (A + B)) : option (B + A) :=
  match x with Some x => Some (flip x) | _ => None end.

Lemma flip_invol A B (x : A + B) : flip (flip x) = x.
Proof. case x as [a|b]; split. Qed.

Lemma oflip_invol A B (x : option (A + B)) : oflip (oflip x) = x.
Proof. case x as [x|]; [simpl; f_equal; apply flip_invol|split]. Qed.

Lemma fplus_next_prev (f g : finite) (x : option ((name g) + (name f)))
: chain (next f) (next g) (chain (prev g) (prev f) x) = x.
Proof.
  case x as [[_g_|_f_]|]; simpl.
  - case_eq (prev g (Some _g_)); simpl.
    + now intros n Hn; rewrite (proj2 (NextPrev g (Some n) (Some _g_))).
    + case_eq (prev f None); simpl.
      * intros n Hn; rewrite (proj2 (NextPrev f (Some n) None)); auto.
        now intros H; rewrite (proj2 (NextPrev g None (Some _g_))).
      * intros A B; rewrite (proj2 (NextPrev f None None)); simpl; auto.
        now rewrite (proj2 (NextPrev g None (Some _g_))).
  - case_eq (prev f (Some _f_)); simpl.
    + intros n Hn; rewrite (proj2 (NextPrev f (Some n) (Some _f_))); auto.
    + intros H; rewrite (proj2 (NextPrev f None (Some _f_))); auto.
  - case_eq (prev g None); simpl.
    + intros n Hn; rewrite (proj2 (NextPrev g (Some n) None)); auto.
    + case_eq (prev f None); simpl.
      * intros n A B; rewrite (proj2 (NextPrev f (Some n) None)); simpl; auto.
        rewrite (proj2 (NextPrev g None None)); auto.
      * intros H; rewrite (proj2 (NextPrev f None None)); simpl; auto.
        intros K; rewrite (proj2 (NextPrev g None None)); simpl; auto.
Qed.

Lemma fplus_prev_next (f g : finite) (x : option ((name f) + (name g)))
: chain (prev g) (prev f) (chain (next f) (next g) x) = x.
Proof.
  case x as [[_f_|_g_]|]; simpl.
  - case_eq (next f (Some _f_)); simpl.
    + now intros n Hn; rewrite (proj1 (NextPrev f (Some _f_) (Some n))).
    + case_eq (next g None); simpl.
      * intros n Hn; rewrite (proj1 (NextPrev g None (Some n))); auto.
        now intros H; rewrite (proj1 (NextPrev f (Some _f_) None)).
      * intros A B; rewrite (proj1 (NextPrev g None None)); simpl; auto.
        now rewrite (proj1 (NextPrev f (Some _f_) None)).
  - case_eq (next g (Some _g_)); simpl.
    + intros n Hn; rewrite (proj1 (NextPrev g (Some _g_) (Some n))); auto.
    + intros H; rewrite (proj1 (NextPrev g (Some _g_) None)); auto.
  - case_eq (next f None); simpl.
    + intros n Hn; rewrite (proj1 (NextPrev f None (Some n))); auto.
    + case_eq (next g None); simpl.
      * intros n A B; rewrite (proj1 (NextPrev g None (Some n))); simpl; auto.
        rewrite (proj1 (NextPrev f None None)); auto.
      * intros H; rewrite (proj1 (NextPrev g None None)); simpl; auto.
        intros K; rewrite (proj1 (NextPrev f None None)); simpl; auto.
Qed.

Lemma chain_inv X Y (f : option X -> option X) (g : option Y -> option Y) y
: match chain f g (Some y) with
  | Some (inr x) => (exists z, y = inl z /\ f (Some z) = Some x)
  | Some (inl x) => (exists z, y = inl z /\ f (Some z) = None) \/
                    (exists z, y = inr z /\ g (Some z) = Some x)
  | None         => True
  end.
Proof.
  destruct y; simpl.
  + case_eq (f (Some x)); simpl; eauto.
    case_eq (g None); simpl; eauto.
  + case_eq (g (Some y)); simpl; eauto.
Qed.

Lemma fchain_acc X Y (f : option X -> option X) (g : option Y -> option Y)
: (forall x, Acc (fun a b => f (Some a) = Some b) x) ->
  (forall y, Acc (fun a b => g (Some a) = Some b) y) ->
  (forall z, Acc (fun a b => oflip (chain f g (Some a)) = Some b) z).
Proof.
  intros HX.
  assert (forall z, Acc (fun a b => oflip (chain f g (Some a))=Some b) (inl z)).
  - intros z; induction (HX z).
    split; intros.
    generalize (chain_inv f g y).
    case (oflip_invol (chain f g (Some y))); rewrite H1; simpl.
    clear H1; intros [z [Heq1 Heq2]]; subst; eauto.
  - clear HX; intros HY.
    intros [x|y]; auto.
    induction (HY y).
    split; intros.
    generalize (chain_inv f g y).
    case (oflip_invol (chain f g (Some y))); rewrite H2; simpl.
    intros [[z [Heq1 _]]|[z [Heq1 Heq2]]]; subst; eauto.
Qed.

Lemma chainf_acc X Y (f : option X -> option X) (g : option Y -> option Y)
: (forall x, Acc (fun a b => f (Some a) = Some b) x) ->
  (forall y, Acc (fun a b => g (Some a) = Some b) y) ->
  (forall z, Acc (fun a b => chain f g (oflip (Some a)) = Some b) z).
Proof.
  intros HX.
  assert (forall z, Acc (fun a b => chain f g (oflip (Some a))=Some b) (inr z)).
  - intros z; induction (HX z).
    split; intros.
    case (flip_invol y); revert H1; unfold oflip; generalize (flip y).
    clear y; intros y H1.
    generalize (chain_inv f g y); rewrite H1.
    clear H1; intros [z [Heq1 Heq2]]; subst; eauto.
  - clear HX; intros HY.
    intros [y|x]; auto.
    induction (HY y).
    split; intros.
    case (flip_invol y); revert H2; unfold oflip; generalize (flip y).
    clear y; intros y H2.
    generalize (chain_inv f g y); rewrite H2; simpl.
    intros [[z [Heq1 _]]|[z [Heq1 Heq2]]]; subst; eauto.
Qed.

Definition fplus (f g : finite) : finite.
refine {| name := (name f) + (name g)
        ; next := fun x => oflip (chain (next f) (next g) x)
        ; prev := fun x => chain (prev g) (prev f) (oflip x)
        |}.
Proof.
  abstract (
  intros x y; split; intros; subst;
  [rewrite oflip_invol; apply fplus_prev_next
  |rewrite fplus_next_prev; apply oflip_invol]
  ).
Proof.
  abstract (apply fchain_acc; apply RecNext).
Proof.
  abstract (apply chainf_acc; apply RecPrev).
Defined.