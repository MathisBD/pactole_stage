Set Implicit Arguments.
Require Import byzance.
Require Import Qcanon.

Require Import Equivalences.

(* Impossibility in a N robots vs N robots *)

(* The two colums position *)
Definition two_col (k : Qc) (f : finite) : position f f :=
  {| good_places := fun x => k
   ; bad_places := fun x => (k+1)%Qc
   |}.

(* The shifting demon *)
Definition shift (k : Qc) f (r : robogram f f) : demon r :=
  let s := fun p => {| bad_replace := fun x => ((bad_places p x)+k)%Qc
                     ; good_activation := fun _ => true
                     |}
  in {| strategy := s
      ; Fairness := fun g p => immediate r s g p I
      |}.

Definition static f (r : robogram f f) : demon r :=
  let s := fun p => {| bad_replace := bad_places p
                     ; good_activation := fun _ => true
                     |}
  in {| strategy := s
      ; Fairness := fun g p => immediate r s g p I
      |}.

(* Identity automorphism *)
Definition id_perm f : automorphism (ident f f).
refine {| section := id
        ; retraction := id
        |}.
abstract (unfold id; split; auto).
Defined.

(* Exchange of the first good and bad robot *)
Definition swap_perm f : automorphism (ident f f).
refine (let s := fun x => match x with
                          | Good x => match next f (Some x) with
                                      | None => Bad f f x
                                      | _ => Good f f x
                                      end
                          | Bad x => match next f (Some x) with
                                     | None => Good f f x
                                     | _ => Bad f f x
                                     end
                          end
        in
       {| section := s
        ; retraction := s
        |}).
abstract (
intros x y; split; intros; subst;
[destruct x as [t|t]|destruct y as [t|t]]; simpl;
(case_eq (next f (Some t)); simpl;
[intros n H|intros H]; rewrite H); auto
).
Defined.

(* Exchange of all but the first good and bad robot *)
Definition paws_perm f : automorphism (ident f f).
refine (let s := fun x => match x with
                          | Good x => match next f (Some x) with
                                      | None => Good f f x
                                      | _ => Bad f f x
                                      end
                          | Bad x => match next f (Some x) with
                                     | None => Bad f f x
                                     | _ => Good f f x
                                     end
                          end
        in
       {| section := s
        ; retraction := s
        |}).
abstract (
intros x y; split; intros; subst;
[destruct x as [t|t]|destruct y as [t|t]]; simpl;
(case_eq (next f (Some t)); simpl;
[intros n H|intros H]; rewrite H); auto
).
Defined.

Lemma winning_property
: forall f (r : robogram f f) (d : demon r),
  forall p, win d (good_places p) ->
  (forall x, bad_places p x = ((good_places p x)+1)%Qc) ->
  let other_pos := pos_remap (swap_perm f) p in
  forall g, move r (center other_pos (good_places other_pos g)) = 0%Qc.
Proof.
  intros f r d p [offset Hp2] Hp1 alt_pos g.
  set (delta := fun g =>
                match next f (Some g) with None => (-1%Qc)%Qc | _ => 1%Qc end).
  cut (PosEquiv (zoom (delta g) (center alt_pos (good_places alt_pos g)))
                (center p (good_places p g))).
  + generalize (center alt_pos (good_places alt_pos g)).
    intros q Hq.
    cut (((delta g) * (move r q))%Qc = 0).
    - generalize (move r q); clear; intros q Hq.
      cut (delta g * (delta g * q) = 0).
      * unfold delta; simpl; destruct (next f (Some g)); intros []; ring.
      * rewrite Hq; ring.
    - case MoveZoom.
      rewrite (MoveMorph r Hq).
      destruct (Hp2 g) as [_ Fixed]; clear - Fixed.
      destruct p; simpl in *; apply Fixed.
  + assert (GStacked := fun g => proj1 (Hp2 g)).
    assert (BStacked : forall b, bad_places p b = offset + 1);
     [intros b; case (GStacked b); apply Hp1|].
    clear - BStacked GStacked.
    subst delta; simpl.
    destruct (next f (Some g)); simpl; rewrite GStacked.
    - split with (swap_perm f); subst alt_pos; split; simpl; intros;
      destruct (next f (Some n0)); ring.
    - rewrite BStacked.
      split with (paws_perm f); subst alt_pos; split; simpl; intros;
      destruct (next f (Some n)); rewrite BStacked, GStacked; ring.
Qed.

Definition at_least_two f :=
  match prev f (prev f None) with None => False | _ => True end.

Lemma no_solution  (f : finite) (r : robogram f f)
: at_least_two f -> solution r -> False.
Proof.
  intros at_least_2 s.
  (* first demon, first position *)
  destruct (s (shift (move r (two_col 0%Qc f)) r) (two_col 0%Qc f))
   as [fpos [chain Hwin]].
  assert (exists k, PosEq fpos (two_col k f)).
  + clear - chain; induction chain.
    * exists 0; apply PosEqRefl.
    * clear chain; destruct IHchain as [offset HPosEq].
      exists (offset + (move r (two_col 0 f))).
      assert (move r (two_col 0 f) = move r (center q offset)).
      - apply MoveMorph; split with (id_perm f).
        destruct HPosEq.
        split; simpl in *; intros; [rewrite good_ext|rewrite bad_ext]; ring.
      - rewrite H; clear H; destruct HPosEq as [HPosEqG HPosEqB].
        split; simpl; intros; [rewrite HPosEqG|rewrite HPosEqB]; simpl; ring.
  + clear chain; destruct H as [offset HPosEq].
    assert (forall x, bad_places fpos x = ((good_places fpos x)+1)%Qc);
     [now destruct HPosEq; intros n; rewrite good_ext, bad_ext|].
    assert (wp := winning_property fpos Hwin H); clear Hwin H.
    set (op := pos_remap (swap_perm f) fpos); cbv zeta in wp; fold op in wp.
    (* second demon, second position *)
    destruct (s (static r) op) as [_fpos_ [chain Hwin]].
    assert (PosEq op _fpos_).
    * revert wp chain; generalize op; clear; intros op wp chain.
      induction chain.
      - apply PosEqRefl.
      - { clear chain.
          assert (forall x, move r (center op x) = move r (center q x)).
          + intros Hx; apply MoveMorph; split with (id_perm f).
            destruct IHchain; split; intros; simpl; f_equal; auto.
          + destruct IHchain; split; simpl; auto.
            intros n; case H; case good_ext; rewrite wp; ring.
        }
    * { clear - at_least_2 HPosEq Hwin H.
        destruct Hwin as [offset2 Hwin].
        assert (Habsurd := fun g => proj1 (Hwin g)); clear Hwin.
        assert (Habs : forall g, good_places op g = offset2);
         [now intros g; case (Habsurd g); apply good_ext|].
        revert at_least_2 Habs; unfold at_least_two; simpl; clear - HPosEq.
        case_eq (prev f None).
        + intros n Hn; case_eq (prev f (Some n)).
          - intros m Hm _ K.
            generalize (K m), (K n); clear K.
            rewrite (proj2 (NextPrev f _ _) Hn).
            rewrite (proj2 (NextPrev f _ _) Hm).
            clear - HPosEq.
            rewrite (good_ext HPosEq), (bad_ext HPosEq); simpl; clear.
            intros; cut (0 = 1)%Qc; [discriminate|].
            transitivity (offset2 - offset); [case H|case H0]; ring.
          - intros _ [].
        + intros H; rewrite H; intros [].
      }
Qed.
