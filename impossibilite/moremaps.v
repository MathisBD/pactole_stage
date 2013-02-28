(* Credits: Stephane Lescuyer. *)

Require Import FMaps.
Require Import OrderedType.
Require Import Morphisms.

Module MorePredicate (Import M:S).

(** Logical predicates *)
  Definition For_all {elt} (P : key -> elt -> Prop) (m:M.t elt) := forall k x, M.MapsTo k x m -> P k x.

End MorePredicate.


Module MapMorphisms (E : OrderedType) (M : S with Module E := E).
  Import M.
  Module MP := OrdProperties M.
  Module OT := OrderedTypeFacts E.

  Generalizable All Variables.

  Section WithElt.
    Context `{elt_Equiv: Equivalence elt elt_eq}.
    Hint Extern 0 (elt_eq _ _) => reflexivity.
    Hint Extern 0 (E.eq _ _) => reflexivity.
    Hint Extern 2 (elt_eq _ _) => symmetry; assumption.
    Hint Extern 2 (E.eq _ _) => symmetry; assumption.
    
    Let Equiv := Equiv elt_eq.

    (** Caractérisation de Equiv plus proche de celle de Containers *)
    Lemma Equiv_1 : forall {m m'}, Equiv m m' ->
      forall k e, MapsTo k e m -> 
        exists e', elt_eq e e' /\ MapsTo k e' m'.
    Proof.
      intros; destruct H as [H1 H2].
      cut (In k m').
      intros [e' He']; exists e'; firstorder.
      rewrite <- H1; exists e; assumption.
    Qed.
    Lemma Equiv_2 : forall {m m'}, Equiv m' m ->
      forall k e, MapsTo k e m -> 
        exists e', elt_eq e e' /\ MapsTo k e' m'.
    Proof.
      intros; destruct H as [H1 H2].
      cut (In k m').
      intros [e' He']; exists e'; firstorder.
      rewrite H1; exists e; assumption.
    Qed.

    Inductive elt_eqo : relation (option elt) :=
    | elt_eqo_None : elt_eqo None None
    | elt_eqo_Some : forall e e', elt_eq e e' -> elt_eqo (Some e) (Some e').

    Global Instance elt_eqo_m : Equivalence elt_eqo.
    Proof.
      intros; constructor.
      intro x; destruct x; constructor; reflexivity.
      intros x y E; inversion E; subst; constructor; symmetry; auto.
      intros x y z E E'; inversion E; subst; inversion E'; subst;
        constructor; etransitivity; eauto. 
    Qed.

    Global Instance find_m :
      Proper (E.eq ==> Equiv ==> elt_eqo) (@find elt).
    Proof.
      intros x y H m m' Heq.
      rewrite H.
      destruct (find y m) as [qy|]_eqn:Hy.
      apply find_2 in Hy.
      destruct (Equiv_1 Heq y qy Hy) as [q'y [Hqq' Hq'y]].
      apply find_1 in Hq'y; rewrite Hq'y; constructor; assumption.
      destruct (find y m') as [q'y|]_eqn:Hy'.
      apply find_2 in Hy'.
      destruct (Equiv_2 Heq y q'y Hy') as [qy [Hqq' Hqy]].
      apply find_1 in Hqy; rewrite Hqy in Hy; discriminate.
      constructor.
    Qed.

    Lemma Equiv_3 : forall m m',
      (forall k, elt_eqo (find k m) (find k m')) -> Equiv m m'.
    Proof.
      intros; split.
      intro k; assert (Hk := H k); inversion Hk; subst.
      symmetry in H1, H2.
      rewrite <- MP.P.F.not_find_in_iff in H1, H2; tauto.
      rewrite !MP.P.F.in_find_iff.
      destruct (find k m); destruct (find k m'); intuition congruence.
      intros k e e' H1 H2; assert (Hk := H k).
      rewrite MP.P.F.find_mapsto_iff in H1, H2; rewrite H1, H2 in Hk.
      inversion Hk; assumption.
    Qed.
    Lemma Equiv_4 : forall m m', Equiv m m' ->
      (forall k, elt_eqo (find k m) (find k m')).
    Proof.
      intros; rewrite H; reflexivity.
    Qed.

    Global Instance add_m :
      Proper (E.eq ==> elt_eq ==> Equiv ==> Equiv) (@add elt). 
    Proof.
      intros k k' Hk q q' Hq m m' Heq.
      apply Equiv_3; intros k''.
      rewrite 2MP.P.F.add_o.
      destruct (M.E.eq_dec k k''); destruct (M.E.eq_dec k' k'').
      constructor. assumption.
      rewrite Hk in e; contradiction.
      rewrite Hk in n; contradiction.
      apply find_m; auto.
    Qed.

    Global Instance remove_m :
      Proper (E.eq ==> Equiv ==> Equiv) (@remove elt).
    Proof.
      intros k k' Hk m m' Heq.
      apply Equiv_3; intros k''.
      rewrite 2MP.P.F.remove_o.
      destruct (M.E.eq_dec k k''); destruct (M.E.eq_dec k' k'').
      constructor 1.
      rewrite Hk in e; contradiction.
      rewrite Hk in n; contradiction.
      apply find_m; auto.
    Qed.

    Inductive list_eq : relation (list (key * elt)) :=
    | list_eq_nil : list_eq nil nil
    | list_eq_cons : forall k v k' v' q q', 
      E.eq k k' -> elt_eq v v' -> list_eq q q' ->
      list_eq ((k,v)::q) ((k',v')::q').

    Notation eq_key_elt := (@M.eq_key_elt elt).
    Hint Extern 0 (eq_key_elt _ _) => (split; reflexivity).

    Notation lt_key := (@M.lt_key elt).

    Global Instance elements_m :
      Proper (Equiv ==> list_eq) (@elements elt).
    Proof.
      intros m m' Hm.
      assert (H := @MP.P.F.elements_mapsto_iff elt m).
      assert (Hsort := @elements_3 elt m).
      assert (H' := @MP.P.F.elements_mapsto_iff elt m').
      assert (Hsort' := @elements_3 elt m').
      assert (Cut :
        forall k v, 
          (exists v', elt_eq v v' /\ InA eq_key_elt (k, v') (elements m)) <->
          (exists v', elt_eq v v' /\ InA eq_key_elt (k, v') (elements m'))).
      - intros k v; split; intros [v' [Hvv' Hv']].
        destruct (Equiv_1 Hm k v') as [v'' [Hvv'' Hv'']].
        rewrite H; assumption.
        exists v''; split. transitivity v'; auto. rewrite <- H'; assumption.
        destruct (Equiv_2 Hm k v') as [v'' [Hvv'' Hv'']].
        rewrite H'; assumption.
        exists v''; split. transitivity v'; auto. rewrite <- H; assumption.

      - clear H H' Hm.
        revert Hsort Hsort' Cut.
        generalize (elements m) (elements m'); clear m m'.
        induction l; intro l'; destruct l'; intros Hsort Hsort' Cut.
        + constructor.
        + destruct p as [a b]; destruct (proj2 (Cut a b)) as [? [_ abs]].
          exists b; split; auto. inversion abs.
        + destruct a as [c d]; destruct (proj1 (Cut c d)) as [? [_ abs]].
          exists d; split; auto. inversion abs.
        + inversion_clear Hsort; inversion_clear Hsort'.
          assert (cutsort : 
                  forall l (x a : key * elt),
                    sort lt_key l ->
                    lelistA lt_key a l -> InA eq_key_elt x l -> lt_key a x).
        apply SortA_InfA_InA; intuition.
        destruct a as [k v]; destruct p as [a b].
        assert (Heq : E.eq k a /\ elt_eq v b).
        destruct (proj1 (Cut k v)) as [k'' [Heq'' Hin'']]; 
          [exists v; split; auto|].
        inversion Hin''; subst; clear Hin''.
        inversion_clear H4; simpl in *; subst. constructor; auto.
        destruct (proj2 (Cut a b)) as [a' [Heq' Hin']]; [exists b; split; auto|].
        inversion Hin'; subst; clear Hin'.
        inversion_clear H5; simpl in *; subst; constructor; auto.      
        assert (R := cutsort _ _ _ H H0 H5).
        assert (R' := cutsort _ _ _ H1 H2 H4).
        unfold M.lt_key in R, R'; simpl in R, R'.
        contradiction (OT.lt_not_gt R R').
        constructor (try tauto).
        apply IHl; try assumption.
        intros g h; split; intros [h' [Hh' Hinh']].
        destruct (proj1 (Cut g h')) as [h'' [Hh'' Hinh'']]; 
          [exists h'; split; auto|].
        inversion Hinh''; auto; subst.
        2:(exists h''; split; [transitivity h'; assumption | auto]).
        inversion_clear H4; simpl in *; subst.
        assert (R := cutsort _ _ _ H H0 Hinh').
        compute in R; rewrite H3, (proj1 Heq) in R; 
        contradiction (OT.lt_antirefl R).
        destruct (proj2 (Cut g h')) as [h'' [Hh'' Hinh'']]; 
          [exists h'; split; auto|].
        inversion Hinh''; auto; subst.
        2:(exists h''; split; [transitivity h'; assumption | auto]).
        inversion_clear H4; simpl in *; subst.
        assert (R := cutsort _ _ _ H1 H2 Hinh').
        compute in R; rewrite H3, <- (proj1 Heq) in R; 
        contradiction (OT.lt_antirefl R).
    Qed.

    (* Morphisme le plus gÃ©nÃ©ral pour fold par rapport Ã  Equiv *)
    Global Instance fold_m `{A_Equiv : Equivalence A Aeq} :
      Proper ((E.eq ==> elt_eq ==> Aeq ==> Aeq) ==> Equiv ==> Aeq ==> Aeq)
      (@fold elt A).
    Proof.
      intros f f' Hf m m' Hm i i' Hi.
      rewrite !fold_1; assert (Heqm := elements_m m m' Hm); clear Hm.
      revert i i' Hi Heqm; generalize (elements m) (elements m'); clear m m'.
      induction l; intros l'; destruct l'; intros; simpl in *.
      assumption.
      inversion Heqm.
      inversion Heqm.
      inversion Heqm; subst; simpl in *.
      apply IHl; auto. apply Hf; auto.
    Qed.

    (** Exemple: fold appliquÃ© Ã  add *)
    Global Instance Equiv_Equivalence : Equivalence Equiv.
    Proof.
      constructor; repeat intro; apply Equiv_3; intros;
        rewrite ?H,?H0; reflexivity.
    Qed.

    Local Instance fold_add : 
      Proper (Equiv ==> Equiv ==> Equiv) (fold (@add _)).
    Proof.
      apply fold_m; exact add_m.
    Qed.

  End WithElt.

  (** Passage Ã  Equal *)
  Section Equal.
    Variable elt : Type.

    Remark Equiv_is_Equal : relation_equivalence (Equiv (@Logic.eq elt)) Equal.
    Proof.
      intros m m'; split; intros.
      intros x; destruct (Equiv_4 m m' H x); congruence.
      apply Equiv_3; intro k; rewrite (H k); reflexivity.
    Qed.

    (* si on exprime cette Ã©quivalence en utilisant 'relation_equivalence',
       on peut rÃ©Ã©crire directement Equiv en Equal dans les signatures de 
       morphisme car 'respectful' est un morphisme pour relation_equivalence *)
    
    Global Instance fold_add_Equal :
      Proper (Equal ==> Equal ==> Equal) (fold (@add elt)).
    Proof.
      rewrite <- Equiv_is_Equal; exact fold_add.
    Qed.

    Goal forall m m', Equal m m' ->
      Equal (fold (@add elt) m m) (fold (@add elt) m' m).
    Proof.
      intros.
      rewrite H; reflexivity.
    Qed.

  End Equal.
End MapMorphisms.




