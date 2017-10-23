(* Require Import OrderedTypeEx. *)

Require Import List SetoidPermutation SetoidList.
Require Import Bool.
Require Import SetoidDec.
Require Pactole.Util.Preliminary.
Require Import Pactole.Util.FSets.FsetInterface.

Generalizable All Variables.

(** This file corresponds to [FSetList.v] in the standard library
   and implements finite sets as ordered lists. The corresponding
   [FSet] and [FSetSpecs] instances are defined in
   the file [SetListInstance.v].
 *)

Set Implicit Arguments.
Open Scope signature_scope.

Definition set_ (A : Type) `{EqDec A} := list A.

Section ListOperations.
  Variable elt : Type.
  Context `{Heqdec:EqDec elt}.
  Definition set := (@set_ elt _ _).

  (* Hypothesis (comparedec : OrderedType elt). *)
  
  Definition empty : set := nil.
  Definition is_empty (s : set) : bool := if s then true else false.

  Fixpoint mem (x : elt) (s : set) {struct s} : bool :=
    match s with
    | nil => false
    | y :: l => if x == y then true else mem x l
    end.

  Definition add (x : elt) (s : set) : set :=
    if mem x s then s else x::s.

  Definition singleton (x : elt) : set := x :: nil.

  Fixpoint remove (x : elt) (s : set) {struct s} : set :=
    match s with
    | nil => nil
    | y :: l => if x == y then l else y :: remove x l
    end.

  Definition fold {B : Type} (f : elt -> B -> B) : set -> B -> B :=
    fold_left (flip f).

  Definition union (s : set) : set -> set := fold add s.
  
  Definition diff (s s' : set) : set := fold remove s' s.

  Definition inter (s s': set) : set :=
    fold (fun x s => if mem x s' then add x s else s) s nil.

  Definition subset (s s' : set) : bool := is_empty (diff s s').

  Definition equal (s s' : set) : bool := andb (subset s s') (subset s' s).

  Fixpoint filter (f : elt -> bool) (s : set) : set :=
    match s with
    | nil => nil
    | x :: l => if f x then x :: filter f l else filter f l
    end.

  Fixpoint for_all (f : elt -> bool) (s : set) : bool :=
    match s with
    | nil => true
    | x :: l => if f x then for_all f l else false
    end.

  Fixpoint exists_ (f : elt -> bool) (s : set) : bool :=
    match s with
    | nil => false
    | x :: l => if f x then true else exists_ f l
    end.

  Fixpoint partition (f : elt -> bool) (s : set) : set * set :=
    match s with
    | nil => (nil, nil)
    | x :: l =>
      let (s1, s2) := partition f l in
      if f x then (x :: s1, s2) else (s1, x :: s2)
    end.

  Definition cardinal (s : set) : nat := length s.

  Definition elements (s : set) : list elt := s.

  Definition choose (s : set) : option elt :=
    match s with
    | nil => None
    | x::_ => Some x
    end.


  Definition map  {B : Type} `{EqDec B} (f : elt -> B) (s : set): list B :=
    @List.map elt B f s.

  Notation In := (@InA elt equiv).
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : set) := exists x, In x s /\ P x.
End ListOperations.

Arguments empty {_%type_scope} {_} {_}.
Arguments In  {_%type_scope} {_} {_} {_} _ _%list_scope.
Arguments is_empty {_%type_scope} {_} {_} _%list_scope.
Arguments mem {_%type_scope} {_} {_}  _ _%set_scope.
Arguments add {_%type_scope} {_} {_} _%set_scope.
Arguments remove {_%type_scope} {_} {_} _ _%set_scope.
Arguments union {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments inter {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments diff {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments equal {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments subset {_%type_scope} {_} {_} _%set_scope _%set_scope.
Arguments fold {elt%type_scope} {_%type_scope} {_} _ _%set_scope _.
Arguments map {elt%type_scope} {_%type_scope} {_} {_} {_} _ _%set_scope.
Arguments for_all {_%type_scope} {_} _ _%set_scope.
Arguments exists_ {_%type_scope} {_} _ _%set_scope.
Arguments filter {_%type_scope} {_} _ _%set_scope.
Arguments partition {_%type_scope} {_} _ _%set_scope.
Arguments cardinal {_%type_scope} {_} _%set_scope.
Arguments elements {_%type_scope} {_} _%set_scope.
Arguments choose {_%type_scope} {_} _%set_scope.


Typeclasses Opaque set.

Set Implicit Arguments.
Unset Strict Implicit.
Section SetSpecs.
  Variable elt : Type.
  Context `{Heqdec:EqDec elt}.

  Let t := @set elt _ Heqdec.

  Notation In := (@InA elt equiv).

  Hint Extern 2 (In ?x (?x::_)) => constructor; reflexivity.
  Hint Immediate setoid_equiv.

  Lemma In_eq : forall l x y, x == y -> In x l -> In y l.
  Proof. apply InA_eqA; simpl;auto.  Qed.
  Global Instance In_eq_m : Proper (equiv ==> (@eq (list elt)) ==> iff) In.
  Proof.
    repeat intro; subst; split; apply In_eq; auto.
  Qed.

  Lemma mem_1 :
    forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof.
    simple induction s.
    - intros x Hs.
      inversion Hs.
    - intros a l Hforall x Hs.
      inversion_clear Hs.
      + simpl.
        destruct (equiv_dec x a);auto.
      + simpl.
        destruct (equiv_dec x a);auto.
  Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof.
    simple induction s.
    - intros; inversion H.
    - intros a l Hrec x.
      simpl.
      destruct (equiv_dec x a); intros; try discriminate; auto.
  Qed.

  Lemma mem_3 : forall (s : t) (x : elt), mem x s = false -> ~In x s.
  Proof.
    simple induction s.
    - intros.
      intro abs.
      inversion abs.
    -  intros a l Hrec x Hmem.
       intro abs.
       inversion abs;subst.
       + simpl in Hmem.
         destruct (equiv_dec x a);try discriminate;try contradiction. 
       + eapply Hrec with x;auto.
         simpl in Hmem.
         destruct (equiv_dec x a); intros; try discriminate; auto.
  Qed.


  Lemma mem_4 :
    forall (s : t) (x : elt), ~In x s -> mem x s = false.
  Proof.
    simple induction s.
    - intros x Hs.
      simpl.
      reflexivity.
    - intros a l Hforall x Hs.
      simpl.
       destruct (equiv_dec x a);auto.
       rewrite e in Hs.
       destruct Hs.
       constructor;auto.
  Qed.

  Lemma add_1 :
    forall (s : t) (x y : elt), x == y -> In y (add x s).
  Proof.
    simple induction s.
    - intros x y H.
      constructor 1;auto.
    - intros a l H x y H0.
      specialize (H _ _ H0).
      unfold add.
      destruct ( mem x (a :: l)) eqn:heq.
      + eapply In_eq;eauto.
        apply mem_2.
        assumption.
      + rewrite H0.
        constructor 1;auto.      
  Qed.

  Lemma add_2 :
    forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    simple induction s.
    - intros x y H.
      constructor 1;auto.
    - intros a l H x y H0.
      destruct (equiv_dec x y).
      apply add_1;auto.
      unfold add.
      destruct ( mem x (a :: l)) eqn:heq.
      + assumption.
      + constructor 2.
        assumption.
  Qed.
  Global Arguments mem {_%type_scope} {_} {_} _ !s%set_scope /.
  Global Arguments add {_%type_scope} {_} {_} _ !s%set_scope / .
  Global Arguments singleton {_%type_scope} {_} {_} _ / .

  Lemma add_3 :
    forall (s : t) (x y : elt),
      x =/= y -> In y (add x s) -> In y s.
  Proof.
    simple induction s.
    - intros x y H H0.
      simpl add in H0.
      inversion H0;subst.
      + symmetry in H2.
        contradiction.
      + inversion H2.
    - intros a l H x y H0 H1. 
      specialize (H _ _ H0).
      destruct (equiv_dec x a) eqn:heq.
      + simpl in H1.
        rewrite heq in H1.
        assumption.
      + simpl in H1.
        rewrite heq in *.
        destruct (mem x l) eqn:heq_mem.
        * assumption.
        * inversion H1.
          -- symmetry in H3;contradiction.
          -- assumption.
  Qed.

  Lemma remove_1 :
    forall (s : t) (Hnd:NoDupA equiv s) (x y : elt), x == y -> ~ In y (remove x s).
  Proof.
    simple induction s.
    - simpl; red; intros; inversion H0.
    - simpl; intros.
      destruct (equiv_dec x a).
      + inversion Hnd;subst.
        rewrite <- H0.
        rewrite e.
        assumption.
      + rewrite H0 in c.
        intro abs.
        inversion abs.
        * contradiction.
        * subst.
          revert H2.
          apply H;auto.
          inversion Hnd;auto.
  Qed.

  Lemma remove_2 :
    forall (s : t) (Hs : NoDupA equiv s) (x y : elt),
      x =/= y -> In y s -> In y (remove x s).
  Proof.
    simple induction s.
    - simpl; intuition.
    - simpl; intros.
      destruct (equiv_dec x a).
      + rewrite e in H0.
        inversion H1.
        * symmetry in H3. contradiction.
        * subst.
          assumption.
      + inversion H1.
        * constructor 1. assumption.
        * subst.
          constructor 2.
          eapply H;eauto.
          inversion Hs;auto.
  Qed.

  Lemma remove_3 :
    forall (s : t) (Hs : NoDupA equiv s) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    simple induction s.
    - simpl; intuition.
    - simpl; intros a l Hrec Hs x y; destruct (equiv_dec x a); intuition.
      inversion_clear Hs; inversion_clear H; auto.
      constructor 2; apply Hrec with x; auto.
  Qed.

  Lemma singleton_sort : forall x : elt, NoDupA equiv (singleton x).
  Proof.
    simpl; constructor; auto.
    rewrite InA_nil;auto.
  Qed.

  Lemma singleton_1 : forall x y : elt, In y (singleton x) -> x == y.
  Proof.
    simpl; intuition.
    inversion_clear H; auto; inversion H0.
  Qed.

  Lemma singleton_2 : forall x y : elt, x == y -> In y (singleton x).
  Proof.
    simpl; auto.
  Qed.

  Ltac DoubleInd :=
    simple induction s;
    [ simpl; auto; try solve [ intros; inversion H ]
    | intros x l Hrec; simple induction s';
      [ simpl; auto; try solve [ intros; inversion H ]
      | intros x' l' Hrec' Hs Hs'; inversion Hs; inversion Hs'; subst;
        simpl ] ].

  Arguments flip {_%type_scope} {_%type_scope} {_%type_scope} _ / _.
  Arguments union {_%type_scope} {_} {_} _%set_scope _%set_scope /.
  (* Arguments fold {_%type_scope} _ _ {_%set_scope} {_%set_scope} _ !_/. *)


  Instance mem_proper: Proper (equiv ==> PermutationA equiv ==> eq) (@mem _ S0 Heqdec).
  Proof.
    repeat red.
    intros x y H x0 y0 H0.
    revert x y H.
    pattern x0, y0.
    
    apply PermutationA_ind with (eqA:=equiv);[ | | | | assumption]; clear H0;simpl.
    - reflexivity.
    - intros x₁ x₂ l₁ l₂ heqx1x2 hpermut IHPermutationA x y heqxy. 
      rewrite (IHPermutationA _ _ heqxy).
      destruct (equiv_dec x x₁); destruct (equiv_dec y x₂);auto.
      + rewrite e,heqx1x2 in heqxy.
        symmetry in heqxy;contradiction.
      + rewrite e, <- heqx1x2 in heqxy.
        contradiction.
    - simpl.
      intros x y l x1 y1 H.
       destruct (equiv_dec x1 y);destruct (equiv_dec y1 y);auto;
      destruct (equiv_dec x1 x);auto;
      destruct (equiv_dec y1 x);auto;
        rewrite H in *; try contradiction.
      { clear c c0 c1 c2.
        induction l;auto.
        simpl.
        destruct (equiv_dec x1 a);destruct (equiv_dec y1 a);auto;rewrite H in *;try contradiction. }
    - intros l₁ l₂ l₃ H H0 H1 H2 x y H3.
      transitivity (mem y l₂);auto.
  Qed.

  Lemma add_compat:
    forall x0 : list elt,
      NoDupA equiv x0 ->
      forall y0 : list elt,
        NoDupA equiv y0 ->
        forall x y : elt,
          x == y ->
          PermutationA equiv x0 y0 -> PermutationA equiv (add x x0) (add y y0).
  Proof.
  intros x0 hnodupx0.
  induction hnodupx0.
  - simpl.
    intros.
    rewrite (Preliminary.PermutationA_nil _ H1).
    simpl.
    constructor 2;auto.
    constructor 1.
  - intros.
    assert (In x (x :: l)) by (constructor;auto).
    specialize (@Preliminary.PermutationA_InA_inside _ _ setoid_equiv x _ _ H2 H3) as hex.
    decompose [and ex] hex;clear hex;subst.
    
    assert (heq_memx0:mem x0 (x :: l) = mem y (x1 ++ x2 :: x3)%list).
    { apply mem_proper;assumption. } (* Why does [rewrite H1,H2] fail? *)
    cbv beta iota delta -[mem app].
    destruct (mem x0 (x :: l)) eqn:heq.
    * rewrite <- heq_memx0.
      change  (PermutationA equiv (x :: l) (x1 ++ x2 :: x3)).
      assumption.
    * rewrite <- heq_memx0.
      change  (PermutationA equiv (x0 :: x :: l) (y :: x1 ++ x2 :: x3)).
      constructor 2.
      -- auto.
      -- Info 2 auto.
  Qed.


  Lemma flip_add_compat: forall x0 : list elt,
      NoDupA equiv x0 ->
      forall y0 : list elt,
        NoDupA equiv y0 ->
        forall x y : elt,
          x == y ->
          PermutationA equiv x0 y0 -> PermutationA equiv (flip add x0 x) (flip add y0 y).
  Proof.
    unfold flip.
    apply add_compat.
  Qed.



  Lemma add_NoDup :
    forall e (s : t) (Hs : NoDupA equiv s), NoDupA equiv (add e s).
  Proof.
    intros e s Hs.
    unfold add.
    destruct (mem e s) eqn:heq.
    - assumption.
    - constructor.
      + apply mem_3.
        assumption.
      + assumption.
  Qed.

  Lemma union_NoDup :
    forall (s s' : t) (Hs : NoDupA equiv s) (Hs' : NoDupA equiv s'), NoDupA equiv (union s s').
  Proof.
    simple induction s;intros.
    -  simpl; auto; try solve [ intros; inversion H ].
    - simpl.
      eapply H.
      + inversion Hs;auto.
      + apply add_NoDup.
        assumption.
  Qed.

  Ltac fold_union :=
    repeat progress match goal with
                    | |- context C [(fold (set (elt:=elt)) add ?s ?s')] =>
                      let x:= context C[(union s s')] in
                      change x
                    | H:context C [(fold (set (elt:=elt)) add ?s ?s')] |- _ =>
                      let x:= context C[(union s s')] in
                      change x in H
                    end.

  Lemma cle1: forall x y l, PermutationA equiv (add x (add y l)) (add y (add x l)).
  Proof.
    intros x y l. 
  unfold add.
  destruct (mem y l) eqn:heqy; destruct (mem x l) eqn:heqx;
    repeat progress (simpl;try rewrite heqy; try rewrite heqx).
  - reflexivity.
  - destruct (equiv_dec y x);reflexivity.
  - destruct (equiv_dec x y);reflexivity.
  - destruct (equiv_dec x y);
      destruct (equiv_dec y x).
    + constructor 2;auto;reflexivity.
    + symmetry in e;contradiction.
    + symmetry in e;contradiction.
    + constructor 3;auto;reflexivity.
  Qed.

  Lemma cle: forall l l' l'',
      PermutationA equiv l' l'' ->
      PermutationA equiv (union l l') (union l l'').
  Proof.
    intros l.
    induction l;simpl;intros.
    - assumption.
    - fold_union.
      assert (PermutationA equiv (add a l') (add a l'')).
      { unfold add.
        destruct (mem a l') eqn:heql'.
        - assert (mem a l'' = true).
          { rewrite <- heql'.
            apply mem_proper;auto.
            symmetry;auto. }
          rewrite H0.
          assumption.
        - assert (mem a l'' = false).
          { rewrite <- heql'.
            apply mem_proper;auto.
            symmetry;auto. }
          rewrite H0.
          constructor 2;auto. }
      apply IHl.
      assumption.
  Qed.

  Lemma cle2: forall x l l', PermutationA equiv (union (x::l) l') (add x (union l l')).
  Proof.
    induction l.
    - intros l'. 
      simpl.
      reflexivity.
    - intros l'. 
      simpl.
      fold_union.
      transitivity (union l (add x (add a l'))).
      + apply cle.
        apply cle1.
      + apply IHl.
  Qed.

  Lemma cle3: forall l l' u u',     
      PermutationA equiv l l' ->
      PermutationA equiv u u' ->
      PermutationA equiv (union l u) (union l' u').
  Proof.
    intros l l' u u' H H0.
    transitivity (union l u').
    { apply cle. assumption. }
    clear H0.
    revert u'.
    pattern l, l'.
    
    apply PermutationA_ind with (eqA:=equiv);[ | | | | assumption];simpl;fold_union.
    - reflexivity.
    - intros x₁ x₂ l₁ l₂ H0 H1 H2 u'. 
      fold_union.
      change (forall u' : list elt, PermutationA equiv (union l₁ u') (union l₂ u')) in H2.
      transitivity (add x₁ (union l₁ u')).
      { apply cle2. }
      transitivity(add x₂ (union l₂ u')).
      2: symmetry;eapply cle2.
      
      constructor 2.
      

      induction H.
    - intros l'. 
      simpl.
      reflexivity.
    - intros l'. 
      simpl.
      fold_union.
      transitivity (union l (add x (add a l'))).
      + apply cle.
        apply cle1.
      + apply IHl.
  Qed.



  Lemma union_1 :
    forall (s s' : t)  (x : elt), 
      In x (union s s') -> In x s \/ In x s'.
  Proof.
    induction s.
    - simpl.
      intros s' x H. 
      right.
      assumption.
    - revert  s a IHs.
      simple induction s'.
      + intros x Hrec.
        left.
        simpl in *.
        apply InA_cons.
        specialize (IHs (a :: nil) x Hrec).
        destruct IHs.
        * right.
          assumption.
        * left.
          inversion H;auto.
      + intros a0 l H x H0. 
        destruct (equiv_dec x a0) eqn:heq.
        * right;constructor 1;auto.
        * enough  (In x (a :: s) \/ In x l).
          { decompose [or] H1.
            - left;auto.
            - right.
              constructor 2;auto. }
          eapply H.

          Lemma foo : forall x s a0 l, 
              In x (union s (a0 :: l)) -> x == a0 \/ In x (union s l).
          Proof.
            induction s.
            simpl.
            - intros a0 l H. 
              inversion H;auto.
            - intros a0 l H.
              destruct (mem a ((a0 :: l))) eqn:heq.
              + cbv beta iota delta [union fold add fold_left flip] in H.
                rewrite heq in H.
                change (In x (union s (a0 :: l))) in H.
                specialize (IHs _ _ H).
                destruct IHs;auto.
                right.

                
              + assert (In x (union s (a0 :: a :: l)) ).
              { cbv beta iota delta [union fold fold_left flip] in H.
                change (In x (fold_left (flip add)
                                        s (if mem a (a0 :: l) then a0 :: l else a :: a0 :: l)))
                  in H.
                change (In x (union
                                        s (if mem a (a0 :: l) then a0 :: l else a :: a0 :: l)))
                  in H.
                rewrite heq in H.
                Lemma bar : forall s x l l',
                    PermutationA equiv l l' ->
                    In x (union s l) -> In x (union s l').
                Proof.
                  induction s.
                  - simpl.
                    intros x l l' H H0. 
                    rewrite <- H.
                    assumption.
                  - intros x l l' H H0. 
                    simpl.
                    unfold add at 2.
                    destruct (mem a l') eqn: heq.
                    + change (In x (union s l')).
                      eapply IHs;eauto.
                      simpl in H0.
                      unfold add in H0 at 2.
                      assert (mem a l = true).
                      { rewrite <- heq.
                        eapply mem_proper;eauto. }
                      rewrite H1 in H0.
                       change (In x (union s l)) in H0.
                       assumption.
                    + change (In x (union s (a::l'))).
                      simpl in H0.
                      unfold add in H0 at 2.
                      assert (mem a l = false).
                      { rewrite <- heq.
                        eapply mem_proper;eauto. }
                      rewrite H1 in H0.
                      change (In x (union s (a::l))) in H0.
                      eapply IHs with (l:= a::l);auto.
                      constructor 2;auto.
                Qed.
                eapply bar;eauto.
                constructor 3. }
              eapply IHs;eauto.
              simpl.
              unfold  add at 2.
              assert (mem a l = false).
              { simpl in heq.
                destruct (equiv_dec a a0);auto; try discriminate. }
              rewrite H1.
              apply H0.
          Qed.
        
        elim (Hrec (x' :: l') H1 Hs' x0); intuition.
        elim (Hrec l' H1 H5 x0); intuition.
        elim (H3 x0); intuition.



intros x H.
        destruct (equiv_dec x a) eqn:heq.
        -- left;constructor 1;auto.
        -- simpl in H. 
          simpl in H|- *.
        


        destruct (equiv_dec a a0) eqn:heq.
        * enough (In x (s) \/ In x (a0 :: s')).
          { destruct H0.
            - left.
              constructor 2.
              assumption.
            - inversion H0;auto. }
          eapply IHs.
          inversion H.
          -- rewrite heq in H0.
             simpl.
             rewrite <- H0.
             constructor 1;auto.
          -- rewrite heq in H0.
             simpl.
             rewrite <- H0.
             constructor 2;auto.
        *
          
          enough (In x s \/ In x (a::a0::s')).
          { decompose [or] H0;auto.
            inversion H1;subst.
            - left.
              constructor 1;auto.
            - inversion H3;subst.
              + right. constructor 1;auto.
              + right.
                constructor 2;auto. }
          eapply IHs.
          simpl in H|- *.
          rewrite heq in H.
          change (In x (union s (a :: a0 :: s'))).
          change  in H.




          enough ( In x (a0 :: nil) \/ In x (a :: s) \/ In x s').
          { decompose [or] H0;auto.
            right.
            constructor 1.
            inversion H1;auto. }
          destruct (equiv_dec x a0) eqn:heq2.
          -- left.
             constructor 1;auto.
          -- right.
             eapply IHs'.
             
             apply mem_1 in H.
             rewrite 
        
        eapply IHs.

    DoubleInd; destruct (compare_dec x x'); intuition;
      inversion_clear H0; intuition.
    elim (Hrec (x' :: l') H1 Hs' x0); intuition.
    elim (Hrec l' H1 H5 x0); intuition.
    elim (H3 x0); intuition.
  Qed.

  Lemma union_2 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x s -> In x (union s s').
  Proof.
    DoubleInd.
    intros i Hi; destruct (compare_dec x x'); intuition;
      inversion_clear Hi; auto.
  Qed.

  Lemma union_3 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x s' -> In x (union s s').
  Proof.
    DoubleInd.
    intros i Hi; destruct (compare_dec x x'); inversion_clear Hi; intuition.
    constructor; transitivity x'; auto.
  Qed.

  Lemma inter_Inf :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
      Inf a s -> Inf a s' -> Inf a (inter s s').
  Proof.
    DoubleInd.
    intros i His His'; inversion His; inversion His'; subst.
    destruct (compare_dec x x'); intuition.
    apply Inf_lt with x; auto.
    apply H4; auto.
    apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve inter_Inf.

  Lemma inter_sort :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (inter s s').
  Proof.
    DoubleInd; destruct (compare_dec x x'); auto.
    constructor; auto.
    apply Inf_eq with x'; trivial;
      apply inter_Inf; trivial; apply Inf_eq with x; auto.
  Qed.

  Lemma inter_1 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x (inter s s') -> In x s.
  Proof.
    DoubleInd; destruct (compare_dec x x'); intuition.
    constructor 2; apply Hrec with (x'::l'); auto.
    inversion_clear H0; auto.
    constructor 2; apply Hrec with l'; auto.
  Qed.

  Lemma inter_2 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x (inter s s') -> In x s'.
  Proof.
    DoubleInd; destruct (compare_dec x x'); intuition; inversion_clear H0.
    constructor 1; transitivity x; auto.
    constructor 2; auto.
  Qed.

  Lemma inter_3 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x s -> In x s' -> In x (inter s s').
  Proof.
    DoubleInd.
    intros i His His'; destruct (compare_dec x x'); intuition.

    inversion_clear His; auto.
    generalize (Sort_Inf_In Hs' (cons_leA _ _ _ _ H) His').
    intro abs; rewrite H0 in abs; contradiction (lt_antirefl abs).

    inversion_clear His; auto; inversion_clear His'; auto.
    constructor; transitivity x'; auto.

    change (In i (inter (x :: l) l')).
    inversion_clear His'; auto.
    generalize (Sort_Inf_In Hs (cons_leA _ _ _ _ H) His).
    intro abs; rewrite H0 in abs; contradiction (lt_antirefl abs).
  Qed.

  Lemma diff_Inf :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
      Inf a s -> Inf a s' -> Inf a (diff s s').
  Proof.
    DoubleInd.
    intros i His His'; inversion His; inversion His'.
    destruct (compare_dec x x'); intuition.
    apply Hrec; trivial.
    apply Inf_lt with x; auto.
    apply Inf_lt with x'; auto.
    apply H11; trivial.
    apply Inf_lt with x'; auto.
  Qed.
  Hint Resolve diff_Inf.

  Lemma diff_sort :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (diff s s').
  Proof.
    DoubleInd; destruct (compare_dec x x'); auto.
  Qed.

  Lemma diff_1 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x (diff s s') -> In x s.
  Proof.
    DoubleInd; destruct (compare_dec x x'); intuition.
    inversion_clear H0; auto.
    constructor 2; apply Hrec with (x'::l'); auto.
    constructor 2; apply Hrec with l'; auto.
  Qed.

  Lemma diff_2 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x (diff s s') -> ~ In x s'.
  Proof.
    DoubleInd.
    intros; intro Abs; inversion Abs.
    destruct (compare_dec x x'); intuition.

    inversion_clear H0.
    generalize (Sort_Inf_In Hs' (cons_leA _ _ _ _ H) H4).
    intro abs; exact (gt_not_eq abs H7).
    apply Hrec with (x'::l') x0; auto.

    inversion_clear H4.
    generalize (Sort_Inf_In H1 H2 (diff_1 H1 H5 H0)).
    apply eq_not_lt; transitivity x'; auto.
    apply Hrec with l' x0; auto.

    inversion_clear H4.
    generalize (Sort_Inf_In Hs (cons_leA _ _ _ _ H) (diff_1 Hs H5 H0)).
    apply eq_not_lt; auto.
    apply H3 with x0; auto.
  Qed.

  Lemma diff_3 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
      In x s -> ~ In x s' -> In x (diff s s').
  Proof.
    DoubleInd.
    intros i His His'; destruct (compare_dec x x'); intuition;
      inversion_clear His; auto.
    elim His'; constructor; transitivity x; auto.
  Qed.

  Lemma equal_1 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
      Equal s s' -> equal s s' = true.
  Proof.
    simple induction s; unfold Equal.
    intro s'; case s'; auto.
    simpl; intuition.
    elim (H e); intros; assert (Z : In e nil);
      [apply H1; constructor; reflexivity | inversion Z].
    intros x l Hrec s'.
    case s'.
    intros; elim (H x); intros; assert (Z : In x nil);
      [apply H0; constructor; reflexivity | inversion Z].
    intros x' l' Hs Hs'; inversion Hs; inversion Hs'; subst.
    simpl; destruct (compare_dec x x'); intros; auto.

    elim (H0 x); intros.
    assert (Z : In x (x' :: l'));
      [apply H3; constructor; reflexivity | inversion_clear Z].
    contradiction (lt_not_eq H H7).
    generalize (Sort_Inf_In H5 H6 H7); intro abs.
    contradiction (lt_not_gt abs H).

    apply Hrec; intuition; elim (H0 a); intros.
    assert (Z : In a (x' :: l')); auto; inversion_clear Z; auto.
    generalize (Sort_Inf_In H1 H2 H3).
    rewrite H; intro abs; contradiction (gt_not_eq abs H8).
    assert (Z : In a (x :: l)); auto; inversion_clear Z; auto.
    generalize (Sort_Inf_In H5 H6 H3).
    rewrite <- H; intro abs; contradiction (gt_not_eq abs H8).

    elim (H0 x'); intros.
    assert (Z : In x' (x :: l));
      [apply H4; constructor; reflexivity | inversion_clear Z].
    contradiction (gt_not_eq H (symmetry H7)).
    generalize (Sort_Inf_In H1 H2 H7); intro abs.
    contradiction (lt_not_gt abs H).
  Qed.

  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
    simple induction s; unfold Equal.
    intro s'; case s'; intros.
    intuition.
    simpl in H; discriminate H.
    intros x l Hrec s'.
    case s'.
    intros; simpl in H; discriminate.
    intros x' l'; simpl; destruct (compare_dec x x');
      intros; auto; try discriminate.
    elim (Hrec l' H0 a); intuition; inversion_clear H3; auto.
    constructor; transitivity x; auto.
    constructor; transitivity x'; auto.
  Qed.

  Lemma subset_1 :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
      Subset s s' -> subset s s' = true.
  Proof.
    intros s s'; generalize s' s; clear s s'.
    simple induction s'; unfold Subset.
    intro s; case s; auto.
    intros; elim (H e); intros; assert (Z : In e nil); auto; inversion Z.
    intros x' l' Hrec s; case s.
    simpl; auto.
    intros x l Hs Hs'; inversion Hs; inversion Hs'; subst.
    simpl; destruct (compare_dec x x'); intros; auto.

    assert (Z : In x (x' :: l')); auto; inversion_clear Z.
    contradiction (lt_not_eq H H3).
    generalize (Sort_Inf_In H5 H6 H3).
    intro abs; contradiction (lt_not_gt H abs).

    apply Hrec; intuition.
    assert (Z : In a (x' :: l')); auto; inversion_clear Z; auto.
    generalize (Sort_Inf_In H1 H2 H3).
    rewrite H; intro abs; contradiction (gt_not_eq abs H4).

    apply Hrec; intuition.
    assert (Z : In a (x' :: l')); auto; inversion_clear Z; auto.
    inversion_clear H3.
    contradiction (lt_antirefl (x:=a)); rewrite H4 at 1; rewrite H7; auto.
    generalize (Sort_Inf_In H1 H2 H7).
    rewrite H4; intro abs; contradiction (lt_not_gt H abs).
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
    intros s s'; generalize s' s; clear s s'.
    simple induction s'; unfold Subset.
    intro s; case s; auto.
    simpl; intros; discriminate H.
    intros x' l' Hrec s; case s.
    intros; inversion H0.
    intros x l; simpl; destruct (compare_dec x x'); intros; auto.
    discriminate.
    inversion_clear H1.
    constructor; transitivity x; auto.
    constructor 2; apply Hrec with l; auto.
    constructor 2; apply Hrec with (x::l); auto.
  Qed.

  Lemma empty_sort : Sort empty.
  Proof.
    unfold empty; constructor.
  Qed.

  Lemma empty_1 : Empty empty.
  Proof.
    unfold Empty, empty; intuition; inversion H.
  Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    unfold Empty; intro s; case s; simpl; intuition.
    elim (H e); auto; constructor; reflexivity.
  Qed.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    unfold Empty; intro s; case s; simpl; intuition;
      inversion H0.
  Qed.

  Lemma elements_1 : forall (s : t) (x : elt), In x s -> In x (elements s).
  Proof.
    unfold elements; auto.
  Qed.

  Lemma elements_2 : forall (s : t) (x : elt), In x (elements s) -> In x s.
  Proof.
    unfold elements; auto.
  Qed.

  Lemma elements_3 : forall (s : t) (Hs : Sort s), Sort (elements s).
  Proof.
    unfold elements; auto.
  Qed.
  Lemma elements_3w : forall (s : t) (Hs : Sort s), NoDupA _eq (elements s).
  Proof.
    unfold elements; intros; apply SortA_NoDupA with _lt; auto.
  Qed.

  Lemma min_elt_1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s.
  Proof.
    intro s; case s; simpl; intros; inversion H; auto.
  Qed.

  Lemma min_elt_2 :
    forall (s : t) (Hs : Sort s) (x y : elt),
      min_elt s = Some x -> In y s -> ~ y <<< x.
  Proof.
    simple induction s; simpl.
    intros; inversion H.
    intros a l; case l; intros; inversion H0; inversion_clear H1; subst.
    apply eq_not_lt; auto.
    inversion H2.
    apply eq_not_lt; auto.
    inversion_clear Hs.
    inversion_clear H3.
    generalize (H H1 e y (refl_equal (Some e)) H2).
    intros Hlt abs; apply Hlt; transitivity x; auto.
  Qed.

  Lemma min_elt_3 : forall s : t, min_elt s = None -> Empty s.
  Proof.
    unfold Empty; intro s; case s; simpl; intuition;
      inversion H; inversion H0.
  Qed.

  Lemma max_elt_1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s.
  Proof.
    simple induction s; simpl.
    intros; inversion H.
    intros x l; case l; simpl.
    intuition.
    inversion H0; auto.
    intros.
    constructor 2; apply (H _ H0).
  Qed.

  Lemma max_elt_2 :
    forall (s : t) (Hs : Sort s) (x y : elt),
      max_elt s = Some x -> In y s -> ~ x <<< y.
  Proof.
    simple induction s; simpl.
    intros; inversion H.
    intros x l; case l; simpl.
    intuition.
    inversion H0; subst.
    inversion_clear H1.
    apply (gt_not_eq H2 H3).
    inversion H3.
    intros; inversion_clear Hs; inversion_clear H3; inversion_clear H1.
    assert (In e (e::l0)) by auto.
    generalize (H H2 x0 e H0 H1).
    intros Hlt abs; apply Hlt; transitivity y; auto; rewrite H3; auto.
    exact (H H2 x0 y H0 H3).
  Qed.

  Lemma max_elt_3 : forall s : t, max_elt s = None -> Empty s.
  Proof.
    unfold Empty; simple induction s; simpl.
    red; intros; inversion H0.
    intros x l; case l; simpl; intros.
    inversion H0.
    elim (H H0 e); auto.
  Qed.

  Definition choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s := min_elt_1.

  Definition choose_2 : forall s : t, choose s = None -> Empty s := min_elt_3.

  Lemma choose_3: forall s s', Sort s -> Sort s' -> forall x x',
                                   choose s = Some x -> choose s' = Some x' -> Equal s s' -> x === x'.
  Proof.
    unfold choose, Equal; intros s s' Hs Hs' x x' Hx Hx' H.
    assert (~x <<< x').
    apply min_elt_2 with s'; auto.
    rewrite <-H; auto using min_elt_1.
    assert (~x' <<< x).
    apply min_elt_2 with s; auto.
    rewrite H; auto using min_elt_1.
    destruct (compare_dec x x'); intuition.
  Qed.

  Lemma fold_1 :
    forall (s : t) (Hs : Sort s) (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof.
    induction s.
    simpl; trivial.
    intros.
    inversion_clear Hs.
    simpl; auto.
  Qed.

  Lemma cardinal_1 :
    forall (s : t) (Hs : Sort s), cardinal s = length (elements s).
  Proof.
    auto.
  Qed.

  Lemma filter_Inf :
    forall (s : t) (Hs : Sort s) (x : elt) (f : elt -> bool),
      Inf x s -> Inf x (filter f s).
  Proof.
    simple induction s; simpl.
    intuition.
    intros x l Hrec Hs a f Ha; inversion_clear Hs; inversion_clear Ha.
    case (f x).
    constructor; auto.
    apply Hrec; auto.
    apply Inf_lt with x; auto.
  Qed.

  Lemma filter_sort :
    forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (filter f s).
  Proof.
    simple induction s; simpl.
    auto.
    intros x l Hrec Hs f; inversion_clear Hs.
    case (f x); auto.
    constructor; auto.
    apply filter_Inf; auto.
  Qed.

  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool)
           `{Proper _ (_eq ==> (@eq bool)) f}, In x (filter f s) -> In x s.
  Proof.
    simple induction s; simpl.
    intros; inversion H0.
    intros x l Hrec a f Hf.
    case (f x); simpl.
    inversion_clear 1.
    constructor; auto.
    constructor 2; apply (Hrec a f Hf); trivial.
    constructor 2; apply (Hrec a f Hf); trivial.
  Qed.

  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool)
           `{Proper _ (_eq ==> (@eq bool)) f},
      In x (filter f s) -> f x = true.
  Proof.
    simple induction s; simpl.
    intros; inversion H0.
    intros x l Hrec a f Hf.
    generalize (Hf x); case (f x); simpl; auto.
    inversion_clear 2; auto.
    symmetry; auto.
  Qed.

  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool)
           `{Proper _ (_eq ==> (@eq bool)) f},
      In x s -> f x = true -> In x (filter f s).
  Proof.
    simple induction s; simpl.
    intros; inversion H0.
    intros x l Hrec a f Hf.
    generalize (Hf x); case (f x); simpl.
    inversion_clear 2; auto.
    inversion_clear 2; auto.
    rewrite <- (H a (symmetry H1)); intros; discriminate.
  Qed.

  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
      For_all (fun x => f x = true) s -> for_all f s = true.
  Proof.
    simple induction s; simpl; auto; unfold For_all.
    intros x l Hrec f Hf.
    generalize (Hf x); case (f x); simpl.
    auto.
    intros; rewrite (H x); auto; reflexivity.
  Qed.

  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
      for_all f s = true -> For_all (fun x => f x = true) s.
  Proof.
    simple induction s; simpl; auto; unfold For_all.
    intros; inversion H1.
    intros x l Hrec f Hf.
    intros Z a; intros.
    assert (f x = true).
    generalize Z; case (f x); auto.
    rewrite H0 in Z; simpl in Z.
    inversion_clear H; auto.
    rewrite (Hf a x); auto.
  Qed.

  Lemma exists_1 :
    forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
      Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof.
    simple induction s; simpl; auto; unfold Exists.
    intros.
    elim H0; intuition.
    inversion H2.
    intros x l Hrec f Hf.
    generalize (Hf x); case (f x); simpl.
    auto.
    destruct 2 as [a (A1,A2)].
    inversion_clear A1.
    rewrite <- (H a (symmetry H0)) in A2; discriminate.
    apply Hrec; auto.
    exists a; auto.
  Qed.

  Lemma exists_2 :
    forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
      exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof.
    simple induction s; simpl; auto; unfold Exists.
    intros; discriminate.
    intros x l Hrec f Hf.
    case_eq (f x); intros.
    exists x; auto.
    destruct (Hrec f Hf H0) as [a (A1,A2)].
    exists a; auto.
  Qed.

  Lemma partition_Inf_1 :
    forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
      Inf x s -> Inf x (fst (partition f s)).
  Proof.
    simple induction s; simpl.
    intuition.
    intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
    generalize (Hrec H f a).
    case (f x); case (partition f l); simpl.
    auto.
    intros; apply H2; apply Inf_lt with x; auto.
  Qed.

  Lemma partition_Inf_2 :
    forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
      Inf x s -> Inf x (snd (partition f s)).
  Proof.
    simple induction s; simpl.
    intuition.
    intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion_clear Ha.
    generalize (Hrec H f a).
    case (f x); case (partition f l); simpl.
    intros; apply H2; apply Inf_lt with x; auto.
    auto.
  Qed.

  Lemma partition_sort_1 :
    forall (s : t) (Hs : Sort s) (f : elt -> bool),
      Sort (fst (partition f s)).
  Proof.
    simple induction s; simpl.
    auto.
    intros x l Hrec Hs f; inversion_clear Hs.
    generalize (Hrec H f); generalize (partition_Inf_1 H f).
    case (f x); case (partition f l); simpl; auto.
  Qed.

  Lemma partition_sort_2 :
    forall (s : t) (Hs : Sort s) (f : elt -> bool),
      Sort (snd (partition f s)).
  Proof.
    simple induction s; simpl.
    auto.
    intros x l Hrec Hs f; inversion_clear Hs.
    generalize (Hrec H f); generalize (partition_Inf_2 H f).
    case (f x); case (partition f l); simpl; auto.
  Qed.

  Lemma partition_1 :
    forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
      Equal (fst (partition f s)) (filter f s).
  Proof.
    simple induction s; simpl; auto; unfold Equal.
    split; auto.
    intros x l Hrec f Hf.
    generalize (Hrec f Hf); clear Hrec.
    destruct partition as [s1 s2]; simpl; intros.
    case (f x); simpl; auto.
    split; inversion_clear 1; auto.
    constructor 2; generalize (proj1 (H a)); auto.
    constructor 2; generalize (proj2 (H a)); auto.
  Qed.

  Lemma partition_2 :
    forall (s : t) (f : elt -> bool) `{Proper _ (_eq ==> (@eq bool)) f},
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
    simple induction s; simpl; auto; unfold Equal.
    split; auto.
    intros x l Hrec f Hf.
    generalize (Hrec f Hf); clear Hrec.
    destruct partition as [s1 s2]; simpl; intros.
    case (f x); simpl; auto.
    split; inversion_clear 1; auto.
    constructor 2; generalize (proj1 (H a)); auto.
    constructor 2; generalize (proj2 (H a)); auto.
  Qed.

  Lemma map_monotonic_Inf `{OrderedType B} :
    forall (s : t) (Hs : Sort s) (x : elt)
           (f : elt -> B) `{Proper _ (_lt ==> _lt) f},
      Inf x s -> lelistA _lt (f x) (map_monotonic f s).
  Proof.
    simple induction s; simpl.
    intuition.
    intros x l Hrec Hs a f Hf Ha; inversion_clear Hs; inversion_clear Ha.
    constructor; auto.
  Qed.

  Lemma map_monotonic_sort `{OrderedType B} :
    forall (s : t) (Hs : Sort s)
           (f : elt -> B) `{Proper _ (_lt ==> _lt) f},
      sort _lt (map_monotonic f s).
  Proof.
    simple induction s; simpl.
    auto.
    intros x l Hrec Hs f Hf; inversion_clear Hs.
    constructor; auto.
    apply map_monotonic_Inf; auto.
  Qed.
End SetSpecs.

Definition In `{OrderedType A} (x : A) (s : set A) := InA _eq x s.
End SetList.

Module S := SetList.

Structure set (A : Type) `{OrderedType A}
  := Build_set {this :> list A; sorted : sort _lt this}.
Implicit Arguments this [[A] [H]].
Implicit Arguments Build_set [[A] [H] [this]].
Implicit Arguments sorted [[A] [H]].

Section SetDefinitions.
  Variable A : Type.
  Hypothesis (comparedec : OrderedType A).

  Let elt := A.
  Let t := set elt.

  Definition empty : t := Build_set (@S.empty_sort _ _).
  Definition is_empty (s : t) : bool := S.is_empty s.
  Definition mem (x : elt) (s : t) : bool := S.mem x s.
  Definition add (x : elt) (s : t) : t :=
    Build_set (S.add_sort (sorted s) x).
  Definition singleton (x : elt) : t :=
    Build_set (S.singleton_sort _ x).
  Definition remove (x : elt) (s : t) : t :=
    Build_set (S.remove_sort (sorted s) x).
  Definition union (s s' : t) : t :=
    Build_set (S.union_sort (sorted s) (sorted s')).
  Definition inter (s s' : t) : t :=
    Build_set (S.inter_sort (sorted s) (sorted s')).
  Definition diff (s s' : t) : t :=
    Build_set (S.diff_sort (sorted s) (sorted s')).

  Definition equal (s s' : t) : bool := S.equal s s'.
  Definition subset (s s' : t) : bool := S.subset s s'.

  Definition fold {B : Type} (f : elt -> B -> B) (s : t) : B -> B :=
    S.fold f s.
  (*   Definition map {B : Type} (f : elt -> B) (s : t) : set B := *)
  (*     Build_set (S.map f s. *)
  Definition map_monotonic {B : Type} `{OrderedType B}
             (f : elt -> B) `{Mono : Proper _ (_lt ==> _lt) f} (s : t) : set B :=
    Build_set (S.map_monotonic_sort (sorted s)).

  Definition filter (f : elt -> bool) (s : t) : t :=
    Build_set (S.filter_sort (sorted s) f).
  Definition for_all (f : elt -> bool) (s : t) : bool := S.for_all f s.
  Definition exists_ (f : elt -> bool) (s : t) : bool := S.exists_ f s.
  Definition partition (f : elt -> bool) (s : t) : t * t :=
    let p := S.partition f s in
    (Build_set (this:=fst p) (S.partition_sort_1 (sorted s) f),
     Build_set (this:=snd p) (S.partition_sort_2 (sorted s) f)).

  Definition cardinal (s : t) : nat := S.cardinal s.
  Definition elements (x : t) : list elt := S.elements x.

  Definition min_elt (s : t) : option elt := S.min_elt s.
  Definition max_elt (s : t) : option elt := S.max_elt s.
  Definition choose := min_elt.
End SetDefinitions.

Implicit Arguments empty [[A] [comparedec]].
Implicit Arguments is_empty [[A] [comparedec]].
Implicit Arguments mem [[A] [comparedec]].
Implicit Arguments add [[A] [comparedec]].
Implicit Arguments singleton [[A] [comparedec]].
Implicit Arguments remove [[A] [comparedec]].
Implicit Arguments union [[A] [comparedec]].
Implicit Arguments inter [[A] [comparedec]].
Implicit Arguments diff [[A] [comparedec]].
Implicit Arguments equal [[A] [comparedec]].
Implicit Arguments subset [[A] [comparedec]].
Implicit Arguments map_monotonic [[A] [comparedec] [B] [H] [Mono]].
Implicit Arguments fold [[A] [comparedec] [B]].
Implicit Arguments filter [[A] [comparedec]].
Implicit Arguments for_all [[A] [comparedec]].
Implicit Arguments exists_ [[A] [comparedec]].
Implicit Arguments partition [[A] [comparedec]].
Implicit Arguments cardinal [[A] [comparedec]].
Implicit Arguments elements [[A] [comparedec]].
Implicit Arguments min_elt [[A] [comparedec]].
Implicit Arguments max_elt [[A] [comparedec]].
Implicit Arguments choose [[A] [comparedec]].

Set Implicit Arguments.
Unset Strict Implicit.

Section Spec.
  Variable A : Type.
  Hypothesis (comparedec : OrderedType A).

  Let elt := A.
  Let t := (set elt).

  Variable s s' s'': t.
  Variable x y : elt.

  Definition In (x : elt) (s : t) : Prop := InA _eq x s.(this).
  Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
  Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
  Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop)(s:t) : Prop := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop)(s:t) : Prop := exists x, In x s /\ P x.

  Lemma In_1 : x === y -> In x s -> In y s.
  Proof. exact (fun H H' => S.In_eq H H'). Qed.

  Lemma mem_1 : In x s -> mem x s = true.
  Proof. exact (fun H => S.mem_1 s.(sorted) H). Qed.
  Lemma mem_2 : mem x s = true -> In x s.
  Proof. exact (fun H => S.mem_2 H). Qed.

  Lemma equal_1 : Equal s s' -> equal s s' = true.
  Proof. exact (S.equal_1 s.(sorted) s'.(sorted)). Qed.
  Lemma equal_2 : equal s s' = true -> Equal s s'.
  Proof. exact (fun H => S.equal_2 H). Qed.

  Lemma subset_1 : Subset s s' -> subset s s' = true.
  Proof. exact (S.subset_1 s.(sorted) s'.(sorted)). Qed.
  Lemma subset_2 : subset s s' = true -> Subset s s'.
  Proof. exact (fun H => S.subset_2 H). Qed.

  Lemma empty_1 : Empty empty.
  Proof. eapply S.empty_1. Qed.

  Lemma is_empty_1 : Empty s -> is_empty s = true.
  Proof. exact (fun H => S.is_empty_1 H). Qed.
  Lemma is_empty_2 : is_empty s = true -> Empty s.
  Proof. exact (fun H => S.is_empty_2 H). Qed.

  Lemma add_1 : x === y -> In y (add x s).
  Proof. exact (fun H => S.add_1 s.(sorted) H). Qed.
  Lemma add_2 : In y s -> In y (add x s).
  Proof. exact (fun H => S.add_2 s.(sorted) x H). Qed.
  Lemma add_3 : x =/= y -> In y (add x s) -> In y s.
  Proof. exact (fun H => S.add_3 s.(sorted) H). Qed.

  Lemma remove_1 : x === y -> ~ In y (remove x s).
  Proof. exact (fun H => S.remove_1 s.(sorted) H). Qed.
  Lemma remove_2 : x =/= y -> In y s -> In y (remove x s).
  Proof. exact (fun H H' => S.remove_2 s.(sorted) H H'). Qed.
  Lemma remove_3 : In y (remove x s) -> In y s.
  Proof. exact (fun H => S.remove_3 s.(sorted) H). Qed.

  Lemma singleton_1 : In y (singleton x) -> x === y.
  Proof. exact (fun H => S.singleton_1 H). Qed.
  Lemma singleton_2 : x === y -> In y (singleton x).
  Proof. exact (fun H => S.singleton_2 H). Qed.

  Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
  Proof. exact (fun H => S.union_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_2 : In x s -> In x (union s s').
  Proof. exact (fun H => S.union_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma union_3 : In x s' -> In x (union s s').
  Proof. exact (fun H => S.union_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma inter_1 : In x (inter s s') -> In x s.
  Proof. exact (fun H => S.inter_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_2 : In x (inter s s') -> In x s'.
  Proof. exact (fun H => S.inter_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
  Proof. exact (fun H => S.inter_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma diff_1 : In x (diff s s') -> In x s.
  Proof. exact (fun H => S.diff_1 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_2 : In x (diff s s') -> ~ In x s'.
  Proof. exact (fun H => S.diff_2 s.(sorted) s'.(sorted) H). Qed.
  Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
  Proof. exact (fun H => S.diff_3 s.(sorted) s'.(sorted) H). Qed.

  Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof. exact (S.fold_1 s.(sorted)). Qed.

  Lemma cardinal_1 : cardinal s = length (elements s).
  Proof. exact (S.cardinal_1 s.(sorted)). Qed.

  Section Filter.

    Variable f : elt -> bool.
    Lemma filter_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      In x (filter f s) -> In x s.
    Proof. intros; eapply S.filter_1 with (f := f); auto. Qed.
    Lemma filter_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      In x (filter f s) -> f x = true.
    Proof. intros; eapply S.filter_2 with (s := s); eauto. Qed.
    Lemma filter_3 `{Proper _ (_eq ==> (@eq bool)) f} :
      In x s -> f x = true -> In x (filter f s).
    Proof. apply S.filter_3; auto. Qed.

    Lemma for_all_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      For_all (fun x => f x = true) s -> for_all f s = true.
    Proof. apply S.for_all_1; auto. Qed.
    Lemma for_all_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      for_all f s = true -> For_all (fun x => f x = true) s.
    Proof. apply S.for_all_2; auto. Qed.

    Lemma exists_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      Exists (fun x => f x = true) s -> exists_ f s = true.
    Proof. apply S.exists_1; auto. Qed.
    Lemma exists_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      exists_ f s = true -> Exists (fun x => f x = true) s.
    Proof. apply S.exists_2; auto. Qed.

    Lemma partition_1 `{Proper _ (_eq ==> (@eq bool)) f} :
      Equal (fst (partition f s)) (filter f s).
    Proof. apply (@S.partition_1 _ _ s f); auto. Qed.
    Lemma partition_2 `{Proper _ (_eq ==> (@eq bool)) f} :
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
    Proof. apply (@S.partition_2 _ _ s f); auto. Qed.

  End Filter.

  Lemma elements_1 : In x s -> InA _eq x (elements s).
  Proof. exact (fun H => S.elements_1 H). Qed.
  Lemma elements_2 : InA _eq x (elements s) -> In x s.
  Proof. exact (fun H => S.elements_2 H). Qed.
  Lemma elements_3 : sort _lt (elements s).
  Proof. exact (S.elements_3 s.(sorted)). Qed.
  Lemma elements_3w : NoDupA _eq (elements s).
  Proof. exact (S.elements_3w s.(sorted)). Qed.

  Lemma min_elt_1 : min_elt s = Some x -> In x s.
  Proof. exact (fun H => S.min_elt_1 H). Qed.
  Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ y <<< x.
  Proof. exact (fun H => S.min_elt_2 s.(sorted) H). Qed.
  Lemma min_elt_3 : min_elt s = None -> Empty s.
  Proof. exact (fun H => S.min_elt_3 H). Qed.

  Lemma max_elt_1 : max_elt s = Some x -> In x s.
  Proof. exact (fun H => S.max_elt_1 H). Qed.
  Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ x <<< y.
  Proof. exact (fun H => S.max_elt_2 s.(sorted) H). Qed.
  Lemma max_elt_3 : max_elt s = None -> Empty s.
  Proof. exact (fun H => S.max_elt_3 H). Qed.

  Lemma choose_1 : choose s = Some x -> In x s.
  Proof. exact (fun H => S.choose_1 H). Qed.
  Lemma choose_2 : choose s = None -> Empty s.
  Proof. exact (fun H => S.choose_2 H). Qed.
  Lemma choose_3 : choose s = Some x -> choose s' = Some y ->
                   Equal s s' -> x === y.
  Proof. eapply S.choose_3; apply sorted. Qed.
End Spec.
Unset Implicit Arguments.

Require FsetInterface.
(** Sets seen as an OrderedType with equality the pointwise equality [Equal] *)
Definition Equal_Equivalence `{OrderedType A} : Equivalence (@Equal A _) :=
  SetInterface.Equal_pw_Equivalence (set A) A (@In _ H).

Lemma Equal_set_eq `{HA : OrderedType A} :
  forall s s', Equal s s' <-> S.set_eq s s'.
Proof.
  intros [s Hs] [s' Hs']; simpl.
  unfold Equal, In; simpl; unfold SetList.set_eq.
  revert s' Hs Hs'; induction s; destruct s'; intros Hs Hs'; split; intro H.
  constructor.
  intro; split; intro abs; inversion abs.
  assert (abs : InA _eq a nil). rewrite H; constructor; auto. inversion abs.
  inversion H.
  assert (abs : InA _eq a nil). rewrite <-H; constructor; auto. inversion abs.
  inversion H.

  inversion Hs; inversion Hs'; subst.
  rewrite Inf_alt in H3 by auto; rewrite Inf_alt in H7 by auto.
  assert (Heq : a === a0).
  assert (Ha : InA _eq a (a0 :: s')). rewrite <- H; constructor; auto.
  assert (Ha' : InA _eq a0 (a :: s)). rewrite H; constructor; auto.
  inversion Ha; inversion Ha'; subst; auto.
  apply False_rec; apply (lt_not_gt (x:=a) (y:=a0)); auto.
  constructor; auto; rewrite <- IHs; auto.
  intro z; split; intro Hz.
  assert (Rz : InA _eq z (a0::s')). rewrite <- H; constructor 2; auto.
  inversion Rz; subst; auto;
    contradiction (lt_not_eq (H3 z Hz)); transitivity a0; auto.
  assert (Rz : InA _eq z (a::s)). rewrite H; constructor 2; auto.
  inversion Rz; subst; auto;
    contradiction (lt_not_eq (H7 z Hz)); transitivity a; auto.

  inversion H; subst; inversion Hs; inversion Hs'; subst.
  rewrite Inf_alt in H4 by auto; rewrite Inf_alt in H9 by auto.
  rewrite <- IHs in H5 by auto.
  intro z; split; intro Hz; inversion Hz; subst.
  constructor; transitivity a; auto.
  constructor 2; rewrite <- H5; auto.
  constructor; transitivity a0; auto.
  constructor 2; rewrite H5; auto.
Qed.

Definition set_lt `{OrderedType A} : relation (set A) := S.set_lt.
Program Definition set_StrictOrder `{OrderedType A} :
  @StrictOrder _ set_lt (@Equal A _) Equal_Equivalence :=
  Build_StrictOrder _ _ _ _ _ _.
Next Obligation.
  intros x y z H1 H2. unfold set_lt, S.set_lt in *.
  now transitivity y.
Qed.
Next Obligation.
  change (~Equal x y); rewrite Equal_set_eq.
  apply lt_not_eq; auto.
Qed.

Definition set_compare `{OrderedType A} : set A -> set A -> comparison :=
  S.set_compare.

Program Instance set_OrderedType `{OrderedType A} :
  SpecificOrderedType (set A) (@Equal A _) := {
                                               SOT_Equivalence := Equal_Equivalence;
                                               SOT_lt := set_lt;
                                               SOT_StrictOrder := set_StrictOrder;
                                               SOT_cmp := set_compare
                                             }.
Next Obligation.
  change (compare_spec (@Equal _ _) set_lt x y ((this x) =?= (this y))).
  destruct (compare_dec (this x) (this y)); constructor; auto.
  rewrite Equal_set_eq; auto.
Qed.
