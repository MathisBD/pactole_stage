(** Labels (from Loco 2.1) *)
Require Import Bool Setoid.
(** Eqtypes with a default value *)

Class Label (l:Type):={
 def : l;
 eqb : l -> l -> bool ;
 eqb_refl : forall x y:l, eqb x y = true <-> x = y}.


Definition label_eq_dec  l (L: Label l) : forall x y:l, {x=y}+{x<>y}.
intros x y;case_eq (eqb x y).
intro H.
rewrite eqb_refl in H;now left.
intro H;right;intro H0.
rewrite <-eqb_refl in H0.
rewrite H0 in H;discriminate.
Defined.


(** examples of Label types *)
Require Import ZArith.
Instance Lbool : Label bool.
exists Bool.eqb.
exact false.
intros x y; rewrite Bool.eqb_true_iff;tauto.
Defined.

Notation  nolabel := (unit) (only parsing).
Instance Lunit : Label nolabel.
exists (fun x y => true).
exact tt.
destruct x;destruct y;tauto.
Defined.

Instance Lz : Label Z.
exists Z.eqb.
exact 0%Z.
intros x y.
case(Z.eqb_spec x y).
tauto.
split.
discriminate.
intro;destruct n;auto. 
Qed.

Instance LN : Label N.
exists N.eqb.
exact 0%N.
intros x y.
case(N.eqb_spec x y).
tauto.
split.
discriminate.
intro;destruct n;auto. 
Defined.


Instance Lnat : Label nat.
exists beq_nat.
exact 0%nat.
intros x y;rewrite beq_nat_true_iff;tauto.
Defined.

Instance Lprod {A B : Type}(LA: Label A)(LB:Label B) : Label (A * B).
Proof.
exists (fun (p q : A * B) => match p, q with (a,b),(c,d) => 
                                 (eqb a c) && (eqb b d)
                             end).
exact (def,def).
destruct x , y; rewrite andb_true_iff; repeat rewrite eqb_refl; intuition .
subst a b;auto.
injection H;auto.
injection H;auto.
Defined.

Instance Lsum {A B : Type}(LA: Label A)(LB:Label B) : Label (A + B).
Proof.
exists (fun (p q : A + B) => match p, q with 
        | inl a, inl a0 => eqb a a0
        | inr b, inr b0 => eqb b  b0
        | _, _ => false
        end).

exact (inl def).

destruct x , y; simpl; repeat rewrite eqb_refl; intuition ; try ((subst a || subst b);auto);try discriminate.
injection H;auto.
injection H;auto.
Defined.

Instance Lopt {A : Type}(LA : Label A) : Label (option A).
Proof.
exists (fun (oA oA':option A)  => match oA, oA' with
                                      Some a, Some a' => eqb a a' 
                                    | None, None => true
                                    | _, _ => false
                                   end).
exact None.
destruct x , y; simpl; repeat rewrite eqb_refl; intuition ; try (reflexivity || discriminate).  
subst a;auto.
injection H;auto.
Defined.


