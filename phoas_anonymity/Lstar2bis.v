(** From Loco2.1 *)
Require Import Bool.
Require Import Setoid.
Require Import ZArith.
Require Import List.
Require Import Labels.
Require  Import first_success.


(** Type class for ports (anonymous neigbours) (just Eqtype) *)

Class Ports ( V:Type):={
 port_eq_dec : forall v w:V ,{v = w}+{v <> w}
}.

Definition port_eqb {V}{P: Ports V} (v w:V):=
if port_eq_dec    v w then true else false.


Definition port_diff {V}{P: Ports V} (v w:V):=
if port_eq_dec    v w then false else true. 

(** elementary relabelling for an lc2 algorithm *)

Inductive lc2_assignment (A B V:Type) : Type :=
 (** sets the center's label *)
| lc2_set_c: A -> lc2_assignment A B V
(** sets the neighbour v's label *)
| lc2_set_v : V -> A -> lc2_assignment A B V 
(** sets the edge c-v's label *)
| lc2_set_cv : V -> B -> lc2_assignment A B V .

Definition lc2_relabelling (A B V:Type):=
  list (lc2_assignment A B V).

Inductive lc1_assignment (A B V:Type) : Type :=
| lc1_set_c: A -> lc1_assignment A B V
| lc1_set_cv : V -> B -> lc1_assignment A B V .

Definition lc1_relabelling (A B V:Type):=
  list (lc1_assignment A B V).

Arguments lc2_set_v {A B V } _ _.
Arguments lc2_set_c {A B V} _.
Arguments lc2_set_cv {A B V } _ _.
Arguments lc1_set_c {A B V} _.
Arguments lc1_set_cv {A B V } _ _.

(** a chooser receives a list of ports, selects some neigbours and results in an 
   answer *)

Inductive chooser {A B :Type} {LA : Label A}{LB: Label B} {V} {P:Ports V}{Ans : Type}: Type :=
  (* chooses some member of l and calls kc *)
| choose (l:list V) (kc : V ->  chooser )

  (* chooses n members of l and calls kc ; fails if l is too short *)
| choose_n (n:nat) (l:list V)(kp:  list V -> chooser )

  (* fails if b is false *)
| assert  (b : bool)(k:   chooser )  

  (* calls kn with the current list of neigbours *)
| Kneigb (kn : list V -> chooser)

  (* calls kc with the current center's label *)
| Kget_c (kc : A -> chooser)

  (* calls kv with the current  label of v *)
| Kget_v (v:V)(kc : A -> chooser)

  (* calls kcv with the current  label of the edge c-v *)
| Kget_cv (v:V)(kcv : B -> chooser)

  (* calls kf with the sublist of l of elements whose labels satisfy p *)
| Kfilter (l:list V)(p :  B -> A -> bool)(kf : list V -> chooser)

 (** calls kl with the list of labels associated with l *)
| Klabels  (l:list V)(Kl : list (B * A) -> chooser)

| returns (result:  Ans)

| fails.

Notation "'choose!' x 'in'  e1 ; e2 " := (choose e1 (fun x => e2))
                               (right associativity, at level 60).
Notation "'choose_n!' x 'in'  e1 ; e2 " := (choose_n e1 (fun x => e2))
                               (right associativity, at level 60).
Notation "'assert!' b ; e" := (assert b e)
                           (right associativity, at level 60).


Notation "x '<-get_c' ; e" := (Kget_c (fun x => e))
(right associativity, at level 60).

Notation "x '<-get_v' v ; e" := (Kget_v v (fun x => e))
(right associativity, at level 60).

Notation "x '<-get_cv' v ; e" := (Kget_cv v (fun x => e))
(right associativity, at level 60).
About Kfilter.

Notation "X '<-select' p 'in' l  ';' e" := (Kfilter l p (fun X => e))
(right associativity, at level 60).

Notation "X '<-labels' l ; e" := (Klabels l (fun X => e))
(right associativity, at level 60).


Notation "X '<-Neigb' ; e" := (Kneigb (fun X => e))
(right associativity, at level 60).





(** an lc1 rule is just a function that receives a list l of neigbours, and
    computes a local relabelling 
    The quantification on V and P ensures the anonimity of neigbours *)


Definition lc1_simple_rule_t (A B :Type) {LA : Label A}{LB: Label B}:=
  forall V (P:Ports V),
    chooser (A:=A)(B:=B)(LA:=LA)(LB:=LB)(V:=V)(P:=P) (Ans:=lc1_relabelling A B V).

Definition lc2_simple_rule_t (A B :Type) {LA : Label A}{LB: Label B}:=
  forall V (P:Ports V),
    chooser (A:=A)(B:=B)(LA:=LA)(LB:=LB)(V:=V)(P:=P) (Ans:=lc2_relabelling A B V).





(** Type class for labelled stars :
   allows to get : 
    - the list of active neighbours
    - the current label of the center
    - the current labzl of any neighbour
    - the current label of any edge *)

Class LStar {A B : Type}(LA: Label A) (LB: Label B) {V} (P : Ports V)
    (lstar_t : Type):={
   the_neighbours : lstar_t -> list V;
   get_c : lstar_t -> A;
   get_v : lstar_t -> V -> A;
   get_cv : lstar_t -> V -> B}.



About choose.
About the_neighbours.
About get_v.


Section Interpretation.
Variables A B : Type.
Context (LA : Label A)(LB : Label B).
Variable V: Type.
Context (P : Ports V).
Variable X : Type.
Context (LS: LStar LA LB P X).
Variable Ans : Type.

Fixpoint chooser_interpret
 ( c : @chooser A B LA LB V P Ans)
    (st : X) : option Ans
:=
  match c with
    | choose l kc     => first_success
      (fun v => chooser_interpret  (kc v) st) l
    | choose_n n l kp => first_success_n 
      (fun l' => chooser_interpret   (kp l') st) l n
    | assert b k      => if b then (chooser_interpret  k st )else None
   | Kneigb kn       => chooser_interpret 
             (kn (the_neighbours  (A:=A) (B:=B) (V:=V) st)) st
 | Kget_c kc       => chooser_interpret 
             (kc (get_c (A:=A) (B:=B) (V:=V) (LStar := LS) st) ) st 
    | Kget_v v kv     => chooser_interpret 
             (kv
               (get_v (A:=A) (B:=B) (V:=V) (LStar := LS) st v) ) st 
    | Kget_cv v kcv     => chooser_interpret 
             (kcv
               (get_cv (A:=A) (B:=B) (V:=V) (LStar := LS) st v) ) st 

    | Kfilter l p kp => 
         let l' :=  (List.filter 
                              (fun (v:V) => p (@get_cv A B LA LB V P X LS st v)
                                              (@get_v A B LA LB V P X LS st v))
                              l)
         in chooser_interpret (kp l') st 
    | Klabels l kl =>
         let l' := List.map (fun (v:V) => (@get_cv A B LA LB V P X LS st v, 
                                              @get_v A B LA LB V P X LS st v)) l
         in chooser_interpret (kl l') st
  | returns a => Some a
  
  | _ => None
end.


End Interpretation.



Print lc2_simple_rule_t.

(** interpreter for lc2 rules *)
About chooser_interpret.
Arguments chooser_interpret A B {LA LB} V {P} X LS  {Ans} c st .

Definition  lc2_interpret
     (A B :Type) {LA : Label A}{LB: Label B}
     (V:Type){P: Ports V} X (LS: LStar LA LB  P X)( r : lc2_simple_rule_t A B)
    (st : X) : option (lc2_relabelling A B V) :=
 chooser_interpret A B V  X LS    (r V P) st.


(** an instance of Ports *)
(** An implementation of Ports built on Z *)

Definition Z_eq_dec (z z':Z) : {z=z'}+{z <> z'}.
Proof.  
  case_eq (Z.eqb z z').
  intro;left.
 destruct (BinInt.Z.eqb_spec z z');auto. 
  discriminate.
 right;intro H0.
 destruct (BinInt.Z.eqb_spec z z');auto.
 discriminate.
Defined.


Instance Ports_Z :  Ports Z.
split; exact Z_eq_dec.
Defined.

Arguments lc2_set_v {A B V} _ _.

(** example 1 :
   choose some neigbour i and copy its label to the center c *)
Example r00 : lc2_simple_rule_t nat bool :=
  fun V (P:Ports V)   =>  
     Nbs <-Neigb ;
     choose! i in   Nbs;
     x <-get_v i ;
     returns  (lc2_set_c x::nil).



Require Import Max.
(* choose two different neigbours i and j, then set i's label 
   to the max of i's and c's labels and j's label to i's label *)
  

Example r01 : lc2_simple_rule_t nat bool :=
 fun V (P:Ports V)   =>   
  Nbs <-Neigb;
  choose! i in Nbs ;
  choose! j in Nbs ;
  assert!  (port_diff i j);
  x <-get_v i ; y <-get_c ;
  returns (lc2_set_v i (max  x y) :: lc2_set_v j x ::  nil).
 

(** sets the center's label to its degree *)

Example r03 : lc2_simple_rule_t nat bool :=
fun V (P:Ports V)   =>  
 Nbs <-Neigb ;
 returns (lc2_set_c (List.length Nbs)::nil).


(** for any neigbour whose label is >= 7, set this label to 7 (exactly) *)
Example r04 : lc2_simple_rule_t nat bool :=
fun V (P:Ports V) =>  
Nbs <-Neigb ;
active <-select (fun x y => leb 7 y) in Nbs;
returns (fold_right (fun i r => lc2_set_v i  7 :: r)
                          nil active).



(** if there are exactly two neigbours i and j whose labels are >= 7
    with true labelled edges,
    set i's label to 42, and j's label to 43 
    if there is exactly one such  neigbour i 
    set its label to 41
    *)

Example r05 : lc2_simple_rule_t nat bool :=
fun V (P:Ports V) =>  
Nbs <-Neigb;
l <-select (fun x y => x && leb 7 y) in Nbs;
match l with 
| i::j::nil =>
          returns (lc2_set_v i 42:: lc2_set_v j 43 :: nil)
| i :: nil => returns (lc2_set_c 41 :: nil)
|  _ => fails
end.



(** How to build cheap LStar implementations *)

Definition a_list (A V : Type) := list (V * A).

Fixpoint a_list_get (A V: Type)(LA: Label A)(V_eq_dec : forall v w: V, {v=w}+{v<>w})
                (the_star : a_list A V) (v : V) : A :=
match the_star with
| nil => def
| (w,a)::the_star' => if V_eq_dec v w then  a else a_list_get A V LA V_eq_dec the_star' v 
end.


Definition a_list_star A B V := (A * a_list (B * A) V)%type.

Definition a_list_star_get_c A B {LA : Label A}{LB : Label B} V {P:Ports V}
 (the_star : a_list_star A B V) : A := fst the_star.

Definition a_list_star_get_v A B {LA : Label A}{LB : Label B} V {P:Ports V}
 (the_star : a_list_star A B V) v : A := snd (a_list_get  (B * A) V _ port_eq_dec (snd the_star) v).
Definition a_list_star_get_cv A B {LA : Label A}{LB : Label B} V {P:Ports V}
 (the_star : a_list_star A B V) v : B := fst (a_list_get  (B * A) V _ port_eq_dec (snd the_star) v).
 

Instance A_List A B (LA: Label A) (LB:Label B) V (P : Ports V) : 
 LStar LA LB P (a_list_star A B V) :=
 Build_LStar A B  LA LB V P  (a_list_star A B V)
   (fun the_star => map (@fst V (B*A)) (snd the_star))
   (a_list_star_get_c A B  V   )
   (a_list_star_get_v A B V   )
   (a_list_star_get_cv A B V   ).


Print a_list_star.

Example st0 : a_list_star nat bool Z :=
  (33, (10%Z,(true,6))::
      (4%Z,(true,8))::
      (89%Z,(true,67))::nil).

About lc2_interpret.

Compute lc2_interpret nat bool Z _ _ r04 st0.

Compute lc2_interpret nat bool Z _ _ r03 st0.

Compute lc2_interpret nat bool Z _ _ r01 st0.


Compute lc2_interpret nat bool Z _ _ r05 st0.


Example st1 : a_list_star nat bool Z :=
  (33, (10%Z,(true,6))::
      (4%Z,(false,8))::
      (89%Z,(true,67))::nil).


Compute lc2_interpret nat bool Z _ _ r05 st1.










