Require Import List.

Fixpoint first_success {A B : Type}(f : A -> option B)(l:list A) : option B :=
match l with nil => None
           | a::l' => match f a with Some b => Some b
                                   | None => first_success f l'
                      end
end.

Example f (n:nat) : option nat :=
match n with 0 => Some 22 | 1 => Some 42 | _ => None end.

Compute first_success f (4::4::1::2::7::nil).

Fixpoint take_n {A}(l:list A)(n:nat) : option (list A) :=
match l, n with
 _, 0 => Some nil
|nil, S _ => None
|a::l' , S p => match take_n l' p with Some r => Some (a::r) | _=> None end
end.

Fixpoint first_success_n {A B : Type}(f : list A -> option B)(l:list A) (n:nat)
: option  B  :=
match l, n with l,0 => f nil
              | nil, S _ => None
              | a::l' , S p => first_success_n (fun r => 
                                               match f (a::r) with Some s => Some s | 
                                                              None => first_success_n
                                                                   f l' (S p) end) l' p
end.

Compute first_success_n (fun l => match l with 2::0::_ => Some l | _=> None end)  (1::4::4::1::2::0::7::nil) 2.

