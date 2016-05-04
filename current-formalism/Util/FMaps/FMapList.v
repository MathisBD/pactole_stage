(* Partly taken from Containers library and the StdLib FMapWeakList.v *)

Require Import List.
Require Import SetoidDec.
Require Import Pactole.Util.FMaps.FMapInterface.


Set Implicit Arguments.


Section ListFacts.
Variable key : Type.
Context `{EqDec key}.
Variable elt : Type.

Notation t := (fun T => list (key * T)).

Fixpoint list_mem (k : key) (s : t elt) {struct s} : bool :=
  match s with
   | nil => false
   | (k',_) :: l => if equiv_dec k k' then true else list_mem k l
  end.

Fixpoint list_add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => (k,x) :: nil
   | (k',y) :: l => if equiv_dec k k' then (k, x) :: l else (k', y) :: list_add k x l
  end.

Fixpoint list_find (k:key) (s: t elt) {struct s} : option elt :=
  match s with
   | nil => None
   | (k',x)::s' => if equiv_dec k k' then Some x else list_find k s'
  end.

Fixpoint list_remove (k : key) (s : t elt) {struct s} : t elt :=
  match s with
   | nil => nil
   | (k',x) :: l => if equiv_dec k k' then l else (k',x) :: list_remove k l
  end.

Fixpoint list_fold (A:Type)(f:key->elt->A->A)(m:t elt) (acc : A) {struct m} : A :=
  match m with
   | nil => acc
   | (k,e)::m' => list_fold f m' (f k e acc)
  end.

Definition list_check (cmp : elt -> elt -> bool)(k:key)(e:elt)(m': t elt) :=
  match list_find k m' with
   | None => false
   | Some e' => cmp e e'
  end.

Definition list_submap (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  list_fold (fun k e b => andb (list_check cmp k e m') b) m true.

Definition list_equal (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
  andb (list_submap cmp m m') (list_submap (fun e' e => cmp e e') m' m).

Fixpoint list_map {elt'} (f:elt -> elt') (m:t elt) : t elt' :=
  match m with
   | nil => nil
   | (k,e)::m' => (k,f e) :: list_map f m'
  end.

Fixpoint list_mapi {elt'} (f: key -> elt -> elt') (m:t elt) : t elt' :=
  match m with
   | nil => nil
   | (k,e)::m' => (k,f k e) :: list_mapi f m'
  end.

End ListFacts.


Instance MapList key `{EqDec key} : FMap := {|
  dict := fun elt => list (key * elt);
  MapsTo := fun elt k e m => List.In (k, e) m;
  empty := fun elt => nil;
  is_empty := fun elt m => match m with nil => true | cons _ _ => false end;
  mem := fun elt k m => list_mem k m;
  add := fun elt => @list_add _ _ _ elt;
  find := fun elt => @list_find _ _ _ elt;
  remove := fun elt => @list_remove _ _ _ elt;
  equal := fun elt => @list_equal _ _ _ elt;
  map := fun elt => @list_map _ elt;
  mapi := fun elt => @list_mapi _ elt;
  fold := fun elt => @list_fold _ elt;
  cardinal := fun elt => @length _;
  elements := fun elt l => l |}.
