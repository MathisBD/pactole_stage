(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   P. Courtieu, L. Rieg, X. Urbain                                      *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Ltac harvest_hyps harvester := constr:(ltac:(harvester; constructor) : True).

Ltac revert_clearbody_all := 
  repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.

Ltac all_hyps := harvest_hyps revert_clearbody_all.

Ltac next_hyp hs step last := 
  lazymatch hs with 
  | (?hs' ?H) => step H hs'
  | _ => last
  end.

Ltac map_hyps tac hs :=
  idtac;
  let rec step H hs := tac H; next_hyp hs step idtac in
  next_hyp hs step idtac.

Ltac revert_new_hyps tac :=
  let old_hyps := all_hyps in
  let revert_if_not_old H :=
      lazymatch old_hyps with 
      | context[H] => idtac
      | _ => revert dependent H
      end in
  tac;
  let new_hyps := all_hyps in
  map_hyps revert_if_not_old new_hyps.


(* Demo *)
Goal forall (a b c:nat), True.
intros a b c.
do 3 pose proof true as ?b; move b0 at top.
Undo.
revert_new_hyps ltac:(do 3 pose proof true as ?b; move b0 at top).
intros.
Abort.


Ltac reduce_eq H :=
  intro H;
  match type of H with ?x = ?y => (is_var x; subst x) || (is_var y; subst y) || rewrite x in *; try clear x end.

