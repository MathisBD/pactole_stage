Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Exploration.Definitions.

Set Implicit Arguments.

Parameter n : nat.

(** The setting is an arbitrary metric space over R. *)
Declare Module Loc : DiscreteSpace.


(** There are nG good robots and no byzantine ones. *)
Parameter kG : nat.

Module K : Size with Definition nG := kG with Definition nB := 0%nat.
  Definition nG := kG.
  Definition nB := 0%nat.
End K.

(** We instantiate in our setting the generic definitions of the exploration problem. *)
Module DefsE := Definitions.ExplorationDefs(Loc)(K).
Export DefsE.

Section ExplorationKDivedesN.
Open Scope Z_scope.


Fixpoint create_confs (names: list Names.Internals.ident) (lloc : list Loc.t) id :=
  match names,lloc with
    | (h1::c1),(h2::c2) => if Names.eq_dec h1 id then h2 else create_confs c1 c2 id
    | _,_ => Loc.origin
  end.

Instance create_confs_compat : Proper (eq ==> eq ==> eq ==> Loc.eq ) create_confs.
Proof.
intros n1 n2 Hnames l1 l2 Hlistloc id1 id2 Hid.
now f_equiv.
Qed.

Fixpoint create_lnat (n:nat) : list nat := 
  match n with
  | O => nil
  | S k => k::(create_lnat k)
  end.

Instance create_lnat_compat : Proper (eq ==> eq) create_lnat.
Proof. intros x y Hxy. rewrite Hxy. reflexivity. Qed.

Definition list_loc1 := 
  let lnat := create_lnat kG in
  let f := (fun n => Loc.mul ((Z_of_nat (n*(kG / n)))) Loc.unit) in
  List.map f lnat.
  
Definition list_loc2 := 
  let lnat := create_lnat kG in
  let f := (fun n => Loc.add Loc.unit (Loc.mul ((Z_of_nat (n*(kG / n)))) Loc.unit)) in
  List.map f lnat.


Definition conf1 : Config.t := fun id => 
  let place := create_confs Names.names list_loc1 id in
     {| Config.loc := place;
      Config.robot_info := {| Config.source := place; Config.target := place |} |}.


Definition conf2 : Config.t := fun id => 
  let place := create_confs Names.names list_loc2 id in
     {| Config.loc := place;
      Config.robot_info := {| Config.source := place; Config.target := place |} |}.

Theorem conf1_conf2_spect_eq : Spect.eq (!! conf1) (!! conf2).
Proof.
intro pt. unfold conf1, conf2.
do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
(* f_equiv. f_equiv. f_equiv. unfold create_confs.
f_equiv. rewrite names_Gnames. *) do 2 rewrite map_map.
unfold create_confs.
(* unfold left_dec, left. generalize (Names.Gnames_NoDup).
 *)apply (@first_last_even_ind _
(fun l => NoDup l ->
     countA_occ _ Loc.eq_dec pt (map (fun x => 
    Spect.Config.loc
        {|
        Config.loc := create_confs Names.names list_loc1 x;
        Config.robot_info := {|
                             Config.source := create_confs Names.names list_loc1 x;
                             Config.target := create_confs Names.names list_loc1 x |} |})
                             Spect.Names.names) =
     countA_occ _ Loc.eq_dec pt (map (fun x =>
     Spect.Config.loc
        {|
        Config.loc := create_confs Names.names list_loc2 x;
        Config.robot_info := {|
                             Config.source := create_confs Names.names list_loc2 x;
                             Config.target := create_confs Names.names list_loc2 x |} |}) 
                             Spect.Names.names))).
* reflexivity.
* intros gl gr l Heven Hrec Hnodup.
  (* Inversing the NoDup property *)
  inversion_clear Hnodup as [| ? ? Helt Hnodup'].
  assert (Hneq : gl <> gr). { intro Habs. subst. intuition. }
  assert (Hgl : ~In gl l) by intuition.
  rewrite <- NoDupA_Leibniz, PermutationA_app_comm, NoDupA_Leibniz in Hnodup'; refine _.
  simpl in Hnodup'. inversion_clear Hnodup' as [| ? ? Hgr Hnodup]. specialize (Hrec Hnodup). clear Helt.
  (* Rewriting in the goal *)
  do 2 rewrite map_app. simpl. repeat rewrite countA_occ_app. simpl. rewrite half1_cons2.
  destruct (in_dec Fin.eq_dec gl (gl :: half1 l)) as [_ | Habs].
  destruct (in_dec Fin.eq_dec gr (gl :: half1 l)) as [Habs | _].
  + (* absurd case : gr ∈ gl :: half1 l *)
    exfalso. destruct Habs.
    - contradiction.
    - apply Hgr. now apply half1_incl.
  + (* valid case *)
    assert (Heq : forall a b : Loc.t,
                  map (fun g => if in_dec Fin.eq_dec g (gl :: half1 l) then a else b) l
                = map (fun g => if in_dec Fin.eq_dec g (half1 l) then a else b) l).
    { intros a b. apply map_ext_in. intros g Hg.
      destruct (in_dec Fin.eq_dec g (gl :: half1 l)) as [Hin | Hout].
      - destruct Hin; try now subst; contradiction.
        destruct (in_dec Fin.eq_dec g (half1 l)); reflexivity || contradiction.
      - destruct (in_dec Fin.eq_dec g (half1 l)); trivial. elim Hout. intuition. }
    do 2 rewrite Heq.
    Ldec_full; subst; Ldec; try Ldec_full; subst; Ldec; setoid_rewrite plus_comm; simpl; auto.
  + (* absurd case : gr ∉ gl :: half1 l *)
    elim Habs. intuition.
* change (Fin.t N.nG) with Spect.Names.Internals.G. rewrite Spect.Names.Gnames_length. apply even_nG.
Qed.

(* final theorem: In the asynchronous model, if k divide n, 
   then the exploration of a n-node ring is not possible. *)

Theorem no_exploration : kG mod n = 0 -> ~(forall r d, 
ValidSolExplorationStop r d).
Proof.

Save.
