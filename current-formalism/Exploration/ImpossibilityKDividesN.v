Require Import Psatz.
Require Import Morphisms.
Require Import Arith.Div2.
Require Import Omega.
Require Import List SetoidList.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.Exploration.Definitions.
Require Import Pactole.Exploration.test_modulo.

Set Implicit Arguments.
(* taille de l'anneau*)
Parameter n : nat.

Print Fin.t.
(** The setting is a ring. *)
Module Loc := ring.


(** There are KG good robots and no byzantine ones. *)
Parameter kG : nat.
Axiom kdn : kG mod n = 0.

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

(* Fin.t k c'est l'ensemble de 1 à k.*)
Definition Fint_to_nat (k:nat) (f:Fin.t k): nat :=
  match f with
  | @Fin.F1 _ => 1%nat
  | @Fin.FS n' f' => 1 + n'
  end.

Fixpoint create_conf1 (k:nat) (f:Fin.t k) : Loc.t :=
  Loc.mul (((Z_of_nat ((Fint_to_nat f)*(kG / n))))) Loc.unit.

Definition config1 : Config.t :=
  fun id => match id with
              | Good g => let pos := create_conf1 g in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := pos |} |}
              | Byz b => let pos := Loc.origin in
                          {| Config.loc := pos;
                             Config.robot_info := {| Config.source := pos; Config.target := pos |} |}
            end.

Definition loc_add k rconfig :=
  let new_pos := Loc.add k (Config.loc rconfig) in
  {| Config.loc := new_pos;
     Config.robot_info := {| Config.source := new_pos; Config.target := new_pos |} |}.

Definition config2 := Config.map (loc_add Loc.unit) config1.
(*
Fixpoint create_conf2 (k:nat) (f:Fin.t k) : Loc.t :=
 Loc.add Loc.unit (Loc.mul (((Z_of_nat ((Fint_to_nat f)*(kG / n))))) Loc.unit).

(* Instance create_confs_compat : Proper (Logic.eq ==> Loc.eq ==> eq ==> Loc.eq ) create_confs.
Proof.
intros n1 n2 Hnames l1 l2 Hlistloc id1 id2 Hid.
now f_equiv.
Qed.
 *)
Fixpoint create_lnat (n:nat) : list nat := 
  match n with
  | O => nil
  | S k => k::(create_lnat k)
  end.

(* Instance create_lnat_compat : Proper (eq ==> eq) create_lnat.
Proof. intros x y Hxy. rewrite Hxy. reflexivity. Qed.
 *)
Definition list_loc1 := 
  let lnat := create_lnat kG in
  let f := (fun id => Loc.mul ((Z_of_nat (id*(kG / n)))) Loc.unit) in
  List.map f lnat.
  
Definition list_loc2 := 
  let lnat := create_lnat kG in
  let f := (fun id => Loc.add Loc.unit (Loc.mul ((Z_of_nat (id*(kG / n)))) Loc.unit)) in
  List.map f lnat.

Lemma same_length : List.length list_loc1 = List.length list_loc2.
Proof.
unfold list_loc1, list_loc2. do 2 rewrite map_length. reflexivity.
Qed.

Lemma lloc1_NoDup : NoDup list_loc1.
Proof.
unfold list_loc1. apply FinFun.Injective_map_NoDup.
+ intros x y. intros Hloc. 
assert (Heq : Loc.mul (Z.of_nat (x * (kG / n))) Loc.unit = Loc.mul (Z.of_nat (y * (kG / n))) Loc.unit
-> (Z.of_nat (x * (kG / n))) = (Z.of_nat (y * (kG / n)))). assert (Hmul := Loc.mul_compat _ (reflexivity Loc.unit)) .

Qed.

Definition conf1 : Config.t := fun id => 
  let place := create_confs Names.names list_loc1 id in
     {| Config.loc := place;
      Config.robot_info := {| Config.source := place; Config.target := place |} |}.


Definition conf2 : Config.t := fun id => 
  let place := create_confs Names.names list_loc2 id in
     {| Config.loc := place;
      Config.robot_info := {| Config.source := place; Config.target := place |} |}.
*)

Lemma translate_eq : forall id v config, let config' := (Config.map (loc_add v) config) in
                     Config.eq (Config.map (loc_add (Loc.opp (Config.loc (config id)))) config)
                               (Config.map (loc_add (Loc.opp (Config.loc (config' id)))) config').

Theorem config1_config2_spect_eq : Spect.eq (!! config1) (!! config2).
Proof.
intro pt. 
do 2 rewrite Spect.from_config_spec, Spect.Config.list_spec.
(* f_equiv. f_equiv. f_equiv. unfold create_confs.
f_equiv. rewrite names_Gnames. *) do 2 rewrite map_map. simpl. unfold Spect.Config.loc.
generalize (Names.names_NoDup). unfold list_loc1, list_loc2. 
(* unfold left_dec, left. generalize (Names.Gnames_NoDup).
 *)apply (@first_last_ind _
(fun l => NoDup l ->
    countA_occ Loc.eq Loc.eq_dec pt
  (map
     (fun x : Spect.Names.ident =>
      create_confs l
        (map (fun id : nat => Loc.mul (Z.of_nat (id * (kG / n))) Loc.unit) (create_lnat kG)) x)
     l) =
countA_occ Loc.eq Loc.eq_dec pt
  (map
     (fun x : Spect.Names.ident =>
      create_confs l
        (map (fun id : nat => Loc.add Loc.unit (Loc.mul (Z.of_nat (id * (kG / n))) Loc.unit))
           (create_lnat kG)) x) l))).
* reflexivity.
* intros x HNoDup. 
  inversion_clear HNoDup as [| ? ? Helt Hnodup'].
  rewrite <- NoDupA_Leibniz, NoDupA_Leibniz in Hnodup'; refine _.
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
