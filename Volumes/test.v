Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Bool.
Require Import Arith.Div2.
Require Import Omega Field.
Require Import Rbase Rbasic_fun R_sqrt Rtrigo_def.
Require Import List.
Require Import SetoidList.
Require Import Relations.
Require Import RelationPairs.
Require Import Morphisms.
Require Import Psatz.
Require Import Inverse_Image.
Require Import Pactole.Spaces.R2.
Require Import Pactole.Core.Robots.
Require Import Pactole.Core.RobotInfo.
Require Import Pactole.Models.Rigid.
Import Permutation.
Import Pactole.Spaces.Similarity.
Import Datatypes. (* to recover [id] *)
Set Implicit Arguments.
Close Scope R_scope.
Close Scope VectorSpace_scope.
Require Import Rbase.
Require Import SetoidList.
Require Import SetoidDec.
Require Import Decidable.
Require Import Pactole.Util.Preliminary.
Require Pactole.Util.Bijection.
Require Import Pactole.Setting.
Require Import Pactole.Util.MMultiset.MMultisetInterface.
Require Import Pactole.Spectra.SetSpectrum.
Require Import Pactole.Spectra.PointedSpectrum.
Set Implicit Arguments.

(* on  veut créer l'algo sur les robots volumiques pour qu'il y ait toujours un chemin entre la base et 1 *)

Parameter n: nat.

(* il y a n "bon" robots et 0 byzantins*)
Instance Robots : Names := Robots n 0.

Definition identifiants := nat.
Definition indentifiants_setoid := eq_setoid nat.

Parameter ident_max : identifiants.

Axiom idnet_max_not_1 : ident_max > 1. 

(*variable pour savoir si les robots sont allumé ou pas: Si la variable de type [light] est à vrai, il est allumé*)
Definition light := bool.
Definition alive := bool.

Parameter D: R.

(* mettre D en variable globale, et faire en sorte que le spectre ne puisse aps changer els distance, ne puisse faire que rotation/translation *)

(*
Definition RILA :Type :=  (R2*identifiants*light*alive)%type.


Axiom ident_not_1 : forall rila : RILA,
    match rila with
      | (pos, ident, light, alive) => 
        ident > 1 /\ ident < ident_max
    end.

*)
Instance Loc : Location := make_Location (R2).
Instance VS : RealVectorSpace location := R2_VS.
Instance ES : EuclideanSpace location := R2_ES.
Remove Hints R2_VS R2_ES : typeclass_instances.
(* le rayon de volume des robots *)
Parameter R_r : R.
(* la distance max parcourue entre 2 activation*)
Parameter Dmax : R.
Definition Dp(*oursuite*) := (Dmax - D)%R.

Definition ILA :Type := identifiants*light*alive. 

Instance ILA_Setoid : Setoid ILA :=
  {
    equiv := fun ila1 ila2 =>
               match ila1, ila2 with
                 |(i1, l1, a1), (i2, l2, a2) =>
                  i1 == i2 /\ l1 == l2 /\ a1 == a2
               end}.
Proof.
  split; intro x; intuition;
    destruct x as ((i1, l1), a1). 
  - intuition.
  - destruct y as ((i2, l2), a2); intuition.
  - destruct y as ((i2, l2), a2), z as ((i3, l3), a3);
      intuition; unfold equiv in *; cbn -[equiv] in *.
    now transitivity i2.
    now transitivity l2.
    now transitivity a2.
Defined.

Instance ILA_EqDec : EqDec ILA_Setoid.
Proof.
  intros x y.
  unfold equiv; cbn -[equiv].
  destruct x as ((ix, lx), ax), y as ((iy, ly), ay);
  unfold light,alive in *.
  destruct (bool_eqdec lx ly), (bool_eqdec ax ay), (nat_eq_eqdec ix iy); intuition.
Defined.



Instance State_ILA : @State (make_Location R2) (R2*ILA) :=
  @AddInfo Loc R2 ILA _ _ (OnlyLocation).


(* Trying to avoid notation problem with implicit arguments *)


Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation "!! config" := (@spect_from_config location _ _ _ set_spectrum config origin) (at level 10).
Notation support := (@support location _ _ _).

Set Debug Typeclasses.


Definition config:= @configuration Loc (R2*ILA) State_ILA _.

Definition upt_aux (config:config) g (rl : R2*light): (R2*ILA) :=
  let (pos, ila) := config (Good g) in 
  match ila with (i,_,a) => 
  let (r, l):= rl in 
  (r,( i,l,a))
  end 
  .

Instance upt_aux_compat : Proper (equiv ==> eq ==> equiv ==>  equiv) upt_aux.
Proof.
  repeat intro.
  unfold upt_aux.
  assert (H_x := H (Good x0)).
  rewrite <- H0 in *.
  destruct (x (Good x0)), (y (Good x0)).
  simpl in *.
  destruct i, p, i0, p, x1, y1.
  simpl in *.
  destruct H_x as (_,(Hi,(_,Ha))), H1.
  repeat split; try assumption.
Qed.

Instance RL_Setoid : Setoid (R2*light) :=  prod_Setoid R2_Setoid bool_Setoid.



Instance robot_choice_RL : robot_choice (R2*light) :=
{| robot_choice_Setoid := RL_Setoid|}.


Context {Frame : frame_choice R2}.
Instance Choice : update_choice bool :=
  {| update_choice_Setoid := _     
  |}.


(* Definition round (r : robogram) (da : demonic_action) (config : configuration) : configuration :=
  (* for a given robot, we compute the new configuration *)
  fun id =>
    let state := config id in
    if da.(activate) id                       
    (* first see whether the robot is activated *)
    then
      match id with
        | Byz b => da.(relocate_byz) config b 
                     (* byzantine robots are relocated by the demon *)
        | Good g =>
          (* change the frame of reference *)
          let frame_choice := da.(change_frame) config g in
          let new_frame := frame_choice_bijection frame_choice in
          let local_config := map_config (lift (existT precondition new_frame
                                                       (precondition_satisfied da config g)))
                                         config in
          let local_pos := get_location (local_config (Good g)) in
          (* compute the spectrum *)
          let spect := spect_from_config local_config local_pos in
          (* apply r on spectrum *)
          let local_robot_decision := r spect in
          (* the demon chooses how to perform the state update *)
          let choice := da.(choose_update) local_config g local_robot_decision in
          (* the actual update of the robot state is performed by the update function *)
          let new_local_state := update local_config g frame_choice local_robot_decision choice in
          (* return to the global frame of reference *)
          lift (existT precondition (new_frame ⁻¹) (precondition_satisfied_inv da config g)) new_local_state
        end
    else inactive config id (da.(choose_inactive) config id).


la question est de savoir si maintenant le changement d'état se fait dans le robogram ou dans le demon, et comment le demon sais comment changer le spectre aussi
 *)

Instance UpdFun : @update_function (R2*ILA) Loc State_ILA _ (R2*light)(* Trobot *)
                                   R2(* Tframe *) bool (* Tactive *) robot_choice_RL Frame Choice:=
  {
    update := fun config g r rl _ => upt_aux config g rl }.
Proof.
  intros c1 c2 Hc g1 g2 Hg t1 t2 Ht ? ? ? ? ? ?.
  apply upt_aux_compat; intuition.
Defined.



(* si on ne veux pas de multiset car les robots ne voient pas les robots non actifs, comment faire pour les mettre en routes? car ça se passe dans el robogram.
   a moins d'ajouter en dur lors de la création du spectre le robot qui a (id = threshold) 
il faut aussi faire attention a ce que le spectre ne modifie pas D, ni aucune distance. a voir comment faire, peut etre en spécifiant plus le Spectre (avec un "S" et pas un "s"), et donc la fonction spect_from_config
 *)
Context {find_id: configuration -> R2 -> (R2*ILA)}.
Context {find_id_compat : Proper (equiv ==> equiv ==> equiv) find_id}.
Axiom find_id_true : forall config loc ila,
    (loc, ila) = find_id config loc ->
    exists id, config id = (loc,ila).

                            
Context {find_lower: configuration -> R2*ILA -> list (R2*light)}.

Definition RLList_eq (list1: (list (R2*light))) (list2:(list (R2*light))) :=
  eqlistA (fun (rl1:R2*light) (rl2:R2*light) => let (r1,l1) := rl1 in let (r2, l2) := rl2 in
           r1 == r2 /\ l1 == l2) list1 list2.

Instance RLList_eq_Setoid : Setoid (list (R2*light)) :=
{
    equiv := fun (list1: (list (R2*light))) (list2:(list (R2*light))) =>
  eqlistA (fun (rl1:R2*light) (rl2:R2*light) => let (r1,l1) := rl1 in let (r2, l2) := rl2 in
           r1 == r2 /\ l1 == l2) list1 list2
             }.
Proof. 
  apply eqlistA_equiv.
  split; intros (rx,lx).
  - intuition.
  - intros (ry,ly); intuition.
  - intros (ry, ly) (rz, lz); intuition. now transitivity ry. now transitivity ly.
Defined.

Instance RLList_eq_EqDec : EqDec RLList_eq_Setoid. 
Proof.
  intros x y. 
  unfold equiv.
  cbn -[equiv].
  apply eqlistA_dec.
  intros (r1, l1) (r2, l2).
  cbn.
  destruct (R2_EqDec r1 r2), (bool_dec l1 l2); intuition.
Defined.

Context {find_lower_compat : Proper (equiv ==> equiv ==> equiv) find_lower}.
Axiom find_lower_true : forall (config:config) (ri:R2*ILA) id list,
    let (r, ila) := ri in
    match ila with (i,l,a) =>
                  let (rc, ila_c) := config id in
                  match ila_c with (ic, lc, ac) =>
                                         list = find_lower config ri ->
                                         List.In (rc,lc) list ->
                                         ic < i
                  end
    end.

Definition spect_is_ok_ILA spect config loc := 

spect =  (fun config loc =>
                            let us := find_id config loc in
                             find_lower config us                               
                         ) config loc
.

Instance Spect_ILA : Spectrum :=
  {|
    spectrum := list (R2*light);
    spectrum_Setoid := RLList_eq_Setoid;
    spectrum_EqDec := RLList_eq_EqDec;
    spect_from_config := (fun config loc =>
                            let us := find_id config loc in
                             find_lower config us                               
                         );
    spect_is_ok := spect_is_ok_ILA |}.
Proof.    
  - intros c1 c2 Hc l1 l2 Hl.
    intuition.
    rewrite (find_id_compat Hc Hl).
    now rewrite (find_lower_compat Hc (reflexivity _)).
  - intros config loc.
    now unfold spect_is_ok_ILA.
Defined.

Definition spect_ILA := @spectrum (R2*ILA) Loc State_ILA _ Spect_ILA.


(* pour ce qui est du robogramme
================================================================================= *)

(* plus besoin, c'est donné avec la fonction find_lower en contexte. *)
(*Definition filtre_lower_spect  (spect:spect_ILA) ident :=
List.filter
    (fun (elt:R2*light)  =>
       let (_,ila) := elt in
       match ila with | (ident', _, _) => 
                        (ident' <? ident)
       end
    ) spect .*)

    
(* todo @set (@location H) (@location_Setoid H) (@location_EqDec H)
              (@FSetList.SetList (@location H) (@location_Setoid H)
                 (@location_EqDec H));

@set_spectrum (R2 * ILA) Loc State_ILA Robots

@set (R2 * ILA) ?S0 ?H ?FSet *)

Definition distance_closest (ident: identifiants) (spect:spect_ILA) : R
  :=
    let closest :=
        List.fold_left (fun a (elt:R2*light) =>
                match elt with
                | (pos, light) =>
                  let distance := dist a (0,0)%R in
                  if Rle_bool 0%R distance
                  then
                    if Rle_bool distance (dist pos (0,0)%R)
                   then a else pos
                 else a
              end) spect (0,0)%R
     in dist closest (0,0)%R.

Parameter threshold : identifiants.

Context {choose_cible : spect_ILA -> (R2*light) -> (R2*light)}.

(* propiété de choose_cible*)

Axiom light_off_first: forall spect nous cible,
    choose_cible spect nous = cible ->
    match cible,nous with |(pos_c, light_c), (pos_n, light_n) => 
                           light_c = true ->
                           (* il n'y a pas de robots etein *)
                           List.filter (fun (elt: R2*light) =>
                                           let (_,light_e) := elt in
                                        eqb light_e false) spect
    = nil
    end.

Axiom light_close_first : forall spect nous cible,
    choose_cible spect nous = cible ->
    match cible,nous with |(pos_c, light_c), (pos_n, light_n) =>       
    light_c = true ->
    Rle Dp (dist pos_n pos_c) ->
    List.filter (fun (elt : R2*light) =>
                        match elt with (pos_e, light_e) =>
              negb (Rle_bool (dist pos_n pos_e) Dp) end) spect = nil
    end.
(* todo *)(*
Definition move_to (cible:ILA) (spect:spect_multi):R2 := 
  match cible with (pos, _, _, _) => 
        let (x,y) := pos in
        let z := (sqrt (D/(((y*y)/(x*x))+1)))%R in
        let t := (z*y/x)%R in
        (z,t) end.
*)

(* À RAJOUTER:
une fonction axiomatisé qui choisit en fonction de la cible et de la distance à 
celle ci un endroit dans la zone qui est l'intersection de {x, dist nous x < D} et
de {y, dist cible y < 7D}. *)
Context {move_to: spect_ILA -> location -> option location }.

Axiom move_to_Some_zone : forall spect cible new_pos,
    move_to spect cible = Some new_pos ->
    (dist new_pos cible < Dp /\ dist new_pos (0,0)%R < D
    /\ forall x, List.In x spect -> let (pos_x, light_x) := x in
                                    dist new_pos pos_x > 2*D)%R.

Axiom move_to_None : forall spect cible,
    move_to spect cible = None ->
    ~(exists pos, forall x, List.In x spect -> let (pos_x, ligth_x) := x in
                                               dist pos pos_x > 2*D)%R.
Context {move_to_compat : Proper (equiv ==> equiv ==> equiv) move_to}.
(* todo *)


Definition robot_a_portée (ident : identifiants) (spect:spect_ILA) (D:R) (new_pos: R2) :bool :=
  (Rle_bool (distance_closest ident spect) (2*D)%R)
    &&
    let closest := List.fold_left (fun a (elt:R2*light) =>
                match elt with
                | (pos, light) =>
                  let distance := dist a (0,0)%R in
                  if Rle_bool 0%R distance
                  then
                    if Rle_bool distance (dist pos (0,0)%R)
                   then a else pos
                 else a
              end) spect new_pos
        in Rle_bool (dist closest new_pos) (2*D)%R .

(* todo *)
(* si il y a un robot a portée tel qu'il risque de rentré en colision avec nous, il faut aller dans une zone d'esquive, mais comment trouver une position dans cette zone?
il faudrait caractérisier les ensemble de points Sd et Rd (voir tableau) *)
(* Context {esquive : spect_ILA -> R -> identifiants -> option R2}.
(* les propriétés de l'esquive *)
(* si Some x, forall y, [xy] > 2D *)
Axiom esquive_Some : forall spect D ident x,
    esquive spect D ident = Some x <-> 
    (List.filter (fun (elt:R2*light) =>
                        match elt with (pos, _) => 
                        let distance := dist x pos in
                        Rle_bool distance 2%R end)
                     (spect)) = nil .
*)

(*  @robogram (@location Loc) Loc State_ILA _ Spect 

le robogram te donne juste la nouvelle position, mais doit_il changer la couleur aussi? *)

Definition path_ILA := path location.
Definition paths_in_ILA : location -> path_ILA := local_straight_path.
Coercion paths_in_ILA : location >-> path_ILA.
Instance paths_in_ILA_compat : Proper (equiv ==> equiv) paths_in_ILA.
Proof. intros [] [] [] x. f_equiv. Qed.


Context {activ_ila :ident-> bool}.

Context {change_frame_ILA : config -> G -> R2}.

Axiom change_frame_not_dist : forall config g loc,
    change_frame_ILA config g = loc ->
    let (pos_c,_) := config (Good g) in
    forall g',
    let (pos_c',_) := config (Good g') in
    dist pos_c pos_c' = dist loc (change_frame_ILA config g').


    
Context {change_frame_ILA_compat : @Proper (@configuration Loc (R2 * ILA) State_ILA Robots -> @G Robots -> R2)
    (@equiv (@configuration Loc (R2 * ILA) State_ILA Robots)
       (@configuration_Setoid Loc (R2 * ILA) State_ILA Robots) ==>
     @eq (@G Robots) ==> @equiv R2 (@frame_choice_Setoid Loc R2 Frame))
    change_frame_ILA}. 
Context {inactive_ila : config -> ident-> bool}.

Context {inactive_choice_ila : inactive_choice bool}.
Context {inactive_ila_compat :
           @Proper (@configuration Loc (R2 * ILA) State_ILA Robots -> @ident Robots -> bool)
                   (@equiv (@configuration Loc (R2 * ILA) State_ILA Robots)
                           (@configuration_Setoid Loc (R2 * ILA) State_ILA Robots) ==>
                           @equiv (@ident Robots) (eq_setoid (@ident Robots)) ==>
                           @equiv bool (@inactive_choice_Setoid bool inactive_choice_ila))
                   inactive_ila}.

Context {relocate_ila : config -> B -> R2*ILA}.
Context {relocate_ila_compat : Proper (equiv ==> eq ==> equiv) relocate_ila}.

Definition demonic_action_ILA : 
  @demonic_action (R2*ILA) Loc State_ILA _ (R2*light) R2 bool bool robot_choice_RL Frame Choice _.
  refine {|
    activate := activ_ila;
    relocate_byz := relocate_ila;
    change_frame := change_frame_ILA;
    choose_update := fun config g rl =>
                       match (config (Good g)) with
                         (pos_c, (ident_c, light_c, alive_c))
                         => alive_c
                       end;
    choose_inactive := inactive_ila 
  |}.
Proof.
  - intros.
    cbn in *. 
    intuition.
  - intros. cbn in *. intuition.
  - intros c1 c2 Hc g1 g2 Hg _ _ _.
    specialize (Hc (Good g1)).
    rewrite Hg in *.
    destruct (c1 (Good g2)) as (r1,((i1,l1),a1)),
    (c2 (Good g2)) as (r2, ((i2, l2), a2)).
    now destruct Hc as (_,(_,(_,Ha))).
Defined.

Set Printing Implicit.

Definition rbg_fnc (s:spect_ILA) : R2*light
  :=
    (* on regarde quel est le robot à 0/0 *)
    let (pos_n, light_n) := List.fold_left (fun acc (elt:R2*light) => let (pos, light) := elt in
                                   if R2dec_bool pos (0,0)%R then
                                     elt
                                   else
                                     acc) s ((0,0)%R,true) in
    (* on choisit la cible *)
    let cible := choose_cible s (pos_n, light_n) in
    match move_to s (fst cible) with
    | Some x => (x,true)
    | None => ((0,0)%R, false)
    end. 
  
(* 
Lemma bourreau_non_coloré : forall (elt:ILA),
    let (x, D) := elt in
    let (x, alive) := x in
    let (x, light) := x in
    let (pos, ident) := x in
    light=true ->
    ~(exists (y:ILA),
         let (y, D_y) := y in
         let (y, alive_y) := y in
         let (y, light_y) := y in
         let (pos_y, ident_y) := y in
         ident_y > ident /\ ((dist pos pos_y) < D)%R). 
Proof.
  intros ((((pos, ident),light),alive),D) Hlight.
  intros (((((pos_y, ident_y), light_y), alive_y), D_y), H).
  destruct H.
  

Qed. *)

(* Trying to avoid notation problem with implicit arguments *)
(*Notation support := (@support location _ _ _).*)
(* (@spect_from_config R2 unit _ _ _ _ _ _ multiset_spectrum) (at level 1). *)
(* Notation "x == y" := (equiv x y).
Notation spectrum := (@spectrum R2 R2 _ R2_EqDec _ R2_EqDec _ MyRobots multiset_spectrum).
Notation robogram := (@robogram R2 R2 _ _ _ _ _ MyRobots _).
Notation configuration := (@configuration R2 _).
Notation config_list := (@config_list R2 _).
Notation round := (@round R2 R2 _ _ _ _ _ _ _ _).
Notation execution := (@execution R2 _). *)



(* pour tout ce qui est config initiale 
===============================================================================*)

Context{ config_init :config }. (* @configuration ILA Loc State_ILA _}.*)

(* tous les robots sont a plus de D dans la conf init *)
Axiom config_init_not_close : forall id,
    match (config_init id) with
      (pos, ident, light, alive) =>
      exists id',
      match config_init id' with
        (pos', ident', light', alive') => 
                (dist pos pos' > D)%R end end.

(* tout le monde est eteint au début *)
Axiom config_init_off : forall id,
    match (config_init id) with
      (_, _, light, _) => light = false
    end.

(* tout robot voit un robot inférieur, ou alors on est le robot 1. *)
Axiom config_init_lower : forall id,
    match (config_init id) with
      (pos,ident,light,alive)
      => alive = true -> ident = 1 \/ exists id', match(config_init id') with
                                             (pos',ident',_,alive') =>
                                             alive' = true ->
                                             (dist pos pos' < Dmax)%R
                                           end
      end.


(* le travail sur le demon/la demonic_action  *)


                                            
Proof.
  unfold RealVectorSpace.
  cbn.
  intros x.

Defined.

  Context {sim_f_rila : @similarity ILA ILA_Setoid}.

Context {change_frame_rila: config -> G -> R2}.

Axiom change_frame_same_dist : forall config g1 g2,
    

Definition da_rila : demonic_action

Definition demon_rila : Demon  
  
