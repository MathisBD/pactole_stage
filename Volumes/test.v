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
  eqlistA equiv.

Instance RLList_eq_Setoid : Setoid (list (R2*light)) :=
{
    equiv := eqlistA equiv}.

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
    spectrum_Setoid := RLList_eq_Setoid ;
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

Context {choose_cible_compat : Proper (equiv ==> equiv ==> equiv) choose_cible}.

Axiom light_off_first: forall spect nous cible,
    choose_cible spect nous = cible ->
    match cible,nous with |(pos_c, light_c), (pos_n, light_n) => 
                           light_c = true ->
                           (* il n'y a pas de robots etein *)
                           List.Forall (fun (elt: R2*light) =>
                                           let (_,light_e) := elt in
                                        light_e == true) spect
    end.

Axiom light_close_first : forall spect nous cible,
    choose_cible spect nous = cible ->
    match cible,nous with |(pos_c, light_c), (pos_n, light_n) =>       
    light_c = true ->
    Rle Dp (dist pos_n pos_c) ->
    List.Forall (fun (elt : R2*light) =>
                   match elt with (pos_e, light_e) =>
                                  ((dist pos_n pos_e) > Dp)%R
                   end) spect
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
    (dist new_pos cible <= Dp /\ dist new_pos (0,0)%R <= D
    /\ forall x, List.In x spect -> let (pos_x, light_x) := x in
                                    dist new_pos pos_x > 2*D)%R.

Axiom move_to_None : forall spect cible,
    move_to spect cible = None ->
    ~(exists pos, forall x, List.In x spect -> let (pos_x, ligth_x) := x in
                                               dist pos pos_x > 2*D /\ dist pos (0,0)%R <= D)%R.
(* todo *)

Context {move_to_compat : Proper (equiv ==> equiv ==> equiv) move_to}.

(*
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
*)
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
 Definition fnc_fold acc  (elt:R2*light) :=
   let (pos, light) := elt in
   if R2dec_bool pos (0,0)%R then
     elt
   else
     acc
.

Instance fnc_fold_compat : Proper (equiv ==> equiv ==> equiv) fnc_fold.
Proof.
  intros acc1 acc2 Hacc (r1,l1) (r2,l2) (Hr, Hl).
  cbn in *.
  rewrite Hr, Hl.
  destruct (R2dec_bool r2 (0,0)%R); intuition.
Qed.  


Definition rbg_fnc (s:spect_ILA) : R2*light
  :=
    (* on regarde quel est le robot à 0/0 *)
    let (pos_n, light_n) := List.fold_left fnc_fold s ((0,0)%R,true) in
    (* on choisit la cible *)
    let cible := choose_cible s (pos_n, light_n) in
    match move_to s (fst cible) with
    (* Si on a pu bouger, on change la position, et on est pas allumé *)
    | Some x => (x,false)
    (* si on a pas pu bouger, on change de couleur *)
    | None => ((0,0)%R, true)
    end. 


Instance rbg_compat : Proper (equiv ==> equiv) rbg_fnc.
Proof.
  intros s1 s2 Hs.
  unfold rbg_fnc.
  destruct (fold_left fnc_fold s1 (0%R, 0%R, true)) as (r1, l1) eqn : Hrl1.
  destruct (fold_left fnc_fold s2 (0%R, 0%R, true)) as (r2, l2) eqn : Hrl2.
  assert (Hequiv : (r1,l1) == (r2,l2)).  
  { 
    rewrite <- Hrl1, <- Hrl2.
    apply (fold_left_compat fnc_fold_compat).
    cbn in *. 
    assumption. 
    reflexivity.
    }
  destruct (move_to s1 (fst (choose_cible s1 (r1, l1)))) as [(rm1, lm1)|] eqn : Hm1;
  destruct (move_to s2 (fst (choose_cible s2 (r2, l2)))) as [(rm2, lm2)|] eqn : Hm2;
  assert (Hmcompat := move_to_compat Hs (fst_compat _ _ _ _ (choose_cible_compat Hs Hequiv)));
  unfold light in *;
  rewrite Hm1, Hm2 in Hmcompat;
  simpl in *; try intuition.
Qed.

Definition rbg_ila : robogram :=
  {| pgm := rbg_fnc |}.

(* au lieu de def une DA, et de metttre des truc dans le contexte petit a petit, ecrire les propriété qu'on veut que la DA suive, les mettres dans un seul prédicat, et dire dans les lemmes qui suivent que la DA utilisée (ou le démon utilisé dans le cas des lemmes sur les execution) suit le prédicat *)
Context {inactive_choice_ila : inactive_choice bool}.

Definition da_ila := @demonic_action (R2*ILA) Loc State_ILA _ (R2*light) R2 bool bool robot_choice_RL Frame Choice _.

Definition change_frame_not_dist (da:da_ila):= forall (config:config) g (loc:R2),
    da.(change_frame) config g = loc ->
    let (pos_c,_) := config (Good g) in
    forall g',
    let (pos_c',_) := config (Good g') in
    dist pos_c pos_c' = dist loc (da.(change_frame) config g').

  
Definition choose_update_close (da:da_ila) := forall config g rl,
    da.(choose_update) config g rl = false ->
    match (config (Good g)) with
      (pos_c, (ident_c, light_c, alive_c)) =>
      alive_c == false \/
      exists g',
        match (config (Good g')) with
          (pos', (ident', light', alive')) =>
          ident' < ident_c -> alive' = true -> (dist pos_c pos' <= D)%R
        end
    end.

Definition da_predicat (da:da_ila) := (change_frame_not_dist da) /\ (choose_update_close da).

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

(* faire la même chose que pour la DA/le démon, faire un predicat ""global"" *)

(* tous les robots sont a plus de D dans la conf init *)
Definition config_init_not_close (config_init:config) := forall id,
    match (config_init id) with
      (pos, ((ident, light), alive)) =>
      exists id',
      match config_init id' with
        (pos', ((ident', light'), alive')) => 
                (dist pos pos' > D)%R end end.

(* tout le monde est eteint au début *)
Definition config_init_off (config_init:config) := forall id,
    match (config_init id) with
      (_,(( _, light), _)) => light = false
    end.

(* tout robot voit un robot inférieur, ou alors on est le robot 1. *)
Definition config_init_lower (config_init:config) := forall id,
    match (config_init id) with
      (pos,((ident,light),alive))
      => alive = true -> ident = 1 \/ exists id', match(config_init id') with
                                             (pos',((ident',_),alive')) =>
                                             alive' = true ->
                                             (dist pos pos' < Dmax)%R
                                           end
      end.


Definition config_init_pred config :=
  config_init_lower config
  /\ config_init_off config
  /\ config_init_not_close config.

Definition demon_ila_type := @demon  (R2*ILA) Loc State_ILA _ (R2*light) R2 bool bool robot_choice_RL Frame Choice _.

Definition demon_ILA (demon : demon_ila_type) := Stream.forever (Stream.instant da_predicat) demon.


Context {inactive_ila : @inactive_function (R2 * ILA) Loc State_ILA Robots bool
         inactive_choice_ila}.

Lemma bourreau_non_coloré : forall (exec: @execution (R2*ILA)%type Loc State_ILA _)
                                   (demon:demon_ila_type) (config : config),
    demon_ILA demon ->
    config_init_pred config ->
    exec = execute rbg_ila demon config ->
    Stream.forever
      (Stream.instant
         (fun config => forall g g',
              match (config (Good g)), (config (Good g')) with
                (pos, ((ident, light), alive)), (pos', ((ident', light'), alive'))
                => (dist pos pos' <= D)%R -> ident < ident' ->
                   alive = alive' -> alive = true -> light = false
         end)
       ) exec.
Proof.
  cofix Hcofix.
  intros exec demon config_init Hdemon Hconfig Hexec.
  split.
  - simpl.
    intros g g'.
    destruct (@Stream.hd (@ident Robots -> R2 * (nat * bool * bool)) exec (@Good Robots g)) as (pos, ((ident,light), alive)) eqn : H_hd.
    destruct (@Stream.hd (@Robots.ident Robots -> R2 * (nat * bool * bool)) exec (@Good Robots g')) as (pos', ((ident',light'), alive')) eqn : H_hd'. 
    intros Hdist Hid Halive1 Halive2.
    destruct Hconfig as (_, (Hoff, _)).
    specialize (Hoff (Good g)).
    rewrite Hexec in *.
    simpl in *.
    rewrite H_hd in *.
    now simpl in *.    
  (*assert (Hequiv_exec1 : @Stream.hd (@Robots.ident Robots -> R2 * (nat * bool * bool)) exec
           (@Good Robots g) == (pos, (ident, light, alive))).
    now rewrite H_hd.
    cbn in Hexec.
    destruct Hexec as (Hexec,_).
    specialize (Hexec (Good g)).
    Set Printing Implicit.
    unfold configuration, ILA, identifiants, Top.light, Top.alive in *.
    simpl in *.
    destruct Hexec as (Hpos_exec, Hila_exec).
    destruct Hequiv_exec1 as (Hpos_equiv, Hila_equiv).
    unfold ILA, identifiants, Top.light, Top.alive in *.
    destruct (@snd R2 (nat * bool * bool)
                   (@Stream.hd (@Robots.ident Robots -> R2 * (nat * bool * bool))
                      exec (@Good Robots g))) as ((i,l),a).
    destruct ((config_init (@Good Robots g))) as (pos_c, ((ident_c, light_c), alive_c)).
    simpl in *.
    destruct Hila_exec as (_,(Hl1, _)).
    destruct Hila_equiv as (_,(Hl2,_)).
    now rewrite Hl1, Hl2 in *. 
   *)
  - rewrite Hexec in *.
    unfold execute in *.
    simpl in *.
    split.
    Focus 2.
    simpl. 
    apply 
Qed.
  
(* le travail sur le demon/la demonic_action  *)
