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
Require Import Pactole.Core.Identifiers.
Require Import Pactole.Core.State.
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
Require Import Pactole.Util.Bijection.
Require Import Pactole.Setting.
Require Import Pactole.Util.MMultiset.MMultisetInterface.
Require Import Pactole.Observations.SetObservation.
Require Import Pactole.Observations.PointedObservation.
Set Implicit Arguments.

(* on  veut créer l'algo sur les robots volumiques pour qu'il y ait toujours un chemin entre la base et 1 *)

Parameter n: nat.

(* il y a n "bon" robots et 0 byzantins*)
Instance Identifiers : Names := Robots n 0.

Definition identifiants := nat.
Definition indentifiants_setoid := eq_setoid nat.

Parameter ident_max : identifiants.

Axiom idnet_max_not_1 : ident_max > 1. 

(*variable pour savoir si les robots sont allumé ou pas: Si la variable de type [light] est à vrai, il est allumé*)
Definition light := bool.
Definition alive := bool.

Parameter D: R.

Set Debug Typeclasses.

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

Axiom D_0: (D>0)%R.
Axiom Dmax_6D : (Dmax > 6*D)%R.

Definition ILA :Type := identifiants*light*alive. 



Instance ILA_Setoid : Setoid ILA.
simple refine  {|
    equiv := fun ila1 ila2 =>
               match ila1, ila2 with
                 |(i1, l1, a1), (i2, l2, a2) =>
                  i1 == i2 /\ l1 == l2 /\ a1 == a2
               end|}
.
Proof.
  apply indentifiants_setoid.
  apply bool_Setoid.
  apply bool_Setoid.
  split; intro x; intuition;
    try destruct x as ((i1, l1), a1). 
  - destruct y as ((i2, l2), a2); intuition.
  - destruct z as ((i3, l3), a3);
      intuition; unfold equiv in *; cbn -[equiv] in *.
    now transitivity a1.
    now transitivity b2.
    now transitivity b1.
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
  @AddInfo Loc R2 ILA _ _ (OnlyLocation (fun _ => location)).


(* Trying to avoid notation problem with implicit arguments *)


Notation "s [ x ]" := (multiplicity x s) (at level 2, no associativity, format "s [ x ]").
Notation "!! config" := (@obs_from_config location _ _ _ set_observation config origin) (at level 10).
Notation support := (@support location _ _ _).



Definition config:= @configuration Loc (R2*ILA) State_ILA _.

Definition get_ident (elt : R2*ILA) : identifiants := fst(fst(snd elt)).
Instance get_ident_compat : Proper (equiv ==> equiv) get_ident.
Proof. intros ? ? Heq. 
       destruct x as (px,((ix,lx),ax)), y as (py,((iy,li),ay)), Heq as (_,(Hi,(_,_))).
       simpl.
       now unfold equiv, nat_Setoid, eq_setoid in Hi.
Qed.

Axiom ident_unique : forall conf g g', g <> g' -> get_ident (conf (Good g)) <> get_ident (conf (Good g')).


Definition get_light (elt : R2*ILA) : light := snd(fst(snd elt)).
Instance get_light_compat : Proper (equiv ==> equiv) get_light.
Proof. intros ? ? Heq. 
       destruct x as (px,((ix,lx),ax)), y as (py,((iy,li),ay)), Heq as (_,(_,(Hl,_))).
       simpl.
       now unfold equiv, nat_Setoid, eq_setoid in Hl.
Qed.

Definition get_alive (elt : R2*ILA) : alive := snd(snd(elt)). 
Instance get_alive_compat : Proper (equiv ==> equiv) get_alive.
Proof. intros ? ? Heq. 
       destruct x as (px,((ix,lx),ax)), y as (py,((iy,li),ay)), Heq as (_,(_,(_,Ha))).
       simpl.
       now unfold equiv, nat_Setoid, eq_setoid in Ha.
Qed.

(* MAP POUR NE PRENDRE QUE LES PLUS PETITS!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)


Axiom ident_0_alive : forall conf g, get_ident (conf (Good g)) = 0 ->
                                     get_alive (conf (Good g)) = true.


Definition upt_robot_dies_b (config:config) (g:G) : bool :=
  existsb (fun elt : R2 * ILA => Rle_bool (dist (@get_location Loc _ _ elt) (@get_location Loc _ _ (config (Good g)))) D)
          (List.filter (fun (elt : R2*ILA) => (get_ident(elt) <? get_ident (config (Good g))) && get_alive (elt)) (config_list config))
  || negb
  (existsb (fun elt : R2 * ILA => (Rle_bool (dist (@get_location Loc _ _ elt) (@get_location Loc _ _ (config (Good g)))) Dmax))
            (List.filter (fun (elt : R2*ILA) => (get_ident(elt) <? get_ident (config (Good g))) && get_alive (elt) )(config_list config))).

Instance upt_robot_dies_b_compat : Proper (equiv ==> eq ==> equiv) upt_robot_dies_b.
Proof.
  intros x y Hconf g g' Hg.
  rewrite <- Hg.
  assert (H_x := Hconf (Good g)).
  unfold upt_robot_dies_b.
  rewrite 2 orb_lazy_alt.
  destruct (existsb
       (fun elt : R2 * ILA =>
        Rle_bool (dist (get_location elt) (get_location (x (Good g)))) D)
       (List.filter (fun elt : R2 * ILA => (get_ident elt <? get_ident (x (Good g))) && get_alive elt)
          (config_list x))) eqn : Hex_x1;
    destruct (existsb
       (fun elt : R2 * ILA =>
        Rle_bool (dist (get_location elt) (get_location (y (Good g)))) D)
       (List.filter (fun elt : R2 * ILA => (get_ident elt <? get_ident (y (Good g))) && get_alive elt)
          (config_list y))) eqn : Hex_y1; try (now simpl in *);
    destruct (negb
       (existsb
          (fun elt : R2 * ILA =>
           Rle_bool (dist (get_location elt) (get_location (x (Good g)))) Dmax)
          (List.filter
             (fun elt : R2 * ILA => (get_ident elt <? get_ident (x (Good g))) && get_alive elt)
             (config_list x)))) eqn : Hex_x2;
   
    destruct (negb
       (existsb
          (fun elt : R2 * ILA =>
           Rle_bool (dist (get_location elt) (get_location (y (Good g)))) Dmax)
          (List.filter
             (fun elt : R2 * ILA => (get_ident elt <? get_ident (y (Good g))) && get_alive elt)
             (config_list y)))) eqn : Hex_y2;
   try (
        generalize (config_list_compat Hconf); intro Hcomp; try ( assert (true == false) by now (rewrite <- Hex_y1, <- Hex_x1;
           apply (@existsb_compat _ equiv);
           try (now intros w z Hwz; rewrite H_x, Hwz);
           try (f_equiv; try (intros v w Hvw;
                              now rewrite H_x, Hvw);
                try assumption)));
           try discriminate); try auto.
  + rewrite negb_false_iff, negb_true_iff in *. 
    rewrite <- Hex_y2, <- Hex_x2.
    rewrite (get_ident_compat (Hconf (Good g))).
    rewrite (get_location_compat _ _ (Hconf (Good g))).
    apply (@existsb_compat _ equiv).
    auto. 
    intros u v Huv.
    rewrite (get_location_compat _ _ Huv).
    auto.
    f_equiv.
    intros a b Hab.
    rewrite Hab.
    reflexivity.
    rewrite Hcomp.
    reflexivity.
  + rewrite negb_false_iff, negb_true_iff in *. 
    rewrite <- Hex_y2, <- Hex_x2.
    apply (@existsb_compat _ equiv).
    intros w z Hwz.
    destruct H_x as (Hr,_).
    rewrite Hwz, Hconf.
    now simpl.
    f_equiv. 
    intros v w Hvw; now rewrite Hvw, Hconf. now rewrite Hconf.
Qed.

Definition upt_aux (config:config) (g: G) (rl : R2*light): (R2*ILA) :=
  match config (Good g) with (r,((i,l),a)) =>
  if upt_robot_dies_b config g
  then (r,((i,l),false))
  else (fst rl,((i,snd rl), a))
  end.

Instance upt_aux_compat : Proper (equiv ==> eq ==> equiv ==>  equiv) upt_aux.
Proof.
  repeat intro.
  unfold upt_aux.
  rewrite (upt_robot_dies_b_compat H H0).
  destruct (upt_robot_dies_b y y0);
  simpl;
  rewrite <- H0 in *;
  assert (H_x := H (Good x0));
  destruct (x (Good x0)) as (?,((?,?),?));
  destruct (y (Good x0)) as (?,((?,?),?));
  destruct H_x as (?,(?,(?,?)));
  now simpl in *.
Qed.

Instance RL_Setoid : Setoid (R2*light) :=  prod_Setoid R2_Setoid bool_Setoid.



Instance robot_choice_RL : robot_choice (R2*light) :=
{| robot_choice_Setoid := _ |}.


Instance Choice : update_choice bool :=
  {| update_choice_Setoid := _     
  |}.


Definition bij_reflexion_f :=
  fun (point : R2) =>
    let (x,y) := point in
    (x,(-y)%R).

Corollary bij_reflexion_Inversion : forall (x y:R2),
    bij_reflexion_f x == y <-> bij_reflexion_f y == x.
Proof.
  intros (xa,xb) (ya,yb).
  split; intros Heq;
  rewrite <-Heq; unfold bij_reflexion_f;
    intuition;
  now rewrite Ropp_involutive.
Qed.

Definition bij_reflexion : Bijection.bijection R2 := {|
  Bijection.section := bij_reflexion_f;
  Bijection.retraction := bij_reflexion_f;
  Bijection.Inversion := bij_reflexion_Inversion |}.

Lemma reflexion_zoom : forall x y, dist (bij_reflexion x) (bij_reflexion y) = (1 * dist x y)%R. 
Proof.
  intros (x1, x2) (y1, y2).
  cbn in *.
  rewrite Ropp_involutive.
  assert (H: forall a b, (( a +- b) * (a +- b))%R = (a * a + b * b - 2 * a * b)%R).
  intros.
  replace (a +- b)%R with (a-b)%R by lra.
  replace ((a - b) * (a - b))%R with (a-b)²%R.
  rewrite R_sqr.Rsqr_minus.
  now unfold Rsqr.
  now unfold Rsqr.
  replace (- x2 + y2)%R with (y2 +- x2)%R by lra.
  repeat rewrite  H.
  rewrite Rmult_1_l.
  f_equiv.
  lra.
Qed.


Definition reflexion :=
  {|
    sim_f := bij_reflexion;
    zoom := 1;
    dist_prop := reflexion_zoom|}.

Instance Frame : @frame_choice Loc (R*(R2)*bool).
refine  {|
    frame_choice_bijection :=
      fun (elt:(R*(R2)*bool)) =>
        let (p,b) := elt in
        let (r,t) := p in
        compose (rotation r)
           (compose (translation t)
                    (if b then reflexion else @Similarity.id R2 R2_Setoid _ _ _))

    ;
    frame_choice_Setoid := prod_Setoid (prod_Setoid R_Setoid R2_Setoid) bool_Setoid |}
.
Proof.
  intros [[b1 v1] a1] [[b2 v2] a2] [[Hb Hv] Ha]. cbn -[equiv] in *.
  repeat f_equiv; trivial; []. now rewrite Ha.
Defined.  

(* Record frame_choice (H : Location) (Tframe : Type) : Type := Build_frame_choice
  { frame_choice_bijection : Tframe -> bijection location;
    frame_choice_Setoid : Setoid Tframe;
    frame_choice_bijection_compat : Proper (equiv ==> equiv) frame_choice_bijection }
 *)

Lemma frame_dist : forall pos1 pos2 tframe,
    let bij := frame_choice_bijection tframe in
    dist pos1 pos2 == dist (bij pos1) (bij pos2).
Proof.
  intros pos1 pos2 ((rot, (tra1, tra2)), b).

 unfold frame_choice_bijection, Frame.
 assert (Hdist := dist_prop (rotation rot
      ∘ (translation (tra1, tra2) ∘ (if b then reflexion else Similarity.id)))).
 rewrite Hdist.
 destruct b eqn : Hb; simpl;
 lra.
Qed.


Instance UpdFun : @update_function (R2*ILA) Loc State_ILA _ (R2*light)(* Trobot *)
                                   (R*R2*bool)(* Tframe *) bool (* Tactive *) robot_choice_RL Frame Choice.
simple refine  {|
    update := fun config g r rl _ => upt_aux config g rl |}.
Proof.
  intros c1 c2 Hc g1 g2 Hg t1 t2 Ht ? ? ? ? ? ?.
  apply upt_aux_compat; intuition.
Defined.



(* si on ne veux pas de multiset car les robots ne voient pas les robots non actifs, comment faire pour les mettre en routes? car ça se passe dans el robogram.
   a moins d'ajouter en dur lors de la création du spectre le robot qui a (id = threshold) 
il faut aussi faire attention a ce que le spectre ne modifie pas D, ni aucune distance. a voir comment faire, peut etre en spécifiant plus le Spectre (avec un "S" et pas un "s"), et donc la fonction obs_from_config
 *)

(*  ça sert a rien c'est même mauvais
Context {find_us: configuration -> R2 -> (R2*ILA)}.
Context {find_us_compat : Proper (equiv ==> equiv ==> equiv) find_us}.
Axiom find_us_true : forall config loc ila,
    InA equiv (loc,ila) (config_list config) ->
    (loc, ila) = find_us config loc.*)

    


Instance Spect_ILA : Observation .
  refine {|
    observation := set (R2*ILA);
    observation_Setoid := (Set_Setoid (R2*ILA)%type);
    observation_EqDec := (@Set_EqDec (R2*ILA)%type _ _ (@FSetList.SetList (R2*ILA)%type _ _)
                                     (@FSetList.SetListFacts (R2*ILA)%type _ _) );

    obs_from_config (config:config) (pt:R2*ILA) :=
      @SetObservation.make_set (R2*ILA)%type _ (@state_EqDec _ _ State_ILA)
                  (List.filter
                     (fun elt => (Rle_bool (dist (fst elt) (fst pt)) Dmax)
                                   && (get_alive elt) && get_alive pt && (get_ident elt <=? get_ident pt))
                     (config_list config));
  obs_is_ok s config pt := 
    forall l, In l s <-> InA equiv l (config_list config) /\ (dist (fst l) (fst pt) <= Dmax)%R /\ get_alive l == true /\ get_alive pt = true /\ get_ident l <= get_ident pt |}.
  Proof.
  - intros config1 config2 Hconfig pt1 pt2 Hpt.
    apply SetObservation.make_set_compat, eqlistA_PermutationA_subrelation.
    f_equiv.
    + intros ? ? Heq. rewrite (get_alive_compat Heq).
      rewrite (dist_compat _ _ (fst_compat Heq) _ _ (fst_compat Hpt)).
      rewrite Hpt, (get_ident_compat Heq).
      auto. 
    + now rewrite (config_list_compat Hconfig). 
  - intros config pt x.
    rewrite SetObservation.make_set_spec.
    rewrite filter_InA.
    split; intros Hlist.
    + destruct Hlist as (rila, Htemp).
      apply andb_prop in Htemp.
      destruct Htemp as (Hdist, Hident).
      apply andb_prop in Hdist.
      destruct Hdist as (Hdist, Halive_pt).
      apply andb_prop in Hdist.
      destruct Hdist as (Hdist, Halive_x).
      rewrite Rle_bool_true_iff in Hdist.
      intuition.
      intuition.
      apply leb_complete in Hident.
      intuition.
    + repeat split; try repeat apply andb_true_intro; try split; destruct Hlist as (?,(?,?));
        try rewrite Rle_bool_true_iff in *; intuition.
      apply andb_true_intro.
      try split; 
        try rewrite Rle_bool_true_iff in *; intuition.
      try rewrite Rle_bool_true_iff in *; intuition.
      rewrite andb_true_iff.
      split.
      rewrite Rle_bool_true_iff.
      auto.
      auto.
      simpl in H2.
      unfold equiv in H2.
      auto.
      simpl.
      now rewrite Nat.leb_le.
    + intros (?,((?,?),?)) (?,((?,?),?)) (?,(?,(?,?))). simpl in *.
      now rewrite H, H0, H1, H2.
Defined.

Definition spect_ILA := @observation (R2*ILA) Loc State_ILA _ Spect_ILA.


(* pour ce qui est du robogramme
================================================================================= *)

Parameter threshold : identifiants.

Context {choose_target : spect_ILA -> (R2*ILA)}.

(* propiété de choose_cible*)

Context {choose_target_compat : Proper (equiv ==> equiv) choose_target}.

Axiom choose_target_alive : forall spect target,
    choose_target spect == target
    -> get_alive target == true.

Axiom light_off_first: forall spect target,
    choose_target spect == target -> 
                      get_light (target) == true ->
                      (* il n'y a pas de robots etein *)
                      For_all (fun (elt: R2*ILA) =>
                                     get_light elt == true) spect
    .

Axiom target_lower : forall spect target (zero: R2*ILA),
        In zero spect -> get_location zero == (0,0)%R ->
        choose_target spect == target ->
        get_ident target < get_ident zero.
        

    
Axiom light_close_first : forall spect target,
    choose_target spect == target ->
    get_light target == true ->
    ((dist (0,0)%R (get_location target)) > Dp)%R ->
    For_all (fun (elt : R2*ILA) =>
               ((dist (0,0)%R (get_location elt)) > Dp)%R) spect.

(* ça ne veux pas dire que il y a toujours au moins un robot dans le spectre? 

faire attention

          /\            /\   
         /  \          /  \    
        /  | \        /  | \
       /   .  \      /   .  \
      /________\    /________\

*)
Axiom choose_target_in_spect : forall spect target,
    choose_target spect = target  ->
    In target spect.


Context {move_to: spect_ILA -> location -> bool }.

(* rajouter un truc qui dit ce qui se passe quand un robot doit s'éliminer. *)

Axiom move_to_Some_zone : forall spect choice,
    move_to spect choice = true ->
    (forall x, In x spect -> let (pos_x, light_x) := x in
                                    dist choice pos_x > 2*D)%R.

Axiom move_to_None :
  forall (spect : spect_ILA) (choice : location),
  move_to spect choice = false ->
  forall pos : location,
  (dist pos (0,0)%R <= D)%R ->
  exists other : R2 * ILA,
    (other ∈ spect)%set /\
    (exists inf, In inf spect /\ (get_location inf) == pos /\ get_ident other < get_ident inf) /\
    (dist (get_location other) choice <= 2*D)%R. 
(*    ~(exists pos, forall x, In x spect -> let (pos_x, ligth_x) := x in
                                               dist pos pos_x > 2*D /\ dist pos (0,0)%R <= D)%R.*)
(* todo *)

Context {move_to_compat : Proper (equiv ==> equiv ==> equiv) move_to}.
(*

le robogram te donne juste la nouvelle position, mais doit_il changer la couleur aussi? *)

Context {choose_new_pos: spect_ILA -> location -> location}.
Context {choose_new_pos_compat : Proper (equiv ==> equiv ==> equiv) choose_new_pos}.
Axiom choose_new_pos_correct : forall spect target new,
    new == choose_new_pos spect target ->
    (dist new target < Dp /\ dist new (0,0) < D)%R.
    

Definition rbg_fnc (s:spect_ILA) : R2*light
  :=
    (* on choisit la target *)
    let target := choose_target s in
    let new_pos := choose_new_pos s (fst target) in
    match move_to s new_pos with
    (* Si on a pu bouger, on change la position, et on est pas allumé *)
    | true => (new_pos,false)
    (* si on a pas pu bouger, on change de couleur *)
    | false => ((0,0)%R, true)
    end. 


Instance rbg_compat : Proper (equiv ==> equiv) rbg_fnc.
Proof.
  intros s1 s2 Hs.
  unfold rbg_fnc.
  assert (Hmcompat := move_to_compat Hs (choose_new_pos_compat Hs (fst_compat (choose_target_compat Hs )))).
  rewrite Hmcompat.
  rewrite (choose_new_pos_compat Hs (fst_compat (choose_target_compat Hs ))).
  reflexivity.
Qed.

Definition rbg_ila : robogram :=
  {| pgm := rbg_fnc |}.

(* au lieu de def une DA, et de metttre des truc dans le contexte petit a petit, ecrire les propriété qu'on veut que la DA suive, les mettres dans un seul prédicat, et dire dans les lemmes qui suivent que la DA utilisée (ou le démon utilisé dans le cas des lemmes sur les execution) suit le prédicat *)
Context {inactive_choice_ila : inactive_choice bool}.

Definition da_ila := @demonic_action (R2*ILA) Loc State_ILA _ (R2*light) (R*R2*bool) bool bool robot_choice_RL Frame Choice _.

Definition change_frame_origin (da:da_ila):= forall (config:config) g (tframe:R*R2*bool),
    da.(change_frame) config g = tframe ->
    let bij := frame_choice_bijection tframe in
    bij (get_location (config (Good g))) == (0,0)%R.
(*{ activate : ident -> bool;
    relocate_byz : configuration -> B -> info;
    change_frame : configuration -> G -> Tframe;
    choose_update : configuration -> G -> Trobot -> Tactive;
    choose_inactive : configuration -> ident -> Tinactive;
    precondition_satisfied : forall (config : configuration) (g : G),
                             precondition
                               (frame_choice_bijection (change_frame config g));
    precondition_satisfied_inv : forall (config : configuration) (g : G),
                                 precondition
                                   (frame_choice_bijection (change_frame config g)
                                    ⁻¹);
    activate_compat : Proper (eq ==> equiv) activate;
    relocate_byz_compat : Proper (equiv ==> eq ==> equiv) relocate_byz;
    change_frame_compat : Proper (equiv ==> eq ==> equiv) change_frame;
    choose_update_compat : Proper (equiv ==> eq ==> equiv ==> equiv) choose_update;
    choose_inactive_compat : Proper (equiv ==> equiv ==> equiv) choose_inactive }
*)
  
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


Definition da_predicat (da:da_ila) := (change_frame_origin da) /\ (choose_update_close da) /\ FSYNC_da da.

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
(* (@obs_from_config R2 unit _ _ _ _ _ _ multiset_observation) (at level 1). *)
(* Notation "x == y" := (equiv x y).
Notation observation := (@observation R2 R2 _ R2_EqDec _ R2_EqDec _ MyIdentifiers multiset_observation).
Notation robogram := (@robogram R2 R2 _ _ _ _ _ MyIdentifiers _).
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
      forall id',
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
      => alive = true ->
         ident = 0 \/
         exists id', match(config_init id') with
                       (pos',((ident',_),alive')) =>
                       alive' = true /\
                       ident' < ident /\
                       (dist pos pos' < Dmax)%R
                                           end
      end.


Definition config_init_pred config :=
  config_init_lower config
  /\ config_init_off config
  /\ config_init_not_close config.

Definition demon_ila_type := @demon  (R2*ILA) Loc State_ILA _ (R2*light) (R*R2*bool) bool bool robot_choice_RL Frame Choice _.

Definition demon_ILA (demon : demon_ila_type) := Stream.forever (Stream.instant da_predicat) demon.


Context {inactive_ila : @inactive_function (R2 * ILA) Loc State_ILA Identifiers bool
         inactive_choice_ila}.

(* faire les invariant en tant que définition de Prop, puis faire une preuve de tous les invariant a une conf C -> tous les invariants a round C (et apres sur la conf init aussi). *)
(* [target vivante] est une propriété sur une config qui suis tout les invariants *)





Definition allume_a_porte :Prop := forall (conf:config) g g',
     match conf (Good g), conf (Good g') with
       (pos, ((ident,light), alive)), (pos', ((ident', light'), alive')) =>
       alive == true /\ alive' == true ->
       (dist pos pos' <= Dmax)%R -> light' == true
       ->  exists g'', match conf (Good g'') with
                         (pos'',(_,alive''))
                         =>
                         alive'' == true ->
                         (dist pos pos'' <= Dp)%R 
                       end
       end.

Definition etein_et_vivant := forall (conf : config) g,
     match conf (Good g) with
       (pos, ((ident,light), alive)) =>
       alive == false -> light == true
     end.

Definition etre_boureau  (conf:config) g : Prop := 
 match conf (Good g) with
      (pos, ((ident,light), alive)) =>
      (exists g', match conf (Good g') with
                    (pos', ((ident', light'), alive')) =>
                    alive == true /\ alive' == true ->
                    ident < ident' -> (dist pos pos' <= D)%R
                  end)
      end.
      
Definition boureau_eteint(conf : config) : Prop := forall g, 
    match conf (Good g) with
      (pos, ((ident,light), alive)) =>

      (etre_boureau conf g) -> light == false
    end.

Inductive robot_inferieur : config -> G -> Prop  :=
  |Ri_Is_1 : forall conf g, 
 match conf (Good g) with
       (pos, ((ident,light), alive)) =>
    ident == 1
 end -> robot_inferieur conf g
| Ri_Path_to_1 : forall (conf:config) g g',
    match conf (Good g) with
      (pos, ((ident,light), alive)) =>
      match conf (Good g') with
        (pos', ((ident', light'), alive')) =>
        ident' < ident /\ alive'== true /\ alive == true /\
        (dist pos' pos <= Dmax)%R
      end
    end
    -> robot_inferieur conf g' -> robot_inferieur conf g.


Lemma allume_non_boureau : forall g (conf:config),
    boureau_eteint conf ->  
    match conf (Good g) with
      (pos, ((ident,light), alive)) =>
      light == true -> ~ etre_boureau conf g
      end.
Proof.
  intros g conf Hbe.
  specialize (Hbe g).
  destruct (conf (Good g)) as (pos, ((ident, light), alive)).
  intros Hlight Hbour.
  specialize (Hbe Hbour).
  rewrite Hbe in Hlight.
  intuition.
Qed.

(* il se passe quoi après un round: 
    si il y a un robot a moins de D, ou qu'il n'y a pas de robots on s'élimine.
    sinon on bouge en fonction du resultat de "move_to" du spectre
    
 *)

Lemma let_split : forall {A B C:Type} (x w:A) (y t:B) (a b:C) (z: A*B*C),
    let (p,a) := z in
    let (x,y):= p in
    let (p0,b) := z in
    let (w,t) := p0 in
    x=w /\ y=t /\ a = b.
Proof. intros. destruct z, p. now simpl. Qed.

Lemma round_good_g :
  forall g config (da:da_ila),
    da_predicat da -> 
    round rbg_ila da config (Good g)
    ==
    let frame_choice := change_frame da config g in
    let new_frame := frame_choice_bijection frame_choice in
    let local_config :=
        map_config
          (lift (existT precondition new_frame (precondition_satisfied da config g)))
          config in
(*    let local_pos := get_location (local_config (Good g)) in*)
    let spect := obs_from_config local_config (local_config (Good g)) in
    let local_robot_decision := rbg_ila spect in
    let choice := choose_update da local_config g local_robot_decision in
    let new_local_state :=
        update local_config g frame_choice local_robot_decision choice in
    lift
      (existT precondition (new_frame ⁻¹) (precondition_satisfied_inv da config g))
      new_local_state                   
.
Proof.
  intros.
  destruct H as (Hchange, (Hchoose, HFSYNC)).
  specialize (HFSYNC (Good g)).
  unfold round.
  destruct (activate da (Good g)) eqn : Hact; try discriminate.

  simpl.
  repeat split.
  apply let_split.
  apply 0. apply 0.
  apply true.
  apply true.
  apply true.
  apply true.
Qed.

Ltac changeR2 :=
  change R2 with location in *;
  change R2_Setoid with location_Setoid in *;
  change R2_EqDec with location_EqDec in *;
  change R2_VS with VS in *;
  change R2_ES with ES in *.

Lemma round_simplify_executioner :
  forall g config (da:da_ila) g' executioner,
    get_ident executioner < get_ident (config (Good g)) ->
    Rle (dist (@get_location Loc _ _ (config (Good g))) (get_location executioner)) D
    ->
    da_predicat da-> config (Good g') = executioner -> get_alive (executioner) = true
    ->
    exists light pos,
      (round rbg_ila da config) (Good g) ==
      (pos, (((get_ident (config (Good g))),light),false)).
Proof.
  intros.
  do 2 eexists.
  rewrite round_good_g.
  simpl.
  repeat split. 
  simpl.
  cbn.
  destruct (config0 (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  simpl.
  unfold get_ident; simpl.
  assert (let_split_2 :
            forall {A B C : Type} (w:A) (x: A*B) (y:C) (z:B) (t: A * B * C) id0 li0 al0 ,
               (fst( fst t)) = id0 /\ (snd (fst t))  = li0 /\ snd t = al0 -> 
  let (x,y) := t in let (w, z) := x in w = id0 /\ z = li0 /\ y = al0
                                         ).
  intros; simpl. 
  destruct t, p.
  now simpl. 
  apply let_split_2.
  apply 0.
  apply (0,true).
  apply true.
  apply true.
  repeat split.
  simpl.
  assert (if_split: forall {A B C D:Type} (a:bool) (b c:(B*((A*C)*D))) (d: A), ((a= true -> fst (fst (snd b)) =d) /\ (a = false -> fst (fst (snd c)) = d)) ->
 fst (fst (snd(if a then b else c))) = d).
  intros; destruct H2, a; intuition.
  apply if_split.
  intros.
  case (upt_robot_dies_b
     (fun id : Identifiers.ident =>
      ((@frame_choice_bijection Loc _ _ (change_frame da config0 g)) (fst (config0 id)),
       snd (config0 id))) g);
  repeat (split; intros; intuition). 
  assert (if_split: forall {A B C D:Type} (a:bool) (b c:(B*((C*A)*D))) (d: A), ((a= true -> snd (fst (snd b)) =d) /\ (a = false -> snd (fst (snd c)) = d)) ->
 snd (fst (snd(if a then b else c))) = d).
  intros; destruct H2, a; intuition.
  apply if_split.
  intros.
  case (upt_robot_dies_b
     (fun id : Identifiers.ident =>
      ((@frame_choice_bijection Loc _ _ (change_frame da config0 g)) (fst (config0 id)),
       snd (config0 id))) g) eqn : Heq.
  repeat (split; intros). simpl.
  assert ((get_light (config0 (Good g))) = light). rewrite Hconf. simpl; intuition.
  rewrite <- H5.
  apply (reflexivity (get_light (config0 (Good g)))).
  simpl.
  assert (forall x, x = true -> x = false -> False).
  intros x Ht Hf; rewrite Ht in Hf.
  discriminate.
  exfalso.
  revert Heq H4.
  apply H5.
  simpl.
  split; simpl.
  intros.
  assert (forall x, x = true -> x = false -> False).
  intros x Ht Hf; rewrite Ht in Hf.
  discriminate.
  exfalso.
  revert H4 Heq.
  apply H5.
  intros.
  clear let_split_2 if_split Heq.
  unfold upt_robot_dies_b in H4.
  rewrite orb_false_iff in H4.
  destruct H4 as (Hlower_d, _).
  rewrite Hconf in *.
  rewrite <- negb_true_iff in Hlower_d.
  rewrite forallb_existsb in Hlower_d.
  rewrite forallb_forall in Hlower_d.
  specialize (Hlower_d ((frame_choice_bijection (change_frame da config0 g) (get_location executioner)), snd executioner)).
  rewrite negb_true_iff in Hlower_d.
  rewrite Rle_bool_false_iff in Hlower_d.
  destruct Hlower_d. 
  rewrite config_list_spec.
  rewrite filter_map.
  rewrite in_map_iff.
  exists (Good g').
  split. 
  unfold map_config.
  unfold frame_choice_bijection, Frame.
  rewrite H2.
  simpl.
  destruct (change_frame da config0 g) as ((r, t), b).
  destruct b; intuition.
  rewrite filter_In.
  split; try apply In_names.
  unfold get_ident in *; simpl in *.
  rewrite andb_true_iff.
  split. 
  rewrite H2, Nat.ltb_lt.
  rewrite Hconf; simpl.
  apply H.
  rewrite H2; unfold get_alive in *; now simpl.
  changeR2.
  rewrite dist_sym. 
  rewrite (frame_dist _ _ (change_frame da config0 g)) in H0.
  unfold frame_choice_bijection, Frame in *.
  unfold map_config.  
  destruct (change_frame da config0 g) as ((r, t), b) eqn : Hchange.
  fold Frame in *.
  changeR2.
  rewrite Hchange, Hconf in *.
  unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in *.
  destruct b; simpl in *; lra.
  + simpl.
  assert (if_split: forall {A B C:Type} (a:bool) (b c:(B*(C*A))) (d: A), ((a= true -> snd (snd b) = d) /\ (a = false -> snd (snd c) = d)) ->
 snd (snd(if a then b else c)) = d).
  intros; destruct H2, a; intuition.
  apply if_split.
  intros.
  repeat split; simpl.
  intros H4.
 unfold upt_robot_dies_b in H4.
  rewrite orb_false_iff in H4.
  destruct H4 as (Hlower_d, _).
  rewrite <- negb_true_iff in Hlower_d.
  rewrite forallb_existsb in Hlower_d.
  rewrite forallb_forall in Hlower_d.
  specialize (Hlower_d ((frame_choice_bijection (change_frame da config0 g) (get_location executioner)), snd executioner)).
  rewrite negb_true_iff in Hlower_d.
  rewrite Rle_bool_false_iff in Hlower_d.
  destruct Hlower_d. 
  rewrite config_list_spec.
  rewrite filter_map.
  rewrite in_map_iff.
  exists (Good g').
  split. 
  unfold map_config.
  unfold frame_choice_bijection, Frame.
  rewrite H2.
  simpl.
  destruct (change_frame da config0 g) as ((r, t), b).
  destruct b; intuition.
  rewrite filter_In.
  split; try apply In_names.
  unfold get_ident in *; simpl in *.
  rewrite andb_true_iff.
  split. 
  rewrite H2, Nat.ltb_lt.
  rewrite Hconf; simpl.
  apply H.
  rewrite H2; unfold get_alive in *; now simpl.
  changeR2.
  rewrite dist_sym. 
  rewrite (frame_dist _ _ (change_frame da config0 g)) in H0.
  unfold frame_choice_bijection, Frame in *.
  unfold map_config.  
  destruct (change_frame da config0 g) as ((r, t), b) eqn : Hchange.
  fold Frame in *.
  changeR2.
  rewrite Hchange, Hconf in *.
  unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in *.
  destruct b; simpl in *; lra.
  + apply H1.
  
Qed.





Lemma round_simplify_alone :
  forall g config (da:da_ila),
    (forall other, 
        get_ident other < get_ident (config (Good g)) ->
        get_alive other = true ->
    ~ (Rle (dist (@get_location Loc _ _ (config (Good g))) (get_location other)) Dmax))
    ->
    da_predicat da-> 
    exists light pos,
      (round rbg_ila da config) (Good g) ==
      (pos, (((get_ident (config (Good g))),light),false)).
Proof.
  intros.
  do 2 eexists.
  rewrite round_good_g.
  simpl.
  repeat split. 
  simpl.
  cbn.
  destruct (config0 (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  simpl.
  unfold get_ident; simpl.
  assert (let_split_2 :
            forall {A B C : Type} (w:A) (x: A*B) (y:C) (z:B) (t: A * B * C) id0 li0 al0 ,
               (fst( fst t)) = id0 /\ (snd (fst t))  = li0 /\ snd t = al0 -> 
  let (x,y) := t in let (w, z) := x in w = id0 /\ z = li0 /\ y = al0
                                         ).
  intros; simpl. 
  destruct t, p.
  now simpl. 
  apply let_split_2.
  apply 0.
  apply (0,true).
  apply true.
  apply true.
  repeat split.
  simpl.
  assert (if_split: forall {A B C D:Type} (a:bool) (b c:(B*((A*C)*D))) (d: A), ((a= true -> fst (fst (snd b)) =d) /\ (a = false -> fst (fst (snd c)) = d)) ->
 fst (fst (snd(if a then b else c))) = d).
  intros; destruct H1, a; intuition.
  apply if_split.
  intros.
  case (upt_robot_dies_b
     (fun id : Identifiers.ident =>
      ((@frame_choice_bijection Loc _ _ (change_frame da config0 g)) (fst (config0 id)),
       snd (config0 id))) g);
  repeat (split; intros; intuition). 
  assert (if_split: forall {A B C D:Type} (a:bool) (b c:(B*((C*A)*D))) (d: A), ((a= true -> snd (fst (snd b)) =d) /\ (a = false -> snd (fst (snd c)) = d)) ->
 snd (fst (snd(if a then b else c))) = d).
  intros; destruct H1, a; intuition.
  apply if_split.
  intros.
  case (upt_robot_dies_b
     (fun id : Identifiers.ident =>
      ((@frame_choice_bijection Loc _ _ (change_frame da config0 g)) (fst (config0 id)),
       snd (config0 id))) g) eqn : Heq.
  repeat (split; intros). simpl.
  assert ((get_light (config0 (Good g))) = light). rewrite Hconf. simpl; intuition.
  rewrite <- H2.
  apply (reflexivity (get_light (config0 (Good g)))).
  simpl.
  assert (forall x, x = true -> x = false -> False).
  intros x Ht Hf; rewrite Ht in Hf.
  discriminate.
  exfalso.
  revert Heq H1.
  apply H2.
  simpl.
  split; simpl.
  intros.
  assert (forall x, x = true -> x = false -> False).
  intros x Ht Hf; rewrite Ht in Hf.
  discriminate.
  exfalso.
  revert H1 Heq.
  apply H2.
  intros.
  clear let_split_2 if_split Heq.
  unfold upt_robot_dies_b in H1.
  rewrite orb_false_iff in H1.
  destruct H1 as (_, Hfarther).
  rewrite Hconf in *.
  rewrite negb_false_iff in Hfarther.
  rewrite existsb_exists in Hfarther.
  destruct Hfarther as (other, (Hin,Hfarther)).
  destruct (@change_frame (R2 * ILA) Loc State_ILA Identifiers 
                       (R2 * NoCollisionAndPath.light) (R * R2 * bool) bool bool robot_choice_RL
                       Frame Choice inactive_choice_ila da config0 g) as ((rot,(tra1, tra2)), bool) eqn : Hchange.
  specialize (H (((retraction (let
                       '(r, t, b) := change_frame da config0 g in
                        comp (bij_rotation r)
                          (comp (bij_translation t)
                                (if b then reflexion else Similarity.id)))) (fst other)), snd other)).
  unfold get_location at 1 in Hfarther.
  unfold State_ILA, AddInfo, OnlyLocation in Hfarther.
  rewrite <- (section_retraction ((comp (bij_rotation rot)
                         (comp (bij_translation (tra1, tra2))
                            (if bool then reflexion else Similarity.id)))) (fst other))
    in Hfarther.
  rewrite Hchange in *.
  rewrite filter_In in Hin.
  destruct Hin as (_,Hid).
  rewrite andb_true_iff in Hid;
    destruct Hid as (Hid,Hal).
  rewrite Nat.ltb_lt in Hid.
  unfold get_ident in *; simpl in Hid; rewrite Hconf in Hid; simpl in Hid.
  specialize (H Hid).
  destruct other as (p_o, ((i_o, l_o), a_o)) eqn : Hother.
  unfold get_alive in *; simpl (snd _) in H ; specialize (H Hal).
  rewrite <- Rle_bool_true_iff in H.
  assert (true == false).
  { rewrite not_true_iff_false in H. rewrite <- H, <- Hfarther.
    f_equiv.
    assert (Hdist := frame_dist (fst (pos, (ident, light, alive)))
                                (retraction
          (comp (bij_rotation rot)
             (comp (bij_translation (tra1, tra2))
                (if bool then reflexion else Similarity.id))) 
          (fst (p_o, (i_o, l_o, a_o))))
                                ((rot,(tra1, tra2)), bool)).
      unfold frame_choice_bijection, Frame in Hdist.
      rewrite Hdist.
      rewrite dist_sym.
      unfold map_config.
      rewrite Hconf.
      destruct bool;
        simpl; intuition.
      
  }
  discriminate.

  + assert (if_split: forall {A B C:Type} (a:bool) (b c:(B*(C*A))) (d: A), ((a= true -> snd (snd b) = d) /\ (a = false -> snd (snd c) = d)) ->
 snd (snd(if a then b else c)) = d).
  intros; destruct H1, a; intuition.
  apply if_split.
  split; intros.
  - now simpl.
  - simpl. unfold upt_robot_dies_b in H1.
  rewrite orb_false_iff in H1.
  destruct H1 as (_, Hfarther).
  rewrite negb_false_iff in Hfarther.
  rewrite existsb_exists in Hfarther.
  destruct Hfarther as (other, (Hin,Hfarther)).
  destruct (@change_frame (R2 * ILA) Loc State_ILA Identifiers 
                       (R2 * NoCollisionAndPath.light) (R * R2 * bool) bool bool robot_choice_RL
                       Frame Choice inactive_choice_ila da config0 g) as ((rot,(tra1, tra2)), bool) eqn : Hchange.
  specialize (H (((retraction (let
                       '(r, t, b) := change_frame da config0 g in
                        comp (bij_rotation r)
                          (comp (bij_translation t)
                                (if b then reflexion else Similarity.id)))) (fst other)), snd other)).
  unfold get_location at 1 in Hfarther.
  unfold State_ILA, AddInfo, OnlyLocation in Hfarther.
  rewrite <- (section_retraction ((comp (bij_rotation rot)
                         (comp (bij_translation (tra1, tra2))
                            (if bool then reflexion else Similarity.id)))) (fst other))
    in Hfarther.
  rewrite Hchange in *.
  rewrite filter_In in Hin.
  destruct Hin as (_,Hid).
  rewrite andb_true_iff in Hid;
    destruct Hid as (Hid, Hal).
  rewrite Nat.ltb_lt in Hid.
  unfold get_alive in *; simpl (snd _) in *.
  unfold get_ident in *; simpl in Hid; rewrite Hconf in Hid; simpl in Hid.
  specialize (H Hid Hal).
  rewrite <- Rle_bool_true_iff in H.
  assert (true == false).
  { rewrite not_true_iff_false in H. rewrite <- H, <- Hfarther.
    f_equiv.
    assert (Hdist := frame_dist (fst (pos, (ident, light, alive)))
                                (retraction
          (comp (bij_rotation rot)
             (comp (bij_translation (tra1, tra2))
                (if bool then reflexion else Similarity.id))) 
          (fst other))
                                ((rot,(tra1, tra2)), bool)).
      unfold frame_choice_bijection, Frame in Hdist.
      rewrite Hdist.
      rewrite dist_sym.
      unfold map_config.
      rewrite Hconf.
      destruct bool;
        simpl; intuition.
  }
  discriminate.
  + apply H0. 
Qed.


Lemma robot_dead_means :
  forall config g (da:da_ila),
    da_predicat da ->
        get_alive (round rbg_ila da config (Good g)) == false
        -> get_alive (config (Good g)) == false
           \/ (exists g',
                  get_ident (config (Good g')) < get_ident (config (Good g)) /\
                  get_alive (config (Good g')) = true /\
                    Rle_bool (dist (get_location (config (Good g)))
                                   (get_location (config (Good g')))) D = true)
           \/ (forall g',
                  get_ident (config (Good g')) < get_ident (config (Good g)) ->
                  get_alive (config (Good g')) = true ->
                  negb (Rle_bool
                          (dist (get_location (config (Good g)))
                                (get_location (config (Good g')))) Dmax) = true).
Proof.
  intros config0 g da Hda_pred Hround.
  rewrite (round_good_g g config0 Hda_pred) in Hround.
  simpl in Hround.
  changeR2.
  unfold Datatypes.id in *.
  unfold upt_aux in *.
  destruct (config0 (Good g)) as (pos, ((ident, light), alive)) eqn : Hconfig.
  simpl in Hround.
  destruct (upt_robot_dies_b _) eqn : Hrobot_dies;
  simpl in Hround;
  unfold get_alive in *;
  simpl in Hround.
  -
    unfold upt_robot_dies_b in Hrobot_dies.
    rewrite orb_true_iff in Hrobot_dies; destruct Hrobot_dies as [Hex|Hneg].
    + rewrite existsb_exists in Hex.
      destruct Hex as (rila, (Hin,Hex)).
      right; left.
      rewrite filter_In in Hin.
      rewrite config_list_spec, in_map_iff in Hin.
      destruct Hin as ((id, HIn),Hid_low).      
      destruct (change_frame da config0 g) as ((r,t),b).
      rewrite Hconfig in *.
      destruct id as [g'|byz].
      simpl in Hid_low.
      exists (g').
      split.
      * destruct HIn as (Heq, _).
        rewrite <- Heq in Hid_low.
        unfold get_ident in *; simpl in *.
        rewrite andb_true_iff in *.
        destruct Hid_low as (?,?).
        rewrite Hconfig in *.
        now rewrite Nat.ltb_lt in *.
      * destruct HIn as (Heq, Hin).
        repeat simpl in Heq.
        unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location in *.
        unfold Datatypes.id in *.
        simpl (fst _) in *.
        assert (Heq' : (R2.bij_rotation_f r
                                          ((fst
                                              ((if b then reflexion else Similarity.id) (fst (config0 (Good g')))) +
                                            fst t)%R,
                                           (snd ((if b then reflexion else Similarity.id) (fst (config0 (Good g')))) +
                                            snd t)%R), snd (config0 (Good g'))) == rila) by now rewrite <- Heq.
        destruct Heq' as (Heq', Helse).
        rewrite (frame_dist pos (fst (config0 (Good g'))) (r,t,b)).
        rewrite <- Heq' in Hex.
        unfold frame_choice_bijection, Frame.
        rewrite andb_true_iff in *.
        destruct Hid_low as (Hid_low, Halive).
        split.
        -- unfold get_alive in Halive.
           destruct (config0 (Good g')) as (?,((?,?),?)) eqn : ?.
           simpl in Helse.
           destruct rila.
           simpl in *.
           destruct i0, p; simpl in *; intuition.
           now rewrite H2.
        -- destruct b; rewrite dist_sym; rewrite Hconfig in *;
             simpl in *;
             now rewrite Hex.
      * assert (Hbyz := @In_Bnames _ byz).
        unfold Bnames, Identifiers in *.
        now simpl in *.
    + rewrite  forallb_existsb, forallb_forall in Hneg.
      right; right.
      destruct (change_frame da config0 g) as ((r,t),b) eqn : Hchange.
      intros g' Hid Halive; specialize (Hneg ((comp (bij_rotation r)
                                             (comp (bij_translation t)
                                                   (if b then reflexion else Similarity.id)))
                                         (fst (config0 (Good g'))),
                                       snd (config0 (Good g')))).
      assert (Hin :@List.In (prod R2 ILA)
                 (@pair R2 ILA
                    (@section R2 R2_Setoid
                       (@comp R2 R2_Setoid (bij_rotation r)
                          (@comp R2 R2_Setoid
                             (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                             match b return (@bijection R2 R2_Setoid) with
                             | true =>
                                 @sim_f R2 R2_Setoid R2_EqDec VS
                                   (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                   reflexion
                             | false =>
                                 @sim_f R2 R2_Setoid R2_EqDec VS
                                   (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                   (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                            ES)))
                             end))
                       (@fst (@location Loc) ILA (config0 (@Good Identifiers g'))))
                    (@snd (@location Loc) ILA (config0 (@Good Identifiers g'))))
                 (@List.filter (prod R2 ILA)
                    (fun elt : prod R2 ILA =>
                     andb
                       (Nat.ltb (get_ident elt)
                          (get_ident
                             (@pair R2 ILA
                                (@section R2 R2_Setoid
                                   (@comp R2 R2_Setoid (bij_rotation r)
                                      (@comp R2 R2_Setoid
                                         (@bij_translation R2 R2_Setoid R2_EqDec VS
                                            t)
                                         (@sim_f R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid
                                                  R2_EqDec VS ES))
                                            match
                                              b
                                              return
                                                (@similarity R2 R2_Setoid R2_EqDec
                                                   VS
                                                   (@Normed2Metric R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                            with
                                            | true => reflexion
                                            | false =>
                                                @Similarity.id R2 R2_Setoid R2_EqDec
                                                  VS
                                                  (@Normed2Metric R2 R2_Setoid
                                                     R2_EqDec VS
                                                     (@Euclidean2Normed R2 R2_Setoid
                                                       R2_EqDec VS ES))
                                            end)))
                                   (@fst R2 ILA (config0 (@Good Identifiers g))))
                                (@snd R2 ILA (config0 (@Good Identifiers g))))))
                       (get_alive elt))
                    (@config_list Loc (prod R2 ILA) State_ILA Identifiers
                       (fun id : @Identifiers.ident Identifiers =>
                        @pair R2 ILA
                          (@section R2 R2_Setoid
                             (@comp R2 R2_Setoid (bij_rotation r)
                                (@comp R2 R2_Setoid
                                   (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                   (@sim_f R2 R2_Setoid R2_EqDec VS
                                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                            ES))
                                      match
                                        b
                                        return
                                          (@similarity R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES)))
                                      with
                                      | true => reflexion
                                      | false =>
                                          @Similarity.id R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid
                                                  R2_EqDec VS ES))
                                      end))) (@fst R2 ILA (config0 id)))
                          (@snd R2 ILA (config0 id)))))).
      { rewrite filter_In.
        split.
        * rewrite config_list_spec.
          rewrite in_map_iff.
          exists (Good g').
          split; intuition.
          destruct b; reflexivity.
          apply In_names.
        * rewrite andb_true_iff.
          unfold get_ident in *; simpl in *.
          split.
          rewrite Nat.ltb_lt in *.
          now rewrite Hconfig; simpl.
          now unfold get_alive; simpl.
      }
      specialize (Hneg Hin).
      rewrite <- Hneg.
      do 2 f_equiv.
      assert (Hdist := frame_dist pos (fst (config0 (Good g'))) ((r, t), b)).
      unfold frame_choice_bijection, Frame in Hdist.
      rewrite Hdist.
      unfold map_config.
      rewrite Hconfig in *.
      destruct b;
        rewrite dist_sym; simpl; intuition.
  
  - changeR2.
    left.
    rewrite Hconfig in Hround.
    unfold get_alive; simpl in *.
    apply Hround.
 Qed.




Lemma moving_means_light_off : forall conf g (da:da_ila),
    da_predicat da ->
    get_alive (round rbg_ila da conf (Good g)) = true -> 
    get_location (conf (Good g)) <> get_location (round rbg_ila da conf (Good g)) ->
    get_light (round rbg_ila da conf (Good g)) = false.
Proof.
  intros conf g da Hpred Halive Hmoving.
  rewrite (round_good_g g _ Hpred) in *.
  unfold rbg_ila, rbg_fnc in *.
  
  Set Printing Implicit.
  changeR2.
  set (s :=(obs_from_config _ _ )).
  destruct ( move_to s (choose_new_pos s (fst (choose_target s)))) eqn : Hmove.
  Unset Printing Implicit.
  simpl in *.
  fold s.
  fold s in Hmoving, Halive.
  rewrite Hmove in *.
  simpl in *.
  destruct (conf (Good g)) as (pos,((ident, light), alive))eqn : Hconf.
  simpl in *.
  changeR2.
  repeat cbn in *.
  rewrite Hconf in *; simpl in *.
  unfold get_alive in Halive; simpl in Halive.
  assert (ifsplit_al : forall {A B C D:Type} (a:bool) (b c:(D*((B*C)*A))) (d: A),  snd (snd(if a then b else c)) = d -> ((a= true -> snd (snd b) = d) /\ (a = false -> snd (snd c) = d))).
  intros; destruct H, a; intuition.
  apply ifsplit_al in Halive.
  destruct Halive as (Hfalse, Halive).
  unfold map_config in *.
  destruct ((upt_robot_dies_b
       (fun id : @Identifiers.ident Identifiers =>
        @pair R2 ILA
          (@section R2 R2_Setoid
             (let (p, b) :=
                @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                  (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                  robot_choice_RL Frame Choice inactive_choice_ila da conf g in
              let (r, t) := p in
              @comp R2 R2_Setoid (bij_rotation r)
                (@comp R2 R2_Setoid
                   (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                   (@sim_f R2 R2_Setoid R2_EqDec VS
                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                      (if b
                       then reflexion
                       else
                        @Similarity.id R2 R2_Setoid R2_EqDec VS
                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                             (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))))))
             (@fst R2 ILA (conf id))) (@snd R2 ILA (conf id))) g)) eqn : Heq.
  specialize (Hfalse (reflexivity true)).
  simpl in Hfalse.
  discriminate.
  specialize (Halive (reflexivity false)).
  destruct (change_frame da conf g) as ((r,t),b); simpl.
  now unfold get_light; simpl.
  destruct Hmoving.
  fold s.
  fold s in Halive.
  simpl in *.
  rewrite Hmove in *.
  destruct Hpred as (Horigin,_).
  unfold change_frame_origin in *.
  unfold get_alive in Halive.
  simpl in Halive.
  specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
  Set Printing Implicit.
  destruct ((@change_frame (R2 * ILA) Loc State_ILA Identifiers 
                  (R2 * light) (R * R2 * bool) bool bool robot_choice_RL Frame
                  Choice inactive_choice_ila da conf g)) as ((r,t),b) eqn : Hchange.
  unfold frame_choice_bijection, Frame in *.
  Unset Printing Implicit.
  unfold upt_aux in *.
  destruct (conf (Good g)) as (pos,((ident, light), alive))eqn : Hconf.
  replace (fst (pos, (ident, light, alive))) with pos by auto.
  unfold Datatypes.id.
  Set Printing All.
  destruct (upt_robot_dies_b
                          (fun id : @Identifiers.ident Identifiers =>
                           @pair R2 ILA
                             (R2.bij_rotation_f r
                                (@pair R R
                                   (Rplus
                                      (@fst R R
                                         (@section R2 R2_Setoid
                                            (@sim_f R2 R2_Setoid R2_EqDec VS
                                               (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                  VS
                                                  (@Euclidean2Normed R2 R2_Setoid
                                                     R2_EqDec VS ES))
                                               match
                                                 b
                                                 return
                                                   (@similarity R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                               with
                                               | true => reflexion
                                               | false =>
                                                   @Similarity.id R2 R2_Setoid
                                                     R2_EqDec VS
                                                     (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                               end) (@fst R2 ILA (conf id))))
                                      (@fst R R t))
                                   (Rplus
                                      (@snd R R
                                         (@section R2 R2_Setoid
                                            (@sim_f R2 R2_Setoid R2_EqDec VS
                                               (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                  VS
                                                  (@Euclidean2Normed R2 R2_Setoid
                                                     R2_EqDec VS ES))
                                               match
                                                 b
                                                 return
                                                   (@similarity R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                               with
                                               | true => reflexion
                                               | false =>
                                                   @Similarity.id R2 R2_Setoid
                                                     R2_EqDec VS
                                                     (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                               end) (@fst R2 ILA (conf id))))
                                      (@snd R R t)))) (@snd R2 ILA (conf id))) g) eqn : Heq.
  Unset Printing All.
  destruct b.
  simpl in *.
  unfold map_config in *.
  rewrite Heq, Hconf in Halive.
  simpl in *.  
  discriminate.
  assert ((fst
       (let (p, a) := snd (pos, (ident, light, alive)) in
        let (i, l) := p in
        if
         upt_robot_dies_b
           (fun id : Identifiers.ident =>
            ((comp (bij_rotation r) (comp (bij_translation t) Similarity.id))
               (fst (conf id)), snd (conf id))) g
        then
         ((comp (bij_rotation r) (comp (bij_translation t) Similarity.id))
            (fst (pos, (ident, light, alive))), (i, l, false))
        else (fst (0%R, 0%R, true), (i, snd (0%R, 0%R, true), a)))) ==
           (fst ((comp (bij_rotation r) (comp (bij_translation t) Similarity.id))
            (fst (pos, (ident, light, alive))), (ident, light, false)))).
  { simpl in *; rewrite Heq.
    now simpl.
  }
  unfold map_config in *.
  rewrite Hconf.
  rewrite H.
  replace ((fst
       ((comp (bij_rotation r) (comp (bij_translation t) Similarity.id))
          (fst (pos, (ident, light, alive))), (ident, light, false)))) with
      ((comp (bij_rotation r) (comp (bij_translation t) Similarity.id))
          (fst (pos, (ident, light, alive)))) by auto.
  now rewrite retraction_section.
  rewrite <- Horigin in *.
  assert (upt_robot_dies_b
          (fun id : Identifiers.ident =>
           (R2.bij_rotation_f r
              ((fst ((if b then reflexion else Similarity.id) (fst (conf id))) +
                fst t)%R,
              (snd ((if b then reflexion else Similarity.id) (fst (conf id))) +
               snd t)%R), snd (conf id))) g == upt_robot_dies_b
           (fun id : Identifiers.ident =>
            ((comp (bij_rotation r)
                (comp (bij_translation t) (if b then reflexion else Similarity.id)))
               (fst (conf id)), snd (conf id))) g).
  f_equiv.
  intros id; split; simpl; auto.
  destruct b; auto.  
  destruct (conf id) as ((?,?),?); simpl; auto.
  now destruct i, p.
  changeR2.
  assert ((let (p, a) := snd (pos, (ident, light, alive)) in
        let (i, l) := p in
        if
         upt_robot_dies_b
           (fun id : Identifiers.ident =>
            ((comp (bij_rotation r)
                (comp (bij_translation t) (if b then reflexion else Similarity.id)))
               (fst (conf id)), snd (conf id))) g
        then
         ((comp (bij_rotation r)
             (comp (bij_translation t) (if b then reflexion else Similarity.id)))
            (fst (pos, (ident, light, alive))), (i, l, false))
        else
         (fst
            ((rotation r
              ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
               (@get_location Loc _ _ (pos, (ident, light, alive))), true),
         (i,
         snd
           ((rotation r ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
              (@get_location Loc _ _ (pos, (ident, light, alive))), true), a)))
    ==
      (if
         upt_robot_dies_b
           (fun id : Identifiers.ident =>
            ((comp (bij_rotation r)
                (comp (bij_translation t) (if b then reflexion else Similarity.id)))
               (fst (conf id)), snd (conf id))) g
        then
         ((comp (bij_rotation r)
             (comp (bij_translation t) (if b then reflexion else Similarity.id)))
            (fst (pos, (ident, light, alive))), (ident, light, false))
        else
         (fst
            ((rotation r
              ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
               (get_location (pos, (ident, light, alive))), true),
         (ident,
         snd
           ((rotation r ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
              (get_location (pos, (ident, light, alive))), true), alive)))).
  repeat split; simpl.
  assert (let_split' : forall (A B C: Type) (x y : (A*B)*C), fst (fst x) = fst (fst y) /\ snd (fst x) = snd (fst y) /\ snd x = snd y -> let (p, a1) := x in let (i1, l1) := p in let (p0, a2) := y in let (i2,l2) := p0 in  i1 = i2 /\ l1 = l2 /\ a1 = a2).
  intros; destruct x as ((?,?),?), y as ((?,?),?); simpl in *; intuition.
  apply let_split'.
  repeat split; simpl.
  clear H0.
  unfold ILA in *.
  changeR2.
  
  assert (test :
            (upt_robot_dies_b
                     (fun id : @Identifiers.ident Identifiers =>
                      @pair (@location Loc)
                        (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                        (@section (@location Loc) (@location_Setoid Loc)
                           (@comp (@location Loc) (@location_Setoid Loc)
                              (bij_rotation r)
                              (@comp (@location Loc) (@location_Setoid Loc)
                                 (@bij_translation (@location Loc)
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS t)
                                 (@sim_f (@location Loc) 
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS
                                    (@Normed2Metric (@location Loc)
                                       (@location_Setoid Loc) 
                                       (@location_EqDec Loc) VS
                                       (@Euclidean2Normed 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS ES))
                                    match
                                      b
                                      return
                                        (@similarity (@location Loc)
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS
                                           (@Normed2Metric 
                                              (@location Loc) 
                                              (@location_Setoid Loc)
                                              (@location_EqDec Loc) VS
                                              (@Euclidean2Normed 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS ES)))
                                    with
                                    | true => reflexion
                                    | false =>
                                        @Similarity.id (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES))
                                    end)))
                           (@fst (@location Loc)
                              (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                              (conf id)))
                        (@snd (@location Loc)
                           (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive) 
                           (conf id))) g = true ->
            match
            @snd (@location Loc) (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
              (@pair (@location Loc) (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                 pos
                 (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                    (@pair identifiants NoCollisionAndPath.light ident light) alive))
            return
              (prod (@location Loc) (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
          with
          | pair p a =>
              match
                p
                return
                  (prod (@location Loc)
                     (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
              with
              | pair i l =>
                  match
                    upt_robot_dies_b
                      (fun id : @Identifiers.ident Identifiers =>
                       @pair (@location Loc)
                         (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                         (@section (@location Loc) (@location_Setoid Loc)
                            (@comp (@location Loc) (@location_Setoid Loc)
                               (bij_rotation r)
                               (@comp (@location Loc) (@location_Setoid Loc)
                                  (@bij_translation (@location Loc)
                                     (@location_Setoid Loc) 
                                     (@location_EqDec Loc) VS t)
                                  (@sim_f (@location Loc) 
                                     (@location_Setoid Loc) 
                                     (@location_EqDec Loc) VS
                                     (@Normed2Metric (@location Loc)
                                        (@location_Setoid Loc) 
                                        (@location_EqDec Loc) VS
                                        (@Euclidean2Normed 
                                           (@location Loc) 
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS ES))
                                     match
                                       b
                                       return
                                         (@similarity (@location Loc)
                                            (@location_Setoid Loc)
                                            (@location_EqDec Loc) VS
                                            (@Normed2Metric 
                                               (@location Loc)
                                               (@location_Setoid Loc)
                                               (@location_EqDec Loc) VS
                                               (@Euclidean2Normed 
                                                  (@location Loc)
                                                  (@location_Setoid Loc)
                                                  (@location_EqDec Loc) VS ES)))
                                     with
                                     | true => reflexion
                                     | false =>
                                         @Similarity.id 
                                           (@location Loc) 
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS
                                           (@Normed2Metric 
                                              (@location Loc) 
                                              (@location_Setoid Loc)
                                              (@location_EqDec Loc) VS
                                              (@Euclidean2Normed 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS ES))
                                     end)))
                            (@fst (@location Loc)
                               (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                               (conf id)))
                         (@snd (@location Loc)
                            (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive) 
                            (conf id))) g
                    return
                      (prod (@location Loc)
                         (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
                  with
                  | true =>
                      @pair (@location Loc)
                        (prod (prod identifiants NoCollisionAndPath.light) bool)
                        (@section (@location Loc) (@location_Setoid Loc)
                           (@comp (@location Loc) (@location_Setoid Loc)
                              (bij_rotation r)
                              (@comp (@location Loc) (@location_Setoid Loc)
                                 (@bij_translation (@location Loc)
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS t)
                                 (@sim_f (@location Loc) 
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS
                                    (@Normed2Metric (@location Loc)
                                       (@location_Setoid Loc) 
                                       (@location_EqDec Loc) VS
                                       (@Euclidean2Normed 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS ES))
                                    match
                                      b
                                      return
                                        (@similarity (@location Loc)
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS
                                           (@Normed2Metric 
                                              (@location Loc) 
                                              (@location_Setoid Loc)
                                              (@location_EqDec Loc) VS
                                              (@Euclidean2Normed 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS ES)))
                                    with
                                    | true => reflexion
                                    | false =>
                                        @Similarity.id (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES))
                                    end)))
                           (@fst (@location Loc)
                              (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                              (@pair (@location Loc)
                                 (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive) pos
                                 (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                                    (@pair identifiants NoCollisionAndPath.light ident light) alive))))
                        (@pair (prod identifiants NoCollisionAndPath.light) bool
                           (@pair identifiants NoCollisionAndPath.light i l) false)
                  | false =>
                      @pair (@location Loc)
                        (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                        (@fst (@location Loc) NoCollisionAndPath.light
                           (@pair (prod R R) bool
                              (@section (@location Loc) 
                                 (@location_Setoid Loc)
                                 (@sim_f (@location Loc) 
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS
                                    (@Normed2Metric (@location Loc)
                                       (@location_Setoid Loc) 
                                       (@location_EqDec Loc) VS
                                       (@Euclidean2Normed 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS ES))
                                    (@compose
                                       (@similarity (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES)))
                                       (@similarity_Setoid 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES)))
                                       (@SimilarityComposition 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES)))
                                       (rotation r)
                                       (@compose
                                          (@similarity (@location Loc)
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Normed2Metric 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Euclidean2Normed 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS ES)))
                                          (@similarity_Setoid 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Normed2Metric 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Euclidean2Normed 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS ES)))
                                          (@SimilarityComposition 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Normed2Metric 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Euclidean2Normed 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS ES)))
                                          (@translation 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES) t)
                                          match
                                            b
                                            return
                                              (@similarity 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS
                                                 (@Normed2Metric 
                                                    (@location Loc)
                                                    (@location_Setoid Loc)
                                                    (@location_EqDec Loc) VS
                                                    (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                          with
                                          | true => reflexion
                                          | false =>
                                              @Similarity.id 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES))
                                          end)))
                                 (@get_location Loc
                                    (prod (@location Loc)
                                       (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
                                    State_ILA
                                    (@pair (@location Loc)
                                       (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                                       pos
                                       (@pair (prod identifiants NoCollisionAndPath.light)
                                          NoCollisionAndPath.alive
                                          (@pair identifiants NoCollisionAndPath.light ident light)
                                          alive)))) true))
                        (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                           (@pair identifiants NoCollisionAndPath.light i
                              (@snd (@location Loc) NoCollisionAndPath.light
                                 (@pair (prod R R) bool
                                    (@section (@location Loc) 
                                       (@location_Setoid Loc)
                                       (@sim_f (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES))
                                          (@compose
                                             (@similarity 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES)))
                                             (@similarity_Setoid 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES)))
                                             (@SimilarityComposition 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES)))
                                             (rotation r)
                                             (@compose
                                                (@similarity 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Normed2Metric 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                (@similarity_Setoid 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Normed2Metric 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                (@SimilarityComposition
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Normed2Metric 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                (@translation 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES) t)
                                                match
                                                  b
                                                  return
                                                    (@similarity 
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS
                                                       (@Normed2Metric
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS
                                                       (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                with
                                                | true => reflexion
                                                | false =>
                                                    @Similarity.id 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Normed2Metric
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS
                                                       (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES))
                                                end)))
                                       (@get_location Loc
                                          (prod (@location Loc)
                                             (prod (prod identifiants NoCollisionAndPath.light)
                                                NoCollisionAndPath.alive)) State_ILA
                                          (@pair (@location Loc)
                                             (prod (prod identifiants NoCollisionAndPath.light)
                                                NoCollisionAndPath.alive) pos
                                             (@pair (prod identifiants NoCollisionAndPath.light)
                                                NoCollisionAndPath.alive
                                                (@pair identifiants NoCollisionAndPath.light ident
                                                   light) alive)))) true))) a)
                  end
              end
              end=
        let (p, a) := snd (pos, (ident, light, alive)) in
             let (i, l) := p in ((comp (bij_rotation r)
                      (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                   (fst (pos, (ident, light, alive))), (i, l, false))) /\
            (upt_robot_dies_b
                     (fun id : @Identifiers.ident Identifiers =>
                      @pair (@location Loc)
                        (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                        (@section (@location Loc) (@location_Setoid Loc)
                           (@comp (@location Loc) (@location_Setoid Loc)
                              (bij_rotation r)
                              (@comp (@location Loc) (@location_Setoid Loc)
                                 (@bij_translation (@location Loc)
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS t)
                                 (@sim_f (@location Loc) 
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS
                                    (@Normed2Metric (@location Loc)
                                       (@location_Setoid Loc) 
                                       (@location_EqDec Loc) VS
                                       (@Euclidean2Normed 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS ES))
                                    match
                                      b
                                      return
                                        (@similarity (@location Loc)
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS
                                           (@Normed2Metric 
                                              (@location Loc) 
                                              (@location_Setoid Loc)
                                              (@location_EqDec Loc) VS
                                              (@Euclidean2Normed 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS ES)))
                                    with
                                    | true => reflexion
                                    | false =>
                                        @Similarity.id (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES))
                                    end)))
                           (@fst (@location Loc)
                              (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                              (conf id)))
                        (@snd (@location Loc)
                           (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive) 
                           (conf id))) g = false ->
            match
            @snd (@location Loc) (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
              (@pair (@location Loc) (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                 pos
                 (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                    (@pair identifiants NoCollisionAndPath.light ident light) alive))
            return
              (prod (@location Loc) (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
          with
          | pair p a =>
              match
                p
                return
                  (prod (@location Loc)
                     (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
              with
              | pair i l =>
                  match
                    upt_robot_dies_b
                      (fun id : @Identifiers.ident Identifiers =>
                       @pair (@location Loc)
                         (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                         (@section (@location Loc) (@location_Setoid Loc)
                            (@comp (@location Loc) (@location_Setoid Loc)
                               (bij_rotation r)
                               (@comp (@location Loc) (@location_Setoid Loc)
                                  (@bij_translation (@location Loc)
                                     (@location_Setoid Loc) 
                                     (@location_EqDec Loc) VS t)
                                  (@sim_f (@location Loc) 
                                     (@location_Setoid Loc) 
                                     (@location_EqDec Loc) VS
                                     (@Normed2Metric (@location Loc)
                                        (@location_Setoid Loc) 
                                        (@location_EqDec Loc) VS
                                        (@Euclidean2Normed 
                                           (@location Loc) 
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS ES))
                                     match
                                       b
                                       return
                                         (@similarity (@location Loc)
                                            (@location_Setoid Loc)
                                            (@location_EqDec Loc) VS
                                            (@Normed2Metric 
                                               (@location Loc)
                                               (@location_Setoid Loc)
                                               (@location_EqDec Loc) VS
                                               (@Euclidean2Normed 
                                                  (@location Loc)
                                                  (@location_Setoid Loc)
                                                  (@location_EqDec Loc) VS ES)))
                                     with
                                     | true => reflexion
                                     | false =>
                                         @Similarity.id 
                                           (@location Loc) 
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS
                                           (@Normed2Metric 
                                              (@location Loc) 
                                              (@location_Setoid Loc)
                                              (@location_EqDec Loc) VS
                                              (@Euclidean2Normed 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS ES))
                                     end)))
                            (@fst (@location Loc)
                               (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                               (conf id)))
                         (@snd (@location Loc)
                            (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive) 
                            (conf id))) g
                    return
                      (prod (@location Loc)
                         (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
                  with
                  | true =>
                      @pair (@location Loc)
                        (prod (prod identifiants NoCollisionAndPath.light) bool)
                        (@section (@location Loc) (@location_Setoid Loc)
                           (@comp (@location Loc) (@location_Setoid Loc)
                              (bij_rotation r)
                              (@comp (@location Loc) (@location_Setoid Loc)
                                 (@bij_translation (@location Loc)
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS t)
                                 (@sim_f (@location Loc) 
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS
                                    (@Normed2Metric (@location Loc)
                                       (@location_Setoid Loc) 
                                       (@location_EqDec Loc) VS
                                       (@Euclidean2Normed 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS ES))
                                    match
                                      b
                                      return
                                        (@similarity (@location Loc)
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS
                                           (@Normed2Metric 
                                              (@location Loc) 
                                              (@location_Setoid Loc)
                                              (@location_EqDec Loc) VS
                                              (@Euclidean2Normed 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS ES)))
                                    with
                                    | true => reflexion
                                    | false =>
                                        @Similarity.id (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES))
                                    end)))
                           (@fst (@location Loc)
                              (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                              (@pair (@location Loc)
                                 (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive) pos
                                 (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                                    (@pair identifiants NoCollisionAndPath.light ident light) alive))))
                        (@pair (prod identifiants NoCollisionAndPath.light) bool
                           (@pair identifiants NoCollisionAndPath.light i l) false)
                  | false =>
                      @pair (@location Loc)
                        (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                        (@fst (@location Loc) NoCollisionAndPath.light
                           (@pair (prod R R) bool
                              (@section (@location Loc) 
                                 (@location_Setoid Loc)
                                 (@sim_f (@location Loc) 
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS
                                    (@Normed2Metric (@location Loc)
                                       (@location_Setoid Loc) 
                                       (@location_EqDec Loc) VS
                                       (@Euclidean2Normed 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS ES))
                                    (@compose
                                       (@similarity (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES)))
                                       (@similarity_Setoid 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES)))
                                       (@SimilarityComposition 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES)))
                                       (rotation r)
                                       (@compose
                                          (@similarity (@location Loc)
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Normed2Metric 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Euclidean2Normed 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS ES)))
                                          (@similarity_Setoid 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Normed2Metric 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Euclidean2Normed 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS ES)))
                                          (@SimilarityComposition 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Normed2Metric 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Euclidean2Normed 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS ES)))
                                          (@translation 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES) t)
                                          match
                                            b
                                            return
                                              (@similarity 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS
                                                 (@Normed2Metric 
                                                    (@location Loc)
                                                    (@location_Setoid Loc)
                                                    (@location_EqDec Loc) VS
                                                    (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                          with
                                          | true => reflexion
                                          | false =>
                                              @Similarity.id 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES))
                                          end)))
                                 (@get_location Loc
                                    (prod (@location Loc)
                                       (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive))
                                    State_ILA
                                    (@pair (@location Loc)
                                       (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                                       pos
                                       (@pair (prod identifiants NoCollisionAndPath.light)
                                          NoCollisionAndPath.alive
                                          (@pair identifiants NoCollisionAndPath.light ident light)
                                          alive)))) true))
                        (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                           (@pair identifiants NoCollisionAndPath.light i
                              (@snd (@location Loc) NoCollisionAndPath.light
                                 (@pair (prod R R) bool
                                    (@section (@location Loc) 
                                       (@location_Setoid Loc)
                                       (@sim_f (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES))
                                          (@compose
                                             (@similarity 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES)))
                                             (@similarity_Setoid 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES)))
                                             (@SimilarityComposition 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS
                                                (@Normed2Metric 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES)))
                                             (rotation r)
                                             (@compose
                                                (@similarity 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Normed2Metric 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                (@similarity_Setoid 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Normed2Metric 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                (@SimilarityComposition
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Normed2Metric 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                (@translation 
                                                   (@location Loc)
                                                   (@location_Setoid Loc)
                                                   (@location_EqDec Loc) VS
                                                   (@Euclidean2Normed
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS ES) t)
                                                match
                                                  b
                                                  return
                                                    (@similarity 
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS
                                                       (@Normed2Metric
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS
                                                       (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES)))
                                                with
                                                | true => reflexion
                                                | false =>
                                                    @Similarity.id 
                                                      (@location Loc)
                                                      (@location_Setoid Loc)
                                                      (@location_EqDec Loc) VS
                                                      (@Normed2Metric
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS
                                                       (@Euclidean2Normed
                                                       (@location Loc)
                                                       (@location_Setoid Loc)
                                                       (@location_EqDec Loc) VS ES))
                                                end)))
                                       (@get_location Loc
                                          (prod (@location Loc)
                                             (prod (prod identifiants NoCollisionAndPath.light)
                                                NoCollisionAndPath.alive)) State_ILA
                                          (@pair (@location Loc)
                                             (prod (prod identifiants NoCollisionAndPath.light)
                                                NoCollisionAndPath.alive) pos
                                             (@pair (prod identifiants NoCollisionAndPath.light)
                                                NoCollisionAndPath.alive
                                                (@pair identifiants NoCollisionAndPath.light ident
                                                   light) alive)))) true))) a)
                  end
              end
              end= let (p, a) := snd (pos, (ident, light, alive)) in
             let (i, l) := p in (fst
            ((rotation r
              ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
               (get_location (pos, (ident, light, alive))), true),
         (i,
         snd
           ((rotation r ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
              (get_location (pos, (ident, light, alive))), true), a))) ).
  intros.
  changeR2.
  
  Unset Printing All.
  split; intros.
  rewrite H0.
  simpl.
  destruct b.
  simpl.
  unfold bij_reflexion_f, R2.bij_rotation_f.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  rewrite H0.
  simpl.
  reflexivity.
  
  unfold map_config.
  rewrite Hconf.
  destruct (upt_robot_dies_b
                     (fun id : @Identifiers.ident Identifiers =>
                      @pair (@location Loc)
                        (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                        (@section (@location Loc) (@location_Setoid Loc)
                           (@comp (@location Loc) (@location_Setoid Loc)
                              (bij_rotation r)
                              (@comp (@location Loc) (@location_Setoid Loc)
                                 (@bij_translation (@location Loc)
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS t)
                                 (@sim_f (@location Loc) 
                                    (@location_Setoid Loc) 
                                    (@location_EqDec Loc) VS
                                    (@Normed2Metric (@location Loc)
                                       (@location_Setoid Loc) 
                                       (@location_EqDec Loc) VS
                                       (@Euclidean2Normed 
                                          (@location Loc) 
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS ES))
                                    match
                                      b
                                      return
                                        (@similarity (@location Loc)
                                           (@location_Setoid Loc)
                                           (@location_EqDec Loc) VS
                                           (@Normed2Metric 
                                              (@location Loc) 
                                              (@location_Setoid Loc)
                                              (@location_EqDec Loc) VS
                                              (@Euclidean2Normed 
                                                 (@location Loc)
                                                 (@location_Setoid Loc)
                                                 (@location_EqDec Loc) VS ES)))
                                    with
                                    | true => reflexion
                                    | false =>
                                        @Similarity.id (@location Loc)
                                          (@location_Setoid Loc)
                                          (@location_EqDec Loc) VS
                                          (@Normed2Metric 
                                             (@location Loc) 
                                             (@location_Setoid Loc)
                                             (@location_EqDec Loc) VS
                                             (@Euclidean2Normed 
                                                (@location Loc)
                                                (@location_Setoid Loc)
                                                (@location_EqDec Loc) VS ES))
                                    end)))
                           (@fst (@location Loc)
                              (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive)
                              (conf id)))
                        (@snd (@location Loc)
                           (prod (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive) 
                           (conf id))) g).
  destruct test as (Htrue, Hfalse).
  specialize (Htrue (reflexivity _)).
  rewrite Htrue.
  rewrite <- (retraction_section (comp (bij_rotation r)
       (comp (bij_translation t) (if b then reflexion else Similarity.id)))) at 1.
  simpl.
  destruct b; simpl; intuition.
  destruct test as (Htrue, Hfalse).
  specialize (Hfalse (reflexivity _)).
  rewrite Hfalse.
  simpl.
  rewrite <- (retraction_section (comp (bij_rotation r)
       (comp (bij_translation t) (if b then reflexion else Similarity.id)))) at 1.
  simpl.
  destruct b; simpl; intuition.
Qed.



Definition no_collision_conf (conf : config) :=
  forall g g',
    g <> g' ->
    get_alive (conf (Good g)) = true -> get_alive (conf (Good g')) = true -> 
    dist (get_location (conf (Good g))) (get_location (conf (Good g'))) <> 0%R.

Definition no_collision (e:(@execution (R2*ILA) Loc State_ILA _ )):=
  forall (config:config) (demon:demon_ila_type),
    e = @execute (R2*ILA) Loc State_ILA _ _ _ _ _ _ robot_choice_RL Frame _ _ UpdFun _ rbg_ila demon config ->
    @Stream.forever NoCollisionAndPath.config (Stream.instant no_collision_conf) e.


Definition path_conf (conf:config) :=
  forall g, get_alive (conf (Good g)) = true ->
            (get_ident (conf (Good g)) = 0 \/
             (exists g', get_alive (conf (Good g')) = true /\
                         (dist (get_location (conf (Good g))) (get_location (conf (Good g'))) <= Dmax)%R /\
                         get_ident (conf (Good g')) < get_ident (conf (Good g)))).




Definition exists_path (e:execution) :=
  forall (config:config) (demon:demon_ila_type),
    e = @execute (R2*ILA) Loc State_ILA _ _ _ _ _ _ robot_choice_RL Frame _ _ UpdFun _ rbg_ila demon config ->
    Stream.forever (Stream.instant path_conf) e.



Lemma no_collision_init : forall config_init, config_init_pred config_init ->
                                              no_collision_conf config_init.
Proof.
  intros config_init Hinit; destruct Hinit as (lower, (off, close)).
  unfold config_init_not_close in close.
  unfold no_collision_conf.
  intros g g' Hg Halive Halive'.
  specialize (close (Good g)); destruct (config_init (Good g)) as (?,((?,?),?)).
  specialize (close (Good g')). destruct (config_init (Good g')) as (?,((?,?),?)).
  simpl in *.
  unfold Datatypes.id.
  set (dist := sqrt
             ((@fst R R r + - @fst R R r0) * (@fst R R r + - @fst R R r0) +
              (@snd R R r + - @snd R R r0) * (@snd R R r + - @snd R R r0))).
  fold dist in close.
  assert (D_0 := D_0).
  lra.
Qed.

Lemma paht_conf_init : forall config_init, config_init_pred config_init ->
                                           path_conf config_init.
Proof.
  intros conf_init Hconf_pred.
  unfold path_conf.
  intros g Halive.
  unfold config_init_pred in Hconf_pred.
  unfold config_init_not_close, config_init_lower, config_init_off in Hconf_pred.
  destruct Hconf_pred as (Hconf_lower, (Hconf_off, Hconf_not_close)).
  specialize (Hconf_lower (Good g)).
  destruct (conf_init (Good g)) as (pos,((ident,light), alive)) eqn : Hconf_init.
  unfold get_alive in *; simpl in Halive.
  specialize (Hconf_lower Halive).
  destruct Hconf_lower as [Hconf_lower_0|Hconf_lower_other].
  left.
  unfold get_ident; simpl in *; auto.
  right.
  destruct Hconf_lower_other as ([g_other|byz], Hother).
  destruct (conf_init (Good g_other)) as (p_other,((i_other, l_other), a_other)) eqn : Hconf_other.
  exists g_other.
  rewrite Hconf_other.
  unfold get_ident.
  unfold get_location, State_ILA, AddInfo, OnlyLocation , get_location.
  repeat split; try (now simpl in *).
  simpl (fst _).
  unfold Datatypes.id.
  intuition.
  assert (Hfalse := In_Bnames byz).
  now simpl in *.
Qed.
                     
Lemma still_alive_means_alive :
  forall conf g (da:da_ila),
    da_predicat da ->
    get_alive (round rbg_ila da conf (Good g)) = true ->
    get_alive(conf (Good g)) = true.
Proof.
  intros conf g da Hpred Halive_r.
  rewrite round_good_g in Halive_r.
  simpl in *.
  unfold get_alive in *; simpl in *. 
  unfold upt_aux in *.
  destruct (conf (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  simpl in *.
  unfold map_config in *.
  destruct (upt_robot_dies_b
                         (fun id : @Identifiers.ident Identifiers =>
                          @pair R2 ILA
                            (@section R2 R2_Setoid
                               match
                                 @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                                   (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool
                                   bool robot_choice_RL Frame Choice
                                   inactive_choice_ila da conf g
                                 return (@bijection R2 R2_Setoid)
                               with
                               | pair p b =>
                                   match p return (@bijection R2 R2_Setoid) with
                                   | pair r t =>
                                       @comp R2 R2_Setoid 
                                         (bij_rotation r)
                                         (@comp R2 R2_Setoid
                                            (@bij_translation R2 R2_Setoid R2_EqDec
                                               VS t)
                                            (@sim_f R2 R2_Setoid R2_EqDec VS
                                               (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                  VS
                                                  (@Euclidean2Normed R2 R2_Setoid
                                                     R2_EqDec VS ES))
                                               match
                                                 b
                                                 return
                                                   (@similarity R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                               with
                                               | true => reflexion
                                               | false =>
                                                   @Similarity.id R2 R2_Setoid
                                                     R2_EqDec VS
                                                     (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                               end))
                                   end
                               end (@fst R2 ILA (conf id))) 
                            (@snd R2 ILA (conf id))) g);
  rewrite Hconf in *;
  simpl in *;
  try discriminate; auto.
  
  apply Hpred.
Qed.



Lemma dist_round_max_d : forall g conf da,
    da_predicat da ->
    path_conf conf ->
    get_alive (conf (Good g)) == true ->
    Rle_bool (dist (get_location (conf (Good g)))
                   (get_location (round rbg_ila da conf (Good g))))
             D == true.
Proof.
  intros g conf da Hpred Hpath Halive.
  rewrite (round_good_g g conf Hpred).
  destruct (conf (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  simpl (get_location _).
  destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange. 
  unfold upt_aux.
  rewrite Hconf; simpl (upt_robot_dies_b _).
  destruct (upt_robot_dies_b _) eqn : Hupt.
  - unfold Datatypes.id.
    unfold map_config.
    rewrite Hconf.
    simpl (fst _).
    destruct b.
    replace ((R2.bij_rotation_f r
                              ((fst (reflexion pos) + fst t)%R, (snd (reflexion pos) + snd t)%R)))
    with ((comp (bij_rotation r) (comp (bij_translation t) reflexion)) pos) by now simpl.
    rewrite retraction_section.
    rewrite R2_dist_defined_2.
    generalize D_0; simpl; rewrite Rle_bool_true_iff.
    lra.
    replace ((R2.bij_rotation_f r
             ((fst (Similarity.id pos) + fst t)%R,
             (snd (Similarity.id pos) + snd t)%R)))
    with ((comp (bij_rotation r) (comp (bij_translation t) Similarity.id)) pos) by now simpl.
    rewrite retraction_section.
    rewrite R2_dist_defined_2.
    generalize D_0; simpl; rewrite Rle_bool_true_iff.
    lra.
  - unfold rbg_fnc.
    destruct (move_to _) eqn : Hmove.
    set (new_pos := choose_new_pos _ _ ).
    set (spect := obs_from_config _ _ ) in *. 
    assert (Hcorrect := @choose_new_pos_correct spect (fst
                  (choose_target spect)) new_pos).
    destruct Hcorrect.
    unfold new_pos. reflexivity.
    fold new_pos.
    simpl (fst _).
    apply Rlt_le in H0. rewrite <- Rle_bool_true_iff in H0.
    rewrite <- H0.
    f_equiv.
    rewrite (frame_dist _ _ (r,t,b)), dist_sym.
    destruct Hpred as (Hori, _).
    revert Hori; intro Hori.
    unfold change_frame_origin in *.
    specialize (Hori conf g (r,t,b) Hchange).
    unfold frame_choice_bijection, Frame in *.
    simpl (_ ∘ _) in *.
    unfold Datatypes.id.
    rewrite section_retraction.
    rewrite Hconf in Hori.
    simpl (get_location _) in Hori.
    unfold Datatypes.id in *.
    rewrite Hori.
    unfold new_pos.
    rewrite Hconf in *. 
    simpl in *. destruct b; reflexivity.
    destruct Hpred as (Hori, _).
    revert Hori; intro Hori.
    unfold change_frame_origin in *.
    specialize (Hori conf g (r,t,b) Hchange).
    unfold frame_choice_bijection, Frame in *.
    simpl (_ ∘ _) in *.
    unfold map_config.
    rewrite Hconf.
    simpl (fst _).
    rewrite <- Hori.
    rewrite retraction_section.
    rewrite Hconf; simpl (get_location _); unfold Datatypes.id; rewrite dist_same.
    generalize D_0. simpl equiv. rewrite Rle_bool_true_iff; lra.
    Qed.


Lemma moving_means_not_near : forall conf (da:da_ila) g,
    da_predicat da ->
    path_conf conf ->
    get_location (conf (Good g)) <> get_location (round rbg_ila da conf (Good g))
    -> get_alive (round rbg_ila da conf (Good g)) = true
    -> ((dist (get_location (conf (Good g)))
            (get_location (round rbg_ila da conf (Good g)))
            <= D)%R
        /\ (forall g', get_ident (conf (Good g')) < get_ident (conf (Good g))
                       -> get_alive (conf (Good g')) = true
                       -> (Rle_bool (dist (get_location (conf (Good g'))) (get_location ((round rbg_ila da conf (Good g))))) (2*D) == false)%R)
        /\ (exists g', get_ident (conf (Good g')) < get_ident (conf (Good g)) /\
                       get_alive (conf (Good g')) = true /\
                   ((Rle_bool (dist (get_location (conf (Good g'))) (get_location (round rbg_ila da conf (Good g)))) Dp) == true)%R)).
Proof.
  intros conf da g Hpred Hpath Hmove Halive.
  destruct (round rbg_ila da conf (Good g)) as (p_round, ((i_round, l_round), a_round)) eqn : Hconf_round.
  assert (Hconf_round' : round rbg_ila da conf (Good g) == (p_round, ((i_round, l_round), a_round))) by now rewrite Hconf_round.
  rewrite <- Hconf_round in *.
  rewrite round_good_g in *; try apply Hpred.
  simpl (get_location _) in *.
  simpl in Halive, Hconf_round'.
  unfold upt_aux, rbg_fnc, Datatypes.id in *.
  unfold map_config in *.
  destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
  destruct (conf (Good g)) as (pos, ((i,l),a)) eqn : Hconf.
  simpl (fst _) in *.
  set (Hdies := upt_robot_dies_b
                         (fun id : @ident Identifiers =>
                          @pair R2 ILA
                            (R2.bij_rotation_f r
                               (@pair R R
                                  (Rplus
                                     (@fst R R
                                        (@section R2 R2_Setoid
                                           (@sim_f R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                 VS
                                                 (@Euclidean2Normed R2 R2_Setoid
                                                    R2_EqDec VS ES))
                                              match
                                                b
                                                return
                                                  (@similarity R2 R2_Setoid R2_EqDec
                                                     VS
                                                     (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                              with
                                              | true => reflexion
                                              | false =>
                                                  @Similarity.id R2 R2_Setoid
                                                    R2_EqDec VS
                                                    (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                              end) (@fst R2 ILA (conf id))))
                                     (@fst R R t))
                                  (Rplus
                                     (@snd R R
                                        (@section R2 R2_Setoid
                                           (@sim_f R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                 VS
                                                 (@Euclidean2Normed R2 R2_Setoid
                                                    R2_EqDec VS ES))
                                              match
                                                b
                                                return
                                                  (@similarity R2 R2_Setoid R2_EqDec
                                                     VS
                                                     (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                              with
                                              | true => reflexion
                                              | false =>
                                                  @Similarity.id R2 R2_Setoid
                                                    R2_EqDec VS
                                                    (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                              end) (@fst R2 ILA (conf id))))
                                     (@snd R R t)))) (@snd R2 ILA (conf id))) g).
  repeat fold Hdies in *.
  unfold get_alive in Halive.
  simpl (snd (let (p,a) := snd (conf  (Good g)) in _)) in Halive, Hconf_round'.
  destruct Hdies eqn : Hd.
  simpl in Halive.
  - unfold Hdies in Hd.
    rewrite Hd in Halive.
    simpl in Halive.
    discriminate.
  -  simpl in Halive; unfold Hdies in Hd; rewrite Hd in Halive.
     simpl in Halive.
     destruct (move_to _) eqn : Hmove_to.
     + set (new_pos := choose_new_pos _ _).
       assert (Hchoose_new_pos_dist := @choose_new_pos_correct _ _ (new_pos) (reflexivity _)).
       repeat split.
       * apply Rlt_le.
         
         rewrite dist_sym;
         destruct Hchoose_new_pos_dist as (_,Hchoose);
         
         rewrite (frame_dist _ pos ((r,t),b)) in *.
         destruct Hpred.
         specialize (H conf g ((r,t),b) Hchange).
         rewrite Hconf in H.
         simpl (let bij := frame_choice_bijection (r, t, b) in _ ) in H.
         unfold frame_choice_bijection, Frame.
         simpl (rotation _ ∘ _).
         rewrite section_retraction.
         simpl (((Similarity.comp (rotation r)
         (Similarity.comp (translation t) (if b then reflexion else Similarity.id)))
                   pos)).
         revert H.
         destruct b;
         unfold Datatypes.id;
         intros H; rewrite H; 
         simpl (fst _);
         apply Hchoose.
         (*  
       assert (Hmove_some := move_to_Some_zone Hmove_to ).
       destruct Hmove_some as (Hdp, (Hd0, H2D)).
       repeat split.
       *)
       * assert (Hmove_some := move_to_Some_zone Hmove_to ).
         fold new_pos in Hmove_some.
         unfold equiv, bool_Setoid, bool_eqdec, eq_setoid.
         intros g' Hident' Halive_g'.
         rewrite Rle_bool_false_iff.
         apply Rgt_not_le.
         destruct (Rle_lt_dec (dist (fst (conf (Good g'))) pos) Dmax).
         assert ((((fun id : ident =>
        (R2.bij_rotation_f r
           ((fst ((if b then reflexion else Similarity.id) (fst (conf id))) + fst t)%R,
           (snd ((if b then reflexion else Similarity.id) (fst (conf id))) + snd t)%R),
        snd (conf id))) (Good g'))
                         ∈ obs_from_config
                    (fun id : ident =>
                     (R2.bij_rotation_f r
                        ((fst ((if b then reflexion else Similarity.id) (fst (conf id))) + fst t)%R,
                        (snd ((if b then reflexion else Similarity.id) (fst (conf id))) + snd t)%R),
                     snd (conf id)))
                    (R2.bij_rotation_f r
                       ((fst ((if b then reflexion else Similarity.id) pos) + fst t)%R,
                       (snd ((if b then reflexion else Similarity.id) pos) + snd t)%R),
                    (i, l, a)))%set).
         unfold obs_from_config, Spect_ILA.
         rewrite make_set_spec, filter_InA.
         split.
         rewrite config_list_InA.
         exists (Good g').
         reflexivity.
         

         (* destruct Hmove_some as (Hdp, (Hd0, H2D)). *)
         rewrite andb_true_iff.
         split.
         -- simpl (fst _).
            assert (Hframe_dist := frame_dist (fst (conf (Good g'))) pos ((r,t),b)).
            unfold frame_choice_bijection, Frame in Hframe_dist.
            simpl (rotation _ ∘ _) in Hframe_dist.
            simpl.
            simpl in *; rewrite <- Hframe_dist.
            rewrite 2 andb_true_iff. repeat split; try rewrite Rle_bool_true_iff; auto.
         -- unfold get_ident in *; simpl in *.
            rewrite Nat.leb_le; omega.
         -- intros x y Hxy.
            destruct x as (rx,((ix,lx),ax)), y as (ry,((iy,ly),ay)).
            simpl in Hxy.
            destruct Hxy as (Hr,(Hi,(Hl,Ha))).
            simpl (fst _); simpl  (snd _).
            rewrite Hr,Hl,Hi,Ha.
            reflexivity.
         -- specialize (Hmove_some ((fun id : ident =>
        (R2.bij_rotation_f r
           ((fst ((if b then reflexion else Similarity.id) (fst (conf id))) + fst t)%R,
           (snd ((if b then reflexion else Similarity.id) (fst (conf id))) + snd t)%R),
        snd (conf id))) (Good g'))). 
            specialize (Hmove_some H).
            rewrite Hd in Hconf_round'.
            simpl in Hconf_round'.
            fold new_pos in Hconf_round'.
            destruct Hconf_round' as (Hpos_round, _).
            revert Hpos_round; intros Hpos_round.
            clear H.
            rewrite Hconf_round.
            simpl (fst (_,_)).
            rewrite <- Hpos_round.
            rewrite (frame_dist _ _ ((r,t),b)).
            unfold frame_choice_bijection, Frame.
            simpl (_ ∘ _).
            assert (Hsec_ret := section_retraction ((Similarity.comp (rotation r)
                                                                     (Similarity.comp (translation t) (if b then reflexion else Similarity.id)))) new_pos).
            simpl (retraction _) in Hsec_ret.
            assert (((Similarity.comp (rotation r)
         (Similarity.comp (translation t) (if b then reflexion else Similarity.id)))
        (retraction (if b then reflexion else Similarity.id)
           (Rgeom.xr (fst new_pos) (snd new_pos) (- r) + - fst t,
           Rgeom.yr (fst new_pos) (snd new_pos) (- r) + - snd t))) == new_pos)%R.
            destruct b; simpl in *; auto.
            destruct b; rewrite H;
            rewrite dist_sym; apply Hmove_some.
         -- assert (Hd_round' := dist_round_max_d g' Hpred Hpath Halive_g').
            unfold equiv, bool_Setoid, eq_setoid in Hd_round'.
            rewrite Rle_bool_true_iff in Hd_round'.
            unfold get_location, State_ILA, AddInfo, OnlyLocation in Hd_round'.
            unfold get_location, State_ILA, AddInfo, OnlyLocation in Hd_round'.
            unfold Datatypes.id in *.

            assert (Dmax - D < dist (fst (round rbg_ila da conf (Good g'))) pos)%R.
            generalize Dmax_6D.
            intros Dmax_6D.
            assert (Htri := RealMetricSpace.triang_ineq (fst (conf (Good g'))) (fst (round rbg_ila da conf (Good g'))) pos).
            assert (Htri' : (dist (fst (conf (Good g'))) (fst (round rbg_ila da conf (Good g'))) +
                             dist (fst (round rbg_ila da conf (Good g'))) pos <= D + dist (fst (round rbg_ila da conf (Good g'))) pos )%R).
            apply Rplus_le_compat_r.
            assumption.
            lra.
            assert (Hd_round := dist_round_max_d g Hpred Hpath).
            unfold get_alive in Hd_round.
            rewrite Hconf in *.
            simpl (snd _) in Hd_round.
            specialize (Hd_round Halive).
            simpl (get_location _) in Hd_round.
            unfold Datatypes.id in *.
            unfold equiv, bool_Setoid, eq_setoid in Hd_round.
            rewrite Rle_bool_true_iff in Hd_round.
            set (d2_r := (@fst R2 ILA
                           (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                              (prod R2 light) (prod (prod R R2) bool) bool bool
                              robot_choice_RL Frame Choice inactive_choice_ila
                              UpdFun inactive_ila rbg_ila da conf 
                              (@Good Identifiers g)))) in *.
            set (d1 := (fst (conf (Good g')))) in *.
            set (d1_r := (@fst R2 ILA
                               (@round (R2 * ILA) Loc State_ILA Identifiers Spect_ILA 
           (R2 * light) (R * R2 * bool) bool bool robot_choice_RL Frame Choice
           inactive_choice_ila UpdFun inactive_ila rbg_ila da conf 
           (@Good Identifiers g)))) in *.
            unfold equiv, bool_Setoid, eq_setoid.
            apply Rnot_le_gt. 
            intro.
            generalize Dmax_6D.
            intros Dmax_6D.
            unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id, equiv, bool_Setoid, eq_setoid in Hd_round; simpl (fst _) in *.
            assert (6*D < dist d1 pos)%R by lra.
            assert (2*D <  dist d1 d2_r)%R.
            { assert (Htri := RealMetricSpace.triang_ineq d1 d2_r pos).
              assert (Htri' : (3*D < dist d1 d2_r +
          dist d2_r pos)%R).
              generalize D_0.
              lra.
              apply (Rplus_lt_reg_l D).
              rewrite dist_sym in Hd_round.
              assert (3*D - dist d2_r pos < dist d1 d2_r)%R by lra.
              assert (Hrlelt := Rplus_lt_le_compat (3 * D - dist d2_r pos) (dist d1 d2_r) (dist d2_r pos) D H2 Hd_round).
              replace (3 * D - dist d2_r pos + dist d2_r pos)%R with (dist d2_r pos + (3*D - dist d2_r pos))%R in Hrlelt.
              rewrite Rplus_minus in Hrlelt.
              lra.
              replace ((dist d2_r pos + (3 * D - dist d2_r pos))%R) with
                  (dist d2_r pos + 3 * D - dist d2_r pos)%R by lra.
              assert (Hr : forall (x y z:R), (x + y - z = y - z + x)%R).
              intros.
              replace (x + y - z)%R with (x + (y - z))%R.
              rewrite  Rplus_comm. lra.
              lra.
              apply Hr.
            }
            apply (Rle_not_lt _ _ H0 H2).
       * set ( spect := ( obs_from_config _ _ )) in *.
         assert (Hin_spect := choose_target_in_spect (reflexivity (choose_target spect))).
         assert (Hg: exists g0, (R2.bij_rotation_f r
           ((fst ((if b then reflexion else Similarity.id) (fst (conf (Good g0)))) +
             fst t)%R,
           (snd ((if b then reflexion else Similarity.id) (fst (conf (Good g0)))) +
            snd t)%R), snd (conf (Good g0))) == choose_target spect).
         { unfold spect, obs_from_config, Spect_ILA in Hin_spect.
           rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff in Hin_spect.
           destruct Hin_spect as ((id,Hin), (Hdist, Halive_g')).
           destruct id as [g0|byz].
           unfold spect, obs_from_config, Spect_ILA.
           exists g0.
           symmetry.
           apply Hin.
           assert (b_In := In_Bnames byz).
           now simpl in b_In.
           intros x y Hxy.
           simpl in Hxy.
           destruct x as (rx,((ix,lx),ax)),
                    y as (ry,((iy,ly),ay)),
                    Hxy as (Hr, (Hi, (Hl, Ha))).                             
           simpl in Hr;
             rewrite Hr, Hi, Hl, Ha.
           reflexivity.
         }
         destruct Hg as (g', Hg).
         exists g'.
         assert (Hlower := @target_lower
                             spect (choose_target spect)
                             ((fun id : ident =>
                                 (R2.bij_rotation_f
                                    r
                                    ((fst ((if b then reflexion
                                            else Similarity.id) (fst (conf id))) +
                                      fst t)%R,
                                     (snd ((if b then reflexion
                                            else Similarity.id) (fst (conf id))) +
                                      snd t)%R), snd (conf id)))
                                (Good g))).
         assert (Heq : (fun id : ident =>
                          (R2.bij_rotation_f r
                                             ((fst ((if b then reflexion else Similarity.id) (fst (conf id))) +
                                               fst t)%R,
                                              (snd ((if b then reflexion else Similarity.id) (fst (conf id))) +
                                               snd t)%R), snd (conf id))) (Good g) == ((0,0)%R, snd (conf (Good g)))).
         destruct Hpred as (Horigin,_).
         specialize (Horigin conf g (r,t,b) Hchange).
         simpl in Horigin.
         unfold Datatypes.id in Horigin.
         now rewrite Horigin.
         repeat split. 
         ++ destruct Hpred as (Horigin,_).
            specialize (Horigin conf g (r,t,b) Hchange).
            simpl in Horigin.
            unfold Datatypes.id in Horigin.
            assert (Hin_l : ((fun id : ident =>
                                (R2.bij_rotation_f r
                                                   ((fst ((if b then reflexion else Similarity.id) (fst (conf id))) +
                                                     fst t)%R,
                                                    (snd ((if b then reflexion else Similarity.id) (fst (conf id))) +
                                                     snd t)%R), snd (conf id))) (Good g) ∈ spect)%set).
            { rewrite Heq.
              unfold spect, obs_from_config, Spect_ILA.
              rewrite make_set_spec, filter_InA, config_list_InA.
              
              split.          
              -- exists (Good g).
                 now rewrite Horigin.
              -- rewrite Hconf in Horigin.  
                 rewrite <- Horigin.
                 simpl (fst _ ) in *.
                 rewrite dist_same.
                 repeat rewrite andb_true_iff;
                   split; intuition.
                 generalize Dmax_6D, D_0.
                 rewrite Rle_bool_true_iff.
                 lra.
                 unfold get_alive.
                 now rewrite Hconf; simpl.
                 rewrite Hconf in *. 
                 unfold get_ident; simpl.
                 rewrite Nat.leb_le.
                 omega.
              -- intros (?,((?,?),?)) (?,((?,?),?)) (Hr,(Hi,(Hl, Ha))).
                 simpl in *.
                 now rewrite Ha, Hl, Hr, Hi. }
            specialize (Hlower Hin_l).
            clear Hin_l.
            assert ( get_location
                       ((fun id : ident =>
                           (R2.bij_rotation_f r
                                              ((fst ((if b then reflexion else Similarity.id) (fst (conf id))) +
                                                fst t)%R,
                                               (snd ((if b then reflexion else Similarity.id) (fst (conf id))) +
                                                snd t)%R), snd (conf id))) (Good g)) = 
                     (0%R, 0%R)).
            {
              rewrite Horigin.
              now simpl in *.
            }
            specialize (Hlower H (reflexivity _)); clear H.
            simpl in Hlower.
            assert (Hident_g : forall g0, get_ident (R2.bij_rotation_f r
                                                                       ((fst ((if b then reflexion else Similarity.id) (fst (conf (Good g0)))) +
                                                                         fst t)%R,
                                                                        (snd ((if b then reflexion else Similarity.id) (fst (conf (Good g0)))) +
                                                                         snd t)%R), snd (conf (Good g0))) == get_ident (conf (Good g0))).
            unfold get_ident; now simpl.
            rewrite <- Hconf, <- 2 Hident_g.
            rewrite Hg.
            apply Hlower.
         ++ assert (Ht_alive := choose_target_alive (symmetry Hg)).
            now unfold get_alive in *; simpl in *.
         ++ assert (Hgood := @round_good_g g conf da Hpred).
            rewrite Hconf_round.
            simpl (fst (_,_)).
            destruct Hconf_round' as (Hpos_round, _).
            rewrite <- Hpos_round.
            rewrite Hd.
            rewrite (frame_dist _ _ ((r,t),b)).
            unfold frame_choice_bijection, Frame.
            simpl (_ ∘ _).
            assert (Hsec_ret := section_retraction ((Similarity.comp (rotation r)
                                                                     (Similarity.comp (translation t) (if b then reflexion else Similarity.id)))) new_pos).
            simpl (retraction _) in Hsec_ret.
            assert (((Similarity.comp (rotation r)
         (Similarity.comp (translation t) (if b then reflexion else Similarity.id)))
        (retraction (if b then reflexion else Similarity.id)
           (Rgeom.xr (fst new_pos) (snd new_pos) (- r) + - fst t,
           Rgeom.yr (fst new_pos) (snd new_pos) (- r) + - snd t))) == new_pos)%R.
            destruct b; simpl in *; auto.
            fold spect in new_pos.
            fold new_pos.
            destruct b; rewrite H;
              rewrite dist_sym;
            revert Hg; intro Hg;
            destruct Hchoose_new_pos_dist as (Htarg, _);
            revert Htarg; intro Htarg;
            rewrite <- (fst_compat (Hg)) in Htarg;
            unfold equiv, bool_Setoid, eq_setoid;
            rewrite Rle_bool_true_iff;
            simpl in *; lra. 
     + rewrite Hd in Hmove.
       simpl ((fst (fst (0%R, 0%R, true), (i, snd (0%R, 0%R, true), a)))) in Hmove.
       destruct Hpred as (Horigin,_).
       specialize (Horigin conf g (r,t,b) Hchange).
       destruct Hmove.
       rewrite <- Horigin.
       unfold frame_choice_bijection, Frame.
       assert ((@retraction R2 R2_Setoid
       (@comp R2 R2_Setoid (bij_rotation r)
          (@comp R2 R2_Setoid (@bij_translation R2 R2_Setoid R2_EqDec VS t)
             (@sim_f R2 R2_Setoid R2_EqDec VS
                (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                   (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                match
                  b
                  return
                    (@similarity R2 R2_Setoid R2_EqDec VS
                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                with
                | true => reflexion
                | false =>
                    @Similarity.id R2 R2_Setoid R2_EqDec VS
                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                end)))
       (@section (@location Loc) (@location_Setoid Loc)
          (@sim_f R2 R2_Setoid R2_EqDec R2_VS
             (@Normed2Metric R2 R2_Setoid R2_EqDec R2_VS
                (@Euclidean2Normed R2 R2_Setoid R2_EqDec R2_VS R2_ES))
             (@compose
                (@similarity R2 R2_Setoid R2_EqDec R2_VS
                   (@Normed2Metric R2 R2_Setoid R2_EqDec R2_VS
                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec R2_VS R2_ES)))
                (@similarity_Setoid R2 R2_Setoid R2_EqDec R2_VS
                   (@Normed2Metric R2 R2_Setoid R2_EqDec R2_VS
                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec R2_VS R2_ES)))
                (@SimilarityComposition R2 R2_Setoid R2_EqDec R2_VS
                   (@Normed2Metric R2 R2_Setoid R2_EqDec R2_VS
                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec R2_VS R2_ES)))
                (rotation r)
                (@compose
                   (@similarity R2 R2_Setoid R2_EqDec VS
                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                   (@similarity_Setoid R2 R2_Setoid R2_EqDec VS
                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                   (@SimilarityComposition R2 R2_Setoid R2_EqDec VS
                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                   (@translation R2 R2_Setoid R2_EqDec VS
                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES) t)
                   match
                     b
                     return
                       (@similarity R2 R2_Setoid R2_EqDec VS
                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                             (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                   with
                   | true => reflexion
                   | false =>
                       @Similarity.id R2 R2_Setoid R2_EqDec VS
                         (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                            (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                   end)))
          (@get_location Loc (prod R2 ILA) State_ILA (conf (@Good Identifiers g)))))
         ==
         ((retraction
              (comp (bij_rotation r)
              (comp (bij_translation t) (if b then reflexion else Similarity.id)))) 
              ((comp (bij_rotation r)
                     (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                  (get_location (conf (Good g)))))).
       destruct b; unfold Similarity.id; simpl in *; auto.
       rewrite H.
       rewrite retraction_section.
       rewrite Hconf; simpl.
       auto.  
Qed.



(*
Lemma not_moving_means_near_or_dangerous :
  forall conf (da:da_ila) g,
    da_predicat da ->
    get_location (conf (Good g)) == get_location (round rbg_ila da conf (Good g))
    -> get_alive (round rbg_ila da conf (Good g)) = true
    -> (* move_to_some but of 0 *)
    ( (forall g', get_ident (conf (Good g')) < get_ident (conf (Good g))
                       -> get_alive (conf (Good g')) = true
                       -> (Rle_bool (dist (get_location (conf (Good g'))) (get_location ((round rbg_ila da conf (Good g))))) (2*D) == false)%R)
    /\ (exists g', get_ident (conf (Good g')) < get_ident (conf (Good g)) /\
                   ((Rle_bool (dist (get_location (conf (Good g'))) (get_location (round rbg_ila da conf (Good g)))) Dp) == true)%R))
    \/
    (* move_to_none *)
    (* forall pot_pos, dist pot_pos g < D -> forall g', ident g' < ident g -> 
       dist g' pot_pos <= 2D \/  COMMENT PARLER DE LA CIBLE DU SPECTRE SANS RENTRER DANS LES DETAILS*)




    
    (forall pot_pos, dist (get_location (conf (Good g))) pot_pos > D \/
                 (exists other, (get_ident other < get_ident  (conf (Good g)))
                                /\ (dist (get_location other) pot_pos <= 2 * D)%R)
                   \/ (dist (fst (choose_target spect)) (fst (conf (Good g))) > Dp)
    ).
*)



(* d'autre propriété sur les conf global en utilisant les axioms de move_to mais les énoncé ne mentionnent pas move_to.  *)



  
Lemma no_collision_cont : forall (conf:config) (da:da_ila),
    no_collision_conf conf -> da_predicat da ->
    path_conf conf ->
    no_collision_conf (round rbg_ila da conf).
Proof.
  intros conf da no_col Hpred Hpath g g' Hg Halive Halive'.
  specialize (no_col g g' Hg).
  specialize (no_col (still_alive_means_alive conf g Hpred Halive) (still_alive_means_alive conf g' Hpred Halive')).
  destruct (R2_EqDec (@get_location Loc _ _ (conf (Good g))) (@get_location Loc _ _ (round rbg_ila da conf (Good g)))%R);
    destruct (R2_EqDec (@get_location Loc _ _ (conf (Good g'))) (@get_location Loc _ _ (round rbg_ila da conf (Good g')))%R).
  - now rewrite <- e, <- e0.
  - assert (Hmove := moving_means_not_near g' Hpred Hpath c Halive').
    destruct Hmove as (HD, (H2d, Hdp)).
    specialize (H2d g).
    destruct ((leb (get_ident (conf (Good g'))) (get_ident (conf (Good g)))))
             eqn : Hident.
    + rewrite Nat.leb_le in Hident.
      destruct (Rle_bool (dist (get_location (conf (Good g'))) (get_location (conf (Good g)))) D) eqn : Hdist_D.
      * rewrite round_good_g in Halive; try apply Hpred.
        unfold get_alive in Halive; 
          simpl in Halive.
        destruct (conf (Good g)) as (pos, ((id, li),al)) eqn : Hconf.
        simpl in Halive. 
        unfold upt_aux in Halive.
        destruct (upt_robot_dies_b _) eqn : Htrue.
        unfold map_config in *; rewrite Hconf in Halive.
        now simpl in Halive.
        unfold map_config in *.
        rewrite Hconf in Halive; simpl in Halive.
        unfold upt_robot_dies_b in Htrue.
        rewrite orb_false_iff in Htrue.
        destruct Htrue as (Htrue,_).
        rewrite <- negb_true_iff in Htrue.
        rewrite forallb_existsb, forallb_forall in Htrue.
        destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
        specialize (Htrue (((comp (bij_rotation r)
                         (comp (bij_translation t)
                               (if b then reflexion else Similarity.id))) (fst (conf (Good g')))), snd (conf (Good g')))).
        assert (@List.In (prod R2 ILA)
                  (@pair R2 ILA
                     (@section R2 R2_Setoid
                        (@comp R2 R2_Setoid (bij_rotation r)
                           (@comp R2 R2_Setoid
                              (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                              match b return (@bijection R2 R2_Setoid) with
                              | true =>
                                  @sim_f R2 R2_Setoid R2_EqDec VS
                                    (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                       (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                          ES)) reflexion
                              | false =>
                                  @sim_f R2 R2_Setoid R2_EqDec VS
                                    (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                       (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                          ES))
                                    (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec
                                             VS ES)))
                              end)) (@fst R2 ILA (conf (@Good Identifiers g'))))
                     (@snd R2 ILA (conf (@Good Identifiers g'))))
                  (@List.filter (prod R2 ILA)
                     (fun elt : prod R2 ILA =>
                      andb
                        (Nat.ltb (get_ident elt)
                           (get_ident
                              (@pair R2 ILA
                                 (@section R2 R2_Setoid
                                    (@comp R2 R2_Setoid 
                                       (bij_rotation r)
                                       (@comp R2 R2_Setoid
                                          (@bij_translation R2 R2_Setoid R2_EqDec VS
                                             t)
                                          (@sim_f R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                             match
                                               b
                                               return
                                                 (@similarity R2 R2_Setoid R2_EqDec
                                                    VS
                                                    (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                             with
                                             | true => reflexion
                                             | false =>
                                                 @Similarity.id R2 R2_Setoid
                                                   R2_EqDec VS
                                                   (@Normed2Metric R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                             end)))
                                    (@fst R2 ILA (conf (@Good Identifiers g))))
                                 (@snd R2 ILA (conf (@Good Identifiers g))))))
                        (get_alive elt))
                     (@config_list Loc (prod R2 ILA) State_ILA Identifiers
                        (fun id : @ident Identifiers =>
                         @pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    (@sim_f R2 R2_Setoid R2_EqDec VS
                                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec
                                             VS ES))
                                       match
                                         b
                                         return
                                           (@similarity R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                 VS
                                                 (@Euclidean2Normed R2 R2_Setoid
                                                    R2_EqDec VS ES)))
                                       with
                                       | true => reflexion
                                       | false =>
                                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                       end))) (@fst R2 ILA (conf id)))
                           (@snd R2 ILA (conf id)))))). 
        { rewrite filter_In.
          rewrite config_list_spec.
          rewrite in_map_iff.
          repeat split; simpl.
          exists (Good g').
          split; auto.
          destruct b; simpl; auto.
          apply In_names.
          generalize (ident_unique conf Hg).
          rewrite Hconf; 
            unfold get_ident in *; simpl in *; auto.
          apply le_lt_or_eq in Hident.
          rewrite andb_true_iff.
          destruct Hident; auto.
          split; try now rewrite Nat.ltb_lt.
          apply (still_alive_means_alive _ _ Hpred) in Halive'.
          now unfold get_alive in *; simpl.
        }
        specialize (Htrue H).
        clear H.
        assert (Hframe := frame_dist (fst (conf (Good g'))) (fst (conf (Good g))) (r,t,b)).
        unfold frame_choice_bijection, Frame in Hframe.

        assert (dist (fst (conf (Good g'))) (fst (conf (Good g))) ==
                (@dist (@location Loc) (@location_Setoid Loc)
                     (@location_EqDec Loc) VS
                     (@Normed2Metric (@location Loc) (@location_Setoid Loc)
                        (@location_EqDec Loc) VS
                        (@Euclidean2Normed (@location Loc) 
                           (@location_Setoid Loc) (@location_EqDec Loc) VS ES))
                     (@get_location Loc (prod R2 ILA) State_ILA
                        (@pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    match b return (@bijection R2 R2_Setoid) with
                                    | true =>
                                        @sim_f R2 R2_Setoid R2_EqDec VS
                                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                             (@Euclidean2Normed R2 R2_Setoid
                                                R2_EqDec VS ES)) reflexion
                                    | false =>
                                        @sim_f R2 R2_Setoid R2_EqDec VS
                                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                             (@Euclidean2Normed R2 R2_Setoid
                                                R2_EqDec VS ES))
                                          (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES)))
                                    end)) (@fst R2 ILA (conf (@Good Identifiers g'))))
                           (@snd R2 ILA (conf (@Good Identifiers g')))))
                     (@get_location Loc (prod R2 ILA) State_ILA
                        (@pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    (@sim_f R2 R2_Setoid R2_EqDec VS
                                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec
                                             VS ES))
                                       match
                                         b
                                         return
                                           (@similarity R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                 VS
                                                 (@Euclidean2Normed R2 R2_Setoid
                                                    R2_EqDec VS ES)))
                                       with
                                       | true => reflexion
                                       | false =>
                                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                       end))) (@fst R2 ILA (conf (@Good Identifiers g))))
                           (@snd R2 ILA (conf (@Good Identifiers g))))))).
        rewrite Hframe.
        destruct b; simpl in *; auto.
        rewrite <- H in Htrue; clear H.
        rewrite Hconf in *. clear Hframe.
        simpl in *; unfold Datatypes.id in *;
          rewrite Hdist_D in Htrue.
        exfalso; apply no_fixpoint_negb in Htrue; auto.
      * rewrite Rle_bool_false_iff in Hdist_D.
        apply Rnot_le_lt in Hdist_D.
        assert (Hdist' :( 0 < dist (get_location (round rbg_ila da conf (Good g'))) (get_location (conf (Good g))))%R).
        { set (x := (get_location (round rbg_ila da conf (Good g')))) in *;
            set (y := (get_location (conf (Good g')))) in *;
            set (z := (get_location (conf (Good g)))) in *.
          apply Rlt_Rminus in Hdist_D.
          assert (dist y z - D <= dist y z - dist y x)%R.
          lra.
          assert (Htri := RealMetricSpace.triang_ineq y x z).
          assert (dist y z - dist y x <= dist x z)%R by lra.
          lra.
        }
        rewrite <- e. rewrite dist_sym. lra.
    + rewrite Nat.leb_gt in Hident.
      specialize (H2d Hident ((still_alive_means_alive conf g Hpred Halive))).
      unfold equiv, bool_Setoid, eq_setoid in H2d.
      rewrite Rle_bool_false_iff in H2d.
      intros Hd; destruct H2d.
      rewrite e, Hd.
      generalize D_0;
      lra.
  - assert (Hmove := moving_means_not_near g Hpred Hpath c Halive).
    destruct Hmove as (HD, (H2d, Hdp)).
    specialize (H2d g').
    destruct ((leb (get_ident (conf (Good g))) (get_ident (conf (Good g')))))
             eqn : Hident.
    + rewrite Nat.leb_le in Hident.
      destruct (Rle_bool (dist (get_location (conf (Good g))) (get_location (conf (Good g')))) D) eqn : Hdist_D.
      * rewrite round_good_g in Halive'; try apply Hpred.
        unfold get_alive in Halive'; 
          simpl in Halive'.
        destruct (conf (Good g')) as (pos, ((id, li),al)) eqn : Hconf.
        simpl in Halive'. 
        unfold upt_aux in Halive'.
        destruct (upt_robot_dies_b _) eqn : Htrue.
        unfold map_config in *;
        rewrite Hconf in Halive'; 
          now simpl in Halive'.
        unfold map_config in *;
        rewrite Hconf in Halive'; simpl in Halive'.
        unfold upt_robot_dies_b in Htrue.
        rewrite orb_false_iff in Htrue.
        destruct Htrue as (Htrue,_).
        rewrite <- negb_true_iff in Htrue.
        rewrite forallb_existsb, forallb_forall in Htrue.
        destruct (change_frame da conf g') as ((r,t),b) eqn : Hchange.
        specialize (Htrue (((comp (bij_rotation r)
                         (comp (bij_translation t)
                            (if b then reflexion else Similarity.id))) (fst (conf (Good g)))), snd (conf (Good g)))).
        assert (@List.In (prod R2 ILA)
                  (@pair R2 ILA
                     (R2.bij_rotation_f r
                        (@pair R R
                           (Rplus
                              (@fst R R
                                 (@section R2 R2_Setoid
                                    match b return (@bijection R2 R2_Setoid) with
                                    | true => bij_reflexion
                                    | false => @Bijection.id R2 R2_Setoid
                                    end (@fst R2 ILA (conf (@Good Identifiers g)))))
                              (@fst R R t))
                           (Rplus
                              (@snd R R
                                 (@section R2 R2_Setoid
                                    match b return (@bijection R2 R2_Setoid) with
                                    | true => bij_reflexion
                                    | false => @Bijection.id R2 R2_Setoid
                                    end (@fst R2 ILA (conf (@Good Identifiers g)))))
                              (@snd R R t)))) (@snd R2 ILA (conf (@Good Identifiers g))))
                  (@List.filter (prod R2 ILA)
                     (fun elt : prod R2 ILA =>
                      andb
                        (Nat.ltb
                           (@fst identifiants light
                              (@fst (prod identifiants light) alive
                                 (@snd R2 ILA elt)))
                           (@fst identifiants light
                              (@fst (prod identifiants light) alive
                                 (@snd R2 ILA (conf (@Good Identifiers g'))))))
                        (get_alive elt))
                     (@config_list Loc (prod R2 ILA) State_ILA Identifiers
                        (fun id : @ident Identifiers =>
                         @pair R2 ILA
                           (R2.bij_rotation_f r
                              (@pair R R
                                 (Rplus
                                    (@fst R R
                                       (@section R2 R2_Setoid
                                          (@sim_f R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                             match
                                               b
                                               return
                                                 (@similarity R2 R2_Setoid R2_EqDec
                                                    VS
                                                    (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                             with
                                             | true => reflexion
                                             | false =>
                                                 @Similarity.id R2 R2_Setoid
                                                   R2_EqDec VS
                                                   (@Normed2Metric R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                             end) (@fst R2 ILA (conf id))))
                                    (@fst R R t))
                                 (Rplus
                                    (@snd R R
                                       (@section R2 R2_Setoid
                                          (@sim_f R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                             match
                                               b
                                               return
                                                 (@similarity R2 R2_Setoid R2_EqDec
                                                    VS
                                                    (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                             with
                                             | true => reflexion
                                             | false =>
                                                 @Similarity.id R2 R2_Setoid
                                                   R2_EqDec VS
                                                   (@Normed2Metric R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                             end) (@fst R2 ILA (conf id))))
                                    (@snd R R t)))) (@snd R2 ILA (conf id)))))). 
        { rewrite filter_In.
          rewrite config_list_spec.
          rewrite in_map_iff.
          repeat split; simpl.
          exists (Good g).
          split; auto.
          destruct b; simpl; auto.
          apply In_names.
          generalize (ident_unique conf Hg).
          rewrite Hconf; 
            unfold get_ident in *; simpl in *; auto.
          rewrite andb_true_iff.
          split. 
          rewrite Nat.ltb_lt.
          apply le_lt_or_eq in Hident.
          destruct Hident.
          auto.
          now destruct H.
          apply (still_alive_means_alive _ _ Hpred) in Halive.
          unfold get_alive in *; simpl in *; auto.
        }
        specialize (Htrue H).
        clear H.
        assert (Hframe := frame_dist (fst (conf (Good g))) (fst (conf (Good g'))) (r,t,b)).
        unfold frame_choice_bijection, Frame in Hframe.

        assert (dist (fst (conf (Good g))) (fst (conf (Good g'))) ==
                (@dist (@location Loc) (@location_Setoid Loc)
                     (@location_EqDec Loc) VS
                     (@Normed2Metric (@location Loc) (@location_Setoid Loc)
                        (@location_EqDec Loc) VS
                        (@Euclidean2Normed (@location Loc) 
                           (@location_Setoid Loc) (@location_EqDec Loc) VS ES))
                     (@get_location Loc (prod R2 ILA) State_ILA
                        (@pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    match b return (@bijection R2 R2_Setoid) with
                                    | true =>
                                        @sim_f R2 R2_Setoid R2_EqDec VS
                                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                             (@Euclidean2Normed R2 R2_Setoid
                                                R2_EqDec VS ES)) reflexion
                                    | false =>
                                        @sim_f R2 R2_Setoid R2_EqDec VS
                                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                             (@Euclidean2Normed R2 R2_Setoid
                                                R2_EqDec VS ES))
                                          (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES)))
                                    end)) (@fst R2 ILA (conf (@Good Identifiers g))))
                           (@snd R2 ILA (conf (@Good Identifiers g)))))
                     (@get_location Loc (prod R2 ILA) State_ILA
                        (@pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    (@sim_f R2 R2_Setoid R2_EqDec VS
                                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec
                                             VS ES))
                                       match
                                         b
                                         return
                                           (@similarity R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                 VS
                                                 (@Euclidean2Normed R2 R2_Setoid
                                                    R2_EqDec VS ES)))
                                       with
                                       | true => reflexion
                                       | false =>
                                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                       end))) (@fst R2 ILA (conf (@Good Identifiers g'))))
                           (@snd R2 ILA (conf (@Good Identifiers g'))))))).
        rewrite Hframe.
        destruct b; simpl in *; auto.
        rewrite <- H in Htrue; clear H.
        rewrite Hconf in *. clear Hframe.
        simpl in *; unfold Datatypes.id in *;
          rewrite Hdist_D in Htrue.
        exfalso; apply no_fixpoint_negb in Htrue; auto.
        * rewrite Rle_bool_false_iff in Hdist_D.
          intros H_0.
          apply Hdist_D.
          rewrite e.
          assert (Htri := RealMetricSpace.triang_ineq (get_location (conf (Good g))) (get_location (round rbg_ila da conf (Good g))) (get_location (round rbg_ila da conf (Good g')))).
          rewrite H_0 in Htri.
          lra.
    + rewrite Nat.leb_gt in Hident.
      specialize (H2d Hident ((still_alive_means_alive conf g' Hpred Halive'))).
      unfold equiv, bool_Setoid, eq_setoid in H2d.
      rewrite Rle_bool_false_iff in H2d.
      intros Hd; destruct H2d.
      rewrite dist_sym.
      rewrite e, Hd.
      generalize D_0;
      lra.
  - assert (Hmove := moving_means_not_near g Hpred Hpath c Halive).
    destruct Hmove as (HD, (H2d, Hdp)).
    specialize (H2d g').
    destruct ((leb (get_ident (conf (Good g))) (get_ident (conf (Good g')))))
             eqn : Hident.
    + rewrite Nat.leb_le in Hident.
      destruct (Rle_bool (dist (get_location (conf (Good g))) (get_location (conf (Good g')))) D) eqn : Hdist_D.
      * rewrite round_good_g in Halive'; try apply Hpred.
        unfold get_alive in Halive'; 
          simpl in Halive'.
        destruct (conf (Good g')) as (pos, ((id, li),al)) eqn : Hconf.
        simpl in Halive'. 
        unfold upt_aux in Halive'.
        destruct (upt_robot_dies_b _) eqn : Htrue.
        unfold map_config in *;
        rewrite Hconf in Halive'; 
          now simpl in Halive'.
        unfold map_config in *;
        rewrite Hconf in Halive'; simpl in Halive'.
        unfold upt_robot_dies_b in Htrue.
        rewrite orb_false_iff in Htrue.
        destruct Htrue as (Htrue,_).
        rewrite <- negb_true_iff in Htrue.
        rewrite forallb_existsb, forallb_forall in Htrue.
        destruct (change_frame da conf g') as ((r,t),b) eqn : Hchange.
        specialize (Htrue (((comp (bij_rotation r)
                         (comp (bij_translation t)
                            (if b then reflexion else Similarity.id))) (fst (conf (Good g)))), snd (conf (Good g)))).
        assert (@List.In (prod R2 ILA)
                  (@pair R2 ILA
                     (@section R2 R2_Setoid
                        (@comp R2 R2_Setoid (bij_rotation r)
                           (@comp R2 R2_Setoid
                              (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                              match b return (@bijection R2 R2_Setoid) with
                              | true =>
                                  @sim_f R2 R2_Setoid R2_EqDec VS
                                    (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                       (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                          ES)) reflexion
                              | false =>
                                  @sim_f R2 R2_Setoid R2_EqDec VS
                                    (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                       (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                          ES))
                                    (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec
                                             VS ES)))
                              end)) (@fst R2 ILA (conf (@Good Identifiers g))))
                     (@snd R2 ILA (conf (@Good Identifiers g))))
                  (@List.filter (prod R2 ILA)
                     (fun elt : prod R2 ILA =>
                      andb
                        (Nat.ltb (get_ident elt)
                           (get_ident
                              (@pair R2 ILA
                                 (@section R2 R2_Setoid
                                    (@comp R2 R2_Setoid 
                                       (bij_rotation r)
                                       (@comp R2 R2_Setoid
                                          (@bij_translation R2 R2_Setoid R2_EqDec VS
                                             t)
                                          (@sim_f R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                             match
                                               b
                                               return
                                                 (@similarity R2 R2_Setoid R2_EqDec
                                                    VS
                                                    (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                             with
                                             | true => reflexion
                                             | false =>
                                                 @Similarity.id R2 R2_Setoid
                                                   R2_EqDec VS
                                                   (@Normed2Metric R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                             end)))
                                    (@fst R2 ILA (conf (@Good Identifiers g'))))
                                 (@snd R2 ILA (conf (@Good Identifiers g'))))))
                        (get_alive elt))
                     (@config_list Loc (prod R2 ILA) State_ILA Identifiers
                        (fun id : @ident Identifiers =>
                         @pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    (@sim_f R2 R2_Setoid R2_EqDec VS
                                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec
                                             VS ES))
                                       match
                                         b
                                         return
                                           (@similarity R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                 VS
                                                 (@Euclidean2Normed R2 R2_Setoid
                                                    R2_EqDec VS ES)))
                                       with
                                       | true => reflexion
                                       | false =>
                                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                       end))) (@fst R2 ILA (conf id)))
                           (@snd R2 ILA (conf id)))))). 
        { rewrite filter_In.
          rewrite config_list_spec.
          rewrite in_map_iff.
          repeat split; simpl.
          exists (Good g).
          split; auto.
          destruct b; simpl; auto.
          apply In_names.
          generalize (ident_unique conf Hg).
          rewrite Hconf; 
            unfold get_ident in *; simpl in *; auto.
          apply le_lt_or_eq in Hident.
          destruct Hident; auto.
          rewrite andb_true_iff.
          split; try now rewrite Nat.ltb_lt.
          apply (still_alive_means_alive _ _ Hpred) in Halive;
            unfold get_alive in *; simpl in *; auto.
        }
        specialize (Htrue H).
        clear H.
        assert (Hframe := frame_dist (fst (conf (Good g))) (fst (conf (Good g'))) (r,t,b)).
        unfold frame_choice_bijection, Frame in Hframe.

        assert (dist (fst (conf (Good g))) (fst (conf (Good g'))) ==
                (@dist (@location Loc) (@location_Setoid Loc)
                     (@location_EqDec Loc) VS
                     (@Normed2Metric (@location Loc) (@location_Setoid Loc)
                        (@location_EqDec Loc) VS
                        (@Euclidean2Normed (@location Loc) 
                           (@location_Setoid Loc) (@location_EqDec Loc) VS ES))
                     (@get_location Loc (prod R2 ILA) State_ILA
                        (@pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    match b return (@bijection R2 R2_Setoid) with
                                    | true =>
                                        @sim_f R2 R2_Setoid R2_EqDec VS
                                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                             (@Euclidean2Normed R2 R2_Setoid
                                                R2_EqDec VS ES)) reflexion
                                    | false =>
                                        @sim_f R2 R2_Setoid R2_EqDec VS
                                          (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                             (@Euclidean2Normed R2 R2_Setoid
                                                R2_EqDec VS ES))
                                          (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES)))
                                    end)) (@fst R2 ILA (conf (@Good Identifiers g))))
                           (@snd R2 ILA (conf (@Good Identifiers g)))))
                     (@get_location Loc (prod R2 ILA) State_ILA
                        (@pair R2 ILA
                           (@section R2 R2_Setoid
                              (@comp R2 R2_Setoid (bij_rotation r)
                                 (@comp R2 R2_Setoid
                                    (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                    (@sim_f R2 R2_Setoid R2_EqDec VS
                                       (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                          (@Euclidean2Normed R2 R2_Setoid R2_EqDec
                                             VS ES))
                                       match
                                         b
                                         return
                                           (@similarity R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                 VS
                                                 (@Euclidean2Normed R2 R2_Setoid
                                                    R2_EqDec VS ES)))
                                       with
                                       | true => reflexion
                                       | false =>
                                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                       end))) (@fst R2 ILA (conf (@Good Identifiers g'))))
                           (@snd R2 ILA (conf (@Good Identifiers g'))))))).
        rewrite Hframe.
        destruct b; simpl in *; auto.
        rewrite <- H in Htrue; clear H.
        rewrite Hconf in *. clear Hframe.
        simpl in *; unfold Datatypes.id in *;
          rewrite Hdist_D in Htrue.
        exfalso; apply no_fixpoint_negb in Htrue; auto.
      * assert (Hmove' := moving_means_not_near g' Hpred Hpath c0 Halive').
        destruct Hmove' as (HD', (H2d', Hdp')).
        specialize (H2d' g).
        assert ( get_ident (conf (Good g)) < get_ident (conf (Good g'))).
        {
          generalize (ident_unique conf Hg).
          apply le_lt_or_eq in Hident.
          destruct Hident; now intro.
        }
        specialize (H2d' H (still_alive_means_alive conf g Hpred Halive)). 
        clear H.
        unfold equiv, bool_Setoid, eq_setoid in H2d'.
        rewrite Rle_bool_false_iff in H2d'.
        intros Heq.
        destruct H2d'.
        set (x := (get_location (round rbg_ila da conf (Good g)))) in *;
          set (y := (get_location (conf (Good g)))) in *;
          set (w := (get_location (round rbg_ila da conf (Good g')))) in *;
          set (z := (get_location (conf (Good g')))) in *.
        assert (Htri := RealMetricSpace.triang_ineq y x w).
        assert (dist y w <= D)%R by lra.
        generalize D_0; lra.
    + rewrite Nat.leb_gt in Hident.
      specialize (H2d Hident ((still_alive_means_alive conf g' Hpred Halive'))).
      unfold equiv, bool_Setoid, eq_setoid in H2d.
      rewrite Rle_bool_false_iff in H2d.
      intros Hd; destruct H2d.
      rewrite dist_sym.
      assert (Hmove' := moving_means_not_near g' Hpred Hpath c0 Halive').
      destruct Hmove' as (HD', (H2d', Hdp')).
      specialize (H2d' g).
      set (x := (get_location (round rbg_ila da conf (Good g)))) in *;
          set (y := (get_location (conf (Good g)))) in *;
          set (w := (get_location (round rbg_ila da conf (Good g')))) in *;
          set (z := (get_location (conf (Good g')))) in *.
      assert (Htri := RealMetricSpace.triang_ineq x w z).
      rewrite dist_sym in HD'.
      assert (dist x z <= D)%R by lra.
      generalize D_0; lra.
Qed.

(*
Definition path_conf (conf:config) :=
  forall g, get_alive (conf (Good g)) = true ->
            (get_ident (conf (Good g)) = 0 \/
             (exists g', get_alive (conf (Good g')) = true /\
                         (dist (get_location (conf (Good g))) (get_location (conf (Good g'))) < Dmax)%R /\
                         get_ident (conf (Good g')) < get_ident (conf (Good g)))).

 *)


Definition target_alive conf :=
  forall g,
    get_ident (conf (Good g)) <> 0 ->
    get_alive (conf (Good g)) = true ->
    exists g', get_alive (conf (Good g')) = true /\
               get_ident (conf (Good g')) < get_ident (conf (Good g)) /\
               (dist (get_location (conf (Good g))) (get_location (conf (Good g')))
                <= Dmax)%R.

Lemma ident_preserved : forall conf g da,
    da_predicat da ->
    get_ident (conf (Good g)) = get_ident (round rbg_ila da conf (Good g)).
Proof.
  intros conf g da Hpred.
  rewrite (round_good_g g conf Hpred).
  unfold get_ident; simpl.
  unfold upt_aux, rbg_fnc; simpl.
  destruct (conf (Good g)) as (?,((?,?),?)).
  destruct (upt_robot_dies_b _); simpl; auto.  
Qed.



Lemma executed_means_not_moving : forall conf da g,
    da_predicat da ->
    get_alive (conf (Good g)) = true ->
    get_alive (round rbg_ila da conf (Good g)) = false ->
    get_location (conf (Good g)) == (get_location (round rbg_ila da conf (Good g))).
Proof.
  intros conf da g Hpred. 
  intros Hal' Hdead'. (*
  assert (Hdeath_means := robot_dead_means (conf) g Hpred' Hdead').
  destruct Hdeath_means; auto.
  unfold get_alive in *; rewrite Hal' in H; discriminate.*)
  rewrite (@round_good_g g) in *; try apply Hpred.
  simpl in *.  
  unfold Datatypes.id in *.
  destruct (change_frame da ( conf) g) as ((r,t),b).
  unfold upt_aux in *.
  destruct (upt_robot_dies_b _) eqn : Hbool.
  - simpl (fst
       (let (p, _) := snd ( conf (Good g)) in
        let (i, l) := p in
        (R2.bij_rotation_f r
           ((fst
               ((if b then reflexion else Similarity.id)
                  (fst ( conf (Good g)))) + 
             fst t)%R,
           (snd
              ((if b then reflexion else Similarity.id)
                 (fst ( conf (Good g)))) + 
            snd t)%R), (i, l, false)))).
    destruct (snd (conf (Good g))) as ((?,?),?) eqn : Hconf_s.

    assert ((@fst R2 ILA
          (@pair R2 (prod (prod identifiants light) bool)
             (@section R2 R2_Setoid
                (@comp R2 R2_Setoid (bij_rotation r)
                   (@comp R2 R2_Setoid (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                      (@sim_f R2 R2_Setoid R2_EqDec VS
                         (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                            (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                         match
                           b
                           return
                             (@similarity R2 R2_Setoid R2_EqDec VS
                                (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                   (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                         with
                         | true => reflexion
                         | false =>
                             @Similarity.id R2 R2_Setoid R2_EqDec VS
                               (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                  (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                         end))) (@fst R2 ILA (conf (@Good Identifiers g))))
             (@pair (prod identifiants light) bool (@pair identifiants light i l)
                false)))
            == ((comp (bij_rotation r)
                      (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                  (fst ( conf (Good g))))).
    destruct b; now simpl in *.
    unfold map_config in *.
    rewrite Hconf_s.
    rewrite H. destruct b; rewrite retraction_section; auto. 
  - unfold get_alive in *; simpl in *.
    destruct (conf (Good g)) as (?,((?,?),?)) eqn : Hconf; simpl in *.
    now rewrite Hal' in Hdead'.  
Qed.


Lemma executed_means_alive_near : forall conf g da,
    da_predicat da ->
    get_alive (conf (Good g)) = true ->
    get_ident (conf (Good g)) <> 0 ->
    get_alive (round rbg_ila da conf (Good g)) = false ->
    path_conf conf ->
    (exists g0,
        get_alive (conf (Good g0)) = true /\
        get_ident (conf (Good g0)) < get_ident (conf (Good g)) /\
        (dist (get_location (conf (Good g0))) (get_location (conf (Good g)))
         <= Dmax)%R) ->
    exists g', get_ident (conf (Good g')) < get_ident (conf (Good g)) /\
               (dist (get_location (conf (Good g)))
                    (get_location (conf (Good g'))) <= D)%R
               /\ get_alive ((conf (Good g'))) = true.
Proof.
  intros conf g da Hpred Halive_g Hident_0 Halive_gr Hpath Hexists.
  assert (Hnot_moving := executed_means_not_moving conf g Hpred).
  specialize (Hnot_moving Halive_g Halive_gr).
  destruct Hexists as (g0, (Halive_g0, (Hident, Hdist))).
  unfold path_conf in Hpath.
  rewrite round_good_g in Halive_gr.
  unfold get_alive in Halive_gr; simpl in Halive_gr.
  unfold upt_aux in *.
  unfold map_config in *.
  destruct (upt_robot_dies_b _) eqn : Hupt.
  destruct (conf (Good g)) as (p_g, ((i_g, l_g), a_g)) eqn : Hconf.
  simpl in Halive_gr.
  unfold upt_robot_dies_b in Hupt.
  apply orb_prop in Hupt.
  destruct Hupt as [Hnear|Halone].
  - rewrite existsb_exists in Hnear.
    destruct Hnear as (exec, (Hin, Hnear)).
    rewrite filter_In in Hin.
    destruct Hin as (HIn, HIn_ident).
    rewrite Hconf in *.
    unfold get_ident in *; 
      simpl in HIn_ident.
    rewrite config_list_spec in HIn.
    rewrite in_map_iff in HIn.
    destruct HIn as (id_exec, (Hid_exec, HIn)).
    destruct id_exec as [g_exec |byz].
    + exists g_exec. 
      split.
      * simpl.
        rewrite andb_true_iff in HIn_ident.
        destruct HIn_ident as (Hin_exec,Halive_exec). 
        rewrite Nat.ltb_lt, <- Hid_exec in Hin_exec.
        now simpl in *.
      * split.
        -- rewrite <- Hid_exec in Hnear.
           unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in *.
           simpl (fst _) in Hnear.
           assert (Hframe_dist := frame_dist (fst (conf (Good g_exec))) p_g (change_frame da conf g)).  
           rewrite <- Hframe_dist in Hnear.
           rewrite dist_sym. now rewrite Rle_bool_true_iff in *; simpl in *.
        -- rewrite andb_true_iff in HIn_ident.
           destruct HIn_ident.
           rewrite <- Hid_exec in *.
           now unfold get_alive in *; simpl in *.
    + simpl in HIn.
      generalize (In_Bnames byz), (Bnames_length). 
      now simpl.
  - rewrite forallb_existsb, forallb_forall in Halone.
    specialize (Halone (((let (p, b) := change_frame da conf g in
          let (r, t) := p in
          comp (bij_rotation r)
               (comp (bij_translation t) (if b then reflexion else Similarity.id))) (fst (conf (Good g0)))), snd (conf(Good g0)))).
    assert (Hin : @List.In (prod R2 ILA)
                   (@pair R2 ILA
                      (@section R2 R2_Setoid
                         match
                           @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                             (prod R2 light) (prod (prod R R2) bool) bool bool
                             robot_choice_RL Frame Choice inactive_choice_ila da
                             conf g return (@bijection R2 R2_Setoid)
                         with
                         | pair p b =>
                             match p return (@bijection R2 R2_Setoid) with
                             | pair r t =>
                                 @comp R2 R2_Setoid (bij_rotation r)
                                   (@comp R2 R2_Setoid
                                      (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                      match b return (@bijection R2 R2_Setoid) with
                                      | true =>
                                          @sim_f R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid
                                                  R2_EqDec VS ES)) reflexion
                                      | false =>
                                          @sim_f R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid
                                                  R2_EqDec VS ES))
                                            (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                               (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                  VS
                                                  (@Euclidean2Normed R2 R2_Setoid
                                                     R2_EqDec VS ES)))
                                      end)
                             end
                         end (@fst R2 ILA (conf (@Good Identifiers g0))))
                      (@snd R2 ILA (conf (@Good Identifiers g0))))
                   (@List.filter (prod R2 ILA)
                      (fun elt : prod R2 ILA =>
                       andb
                         (Nat.ltb (get_ident elt)
                            (get_ident
                               (@pair R2 ILA
                                  (@section R2 R2_Setoid
                                     match
                                       @change_frame (prod R2 ILA) Loc State_ILA
                                         Identifiers (prod R2 light)
                                         (prod (prod R R2) bool) bool bool
                                         robot_choice_RL Frame Choice
                                         inactive_choice_ila da conf g
                                       return (@bijection R2 R2_Setoid)
                                     with
                                     | pair p b =>
                                         match
                                           p return (@bijection R2 R2_Setoid)
                                         with
                                         | pair r t =>
                                             @comp R2 R2_Setoid 
                                               (bij_rotation r)
                                               (@comp R2 R2_Setoid
                                                  (@bij_translation R2 R2_Setoid
                                                     R2_EqDec VS t)
                                                  (@sim_f R2 R2_Setoid R2_EqDec VS
                                                     (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                                     match
                                                       b
                                                       return
                                                       (@similarity R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                                     with
                                                     | true => reflexion
                                                     | false =>
                                                       @Similarity.id R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                                     end))
                                         end
                                     end (@fst R2 ILA (conf (@Good Identifiers g))))
                                  (@snd R2 ILA (conf (@Good Identifiers g))))))
                         (get_alive elt))
                      (@config_list Loc (prod R2 ILA) State_ILA Identifiers
                         (fun id : @ident Identifiers =>
                          @pair R2 ILA
                            (@section R2 R2_Setoid
                               match
                                 @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                                   (prod R2 light) (prod (prod R R2) bool) bool bool
                                   robot_choice_RL Frame Choice inactive_choice_ila
                                   da conf g return (@bijection R2 R2_Setoid)
                               with
                               | pair p b =>
                                   match p return (@bijection R2 R2_Setoid) with
                                   | pair r t =>
                                       @comp R2 R2_Setoid 
                                         (bij_rotation r)
                                         (@comp R2 R2_Setoid
                                            (@bij_translation R2 R2_Setoid R2_EqDec
                                               VS t)
                                            (@sim_f R2 R2_Setoid R2_EqDec VS
                                               (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                  VS
                                                  (@Euclidean2Normed R2 R2_Setoid
                                                     R2_EqDec VS ES))
                                               match
                                                 b
                                                 return
                                                   (@similarity R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                               with
                                               | true => reflexion
                                               | false =>
                                                   @Similarity.id R2 R2_Setoid
                                                     R2_EqDec VS
                                                     (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                               end))
                                   end
                               end (@fst R2 ILA (conf id))) 
                            (@snd R2 ILA (conf id)))))).
    {
      rewrite filter_In.
      rewrite andb_true_iff.
      repeat split.
      * rewrite config_list_spec, in_map_iff.
        exists (Good g0).
        split; auto; try apply In_names.
        destruct (change_frame da conf g) as (?,b);
        now destruct b.
      * unfold get_ident in *; rewrite Hconf in *; simpl in *; auto.
        now rewrite Nat.ltb_lt.
      * now unfold get_alive in *; simpl in *.
    }
    specialize (Halone Hin).
    clear Hin.
    rewrite negb_true_iff in *.
    rewrite Hconf in *.
    assert (Hframe_dist := frame_dist (fst (conf (Good g0))) p_g (change_frame da conf g)).
    unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in *.
    unfold frame_choice_bijection, Frame in Hframe_dist.
    destruct (change_frame _) as ((r,t),b) eqn : Hchange.
    simpl (fst _) in *.
    assert (((@dist (@location Loc) (@location_Setoid Loc) 
                   (@location_EqDec Loc) VS
                   (@Normed2Metric (@location Loc) (@location_Setoid Loc)
                      (@location_EqDec Loc) VS
                      (@Euclidean2Normed (@location Loc) 
                         (@location_Setoid Loc) (@location_EqDec Loc) VS ES))
                   (R2.bij_rotation_f r
                      (@pair R R
                         (Rplus
                            (@fst R R
                               (@section R2 R2_Setoid
                                  match b return (@bijection R2 R2_Setoid) with
                                  | true => bij_reflexion
                                  | false => @id R2 R2_Setoid
                                  end (@fst R2 ILA (conf (@Good Identifiers g0)))))
                            (@fst R R t))
                         (Rplus
                            (@snd R R
                               (@section R2 R2_Setoid
                                  match b return (@bijection R2 R2_Setoid) with
                                  | true => bij_reflexion
                                  | false => @id R2 R2_Setoid
                                  end (@fst R2 ILA (conf (@Good Identifiers g0)))))
                            (@snd R R t))))
                   (R2.bij_rotation_f r
                      (@pair R R
                         (Rplus
                            (@fst R R
                               (@section R2 R2_Setoid
                                  (@sim_f R2 R2_Setoid R2_EqDec VS
                                     (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                        (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                           ES))
                                     match
                                       b
                                       return
                                         (@similarity R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid
                                                  R2_EqDec VS ES)))
                                     with
                                     | true => reflexion
                                     | false =>
                                         @Similarity.id R2 R2_Setoid R2_EqDec VS
                                           (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                              (@Euclidean2Normed R2 R2_Setoid
                                                 R2_EqDec VS ES))
                                     end) p_g)) (@fst R R t))
                         (Rplus
                            (@snd R R
                               (@section R2 R2_Setoid
                                  (@sim_f R2 R2_Setoid R2_EqDec VS
                                     (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                        (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                           ES))
                                     match
                                       b
                                       return
                                         (@similarity R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid
                                                  R2_EqDec VS ES)))
                                     with
                                     | true => reflexion
                                     | false =>
                                         @Similarity.id R2 R2_Setoid R2_EqDec VS
                                           (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                              (@Euclidean2Normed R2 R2_Setoid
                                                 R2_EqDec VS ES))
                                     end) p_g)) (@snd R R t)))))) ==  dist
                  ((rotation r
                    ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
                     (fst (conf (Good g0))))
                  ((rotation r
                    ∘ (translation t ∘ (if b then reflexion else Similarity.id)))
                     p_g)).
    now destruct b; simpl.
    rewrite <- H in Hframe_dist.
    rewrite <- Hframe_dist in Halone.
    clear H.
    rewrite Rle_bool_false_iff in Halone; now destruct Halone.
  - unfold get_alive in *; simpl in Halive_gr.
    destruct (conf (Good g)) as (p_g, ((i_g, l_g), a_g)).
    simpl in *.
    now rewrite Halive_g in *.
  - apply Hpred.    
Qed.    







Definition executioner_means_light_off conf :=
  forall g da,
    da_predicat da ->
    get_alive (conf (Good g)) = true ->
    (exists g', get_alive (conf (Good g')) = true /\
               get_ident (conf (Good g)) < get_ident (conf (Good g')) /\
               (dist (get_location (conf (Good g))) (get_location (conf (Good g')))
                    <= D)%R) ->
    get_light (conf (Good g)) = false.


Definition executed_means_light_on conf := forall g da,
    da_predicat da ->
    get_alive (conf (Good g)) = true ->
    get_alive (round rbg_ila da conf (Good g)) = false ->
    get_light (conf (Good g)) = true.



Lemma light_on_means_not_moving_before : forall conf g da,
    da_predicat da ->
    path_conf conf ->
    get_alive (round rbg_ila da conf (Good g)) = true ->
    get_light (round rbg_ila da conf (Good g)) = true ->
    get_location (conf (Good g)) == get_location (round rbg_ila da conf (Good g)).
Proof.
  intros conf g da Hpred Hpath Halive Hlight.
  rewrite round_good_g in *; try apply Hpred.
  destruct (conf (Good g)) as (pos, ((ide, lig), ali)) eqn : Hconf.
  simpl in *.
  unfold upt_aux in *.
  unfold map_config in *;
  destruct (upt_robot_dies_b _) eqn : Hbool.
  unfold get_alive in *; rewrite Hconf in *;
    simpl in *.
  discriminate.
  unfold get_light in *; rewrite Hconf in *; simpl in *.
  unfold rbg_fnc in *.
  destruct (move_to _) eqn : Hmove.
  simpl in *; discriminate.
  destruct (change_frame _) as ((r,t),b) eqn : Hchange.
  destruct Hpred as (Horigin,_).
  specialize (Horigin conf g ((r,t),b) Hchange).
  symmetry.
  fold equiv.
  assert (Datatypes.id
    (retraction
       (comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
       (fst (0%R, 0%R, true))) == Datatypes.id pos).
  unfold Datatypes.id in *.
  destruct b; rewrite <- Inversion;
    simpl in *;
    unfold Datatypes.id in *;  rewrite Hconf in *; simpl in *;
      apply Horigin.
  simpl in *.
  unfold Datatypes.id in *.
  now destruct b; simpl in *.
Qed.




Definition exists_at_less_that_Dp conf :=
  forall g,
    get_alive (conf (Good g)) = true ->
    get_ident (conf (Good g)) > 0 ->
    (forall g_near, get_alive (conf (Good g_near)) = true ->
                    (dist (get_location (conf (Good g_near)))
                          (get_location (conf (Good g))) <= Dmax)%R ->
                    get_ident (conf (Good g_near)) < get_ident (conf (Good g)) ->
                    get_light (conf (Good g_near)) = true) ->
    exists g',
      get_alive (conf (Good g')) = true /\
      get_ident (conf (Good g')) < get_ident (conf (Good g)) /\
      (dist (get_location (conf (Good g))) (get_location (conf (Good g'))) <= Dp)%R
.


  
Lemma executed_means_light_on_round :
  forall conf da,
    da_predicat da ->
    path_conf conf ->
    no_collision_conf conf ->
    executioner_means_light_off conf ->
    executed_means_light_on conf ->
    exists_at_less_that_Dp conf ->
    executed_means_light_on (round rbg_ila da conf). 
Proof.
  intros conf da Hpred Hpath Hcol Hexecutioner Hexecuted Hless_that_Dp.
  intros g da' Hpred' Halive_r Halive_rr.
  destruct (conf (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  destruct (round rbg_ila da conf (Good g)) as (pos_r, ((ident_r, light_r), alive_r)) eqn : Hconf_r.
  rewrite round_good_g in *; try apply Hpred; try apply Hpred'.
  assert (Hconfr : round rbg_ila da conf (Good g) == (pos_r, (ident_r, light_r, alive_r))) by now rewrite Hconf_r.
  rewrite <- Hconf_r in *.
  rewrite round_good_g in *; try apply Hpred; try apply Hpred'.
  unfold get_light; unfold get_alive in Halive_rr, Halive_r; simpl; simpl in *.
  unfold upt_aux in *.
  unfold map_config in *;
    destruct (upt_robot_dies_b _) eqn : Hbool; rewrite Hconf in *; try now simpl in *.
  simpl.
  simpl in Halive_r, Halive_rr.
  destruct (upt_robot_dies_b
                          (fun id : @Identifiers.ident Identifiers =>
                           @pair R2 ILA
                             (@section R2 R2_Setoid
                                match
                                  @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                                    (prod R2 NoCollisionAndPath.light) 
                                    (prod (prod R R2) bool) bool bool
                                    robot_choice_RL Frame Choice inactive_choice_ila
                                    da'
                                    (@round (prod R2 ILA) Loc State_ILA Identifiers
                                       Spect_ILA (prod R2 NoCollisionAndPath.light)
                                       (prod (prod R R2) bool) bool bool
                                       robot_choice_RL Frame Choice
                                       inactive_choice_ila UpdFun inactive_ila
                                       rbg_ila da conf) g
                                  return (@bijection R2 R2_Setoid)
                                with
                                | pair p b =>
                                    match p return (@bijection R2 R2_Setoid) with
                                    | pair r t =>
                                        @comp R2 R2_Setoid 
                                          (bij_rotation r)
                                          (@comp R2 R2_Setoid
                                             (@bij_translation R2 R2_Setoid R2_EqDec
                                                VS t)
                                             (@sim_f R2 R2_Setoid R2_EqDec VS
                                                (@Normed2Metric R2 R2_Setoid
                                                   R2_EqDec VS
                                                   (@Euclidean2Normed R2 R2_Setoid
                                                      R2_EqDec VS ES))
                                                match
                                                  b
                                                  return
                                                    (@similarity R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                                with
                                                | true => reflexion
                                                | false =>
                                                    @Similarity.id R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                                end))
                                    end
                                end
                                (@fst R2 ILA
                                   (@round (prod R2 ILA) Loc State_ILA Identifiers
                                      Spect_ILA (prod R2 NoCollisionAndPath.light)
                                      (prod (prod R R2) bool) bool bool
                                      robot_choice_RL Frame Choice
                                      inactive_choice_ila UpdFun inactive_ila
                                      rbg_ila da conf id)))
                             (@snd R2 ILA
                                (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                                   (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool
                                   bool robot_choice_RL Frame Choice
                                   inactive_choice_ila UpdFun inactive_ila rbg_ila
                                   da conf id))) g) eqn : Hbool_r; try now simpl in *;
  try (simpl in *;
  unfold rbg_fnc in *;
  rewrite Hconf_r in *;
  simpl in Halive_rr, Hconf_r;
  destruct Hconfr as (_,(_,(_,Halive_false)));
  rewrite Halive_r, Halive_rr in Halive_false; discriminate).
  rewrite Hconf_r in *.
    simpl in *.
 
    
    unfold rbg_fnc.
  destruct (move_to _) eqn : Hmove; try now simpl in *.
  simpl in Halive_r.
  unfold upt_robot_dies_b in Hbool.
  
  rewrite orb_false_iff in *.
  
  assert (Hbool_safe := Hbool).
  
  destruct Hbool as (Hexists, Hfar).
  rewrite negb_false_iff in Hfar.
  rewrite <- negb_true_iff in Hexists.
  rewrite forallb_existsb, forallb_forall in Hexists.
  rewrite existsb_exists in Hfar.
  destruct Hfar as (far, (Hfar_in, Hfar_dist)).
  assert (Hmsz := move_to_Some_zone Hmove).
  simpl.
  exfalso.
(*il faut un robot dans le spectre pour dire qu'il est à plus de 2*D  *)

(*  destruct Hmsz as (Hdist_some, (Hdist, Hforall)).*)
  assert (Hpath_backup := Hpath).
  specialize (Hpath g).
  unfold get_alive at 1 in Hpath.
  rewrite Hconf in Hpath at 1.
  specialize (Hpath Halive_r).
  destruct Hpath.
  - rewrite (ident_preserved conf g Hpred) in H.
    rewrite (ident_preserved (round rbg_ila da conf) g Hpred') in H.
    assert (H0 := ident_0_alive (round rbg_ila da' (round rbg_ila da conf)) g H).
    rewrite round_good_g in H0.
    simpl in H0.
    unfold upt_aux in H0;
      unfold map_config in *;
      rewrite Hbool_r in H0.
    unfold get_alive in H0;
      simpl in H0.
    rewrite Hconf_r in H0; simpl in H0.
    discriminate.
    apply Hpred'.
  - destruct H as (g', (Halive_g', (Hdist_d_g', Hident_g'))).
    destruct (R2_EqDec pos pos_r).
    + (* monter que si il bouge aps, comme il s'élimine a (round (round)), c'est pas possible car selon Hforall, il ne peux pas en y avoir a moins de 2D, donc au round suivant il n'y en a aps a moins de D, et selon dist_some, il y en a un a moins de DP, donc il y en a un  amoins de Dmax a round d'apres.*)
      clear Hexists Hfar_in.
      unfold upt_robot_dies_b in Hbool_r.
      rewrite orb_true_iff in *.
      destruct Hbool_r as [Hexists|Hfar].
      * rewrite existsb_exists in Hexists.
        destruct Hexists as (exec, (Hexists_in, Hexists_dist)).
        rewrite filter_In in Hexists_in.
        destruct Hexists_in as (Hexists_in, Hexists_prop).
        rewrite config_list_spec, in_map_iff in Hexists_in.
        destruct Hexists_in as (exec_id, (exec_comp, Hexec_names)).
        rewrite andb_true_iff in Hexists_prop.
        rewrite <- exec_comp in *.
        destruct exec_id as [g_exec|byz].
       
        
        destruct Hexists_prop as (Hident_exec, Halive_exec).
        unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in Hexists_dist.
        destruct (change_frame da' _) as ((r_r, t_r), b_r) eqn : Hchange_r.
        assert (Rle_bool (dist (fst (round rbg_ila da conf (Good g_exec)))
                               (fst (round rbg_ila da conf (Good g)))) D = true).
        rewrite <- Hexists_dist.
        f_equal.
        assert (Hframe := frame_dist (fst (round rbg_ila da conf (Good g_exec))) (fst (round rbg_ila da conf (Good g))) ((r_r, t_r), b_r)).
        unfold frame_choice_bijection, Frame in Hframe.
        now simpl in *.

        assert (get_alive ((comp (bij_rotation r_r)
                      (comp (bij_translation t_r)
                         (if b_r then reflexion else Similarity.id)))
                     (fst (round rbg_ila da conf (Good g_exec))),
                           snd (round rbg_ila da conf (Good g_exec))) == true).
        rewrite <-Halive_exec.
        reflexivity.
        assert ((fst (round rbg_ila da conf (Good g_exec))) ==
                fst ((let frame_choice := change_frame da conf g_exec in
        let new_frame := frame_choice_bijection frame_choice in
        let local_config :=
          map_config
            (lift
               (existT precondition new_frame (precondition_satisfied da conf g)))
            conf in
        let spect := obs_from_config local_config (local_config (Good g_exec))  in
        let local_robot_decision := rbg_ila spect in
        let choice := choose_update da local_config g_exec local_robot_decision in
        let new_local_state :=
          update local_config g_exec frame_choice local_robot_decision choice in
        lift
          (existT precondition (new_frame ⁻¹)
             (precondition_satisfied_inv da conf g_exec)) new_local_state))).
        rewrite (RelationPairs.fst_compat _ _ _ _ (round_good_g g_exec _ Hpred)).
        reflexivity.
        assert (Hexec_comp : ((comp (bij_rotation r_r)
                  (comp (bij_translation t_r)
                     (if b_r then reflexion else Similarity.id)))
                 (fst (round rbg_ila da conf (Good g_exec))),
                              snd (round rbg_ila da conf (Good g_exec))) == exec).
        rewrite <- exec_comp.
        f_equiv.
        f_equal.
        now destruct b_r; simpl.
        destruct ((round rbg_ila da conf (Good g_exec))) as (pos', ((ide', lid'), ali')) eqn : Hconf'.
        simpl in H1.
        rewrite H1 in Hexec_comp.
        clear H1.
        simpl in Hexec_comp.
        assert ((snd (round rbg_ila da conf (Good g_exec))) ==
                snd ((let frame_choice := change_frame da conf g_exec in
        let new_frame := frame_choice_bijection frame_choice in
        let local_config :=
          map_config
            (lift
               (existT precondition new_frame (precondition_satisfied da conf g)))
            conf in
        let spect := obs_from_config local_config (local_config (Good g_exec)) in
        let local_robot_decision := rbg_ila spect in
        let choice := choose_update da local_config g_exec local_robot_decision in
        let new_local_state :=
          update local_config g_exec frame_choice local_robot_decision choice in
        lift
          (existT precondition (new_frame ⁻¹)
             (precondition_satisfied_inv da conf g_exec)) new_local_state))).
        rewrite (RelationPairs.snd_compat _ _ _ _ (round_good_g g_exec _ Hpred)).
        reflexivity.
        rewrite <- exec_comp in Hexec_comp.
        rewrite Hconf' in H1.
        simpl in H1.
        simpl in Hexec_comp.
        destruct (change_frame da conf g_exec) as ((r',t'),b') eqn : Hchange'.
        unfold upt_aux in Hexec_comp, H1.
        unfold map_config in *;
          destruct (upt_robot_dies_b _) eqn : Hbool'.
        -- destruct (conf (Good g_exec)) as (?,((?,?),?));
             simpl in H1.
           unfold get_alive in Halive_exec; simpl in Halive_exec.
           now rewrite Halive_exec in *.
        -- destruct (conf (Good g_exec)) as (pos_exec,((ident_exec,light_exec),alive_exec)) eqn : Hconf_exec.
           unfold rbg_fnc in Hexec_comp.
           destruct (move_to _) eqn : Hmove'.
           auto.
           (*  destruct Hmsz as (Hdist_some, (Hdist, Hforall)).*)

           specialize (Hmsz ((let (p, b) := change_frame da conf g in
                    let (r, t) := p in
                    comp (bij_rotation r)
                      (comp (bij_translation t)
                            (if b then reflexion else Similarity.id)))
                                  (fst (conf (Good g_exec))), snd (conf (Good g_exec)))).
           set (new_pos := choose_new_pos _ _) in *.
           
           assert (            let (pos_x, _) :=
              ((let (p, b) := change_frame da conf g in
                let (r, t) := p in
                comp (bij_rotation r)
                  (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                 (fst (conf (Good g_exec))), snd (conf (Good g_exec))) in
            (dist new_pos pos_x > 2 * D)%R).
           { apply Hmsz.
             unfold obs_from_config, Spect_ILA.
             rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.
             destruct (change_frame da conf g) as ((?,?),?).
             repeat split.
             *
               exists (Good g_exec); repeat split; simpl.
               destruct b; now simpl.
               now destruct (snd (conf (Good g_exec))) as ((?,?),?).
             * unfold Datatypes.id.
               assert ((@dist (@location Loc) (@location_Setoid Loc) (@location_EqDec Loc) VS
                              (@Normed2Metric (@location Loc) (@location_Setoid Loc)
             (@location_EqDec Loc) VS
             (@Euclidean2Normed (@location Loc) (@location_Setoid Loc)
                (@location_EqDec Loc) VS ES))
          (@fst (@location Loc) ILA
             (@pair R2 ILA
                (@section R2 R2_Setoid
                   (@comp R2 R2_Setoid (bij_rotation r)
                      (@comp R2 R2_Setoid
                         (@bij_translation R2 R2_Setoid R2_EqDec VS r0)
                         match b return (@bijection R2 R2_Setoid) with
                         | true =>
                             @sim_f R2 R2_Setoid R2_EqDec VS
                               (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                  (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                               reflexion
                         | false =>
                             @sim_f R2 R2_Setoid R2_EqDec VS
                               (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                  (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                               (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                  (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                     (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                         end)) (@fst R2 ILA (conf (@Good Identifiers g_exec))))
                (@snd R2 ILA (conf (@Good Identifiers g_exec)))))
          (@section R2 R2_Setoid
             (@comp R2 R2_Setoid (bij_rotation r)
                (@comp R2 R2_Setoid (@bij_translation R2 R2_Setoid R2_EqDec VS r0)
                   (@sim_f R2 R2_Setoid R2_EqDec VS
                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                      match
                        b
                        return
                          (@similarity R2 R2_Setoid R2_EqDec VS
                             (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                      with
                      | true => reflexion
                      | false =>
                          @Similarity.id R2 R2_Setoid R2_EqDec VS
                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                               (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                      end))) pos)) == dist (fst (conf (Good g_exec))) pos).
               rewrite (frame_dist _ pos ((r , r0), b)).
               unfold frame_choice_bijection, Frame; destruct b; now simpl.
               rewrite H2.
               clear H2.
               assert (Rle_bool
                         (dist
                            (fst (round rbg_ila da conf (Good g_exec)))
                            (fst (round rbg_ila da conf (Good g)))) D = true).
               rewrite <- Hexists_dist.
               rewrite (frame_dist (fst (round rbg_ila da conf (Good g_exec))) _ ((r_r,t_r), b_r)).
               unfold frame_choice_bijection, Frame; destruct b_r; now simpl in *.
               rewrite Rle_bool_true_iff in *.
               assert (Rle_bool (dist (get_location (conf (Good g))) (get_location (round rbg_ila da conf (Good g)))) D = true)%R.
               apply dist_round_max_d.
               apply Hpred.
               apply Hpath_backup.
               rewrite Hconf.
               now unfold get_alive; simpl.
               assert (Rle_bool (dist (get_location (conf (Good g_exec))) (get_location (round rbg_ila da conf (Good g_exec)))) D = true)%R.
               apply dist_round_max_d.
               apply Hpred.
               apply Hpath_backup.
               unfold get_alive in *; simpl in Halive_exec.
               assert (get_alive (round rbg_ila da conf (Good g_exec)) = true).
               rewrite Hconf'.
               now unfold get_alive; simpl.
               apply still_alive_means_alive in H4.
               now unfold get_alive in *.
               apply Hpred.
               
               generalize Dmax_6D.
               rewrite Rle_bool_true_iff in *.
               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in H3, H4.
               rewrite Hconf in H3.
               simpl (fst (pos, (ident, light, alive))) in *.
               set (u:= (fst (conf (Good g_exec)))) in *;
                 set (v := (fst (round rbg_ila da conf (Good g_exec)))) in *;
                 set (w := (fst (round rbg_ila da conf (Good g)))) in *.
               assert (dist pos w <= D)%R by now unfold w; apply H3.
               assert (dist u v <= D)%R by now unfold v.
               clear H3 H4.
               assert (dist u w <= 2*D)%R.
               assert (Htri := RealMetricSpace.triang_ineq u v w).
               lra.
               intros; rewrite 2 andb_true_iff.
               repeat split.
               rewrite Rle_bool_true_iff.
               assert (Htri := RealMetricSpace.triang_ineq u w pos).
               generalize D_0.
               rewrite dist_sym in H5; lra.
               apply (still_alive_means_alive conf g_exec Hpred). 
               unfold get_alive in *; rewrite Hconf'; simpl (snd _) in *.
               auto.
               unfold get_alive in *; simpl (snd _) in *.
               auto.
               
             * assert (Hident_exec' : (get_ident
                   (comp (bij_rotation r_r)
                      (comp (bij_translation t_r) (if b_r then reflexion else Similarity.id))
                      (fst (pos', (ide', lid', ali'))), snd (pos', (ide', lid', ali')))) <?
                 get_ident (round rbg_ila da conf (Good g)) = true).
               now unfold get_ident in *; simpl in *. 
               rewrite <- ident_preserved in Hident_exec'; try auto. 
               auto.
               unfold ILA in *.
               assert (Haux : get_ident (round rbg_ila da conf (Good g_exec)) = ide').
               unfold ILA in *;
               rewrite Hconf'; unfold get_ident; simpl; auto.
               unfold get_ident in Hident_exec'. simpl in Hident_exec'.
               rewrite <- Haux in Hident_exec'.
               rewrite <- ident_preserved, Hconf in Hident_exec'; try auto.
               unfold get_ident in *; simpl in *.
               rewrite Nat.leb_le, Nat.ltb_lt in *.
               unfold ILA in *; omega.
               
             * intros x y Hxy.
               rewrite (get_alive_compat Hxy).
               rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
               rewrite (get_ident_compat Hxy).
               destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
               reflexivity.
                       }
           destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
           clear H1.
           assert (new_pos == ((comp (bij_rotation r)
              (comp (bij_translation t) (if b then reflexion else Similarity.id)))
             (fst (round rbg_ila da conf (Good g))))).
           unfold round.
           destruct (Hpred) as (?,(?,?)).
          specialize (H4 (Good g)).
          rewrite H4.
          simpl ((fst
       (lift
          _ _))). 
          rewrite Hchange.
          unfold upt_aux.
          unfold map_config in *;
            clear Hbool'.
          destruct (upt_robot_dies_b _) eqn : Hfalse.
          rewrite <- orb_false_iff in Hbool_safe.
          simpl in Hfalse.
          unfold upt_robot_dies_b in Hfalse.
          revert Hbool_safe; intro Hbool_safe.
          simpl in *. rewrite Hfalse in Hbool_safe.
          discriminate.
          clear Hfalse.
          unfold rbg_fnc. rewrite Hconf. simpl (move_to _ _); simpl in Hmove'. unfold new_pos in Hmove'. simpl in *; rewrite Hmove'.
          rewrite <- (section_retraction (comp (bij_rotation r)
     (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos).
          now destruct b; simpl in *.
          rewrite H1 in H2.
          assert (Hdist_round_g_to_exec :  (dist
             (fst (round rbg_ila da conf (Good g)))
             (fst (conf (Good g_exec))) > 2 * D)%R).
          rewrite (frame_dist _ _ ((r,t),b)).
          unfold frame_choice_bijection, Frame.
          destruct b; now simpl in *.
          clear H1 H2.
          assert ( Rle_bool
                   (dist (fst (round rbg_ila da conf (Good g_exec)))
                      (fst (round rbg_ila da conf (Good g)))) D = true)%R.
          rewrite (frame_dist _ _ ((r_r,t_r),b_r)).
          unfold frame_choice_bijection, Frame.
          destruct (b_r); now simpl in *.
          rewrite Rle_bool_true_iff in H1.
          assert (Rle_bool (dist (get_location (conf (Good g_exec))) (get_location (round rbg_ila da conf (Good g_exec)))) D = true).
          apply dist_round_max_d.
          apply Hpred.
          apply Hpath_backup.
          rewrite <- Hconf' in Halive_exec.
          unfold get_alive in Halive_exec.
          assert (get_alive (round rbg_ila da conf (Good g_exec)) = true).
          rewrite Hconf'.
          now unfold get_alive; simpl.
          apply still_alive_means_alive in H2.
          unfold get_alive in *; now simpl in *.
          apply Hpred.
          rewrite Rle_bool_true_iff in H2.
          assert (Htri := RealMetricSpace.triang_ineq (fst (round rbg_ila da conf (Good g))) (get_location (round rbg_ila da conf (Good g_exec))) (fst (conf (Good g_exec)))).
          unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
         rewrite dist_sym in H1, H2.
         lra.
         
         discriminate.
        -- 
           assert (Hfalse := In_Bnames byz).
             now simpl in *.
      * rewrite forallb_existsb, forallb_forall in Hfar.
        set (target := choose_target _) in *.
        assert (Hin_spect := @choose_target_in_spect (obs_from_config _  _)
                           (target) (reflexivity _)).
        destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange;
          destruct (change_frame da' (round rbg_ila da conf) g) as ((r_r, t_r),b_r) eqn : Hchange_r.
        
        unfold obs_from_config, Spect_ILA in Hin_spect.
        rewrite make_set_spec, filter_InA in Hin_spect.
        destruct Hin_spect.
        rewrite config_list_InA in H.
        destruct H as (id, H).
        destruct id as [g_far|byz].
        rewrite andb_true_iff in H0; destruct H0.
        assert (Hfar':=Hfar).
        specialize (Hfar  ((comp (bij_rotation r_r)
        (comp (bij_translation t_r) (if b_r then reflexion else Similarity.id)))
       (fst (round rbg_ila da conf (Good g_far))), snd (round rbg_ila da conf (Good g_far)))).
        assert (@List.In (prod R2 ILA)
                 (@pair R2 ILA
                    (@section R2 R2_Setoid
                       (@comp R2 R2_Setoid (bij_rotation r_r)
                          (@comp R2 R2_Setoid (@bij_translation R2 R2_Setoid R2_EqDec VS t_r)
                             match b_r return (@bijection R2 R2_Setoid) with
                             | true =>
                                 @sim_f R2 R2_Setoid R2_EqDec VS
                                   (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)) reflexion
                             | false =>
                                 @sim_f R2 R2_Setoid R2_EqDec VS
                                   (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                   (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                             end))
                       (@fst R2 ILA
                          (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                             (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                             robot_choice_RL Frame Choice inactive_choice_ila UpdFun inactive_ila
                             rbg_ila da conf (@Good Identifiers g_far))))
                    (@snd R2 ILA
                       (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA 
                          (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool robot_choice_RL
                          Frame Choice inactive_choice_ila UpdFun inactive_ila rbg_ila da conf
                          (@Good Identifiers g_far))))
                 (@List.filter (prod R2 ILA)
                    (fun elt : prod R2 ILA =>
                     andb
                       (Nat.ltb (get_ident elt)
                          (get_ident
                             (@pair R2 ILA
                                (@section R2 R2_Setoid
                                   (@comp R2 R2_Setoid (bij_rotation r_r)
                                      (@comp R2 R2_Setoid
                                         (@bij_translation R2 R2_Setoid R2_EqDec VS t_r)
                                         (@sim_f R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                            match
                                              b_r
                                              return
                                                (@similarity R2 R2_Setoid R2_EqDec VS
                                                   (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                      (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                                         ES)))
                                            with
                                            | true => reflexion
                                            | false =>
                                                @Similarity.id R2 R2_Setoid R2_EqDec VS
                                                  (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                     (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                                        ES))
                                            end)))
                                   (@fst R2 ILA
                                      (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                                         (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                                         robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                                         inactive_ila rbg_ila da conf 
                                         (@Good Identifiers g))))
                                (@snd R2 ILA
                                   (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                                      (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                                      robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                                      inactive_ila rbg_ila da conf (@Good Identifiers g))))))
                       (get_alive elt))
                    (@config_list Loc (prod R2 ILA) State_ILA Identifiers
                       (fun id : @Identifiers.ident Identifiers =>
                        @pair R2 ILA
                          (@section R2 R2_Setoid
                             (@comp R2 R2_Setoid (bij_rotation r_r)
                                (@comp R2 R2_Setoid
                                   (@bij_translation R2 R2_Setoid R2_EqDec VS t_r)
                                   (@sim_f R2 R2_Setoid R2_EqDec VS
                                      (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                         (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                      match
                                        b_r
                                        return
                                          (@similarity R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                                      with
                                      | true => reflexion
                                      | false =>
                                          @Similarity.id R2 R2_Setoid R2_EqDec VS
                                            (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                               (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                      end)))
                             (@fst R2 ILA
                                (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                                   (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                                   robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                                   inactive_ila rbg_ila da conf id)))
                          (@snd R2 ILA
                             (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                                (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                                robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                                inactive_ila rbg_ila da conf id)))))).
        { rewrite filter_In, config_list_spec, in_map_iff. 
          repeat split.
          - exists (Good g_far).
            split; try (now destruct b_r; simpl).
            apply In_names.
          - rewrite andb_true_iff.
            split.
            assert (Hident := ident_preserved).
            unfold get_ident in *.
            simpl (snd _).
            rewrite <- 2 Hident; try apply Hpred.
            rewrite Nat.ltb_lt.
            assert (Hlower_target := target_lower).
            changeR2.
            fold obs_from_config in *.
            set (spect :=  obs_from_config _ _) in *.
            specialize (@Hlower_target spect 
                                       target
            ((let (p, b) := change_frame da conf g in
                              let (r, t) := p in
                              comp (bij_rotation r)
                                (comp (bij_translation t)
                                   (if b then reflexion else Similarity.id)))
                               (fst (conf (Good g))), snd (conf (Good g)))

                       ).
            unfold get_ident in Hlower_target.
            simpl (snd _) in Hlower_target.
            unfold obs_from_config, Spect_ILA in Hlower_target.
            destruct (change_frame _) as ((rr,tt),bb) eqn : Hchangee.
            assert (((r,t),b) == ((rr,tt),bb)).
            rewrite <- Hchange, <- Hchangee.
            reflexivity.
            do 2 destruct H2.
            simpl in H2, H3, H4.
            rewrite <- H2, <- H4, <- H3 in Hlower_target.
            assert ((fst (fst (snd (
      ((comp (bij_rotation r) (comp (bij_translation t) (if b then reflexion else Similarity.id)))
         (fst (conf (Good g_far))), snd (conf (Good g_far))))))) <?
                   (fst (fst (snd (conf (Good g))))) == true).
            rewrite <- Nat.ltb_lt in Hlower_target.
            rewrite <- Hlower_target.
            f_equiv.
            destruct H as (?,Hsnd).
            unfold location, Loc, make_Location in Hsnd.
            destruct (target) as (p_target, ((i_target,l_target), a_target)) eqn : Hconf_target.
            destruct ((conf (Good g_far))) as (?,((?,?),?)) eqn : Hconf_bij.
            simpl in Hsnd.
            destruct Hsnd as (?,(?,?)).
            
            rewrite H. now simpl.
            unfold spect, obs_from_config, Spect_ILA.
            rewrite make_set_spec, filter_InA, config_list_InA.
            split.
            exists (Good g).
            split; destruct b; simpl;
              auto.
            now rewrite Hconf; simpl.
            now rewrite Hconf; simpl.
            rewrite 3 andb_true_iff, Rle_bool_true_iff.
            unfold Datatypes.id.
            rewrite Hconf in *.
            split. 
            assert (Hframe :=(frame_dist (fst (pos, (ident, light, alive))) pos ((r,t),b))).
            unfold frame_choice_bijection, Frame in Hframe.
            simpl in *.
            destruct b; simpl in *;
            rewrite <- Hframe;
            repeat rewrite Rplus_opp_r;
            replace (0*0+0*0)%R with 0%R by lra;
            generalize Dmax_6D D_0;
            rewrite sqrt_0; try (
            intros; split; try (lra);
            unfold get_alive; simpl; auto;
            intros; split; try (lra);
            unfold get_alive; simpl; 
            auto).
            unfold get_ident; simpl; rewrite Nat.leb_le; omega.
            intros x y Hxy.
            rewrite (get_alive_compat Hxy).
            rewrite (get_ident_compat Hxy), (get_location_compat _ _ Hxy).
            f_equiv.
            destruct Hpred as (Horigin, ?).
            specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
            unfold frame_choice_bijection, Frame, Datatypes.id in *.
            rewrite <- Horigin.
            rewrite Hchangee.
            rewrite H2, H4, H3.
            destruct bb; simpl; auto.
            reflexivity.
            rewrite <- Nat.ltb_lt in *.
            now simpl in *.
            unfold get_alive; simpl.
            unfold round.
            assert(Hpred_backup := Hpred).
            destruct Hpred as (?,(?,?)).
            specialize (H4 (Good g_far)).
            rewrite H4.
            simpl ((lift _ _)). 
            unfold upt_aux.
            unfold map_config in *.
            destruct (conf (Good g_far)) as (p_far, ((i_far,l_far),a_far)) eqn : Hconf_far.
            destruct (upt_robot_dies_b _) eqn : Hbool_far; try now simpl.            
            simpl.
            specialize (Hexecuted (g_far)).
            assert (Halive_far : get_alive (round rbg_ila da conf (Good g_far)) == false).
            rewrite round_good_g.
            simpl ; unfold upt_aux; unfold map_config.
            rewrite Hbool_far.
            unfold get_alive; simpl.
            rewrite Hconf_far;
              now simpl.
            apply Hpred_backup.
            assert (get_light (conf (Good g_far)) == true).
            {
              apply (Hexecuted da).
              apply  Hpred_backup.
              assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
              unfold get_alive; rewrite Hconf_far; now simpl.
              destruct b; rewrite <- H5, <- H; rewrite 2 andb_true_iff in H0; destruct H0;
                try (now rewrite H6);
                now simpl in *.
              auto. 
            }
            assert (Htarget_light : get_light (target) = true).
            unfold target, obs_from_config, Spect_ILA.
            unfold target in *.
            rewrite H, <- Hconf_far.
            now unfold get_light in *; simpl in *.
            assert (Hlight_off_first := light_off_first (reflexivity _) Htarget_light).
            unfold For_all in *.
            set (new_pos := choose_new_pos _ _) in *.
            assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
            destruct Hchoose_correct as (Hdist_dp, Hdist_d).
            unfold obs_from_config, Spect_ILA in Hdist_dp.
            assert ((dist pos p_far) <= Dp)%R.
            { destruct Hconfr as (Hpos_rl,_).
              set (spect := obs_from_config _ _) in *.
              assert (Hpos_rl' : @equiv R2 R2_Setoid (retraction
              (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id)))
              (fst
                 (rbg_fnc
                    spect)))             pos_r) by (rewrite <- Hpos_rl; destruct b; now simpl). 
              rewrite <- Inversion in Hpos_rl'.
              destruct b;
                rewrite (RelationPairs.fst_compat _ _ _ _ H) in Hdist_dp;
                unfold rbg_fnc in Hpos_rl';  unfold new_pos, spect, target, spect in *; rewrite Hmove in Hpos_rl';
              simpl (fst _) in Hpos_rl';
              unfold equiv, R2_Setoid in Hpos_rl';
              simpl in *; rewrite <- Hpos_rl' in Hdist_dp;
              rewrite (@frame_dist pos p_far (@change_frame (prod R2 ILA) Loc State_ILA Identifiers 
                 (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                 robot_choice_RL Frame Choice inactive_choice_ila da conf g));
              unfold frame_choice_bijection, Frame; fold Frame; try rewrite Hchange;
              simpl in *; rewrite e in *. lra. lra. 
            }
            unfold upt_robot_dies_b in Hbool_far.
            rewrite orb_true_iff in Hbool_far.
            destruct Hbool_far as [Htoo_close_so_lighted|Htoo_far_but_path_conf].
            rewrite existsb_exists in *.
            destruct Htoo_close_so_lighted as (too_close, (Hin_too_close, Hdist_too_close)).
            ++ unfold executioner_means_light_off in *.
               rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff in Hin_too_close.
               destruct Hin_too_close as (([g_too_close | byz], (Hspec_too_close, Hnames_too_close)), (Hident_too_close, Halive_too_close));
                 try (assert (Hfalse := In_Bnames byz);
                      now simpl in *).
                   specialize (Hexecutioner g_too_close da Hpred_backup).
                   rewrite <- Hspec_too_close in Halive_too_close.
                   unfold get_alive in *.
                   simpl (snd (snd _)) in *.
                   specialize (Hexecutioner Halive_too_close).
                   assert (Hex : (exists g' : G,
                    snd (snd (conf (Good g'))) = true /\
                    get_ident (conf (Good g_too_close)) < get_ident (conf (Good g')) /\
                    (dist (get_location (conf (Good g_too_close)))
                       (get_location (conf (Good g'))) <= D)%R)).
                   { exists g_far.
                     repeat split; try now simpl.
                     assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
                     unfold get_alive; rewrite Hconf_far; now simpl.
                     revert H H0; intros H H0.
                     rewrite 2 andb_true_iff in H0; destruct H0 as ((H0, H0_ident), H0'). 
                     rewrite <- H7.
                     rewrite <- (get_alive_compat H).
                     now unfold get_alive.
                     rewrite Nat.ltb_lt in Hident_too_close.
                     rewrite <- Hspec_too_close in Hident_too_close.
                     unfold get_ident in *; simpl in *; auto.
                     rewrite <- Hspec_too_close, Rle_bool_true_iff in Hdist_too_close.
                     unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_too_close.
                     rewrite (frame_dist _ _ (change_frame da conf g_far)).
                     unfold frame_choice_bijection, Frame; now simpl in *.
                   }
                   specialize (Hexecutioner Hex).
                   clear Hex.
                   specialize (Hlight_off_first ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf (Good g_too_close))), snd (conf (Good g_too_close)))).
                   unfold equiv, bool_Setoid, eq_setoid in Hlight_off_first.
                   rewrite <- Hlight_off_first, <- Hexecutioner.
                   unfold get_light; now simpl in *.
                   unfold obs_from_config, Spect_ILA.
                   rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.                   repeat split.
                   exists (Good g_too_close).
                   destruct b; reflexivity.
                   rewrite 2 andb_true_iff; repeat split.
                   rewrite Rle_bool_true_iff.
                   replace (fst
        ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g_too_close))), snd (conf (Good g_too_close))))%R
                     with
                       ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g_too_close))))%R.
                   unfold Datatypes.id.
                   assert (Hframe := frame_dist (fst (conf (Good g_too_close))) pos ((r,t),b)).
                   unfold frame_choice_bijection, Frame in Hframe.
                   assert (dist (fst (conf (Good g_too_close))) pos <= Dmax)%R.
                   rewrite Rle_bool_true_iff in Hdist_too_close.
                   unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_too_close.
                   rewrite <- Hspec_too_close in Hdist_too_close.
                   assert ((dist (fst (conf (Good g_too_close)))
                                 (fst (conf (Good g_far))) <= D)%R).
                   rewrite (frame_dist _ _ (change_frame da conf g_far)).
                   unfold frame_choice_bijection, Frame, Datatypes.id in *.
                   now simpl; simpl in Hdist_too_close.
                   assert (Hti := RealMetricSpace.triang_ineq (fst (conf (Good g_too_close))) (fst (conf (Good g_far))) pos ).
                   rewrite Hconf_far in Hti at 2.
                   simpl ( (fst _)) in Hti.
                   rewrite dist_sym in H6.
                   generalize (D_0), Dmax_6D.
                   unfold Dp in *.
                   lra.
                   now destruct b; simpl in *; rewrite <- Hframe.
                   now destruct b; simpl in *.
                   unfold get_alive; now simpl.
                   unfold get_alive; now simpl. 
                   assert (Htarget_lower := target_lower).
                   set (spect := obs_from_config _ _) in *.
                   specialize (Htarget_lower spect ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
         (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))) ((comp (bij_rotation r)
         (comp (bij_translation t) (if b then reflexion else Similarity.id)))
        (fst (conf (Good g))), snd (conf (Good g)))).
                   rewrite Hconf in Htarget_lower.
                   assert (get_ident (conf (Good g_far)) < get_ident (conf (Good g))).
                   unfold get_ident in *; simpl (fst _) in *; rewrite Hconf, Hconf_far; apply Htarget_lower.
                   unfold spect, obs_from_config, Spect_ILA.

                   rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff.
                   repeat split.
                   exists (Good g).
                   now destruct b; rewrite Hconf.
                   unfold Datatypes.id.
                   generalize (dist_same ((comp (bij_rotation r)
                                                (comp (bij_translation t) (if b then reflexion else Similarity.id))) pos)), Dmax_6D, D_0;
                     rewrite Rle_bool_true_iff.
                   intro Hdist_0.
                   simpl (snd _).
                   destruct b; rewrite dist_same; lra.
                   simpl in *; assumption.
                   simpl in *; assumption.
                   unfold get_ident in *; rewrite Nat.leb_le; simpl; omega.
                   intros x y Hxy.
                   rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                   rewrite (get_alive_compat Hxy).
                   assert (Hcompat' := get_ident_compat Hxy); unfold get_ident in Hcompat'; rewrite Hcompat'.
                   reflexivity.
                   destruct Hpred_backup as (Horigin, ?).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   unfold frame_choice_bijection, Frame, Datatypes.id in *.
                   rewrite <- Horigin.
                   rewrite Hchange.
                   unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                   rewrite Hconf; simpl. destruct b; simpl; reflexivity.
                   unfold target, obs_from_config, Spect_ILA in *.
                   unfold get_alive in *.
                   unfold location, Loc, make_Location.
                   rewrite H.
                   destruct b; reflexivity.
                   rewrite Nat.leb_le.
                   transitivity (get_ident (conf (Good g_far))).
                   rewrite <- Hspec_too_close in Hident_too_close;
                     unfold get_ident in *; simpl in Hident_too_close;
                     rewrite Nat.ltb_lt in Hident_too_close; simpl.
                   omega.
                   unfold get_ident in *; simpl in *; rewrite Hconf in *; simpl in *; 
                     omega.
                   intros x y Hxy.
                   rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                   rewrite (get_alive_compat Hxy).
                   rewrite (get_ident_compat Hxy).
                   reflexivity.
            ++
               specialize (Hpath_backup g_far).
               assert (get_alive (conf (Good g_far)) == true).
               assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
                     unfold get_alive; rewrite Hconf_far; now simpl.
                     revert H H0; intros H H0.
                     rewrite 2 andb_true_iff in H0; destruct H0 as ((H0, H0_ident), H0'). 
                     rewrite <- H7.
                     rewrite <- (get_alive_compat H).
                     now unfold get_alive.
               simpl in H7.
               specialize (Hpath_backup H7); clear H7.
               destruct Hpath_backup as [Hident_0|Hpath_backup].
               rewrite (ident_preserved _ _ Hpred_backup) in Hident_0.
               assert (get_alive (round rbg_ila da conf (Good g_far)) = true).
               apply ident_0_alive; intuition.
               rewrite H7 in *; discriminate.
               rewrite forallb_existsb, forallb_forall in Htoo_far_but_path_conf.
               destruct Hpath_backup as (g_too_close, (Halive_close,( Hdist_close, Hident_close))). 
               specialize (Htoo_far_but_path_conf
                             ((((let (p, b) := change_frame da conf g_far in
                                 let (r, t) := p in
                                 comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf (Good g_too_close))), snd (conf (Good g_too_close)))))).
               rewrite negb_true_iff, Rle_bool_false_iff in Htoo_far_but_path_conf.
               destruct Htoo_far_but_path_conf.
               rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff.
               repeat split.
               ** exists (Good g_too_close).
                  split.
                  destruct (change_frame da conf g_far) as (?,b0); destruct b0;
                    now simpl.
                  apply In_names.
               ** rewrite Nat.ltb_lt.
                  unfold get_ident in *; simpl in Hident_close; simpl.
                  auto.
               ** rewrite <- Halive_close.
                  now unfold get_alive; simpl.
               ** rewrite dist_sym, (frame_dist _ _ (change_frame da conf g_far)) in Hdist_close.
                  unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                  unfold frame_choice_bijection, Frame in Hdist_close; fold Frame in *.
                  revert Hdist_close; intros Hdist_close.
                  destruct (change_frame _ _ g_far) as ((r_f, t_f), b_f)
                                                         eqn : Hchange_far.
                  now destruct b_f; simpl in *.
            ++ simpl.

               rewrite 2 andb_true_iff in H0.
               destruct H0 as ((H0,H0_aux), H0').
               rewrite <- (get_alive_compat H).
               now unfold get_alive; simpl.
         }
         specialize (Hfar H2).
         rewrite negb_true_iff, Rle_bool_false_iff in Hfar.
         clear H2.
         destruct Hfar.
         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.
         rewrite 2 andb_true_iff in H0.
         destruct H0 as ((H0, H0_aux), H0').
         rewrite Rle_bool_true_iff in H0.
         rewrite (RelationPairs.fst_compat _ _ _ _ H) in H0.
         revert H0; intros H0.
         assert (Hdist_round : (dist (fst (conf (Good g_far))) (fst (round rbg_ila da conf (Good g_far))) <= D)%R).
         rewrite <- Rle_bool_true_iff.
         assert (Hd := dist_round_max_d g_far Hpred Hpath_backup).
         destruct (conf (Good g_far)) as (p_far,((i_far, l_far), a_far)) eqn : Hconf_far.
         assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
         unfold get_alive; rewrite Hconf_far; now simpl.
         rewrite <- (get_alive_compat H) in H2.
         rewrite Hconf_far in H2.
         rewrite H0_aux in H2.
         now specialize (Hd (symmetry H2)).
         assert (Hconf_r_equiv : round rbg_ila da conf (Good g) == (pos_r, (ident_r, light_r, alive_r))) by now rewrite Hconf_r.
         rewrite (RelationPairs.fst_compat _ _ _ _ Hconf_r_equiv).
         rewrite <- e.
         simpl ((fst (pos, (ident_r, light_r, alive_r)))).
         assert (dist ((comp (bij_rotation r_r)
            (comp (bij_translation t_r) (if b_r then reflexion else Similarity.id)))
           (fst (round rbg_ila da conf (Good g_far))))
                      ((comp (bij_rotation r_r)
            (comp (bij_translation t_r) (if b_r then reflexion else Similarity.id)))
           pos) <= Dmax)%R.
         assert (dist (fst (round rbg_ila da conf (Good g_far))) pos <= Dmax)%R.
         destruct (conf (Good g_far)) as (p_far, ((i_far, l_far), a_far)) eqn : Hconf_far.
         assert ((dist pos p_far) <= Dp)%R.
         { destruct Hconfr as (Hpos_rl,_).
           set (spect := obs_from_config _ _) in *.
           assert (Hpos_rl' : @equiv R2 R2_Setoid (retraction
              (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id)))
              (fst
                 (rbg_fnc
                    spect)))
                                     pos_r) by (rewrite <- Hpos_rl; destruct b; now simpl). 
              rewrite <- Inversion in Hpos_rl'.
              set (new_pos := choose_new_pos _ _) in *.
              assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
              destruct Hchoose_correct as (Hdist_dp, Hdist_d).
            
              destruct b;
                rewrite (RelationPairs.fst_compat _ _ _ _ H) in Hdist_dp;
                unfold rbg_fnc in Hpos_rl'; unfold new_pos, spect, target, spect in *; rewrite Hmove in Hpos_rl';
              simpl (fst _) in Hpos_rl';
              unfold equiv, R2_Setoid in Hpos_rl';
              simpl in *; rewrite <- Hpos_rl' in Hdist_dp;
              rewrite (@frame_dist pos p_far (@change_frame (prod R2 ILA) Loc State_ILA Identifiers 
                 (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                 robot_choice_RL Frame Choice inactive_choice_ila da conf g));
              unfold frame_choice_bijection, Frame; fold Frame; try rewrite Hchange;
              simpl in *; rewrite e in *; lra. 
            }
            simpl (fst _) at 1 in Hdist_round.
            assert (Htri := RealMetricSpace.triang_ineq (fst (round rbg_ila da conf (Good g_far))) p_far pos).
            rewrite dist_sym in Hdist_round, H2.
            generalize D_0, Dmax_6D.
            unfold Dp in *. lra.
            rewrite (frame_dist _ _ ((r_r, t_r), b_r)) in H2.
            unfold frame_choice_bijection, Frame in H2; fold Frame in H2.
            destruct b_r; now simpl in *.
            destruct b_r; now simpl in *.
            assert (Hfalse := In_Bnames byz).
             now simpl in *.
             
            

            intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy),
                            (get_alive_compat Hxy), (get_ident_compat Hxy);
            reflexivity.
    + unfold rbg_fnc in Hconfr.
      rewrite Hmove in Hconfr.
      unfold upt_robot_dies_b in Hbool_r.
      rewrite (orb_true_iff) in Hbool_r.
      destruct Hbool_r as [Hnear|Hfar].
      * rewrite existsb_exists in Hnear.
        destruct Hnear as (near, (Hin_near, Hdist_near)).
        rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff in Hin_near.
        destruct Hin_near as (([g_near|byz],(Hspec_near, Hnames_near)), (Hident_near, Halive_near)); try (assert (Hfalse := In_Bnames byz);
               simpl in *; auto).
        rewrite <- Hspec_near in *.
        destruct Hconfr as (Hpos_rl, _).
        destruct (change_frame _ _ g) as ((r,t),b) eqn : Hchange.
        set (new_pos := choose_new_pos _ _) in *.
              assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
              destruct Hchoose_correct as (Hdist_dp, Hdist_d).
        assert (Hpos_rl_equiv : retraction
              (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id)))
              (fst (new_pos, false)) == pos_r).
        rewrite <- Hpos_rl.
        destruct b; reflexivity.
        rewrite <- Inversion in Hpos_rl_equiv.
        simpl (fst _) in Hpos_rl_equiv.
        rewrite <- Hpos_rl_equiv in *.
        specialize (Hmsz ((comp (bij_rotation r)
                   (comp (bij_translation t)
                         (if b then reflexion else Similarity.id))) (fst (conf (Good g_near))), snd (conf (Good g_near)))).
        apply Rgt_not_le in Hmsz.
        assert (dist pos_r (fst (conf (Good g_near))) <= 2*D)%R.
        revert Hdist_near; intros Hdist_near.
        rewrite Hconf_r in Hdist_near.
        assert (dist (fst (conf (Good g_near))) (fst (round rbg_ila da conf (Good g_near))) <= D)%R.
        rewrite <- Rle_bool_true_iff.
        apply dist_round_max_d.
        apply Hpred.
        apply Hpath_backup.
        assert (get_alive ((round rbg_ila da conf (Good g_near))) == true).
        rewrite <- Halive_near; unfold get_alive; now simpl.
        apply still_alive_means_alive in H; try apply Hpred.
        auto.
        rewrite Rle_bool_true_iff in Hdist_near.
        assert (@dist (@location Loc) (@location_Setoid Loc) (@location_EqDec Loc) VS
       (@Normed2Metric (@location Loc) (@location_Setoid Loc)
          (@location_EqDec Loc) VS
          (@Euclidean2Normed (@location Loc) (@location_Setoid Loc)
             (@location_EqDec Loc) VS ES))
       (@get_location Loc (prod R2 ILA) State_ILA
          (@pair R2 ILA
             (@section R2 R2_Setoid
                (let (p, b) :=
                   @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                     (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                     robot_choice_RL Frame Choice inactive_choice_ila da'
                     (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                        (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                        robot_choice_RL Frame Choice inactive_choice_ila
                        UpdFun inactive_ila rbg_ila da conf) g in
                 let (r, t) := p in
                 @comp R2 R2_Setoid (bij_rotation r)
                   (@comp R2 R2_Setoid
                      (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                      (@sim_f R2 R2_Setoid R2_EqDec VS
                         (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                            (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                         (if b
                          then reflexion
                          else
                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                             (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                   ES))))))
                (@fst R2 ILA
                   (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                      (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                      robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                      inactive_ila rbg_ila da conf 
                      (@Good Identifiers g_near))))
             (@snd R2 ILA
                (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                   (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                   robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                   inactive_ila rbg_ila da conf (@Good Identifiers g_near)))))
       (@get_location Loc (prod R2 ILA) State_ILA
          (@pair R2 ILA
             (@section R2 R2_Setoid
                (let (p, b) :=
                   @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                     (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                     robot_choice_RL Frame Choice inactive_choice_ila da'
                     (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                        (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                        robot_choice_RL Frame Choice inactive_choice_ila
                        UpdFun inactive_ila rbg_ila da conf) g in
                 let (r, t) := p in
                 @comp R2 R2_Setoid (bij_rotation r)
                   (@comp R2 R2_Setoid
                      (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                      (@sim_f R2 R2_Setoid R2_EqDec VS
                         (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                            (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                         (if b
                          then reflexion
                          else
                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                             (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                   ES))))))
                (@fst R2 ILA
                   (@pair R2 ILA pos_r
                      (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                         (@pair identifiants NoCollisionAndPath.light ident_r light_r)
                         alive_r))))
             (@snd R2 ILA
                (@pair R2 ILA pos_r
                   (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                      (@pair identifiants NoCollisionAndPath.light ident_r light_r) alive_r))))) ==
                dist (fst (round rbg_ila da conf (Good g_near)))
                     (fst (pos_r, (ident_r, light_r, alive_r)))).
        rewrite (frame_dist (fst (round rbg_ila da conf (Good g_near))) _ (change_frame da' (round rbg_ila da conf) g)).
        unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.

        unfold frame_choice_bijection, Frame. fold Frame.
        destruct (change_frame _ (round _ _ _) g) as ((?,?), xb) eqn : Hchange'; destruct xb;
          simpl in *; auto.
        assert (dist (fst (round rbg_ila da conf (Good g_near)))
         (fst (pos_r, (ident_r, light_r, alive_r))) <= D)%R.
        rewrite <- H0. apply Hdist_near.
        simpl (fst _) in H1.
        rewrite dist_sym in H1.
        assert (Htri := RealMetricSpace.triang_ineq pos_r (fst (round rbg_ila da conf (Good g_near))) (fst (conf (Good g_near)))). 
        generalize D_0. rewrite dist_sym in H. lra.

        destruct Hmsz.
        rewrite (frame_dist _ _ ((r,t),b)) in H.
        unfold frame_choice_bijection, Frame in H.
        destruct b; simpl in *; lra.
                assert (dist pos_r (fst (conf (Good g_near))) <= 2*D)%R.
        revert Hdist_near; intros Hdist_near.
        rewrite Hconf_r in Hdist_near.
        assert (dist (fst (conf (Good g_near))) (fst (round rbg_ila da conf (Good g_near))) <= D)%R.
        rewrite <- Rle_bool_true_iff.
        apply dist_round_max_d.
        apply Hpred.
        apply Hpath_backup.
        assert (get_alive ((round rbg_ila da conf (Good g_near))) == true).
        rewrite <- Halive_near; unfold get_alive; now simpl.
        apply still_alive_means_alive in H; try apply Hpred.
        auto.
        rewrite Rle_bool_true_iff in Hdist_near.
        assert (@dist (@location Loc) (@location_Setoid Loc) (@location_EqDec Loc) VS
       (@Normed2Metric (@location Loc) (@location_Setoid Loc)
          (@location_EqDec Loc) VS
          (@Euclidean2Normed (@location Loc) (@location_Setoid Loc)
             (@location_EqDec Loc) VS ES))
       (@get_location Loc (prod R2 ILA) State_ILA
          (@pair R2 ILA
             (@section R2 R2_Setoid
                (let (p, b) :=
                   @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                     (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                     robot_choice_RL Frame Choice inactive_choice_ila da'
                     (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                        (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                        robot_choice_RL Frame Choice inactive_choice_ila
                        UpdFun inactive_ila rbg_ila da conf) g in
                 let (r, t) := p in
                 @comp R2 R2_Setoid (bij_rotation r)
                   (@comp R2 R2_Setoid
                      (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                      (@sim_f R2 R2_Setoid R2_EqDec VS
                         (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                            (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                         (if b
                          then reflexion
                          else
                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                             (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                   ES))))))
                (@fst R2 ILA
                   (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                      (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                      robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                      inactive_ila rbg_ila da conf 
                      (@Good Identifiers g_near))))
             (@snd R2 ILA
                (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                   (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                   robot_choice_RL Frame Choice inactive_choice_ila UpdFun
                   inactive_ila rbg_ila da conf (@Good Identifiers g_near)))))
       (@get_location Loc (prod R2 ILA) State_ILA
          (@pair R2 ILA
             (@section R2 R2_Setoid
                (let (p, b) :=
                   @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                     (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                     robot_choice_RL Frame Choice inactive_choice_ila da'
                     (@round (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                        (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                        robot_choice_RL Frame Choice inactive_choice_ila
                        UpdFun inactive_ila rbg_ila da conf) g in
                 let (r, t) := p in
                 @comp R2 R2_Setoid (bij_rotation r)
                   (@comp R2 R2_Setoid
                      (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                      (@sim_f R2 R2_Setoid R2_EqDec VS
                         (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                            (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                         (if b
                          then reflexion
                          else
                           @Similarity.id R2 R2_Setoid R2_EqDec VS
                             (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                   ES))))))
                (@fst R2 ILA
                   (@pair R2 ILA pos_r
                      (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                         (@pair identifiants NoCollisionAndPath.light ident_r light_r)
                         alive_r))))
             (@snd R2 ILA
                (@pair R2 ILA pos_r
                   (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                      (@pair identifiants NoCollisionAndPath.light ident_r light_r) alive_r))))) ==
                dist (fst (round rbg_ila da conf (Good g_near)))
                     (fst (pos_r, (ident_r, light_r, alive_r)))).
        rewrite (frame_dist (fst (round rbg_ila da conf (Good g_near))) _ (change_frame da' (round rbg_ila da conf) g)).
        unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.

        unfold frame_choice_bijection, Frame. fold Frame.
        destruct (change_frame _ (round _ _ _) g) as ((?,?), xb) eqn : Hchange'; destruct xb;
          simpl in *; auto.
        assert (dist (fst (round rbg_ila da conf (Good g_near)))
         (fst (pos_r, (ident_r, light_r, alive_r))) <= D)%R.
        rewrite <- H0. apply Hdist_near.
        simpl (fst _) in H1.
        rewrite dist_sym in H1.
        assert (Htri := RealMetricSpace.triang_ineq pos_r (fst (round rbg_ila da conf (Good g_near))) (fst (conf (Good g_near)))). 
        generalize D_0. rewrite dist_sym in H. lra.
        
        unfold obs_from_config, Spect_ILA.
        rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.
        repeat split.
        exists (Good g_near).
        destruct b; reflexivity.
        rewrite 2 andb_true_iff.
        repeat split.
        rewrite Rle_bool_true_iff.
        assert (Hdist_round := dist_round_max_d g Hpred Hpath_backup).
        rewrite Hconf in Hdist_round; unfold get_alive in Hdist_round.
        simpl (snd _ ) in Hdist_round.
        rewrite Halive_r in *.
        specialize (Hdist_round (reflexivity _)).
        simpl (equiv) in Hdist_round.
        rewrite Rle_bool_true_iff in Hdist_round.
        assert (dist (fst (conf (Good g_near))) (pos)<= Dmax)%R.
        assert (Htri := RealMetricSpace.triang_ineq (fst (conf (Good g_near))) (fst (round rbg_ila da conf (Good g))) pos).
        rewrite Hconf_r in *.
        unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
        simpl (fst _) in *.
        rewrite dist_sym in H, Hdist_round.
        generalize D_0, Dmax_6D.
        lra.
        rewrite (frame_dist _ _ ((r,t),b)) in H0. 
        now destruct b; simpl in *.
        assert (get_alive (round rbg_ila da conf (Good g_near)) = true).
        rewrite <- Halive_near.
        now unfold get_alive; simpl in *.
        apply still_alive_means_alive in H0; try apply Hpred.
        unfold get_alive in *; now simpl in *.
        unfold get_alive in *; simpl in *; auto. 
        rewrite Nat.leb_le. unfold get_ident; simpl.
        rewrite Nat.ltb_lt in Hident_near.
        revert Hident_near; intro Hident_near.
        assert (Hident_near' : get_ident ( (round rbg_ila da conf (Good g_near))) <
                               get_ident ( (round rbg_ila da conf (Good g))))by
            (unfold get_ident in *; simpl in *; omega).
        rewrite <- 2 ident_preserved in Hident_near'; try apply Hpred.
        rewrite Hconf in Hident_near'; unfold get_ident in *; simpl in *; omega.
        intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy), (get_ident_compat Hxy).
        reflexivity.
      * set (spect := obs_from_config _ _) in *.
        assert (Hin_spect := @choose_target_in_spect spect
                           (choose_target spect) (reflexivity _)).
        destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange;
          destruct (change_frame da' (round rbg_ila da conf) g) as ((r_r, t_r),b_r) eqn : Hchange_r.
        
        unfold spect, obs_from_config, Spect_ILA in Hin_spect.
        rewrite make_set_spec, filter_InA in Hin_spect.
        destruct Hin_spect.
        rewrite config_list_InA in H.
        destruct H as (id, H).
        destruct id as [g_far|byz];
        try now ( assert (Hfalse := In_Bnames byz);
             now simpl in *).
             
        rewrite andb_true_iff in H0; destruct H0.
        assert (Hfar':=Hfar).
        rewrite forallb_existsb, forallb_forall in Hfar.
        
        specialize (Hfar  ((comp (bij_rotation r_r)
        (comp (bij_translation t_r) (if b_r then reflexion else Similarity.id)))
                             (fst (round rbg_ila da conf (Good g_far))), snd (round rbg_ila da conf (Good g_far)))).
        rewrite negb_true_iff, Rle_bool_false_iff in Hfar.
        destruct Hfar.
        { rewrite filter_In, config_list_spec, in_map_iff. 
          repeat split.
          - exists (Good g_far).
            split; try (now destruct b_r; simpl).
            apply In_names.
          - rewrite andb_true_iff.
            split.
            assert (Hident := ident_preserved).
            unfold get_ident in *.
            simpl (snd _).
            rewrite <- 2 Hident; try apply Hpred.
            rewrite Nat.ltb_lt.
            assert (Hlower_target := target_lower).
            changeR2.
            fold obs_from_config in *.
            specialize (@Hlower_target spect (choose_target spect) ((comp (bij_rotation r)
                      (comp (bij_translation t)
                         (if b then reflexion else Similarity.id))) 
                                                             (fst (conf (Good g))), snd (conf (Good g)))).
            unfold spect, obs_from_config, Spect_ILA in *.
            rewrite H in Hlower_target.
            unfold get_ident in *.
            unfold obs_from_config, Spect_ILA in Hlower_target.
            destruct (change_frame _) as ((rr,tt),bb) eqn : Hchangee.
            assert (((r,t),b) == ((rr,tt),bb)).
            rewrite <- Hchange, <- Hchangee.
            reflexivity.
            do 2 destruct H2.
            simpl in H2, H3, H4.
            (* rewrite <- H2, <- H4, <- H3 in Hlower_target.*)

            assert ((fst (fst (snd (
      ((comp (bij_rotation r) (comp (bij_translation t) (if b then reflexion else Similarity.id)))
         (fst (conf (Good g_far))), snd (conf (Good g_far))))))) <?
                   (fst (fst (snd (conf (Good g))))) == true).
            rewrite <- Nat.ltb_lt in Hlower_target.
            rewrite <- Hlower_target.
            f_equiv.
            rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.
            repeat split.            
            exists (Good g).
            destruct b; auto.
            unfold Datatypes.id.
            rewrite 2 andb_true_iff; repeat split.
            generalize (dist_same ((comp (bij_rotation r)
                                         (comp (bij_translation t) (if b then reflexion else Similarity.id))) pos)), Dmax_6D, D_0;
              rewrite Rle_bool_true_iff.
            intro Hdist_0.
            rewrite Hconf.
            simpl (fst _).
            destruct b; rewrite dist_same;
            lra.
            unfold get_alive; rewrite Hconf; simpl in *; assumption.
            unfold get_alive; simpl in *; assumption.
            rewrite Hconf; simpl in *; rewrite Nat.leb_le; omega.
            intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy), (get_ident_compat Hxy).
            reflexivity.
            destruct Hpred as (Horigin, ?).
            specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
            unfold frame_choice_bijection, Frame, Datatypes.id in *.
            rewrite <- Horigin.
            unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.

            (* rewrite Hchangee, H2, H3, H4. *)
            rewrite Hconf; simpl.
            fold Frame. fold Spect_ILA.
            fold Frame in Hchangee. fold Spect_ILA in Hchangee.
            destruct (change_frame _) eqn : Heq.
            destruct p.
            rewrite H3.
            assert (tt = r1). assert (snd (fst (rr,tt,bb)) = (snd (fst (r0,r1,b0)))).
            auto. rewrite Hchangee. auto.
            now simpl in H6.
            auto. 
            simpl. rewrite H4, H6; clear H6.
            assert (rr = r0). assert (fst (fst (rr,tt,bb)) = (fst (fst (r0,r1,b0)))).
            auto. rewrite Hchangee. auto.
            auto.
            rewrite H2, H6; clear H6.
            assert (bb = b0). assert (snd (rr,tt,bb) = (snd (r0,r1,b0))).
            auto. rewrite Hchangee. auto.
            now simpl in H6.
            rewrite H6.
            destruct b0; simpl; reflexivity.
            reflexivity.
            simpl in H5.
            rewrite Nat.ltb_lt in H5.
            apply H5.
            unfold get_alive; simpl.
            unfold round.
            assert(Hpred_backup := Hpred).
            destruct Hpred as (?,(?,?)).
            specialize (H4 (Good g_far)).
            rewrite H4.
            simpl ((lift _ _)).
            unfold upt_aux, map_config.
            destruct (conf (Good g_far)) as (p_far, ((i_far,l_far),a_far)) eqn : Hconf_far.
            destruct (upt_robot_dies_b _) eqn : Hbool_far; try now simpl.            
            simpl.
            specialize (Hexecuted (g_far)).
            assert (Halive_far : get_alive (round rbg_ila da conf (Good g_far)) == false).
            rewrite round_good_g.
            simpl ; unfold upt_aux, map_config.
            rewrite Hbool_far.
            unfold get_alive; simpl.
            rewrite Hconf_far;
              now simpl.
            apply Hpred_backup.
            assert (get_light (conf (Good g_far)) == true).
            {
              apply (Hexecuted da).
              apply  Hpred_backup.
              assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
              unfold get_alive; rewrite Hconf_far; now simpl.
              set (target := choose_target _) in *. 

              rewrite <- H5. rewrite 2 andb_true_iff in H0. destruct H0 as ((?,?),?).
              rewrite <- (get_alive_compat H). auto.
              now simpl in *.
            }
            set (target := choose_target _) in *. 

            assert (Htarget_light : get_light target = true).
            rewrite (get_light_compat H).
            rewrite Hconf_far in H5.
            now unfold get_light; simpl in *.
            assert (Hlight_off_first := light_off_first (reflexivity _) Htarget_light).
            unfold For_all in *.
            set (new_pos := choose_new_pos _ _) in *.
              assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
              destruct Hchoose_correct as (Hdist_dp, Hdist_d).
            unfold obs_from_config, Spect_ILA in Hdist_dp.
            assert ((dist pos_r p_far) <= Dp)%R.
            { destruct Hconfr as (Hpos_rl,_).
              revert Hpos_rl; intros Hpos_rl.
              assert (Hpos_rl' : @equiv R2 R2_Setoid (retraction
              (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id)))
              (fst (new_pos, false))) pos_r)
                by (rewrite <- Hpos_rl; destruct b; now simpl). 
              rewrite <- Inversion in Hpos_rl'.
              destruct b;
                rewrite (RelationPairs.fst_compat _ _ _ _ H) in Hdist_dp;
               
              simpl (fst _) in Hpos_rl';
              unfold equiv, R2_Setoid in Hpos_rl';
              rewrite <- Hpos_rl' in Hdist_dp;
              rewrite (frame_dist pos_r p_far (@change_frame (prod R2 ILA) Loc State_ILA Identifiers 
                 (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                 robot_choice_RL Frame Choice inactive_choice_ila da conf g));
              unfold frame_choice_bijection, Frame; fold Frame; try rewrite Hchange;
              simpl in *; lra. 
            }
            unfold upt_robot_dies_b in Hbool_far.
            rewrite orb_true_iff in Hbool_far.
            destruct Hbool_far as [Htoo_close_so_lighted|Htoo_far_but_path_conf].
            rewrite existsb_exists in *.
            destruct Htoo_close_so_lighted as (too_close, (Hin_too_close, Hdist_too_close)).
            ++ unfold executioner_means_light_off in *.
               rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff in Hin_too_close.
               destruct Hin_too_close as (([g_too_close | byz], (Hspec_too_close, Hnames_too_close)), (Hident_too_close, Halive_too_close));
                 try (assert (Hfalse := In_Bnames byz);
                      now simpl in *).
                   specialize (Hexecutioner g_too_close da Hpred_backup).
                   rewrite <- Hspec_too_close in Halive_too_close.
                   unfold get_alive in *.
                   simpl (snd (snd _)) in *.
                   specialize (Hexecutioner Halive_too_close).
                   assert (Hex : (exists g' : G,
                    snd (snd (conf (Good g'))) = true /\
                    get_ident (conf (Good g_too_close)) < get_ident (conf (Good g')) /\
                    (dist (get_location (conf (Good g_too_close)))
                       (get_location (conf (Good g'))) <= D)%R)).
                   { exists g_far.
                     repeat split; try now simpl.
                     assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
                     unfold get_alive; rewrite Hconf_far; now simpl.
                     rewrite <- (get_alive_compat H) in H7.
                     rewrite 2 andb_true_iff in H0.
                     destruct H0 as ((H0,H0_aux), H0').
                     unfold get_alive in H7; simpl in H7; rewrite H0_aux in H7.
                     now symmetry.
                     rewrite Nat.ltb_lt in Hident_too_close.
                     rewrite <- Hspec_too_close in Hident_too_close.
                     unfold get_ident in *; simpl in *; auto.
                     rewrite <- Hspec_too_close, Rle_bool_true_iff in Hdist_too_close.
                     unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_too_close.
                     rewrite (frame_dist _ _ (change_frame da conf g_far)).
                     unfold frame_choice_bijection, Frame; now simpl in *.
                   }
                   specialize (Hexecutioner Hex).
                   clear Hex.

                   
                   specialize (Hlight_off_first ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf (Good g_too_close))), snd (conf (Good g_too_close)))).
                   unfold equiv, bool_Setoid, eq_setoid in Hlight_off_first.
                   rewrite <- Hlight_off_first, <- Hexecutioner.
                   unfold get_light; now simpl in *.
                   unfold obs_from_config, Spect_ILA.
                   rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.                   repeat split.
                   exists (Good g_too_close).
                   destruct b; reflexivity.
                   rewrite 2 andb_true_iff.
                   rewrite Rle_bool_true_iff.
                   replace (fst
        ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g_too_close))), snd (conf (Good g_too_close))))%R
                     with
                       ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g_too_close))))%R.
                   unfold Datatypes.id.
                   assert (Hframe := frame_dist (fst (conf (Good g_too_close))) pos ((r,t),b)).
                   unfold frame_choice_bijection, Frame in Hframe.
                   assert (dist (fst (conf (Good g_too_close))) pos <= Dmax)%R.
                   rewrite Rle_bool_true_iff in Hdist_too_close.
                   unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_too_close.
                   rewrite <- Hspec_too_close in Hdist_too_close.
                   assert ((dist (fst (conf (Good g_too_close)))
                                 (fst (conf (Good g_far))) <= D)%R).
                   rewrite (frame_dist _ _ (change_frame da conf g_far)).
                   unfold frame_choice_bijection, Frame, Datatypes.id in *.
                   now simpl; simpl in Hdist_too_close.
                   rewrite (RelationPairs.fst_compat _ _ _ _ H) in H0.
                   simpl (fst _) in H0.
                   revert H0; intros H0.
                   specialize (Hless_that_Dp g).
                   unfold get_alive in Hless_that_Dp;
                     rewrite Hconf, Halive_r in Hless_that_Dp;
                     simpl (snd (snd _)) in Hless_that_Dp.
                   specialize (Hless_that_Dp (reflexivity _)).
                   destruct (Rle_bool (dist pos (fst (conf (Good g_far)))) Dp) eqn : Hhow_far.
                   rewrite Rle_bool_true_iff, dist_sym in Hhow_far.
                   assert (Hti := RealMetricSpace.triang_ineq (fst (conf (Good g_too_close))) (fst (conf (Good g_far))) pos ).
                   rewrite Hconf_far in Hti at 2.
                   simpl ( (fst _)) in Hti.
                   rewrite dist_sym in H6.
                   generalize (D_0), Dmax_6D.
                   unfold Dp in *.
                   rewrite Hconf_far in *; simpl (fst _) in *.
                   lra.
                   rewrite Rle_bool_false_iff in Hhow_far.
                   assert (Hlight_close_first :=
                             @light_close_first
                               _ _  (reflexivity _) Htarget_light).
                   apply Rnot_le_gt in Hhow_far.
                   assert ((dist (0, 0)
                          (get_location target) > Dp)%R).
                   destruct Hpred_backup as (Horigin, _).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   revert Horigin; intros Horigin.
                   rewrite <- Horigin. revert H; intro H; rewrite H.
                   rewrite (frame_dist _ _ (r,t,b)) in Hhow_far.
                   unfold frame_choice_bijection, Frame in *.
                   fold Frame in *. rewrite Hchange in *.
                   revert Hhow_far. rewrite Hconf_far, Hconf.
                   unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.
                   now destruct b; simpl in *.
                   specialize (Hlight_close_first H8).
                   clear H8.
                   unfold For_all in Hlight_close_first.
                   revert Hless_that_Dp; intros Hless_that_Dp.
                   assert (get_alive (conf (Good g_far)) = true).
                   { rewrite 2 andb_true_iff in H0; destruct H0 as ((H0, Haux),H0').
                     assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
                     unfold get_alive; rewrite Hconf_far; now simpl.
                     rewrite <- H8.
                     rewrite <- (get_alive_compat H).
                     unfold get_alive in *; auto. 
                     }
                   specialize (Hexecuted da Hpred_backup H8 Halive_far).
                   destruct Hless_that_Dp as (g_less, (Halive_less, (Hident_less, Hpos_less))).
                   rewrite Hconf in *. rewrite Halive_r in *. omega. 
                   rewrite <- Nat.le_succ_l in Hident_g'.
                   intros g_near Halive_near  Hdist_near Hindent_near.
                   simpl.
                   assert (Hlight_off_first_2 := @light_off_first spect _ (reflexivity _)).
                   unfold spect, target in *.
                   rewrite (get_light_compat H) in Hlight_off_first_2.
                   unfold get_light in *; rewrite Hconf_far in Hexecuted;
                     simpl ( snd (fst _)) in *.
                   specialize (Hlight_off_first_2 Hexecuted).
                   unfold For_all in Hlight_off_first_2.
                   specialize (Hlight_off_first_2 (((comp (bij_rotation r)
                                       (comp (bij_translation t)
                                          (if b then reflexion else Similarity.id)))
                                      (fst (conf (Good g_near))), snd (conf (Good g_near))))).
                   destruct (conf (Good g_near)) as (p_near, ((i_near, l_near), a_near)) eqn : Hconf_near.
                   simpl (snd (fst  _)) in *.
                   apply Hlight_off_first_2.
                   {
                     unfold obs_from_config, Spect_ILA.
                     rewrite make_set_spec, filter_InA, config_list_InA,
                     3 andb_true_iff, Rle_bool_true_iff.
                     repeat split.
                     exists (Good g_near).
                     rewrite Hconf_near; destruct b; now simpl.
                     assert (dist p_near pos <= Dmax)%R.
                     unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.
                     now simpl in *.
                     rewrite (frame_dist _ _ (r,t,b)) in H9.
                     unfold frame_choice_bijection, Frame in H9; fold Frame in H9.
                     destruct b; simpl in *. lra.
                     lra.
                     now simpl in *.
                     now simpl in *.
                     
                     unfold get_ident in *; simpl in *; auto.  rewrite Nat.leb_le; omega.  
                     intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy), (get_ident_compat Hxy).
                     reflexivity.
                   }
                   
                   assert (Hpos_less' := Hpos_less).
                   apply Rle_not_gt in Hpos_less.
                   destruct Hpos_less.
                   
                   destruct Hpred_backup as (Horigin, _).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   revert Horigin; intros Horigin.
                   rewrite Hconf in *;
                     unfold get_location, State_ILA, OnlyLocation, AddInfo,
                     get_location, Datatypes.id in *;
                     simpl (fst _) in *.

                   specialize (Hlight_close_first (((comp (bij_rotation r)
                                       (comp (bij_translation t)
                                          (if b then reflexion else Similarity.id)))
                                                      (fst (conf (Good g_less))), snd (conf (Good g_less))))).
                   clear H8.
                   assert (dist (0, 0)%R
                          (fst
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (conf (Good g_less))),
                              snd (conf (Good g_less)))) ==
                           dist pos (fst (conf (Good g_less)))).
                   {
                     rewrite <- Horigin.
                     rewrite (frame_dist pos _ (change_frame da conf g)).
                     unfold frame_choice_bijection, Frame in *.
                     destruct (change_frame _) as ((?,?),xb) eqn : Hxchange;
                       destruct xb, b; try discriminate;
                     try (assert (fst (fst (r0, r1, true)) = fst (fst (r, t, true)) /\ snd (fst  (r0, r1, true)) = snd (fst (r, t, true)))
                       by (
                           rewrite Hchange;
                           split; reflexivity));
                      try (assert (fst (fst (r0, r1, false)) = fst (fst (r, t, false)) /\ snd (fst  (r0, r1, false)) = snd (fst (r, t, false)))
                       by (
                           rewrite Hchange;
                           split; reflexivity));
                     simpl in H8;
                     destruct H8 as (H8_a, H8_b);
                     try rewrite H8_a ,H8_b;
                     try now simpl in *.
                   }
                   rewrite <- H8.
                   apply Hlight_close_first.
                   unfold obs_from_config, Spect_ILA.
                   rewrite make_set_spec, filter_InA, config_list_InA,
                   3 andb_true_iff, Rle_bool_true_iff.
                   repeat split. 
                   exists ((Good g_less)).
                   destruct b; reflexivity.
                   simpl (fst _).
                   rewrite (frame_dist _ _ (r,t,b)) in Hpos_less'.
                   unfold frame_choice_bijection, Frame in *; fold Frame in *.
                   unfold Dp in *; generalize D_0; destruct b;
                   rewrite dist_sym in Hpos_less';
                   simpl in *;
                   lra.
                   now simpl in *.
                   now simpl in *.
                   rewrite Nat.leb_le.
                   unfold get_ident in *; simpl in *; omega.
                   intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy). 
                   rewrite (get_alive_compat Hxy), (get_ident_compat (Hxy)).
                   reflexivity. 
                   rewrite (frame_dist _ _ ((r,t),b)) in H7.
                   now unfold frame_choice_bijection, Frame; destruct b; simpl in *. 
                   now simpl.
                   rewrite Nat.leb_le.
                   rewrite Nat.ltb_lt in *.
                   transitivity (get_ident (((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
         (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))).
                   unfold get_ident in *; rewrite <- Hspec_too_close, Hconf_far in *;
                     simpl in *. omega.
                   assert (get_ident
    ((comp (bij_rotation r)
        (comp (bij_translation t) (if b then reflexion else Similarity.id)))
       (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))) <
  get_ident
    ((comp (bij_rotation r)
        (comp (bij_translation t) (if b then reflexion else Similarity.id)))
       (fst (pos, (ident, light, alive))), snd (pos, (ident, light, alive)))).
                   assert (Htarget_lower:= target_lower).
                   specialize (Htarget_lower spect
                                             
                                 ((comp (bij_rotation r)
        (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                    (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far)))
                                 ((comp (bij_rotation r)
        (comp (bij_translation t) (if b then reflexion else Similarity.id)))
       (fst (pos, (ident, light, alive))), snd (pos, (ident, light, alive)))
                                 

                              ).
                   unfold get_ident in *; apply Htarget_lower.
                   unfold spect, obs_from_config, Spect_ILA.
                   rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.
                   repeat split.            
                   exists (Good g).
                   destruct b; rewrite Hconf; auto.
                   unfold Datatypes.id.
                   
                   rewrite 2 andb_true_iff; repeat split.
                   generalize (dist_same ((comp (bij_rotation r)
                                                (comp (bij_translation t) (if b then reflexion else Similarity.id))) pos)), Dmax_6D, D_0;
                     rewrite Rle_bool_true_iff.
                   intro Hdist_0.
                   destruct b; rewrite dist_same;
                   lra.
                   unfold get_alive; simpl in *; assumption.
                   unfold get_alive; simpl in *; assumption.
                   rewrite Nat.leb_le.
                   reflexivity.
                   intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy). 
                   assert (Hcompat := get_ident_compat Hxy).
                   unfold get_ident in Hcompat.
                   rewrite Hcompat.
                   reflexivity.
                   destruct Hpred_backup as (Horigin, ?).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   unfold frame_choice_bijection, Frame, Datatypes.id in *.
                   rewrite <- Horigin.
                   unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                   rewrite Hchange, Hconf; destruct b; simpl; reflexivity.
                   destruct b; rewrite <- H; unfold target, spect, obs_from_config, Spect_ILA;
                   unfold get_alive, get_ident; reflexivity. 
                   unfold get_ident in *; simpl in *; 
                   destruct b; omega.
                   intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy). 
                   rewrite (get_alive_compat Hxy), (get_ident_compat (Hxy)).
                   reflexivity. 
            ++ specialize (Hpath_backup g_far).
               assert (get_alive (conf (Good g_far)) == true).
               rewrite 2 andb_true_iff in H0.
               destruct H0 as ((H0, H0_aux), H0').
               rewrite <- H0_aux, (get_alive_compat H).
               unfold get_alive; rewrite Hconf_far; now simpl.
               simpl in H7.
               specialize (Hpath_backup H7); clear H7.
               destruct Hpath_backup as [Hident_0|Hpath_backup].
               rewrite (ident_preserved _ _ Hpred_backup) in Hident_0.
               assert (get_alive (round rbg_ila da conf (Good g_far)) = true).
               apply ident_0_alive; intuition.
               rewrite H7 in *; discriminate.
               rewrite forallb_existsb, forallb_forall in Htoo_far_but_path_conf.
               destruct Hpath_backup as (g_too_close, (Halive_close,( Hdist_close, Hident_close))). 
               specialize (Htoo_far_but_path_conf
                             ((((let (p, b) := change_frame da conf g_far in
                                 let (r, t) := p in
                                 comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf (Good g_too_close))), snd (conf (Good g_too_close)))))).
               rewrite negb_true_iff, Rle_bool_false_iff in Htoo_far_but_path_conf.
               destruct Htoo_far_but_path_conf.
               rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff.
               repeat split.
               ** exists (Good g_too_close).
                  split.
                  destruct (change_frame da conf g_far) as (?,b0); destruct b0;
                    now simpl.
                  apply In_names.
               ** rewrite Nat.ltb_lt.
                  unfold get_ident in *; simpl in Hident_close; simpl.
                  auto.
               ** rewrite <- Halive_close.
                  now unfold get_alive; simpl.
               ** rewrite dist_sym, (frame_dist _ _ (change_frame da conf g_far)) in Hdist_close.
                  unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                  unfold frame_choice_bijection, Frame in Hdist_close; fold Frame in *.
                  revert Hdist_close; intros Hdist_close.
                  destruct (change_frame _ _ g_far) as ((r_f, t_f), b_f)
                                                         eqn : Hchange_far.
                  now destruct b_f; simpl in *.
            ++ simpl.
               rewrite 2 andb_true_iff in H0.
               destruct H0 as ((H0, H0_aux), H0').
               rewrite <- H0_aux.
               rewrite (get_alive_compat H).
               now unfold get_alive; simpl.
         }
         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.
         rewrite 2 andb_true_iff in H0; destruct H0 as ((H0, H0'), Haux).
         rewrite Rle_bool_true_iff in H0.
         rewrite (RelationPairs.fst_compat _ _ _ _ H) in H0.
         revert H0; intros H0.
         assert (Hdist_round : (dist (fst (conf (Good g_far))) (fst (round rbg_ila da conf (Good g_far))) <= D)%R).
         rewrite <- Rle_bool_true_iff.
         assert (Hd := dist_round_max_d g_far Hpred Hpath_backup).
         destruct (conf (Good g_far)) as (p_far,((i_far, l_far), a_far)) eqn : Hconf_far.
         assert (get_alive ( ((comp (bij_rotation r)
          (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                     (fst (p_far, (i_far, l_far, a_far))), snd (p_far, (i_far, l_far, a_far))))
                      ==
                      get_alive (conf (Good g_far))).
         unfold get_alive; rewrite Hconf_far; now simpl.
         rewrite <- (get_alive_compat H) in H2.
         rewrite Hconf_far in H2.
         rewrite H0' in H2.
         now specialize (Hd (symmetry H2)).
         assert (Hconf_r_equiv : round rbg_ila da conf (Good g) == (pos_r, (ident_r, light_r, alive_r))) by now rewrite Hconf_r.
         rewrite (fst_compat Hconf_r_equiv).

         simpl ((fst (pos_r, (ident_r, light_r, alive_r)))).
         assert (dist ((comp (bij_rotation r_r)
            (comp (bij_translation t_r) (if b_r then reflexion else Similarity.id)))
           (fst (round rbg_ila da conf (Good g_far))))
                      ((comp (bij_rotation r_r)
            (comp (bij_translation t_r) (if b_r then reflexion else Similarity.id)))
           pos_r) <= Dmax)%R.
         assert (dist (fst (round rbg_ila da conf (Good g_far))) pos_r <= Dmax)%R.
         destruct (conf (Good g_far)) as (p_far, ((i_far, l_far), a_far)) eqn : Hconf_far.
         assert ((dist pos_r p_far) <= Dp)%R.
         { destruct Hconfr as (Hpos_rl,_).
           set (new_pos := choose_new_pos _ _) in *.
              assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
              destruct Hchoose_correct as (Hdist_dp, Hdist_d).
            
              assert (Hpos_rl' : retraction
              (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id)))
              (fst (new_pos, false)) == pos_r) by (rewrite <- Hpos_rl; destruct b; now simpl). 
              rewrite <- Inversion in Hpos_rl'.
              simpl (fst _) in Hpos_rl'.
              unfold equiv, R2_Setoid in Hpos_rl';
                simpl (obs_from_config _ _) in *. 
                rewrite <- Hpos_rl' in Hdist_dp. 
              destruct b; unfold new_pos, spect in *;
                rewrite (fst_compat H) in Hdist_dp;
              rewrite (@frame_dist pos_r p_far (@change_frame (prod R2 ILA) Loc State_ILA Identifiers 
                 (prod R2 NoCollisionAndPath.light) (prod (prod R R2) bool) bool bool
                 robot_choice_RL Frame Choice inactive_choice_ila da conf g));
              unfold frame_choice_bijection, Frame; fold Frame; try rewrite Hchange;
              simpl in *; lra. 
            }
            simpl (fst _) at 1 in Hdist_round.
            assert (Htri := RealMetricSpace.triang_ineq (fst (round rbg_ila da conf (Good g_far))) p_far pos_r).
            rewrite dist_sym in Hdist_round, H2.
            generalize D_0, Dmax_6D.
            unfold Dp in *. lra.
            rewrite (frame_dist _ _ ((r_r, t_r), b_r)) in H2.
            unfold frame_choice_bijection, Frame in H2; fold Frame in H2.
            destruct b_r; now simpl in *.
            destruct b_r; now simpl in *.
            intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy),
                           (get_alive_compat Hxy), (get_ident_compat Hxy);
            reflexivity.
  Qed.


Lemma executioner_means_light_off_round :
  forall conf da,
    da_predicat da ->
    path_conf conf ->
    no_collision_conf conf -> 
    executioner_means_light_off conf ->
    executed_means_light_on conf ->
    exists_at_less_that_Dp conf ->
    executioner_means_light_off (round rbg_ila da conf).

Proof.
  intros conf da Hpred Hpath Hcol Hexecutioner Hexecuted Hexists.
  assert (Hexecuted_round := executed_means_light_on_round Hpred Hpath Hcol Hexecutioner Hexecuted Hexists).
  - intros g da' Hpred' Halive_r (g_dead, (Halive_dead, (Hident_dead, Hdist_dead))).
    apply (moving_means_light_off conf g Hpred Halive_r).
    specialize (Hexecuted_round g_dead da' Hpred' Halive_dead).
    assert (Halive_dead_r: get_alive
                      (round rbg_ila da' (round rbg_ila da conf) (Good g_dead)) =
                    false).
    { rewrite (round_good_g g_dead (round rbg_ila da conf)).
      unfold get_alive;
      simpl.
      unfold upt_aux, map_config.
      destruct (upt_robot_dies_b _) eqn : Hbool_dead.
      + destruct ((round rbg_ila da conf (Good g_dead))) as (?,((?,?),?));
          intuition.
      + destruct ((round rbg_ila da conf (Good g_dead))) as (pos_dead_r,((ident_dead_r,light_dead_r),alive_dead_r)) eqn : Hconf_dead_r;
          simpl;  intuition.
        unfold upt_robot_dies_b in Hbool_dead.
        rewrite orb_false_iff in Hbool_dead.
        destruct Hbool_dead as (Hnear, _).
        rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hnear.
        unfold get_alive in *; simpl in Halive_dead; rewrite Halive_dead.
        destruct (change_frame _ (round _ _ _) g_dead) as ((r_dead, t_dead), b_dead) eqn : Hchange_r'.
        specialize (Hnear
                      (((comp (bij_rotation r_dead)
                       (comp (bij_translation t_dead)
                          (if b_dead then reflexion else Similarity.id)))
                      (fst (round rbg_ila da conf (Good g))),
                   snd (round rbg_ila da conf (Good g))))).
        rewrite <- Hnear.
        rewrite negb_false_iff, Rle_bool_true_iff.        
        unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
        clear Hnear.
        rewrite <- Hconf_dead_r in Hdist_dead.
        assert (dist
                  ((comp (bij_rotation r_dead)
                         (comp (bij_translation t_dead)
                               (if b_dead then reflexion else Similarity.id)))
                     (fst (round rbg_ila da conf (Good g))))
                  ((comp (bij_rotation r_dead)
                         (comp (bij_translation t_dead)
                               (if b_dead then reflexion else Similarity.id)))
                     (fst (round rbg_ila da conf (Good g_dead)))) <= D)%R.
        rewrite (frame_dist _ _ ((r_dead, t_dead), b_dead)) in Hdist_dead.
        unfold frame_choice_bijection, Frame in Hdist_dead.
        now destruct b_dead; simpl in *. 
        now destruct b_dead; simpl in *.
        rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff.
        repeat split.
        exists (Good g).
        split; try apply In_names; try (destruct b_dead; reflexivity).
        rewrite Nat.ltb_lt.
        unfold get_ident in *. rewrite <- Hconf_dead_r in *; now simpl in *.
        rewrite <- Hconf_dead_r in *; now simpl in *.
      + apply Hpred'.
    }
    specialize (Hexecuted_round Halive_dead_r).
    assert (Hexecuted_not_moving := light_on_means_not_moving_before g_dead Hpred Hpath Halive_dead Hexecuted_round).
    intros Hnot_moving.
    rewrite round_good_g in Halive_dead; try apply Hpred.
    simpl in Halive_dead.
    unfold upt_aux, map_config in *.
    destruct (upt_robot_dies_b _) eqn : Hbool_r;
      unfold get_alive in Halive_dead;
      destruct (conf (Good g_dead)) as (p_dead, ((i_dead, l_dead), a_dead)) eqn : Hconf_dead; simpl in Halive_dead.
    + discriminate.
    + unfold upt_robot_dies_b in Hbool_r.
      rewrite orb_false_iff in Hbool_r.
      destruct Hbool_r as (Hnear, _).
      rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hnear.
      destruct (change_frame _ _ g_dead) as ((r_dead, t_dead), b_dead) eqn : Hchange_dead.
      specialize (Hnear ((comp (bij_rotation r_dead)
                               (comp (bij_translation t_dead)
                                     (if b_dead then reflexion else Similarity.id)))
                           (fst (conf (Good g))), snd (conf (Good g)))).
      rewrite negb_true_iff, Rle_bool_false_iff in Hnear.        
      destruct Hnear.
      rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff.
      repeat split.
      exists (Good g).
      split; try apply In_names; try (destruct b_dead; reflexivity).
      rewrite Nat.ltb_lt.
      rewrite <- 2 ident_preserved in Hident_dead.
      unfold get_ident in *. rewrite <- Hconf_dead in *. now simpl in *.
      apply Hpred.
      apply Hpred.
      apply still_alive_means_alive in Halive_r.
      unfold get_alive in *; now simpl in *.
      apply Hpred.
      assert (dist
                  ((comp (bij_rotation r_dead)
                         (comp (bij_translation t_dead)
                               (if b_dead then reflexion else Similarity.id)))
                     (fst (round rbg_ila da conf (Good g))))
                  ((comp (bij_rotation r_dead)
                         (comp (bij_translation t_dead)
                               (if b_dead then reflexion else Similarity.id)))
                     (fst (round rbg_ila da conf (Good g_dead)))) <= D)%R.
      rewrite (frame_dist _ _ ((r_dead, t_dead), b_dead)) in Hdist_dead.
      unfold frame_choice_bijection, Frame in Hdist_dead.
      now destruct b_dead; simpl in *. 
      unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
      rewrite Hnot_moving, Hconf_dead, Hexecuted_not_moving.
      now destruct b_dead; simpl in *.



Qed.

Parameter conf_init : config.

Axiom conf_init_or_exists_conf_before : forall conf,
(*    conf == conf_init \/*)
    exists conf_p da_p, da_predicat da_p /\ conf == round rbg_ila da_p conf_p.


Lemma light_off_means_alive_next : forall conf da g,
    da_predicat da ->
    path_conf conf ->
    get_alive (conf (Good g)) = true ->
    get_light (conf (Good g)) = false ->
    executed_means_light_on conf ->
    get_alive (round rbg_ila da conf (Good g)) = true.
Proof.
  intros conf da g Hpred Hpath Halive Hlight Hexec.
  destruct (get_alive (round rbg_ila da conf (Good g))) eqn : Halive_round; try auto.
  specialize (Hexec g da Hpred Halive Halive_round).
  rewrite Hexec in *; discriminate. 
Qed.



Lemma executioner_next_means_moving :
   forall conf g da (* da' *),
     executed_means_light_on (round rbg_ila da conf) ->
     da_predicat da -> (*da_predicat da' -> *)path_conf conf -> 
     get_alive (conf (Good g)) = true ->
    (exists g', get_alive (round rbg_ila da conf (Good g')) = true /\
               get_ident (round rbg_ila da conf (Good g)) < get_ident (round rbg_ila da conf (Good g')) /\
               (dist (get_location (round rbg_ila da conf (Good g))) (get_location (round rbg_ila da conf (Good g')))
                <= D)%R) ->
    get_location (conf (Good g)) <> get_location (round rbg_ila da conf (Good g)).
Proof.
  intros conf g da (*da'*) Hex_light Hpred (*Hpred'*) Hpath Halive (g', (Halive_exec, (Hident_exec, Hdist_exec))).
  assert (Halive_exec_backup := Halive_exec).
  rewrite round_good_g in Halive_exec; try apply Hpred.
  unfold get_alive in Halive_exec; simpl in Halive_exec.
  unfold upt_aux, map_config in Halive_exec.
  destruct (conf (Good g')) as (pos', ((ident', light'), alive')) eqn : Hconf'.
  destruct (upt_robot_dies_b _) eqn : Hbool.
  - now simpl in *.
  - intro Hdist.
    assert (dist (get_location (conf (Good g))) (get_location (conf (Good g'))) <= 2*D)%R.
    {
      rewrite Hdist.
      assert (Hdist' := dist_round_max_d g' Hpred Hpath (still_alive_means_alive conf g' Hpred Halive_exec_backup)).
      assert (Htri := RealMetricSpace.triang_ineq (get_location (conf (Good g'))) (get_location (round rbg_ila da conf (Good g'))) (get_location (round rbg_ila da conf (Good g)))).
      apply Rle_bool_true_iff in Hdist'.
      assert (dist (get_location (conf (Good g'))) (get_location (round rbg_ila da conf (Good g))) <=
          D +
          dist (get_location (round rbg_ila da conf (Good g')))
               (get_location (round rbg_ila da conf (Good g))))%R.
      lra.
      rewrite dist_sym in Hdist_exec.
      assert (dist (get_location (conf (Good g'))) (get_location (round rbg_ila da conf (Good g))) <=
          D +
          D)%R.
      lra.
      rewrite dist_sym. lra.
    }
    assert (get_light (round rbg_ila da conf (Good g')) = true).
    rewrite round_good_g; try apply Hpred.
    simpl; unfold upt_aux, map_config; rewrite Hbool.
    unfold rbg_fnc.
    destruct (move_to _) eqn : Hmove; try now (unfold get_light; simpl; rewrite Hconf'; simpl).
    exfalso.
    assert (Hfalse := move_to_Some_zone Hmove).
    set (new_pos := choose_new_pos _ _) in *.
    assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
    destruct Hchoose_correct as (Hdist_dp, Hdist_d).
    destruct (change_frame da conf g') as ((r, t), b) eqn : Hchange'. 
    specialize (Hfalse ((fun id : ident =>
                 ((comp (bij_rotation r)
                     (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                    (fst (conf id)), snd (conf id))) (Good g))).
    set (spect := obs_from_config _ _) in *.
    assert (((fun id : ident =>
             ((comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                (fst (conf id)), snd (conf id))) (Good g)
            ∈ spect)%set).
    unfold spect, obs_from_config, Spect_ILA.
    rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.
    repeat split.
    exists (Good g).
    destruct b; reflexivity.
    rewrite 2 andb_true_iff.
    rewrite Rle_bool_true_iff.
    repeat split.
    replace (fst
               ((comp (bij_rotation r)
                      (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                  (fst (conf (Good g))), snd (conf (Good g))))%R
                     with
                       ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g))))%R.
    unfold Datatypes.id.
    assert (Hframe := frame_dist (fst (conf (Good g))) (fst (conf (Good g'))) ((r,t),b)).
    unfold frame_choice_bijection, Frame in Hframe.
    assert (dist (fst (conf (Good g))) (fst (conf (Good g'))) <= Dmax)%R.
    revert H; intro H.
    unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in H.
    generalize Dmax_6D D_0.
    transitivity (2*D)%R.
    apply H.
    lra.
    rewrite <- Hconf'.
    destruct b; simpl in *; lra.
    now simpl.
    now unfold get_alive in *; simpl in *.
    now unfold get_alive in *; simpl in *.
    rewrite <- 2 ident_preserved in Hident_exec; auto. 
    rewrite <- Hconf', Nat.leb_le; unfold get_ident in *; simpl in *; omega.
    intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy). 
    assert (Hcompat := get_ident_compat Hxy).
    rewrite Hcompat.
    reflexivity.
    assert(Hfalse' : (dist new_pos (fst ((
              ((comp (bij_rotation r)
                  (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                 (fst (conf (Good g))), snd (conf (Good g)))) )) > 2 * D)%R).
    unfold spect in *.
    rewrite Hconf' in *. 
    destruct b; specialize (Hfalse H0); apply Hfalse.
    clear Hfalse H0; rename Hfalse' into Hfalse.
    destruct (round rbg_ila da conf (Good g')) as (pos_round', ((ident_round', light_round'), alive_round')) eqn : Hconf_round'.
    assert (round rbg_ila da conf (Good g') == (pos_round', ((ident_round', light_round'), alive_round'))) by now rewrite Hconf_round'.
    rewrite round_good_g in H0; try apply Hpred.
    destruct H0 as (Hpos_round',_).
    simpl in Hpos_round'.
    rewrite Hchange' in Hpos_round'.
    unfold upt_aux, map_config in Hpos_round'; rewrite Hbool in Hpos_round'.
    unfold rbg_fnc in *.
    unfold new_pos in *; rewrite Hmove in *.
    rewrite Hconf' in *; simpl (fst _) in Hpos_round'.
    assert (Hpos_round_aux :  retraction
                  (comp (bij_rotation r)
                     (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos  ==
                              pos_round').
    { destruct b; unfold new_pos; rewrite <- Hpos_round'; rewrite Hconf'.  f_equiv. unfold comp. simpl. f_equiv. }
    rewrite <- Inversion in Hpos_round_aux.
    unfold new_pos in *; rewrite Hconf' in *.
    rewrite <- Hpos_round_aux in *.
    revert Hdist_exec; intro Hdist_exec.
    replace (fst
               ((comp (bij_rotation r)
                      (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                  (fst (conf (Good g))), snd (conf (Good g))))%R
                     with
                       ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g))))%R in Hfalse.
    unfold Datatypes.id.
    assert (Hframe := frame_dist pos_round' (fst (conf (Good g))) ((r,t),b)).
    unfold frame_choice_bijection, Frame in Hframe.
    assert (dist pos_round' (fst (conf (Good g))) > 2*D)%R.
    rewrite Hframe.
    destruct b; simpl in *; lra. 
    clear Hframe.
    unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_exec.
    rewrite <- Hconf_round' in Halive_exec_backup.
    assert (Hdist_round := dist_round_max_d g Hpred Hpath (Halive)).
    unfold equiv, bool_Setoid, eq_setoid in Hdist_round.
    rewrite Rle_bool_true_iff in Hdist_round.
    assert (Hd_0 := D_0).
    assert (Htri := RealMetricSpace.triang_ineq pos_round' (fst (round rbg_ila da conf (Good g)))
                                                (fst (conf (Good g)))).
    assert ((dist pos_round' (fst (conf (Good g))) <=
          D +
          dist (fst (round rbg_ila da conf (Good g))) (fst (conf (Good g))))%R).
    rewrite dist_sym in Hdist_exec.
    simpl ( (fst (pos_round', (ident_round', light_round', alive_round')))) in *.
    transitivity (dist pos_round' (fst (round rbg_ila da conf (Good g))) +
                  dist (fst (round rbg_ila da conf (Good g))) (fst (conf (Good g))))%R.
    lra.
    apply (Rplus_le_compat_r).
    apply Hdist_exec.
    assert (dist pos_round' (fst (conf (Good g))) <=
            D + D)%R.
    transitivity (D + dist (fst (round rbg_ila da conf (Good g))) (fst (conf (Good g))))%R.
    lra.
    apply (Rplus_le_compat_l).
    unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.    
    rewrite dist_sym; apply Hdist_round.    
    lra.     
    destruct b; simpl; auto.
    assert (Hfalse := light_on_means_not_moving_before g' Hpred Hpath Halive_exec_backup H0).
    revert Hbool; intro Hbool.
    unfold upt_robot_dies_b in *.
    rewrite orb_false_iff in Hbool.
    destruct Hbool as (Hnot_near,_).
    rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hnot_near.
    destruct (change_frame da conf g') as ((r,t),b) eqn : Hchange'.
    
    specialize (Hnot_near (
                         ((comp (bij_rotation r)
                             (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                            (fst (conf (Good g))), snd (conf (Good g))))).
    rewrite negb_true_iff, Rle_bool_false_iff in Hnot_near.
    destruct Hnot_near.
    + rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff.
      repeat split.
      * exists (Good g).
        split; destruct b; auto; try apply In_names.
      * rewrite <- 2 ident_preserved in Hident_exec; try apply Hpred.
        unfold get_ident; simpl.
        now rewrite Nat.ltb_lt.
      * unfold get_alive in *; simpl in *; auto.
    + 
    unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.    
    assert (Hframe := frame_dist (fst (conf (Good g))) (fst (conf (Good g'))) ((r,t),b)).
    unfold frame_choice_bijection, Frame in Hframe.
    rewrite <- Hfalse, <- Hdist in Hdist_exec.
    rewrite Hframe in Hdist_exec.
    simpl in *; destruct b; simpl in*; lra.
Qed.





Lemma moving_means_alive_next :
forall conf g da,
    da_predicat da ->
    path_conf conf ->
    no_collision_conf conf ->
    executioner_means_light_off conf ->
    executed_means_light_on conf ->
    exists_at_less_that_Dp conf ->
    get_alive (conf (Good g)) = true ->
    get_location (conf (Good g)) <> (get_location (round rbg_ila da conf (Good g))) ->
    get_alive (round rbg_ila da conf (Good g)) = true.
Proof.
  intros conf g da Hpred Hpath Hcol Hexecutioner_light Hexecuted_light Hexists Halive Hmoving.
  rewrite round_good_g in *; try apply Hpred.
  destruct (change_frame da conf g) as ((r, t), b) eqn : Hchange_frame.
  unfold upt_aux, map_config in *.
  unfold rbg_ila in *.
  unfold get_alive in *.
  unfold update, UpdFun, upt_aux in *.
  destruct (conf (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  destruct (upt_robot_dies_b _) eqn : Hbool.
  - destruct Hmoving.
    unfold map_config.
    unfold lift, State_ILA, OnlyLocation, AddInfo, lift.
    simpl (fst _).
    unfold projT1.
    assert (Hbij := (retraction_section (frame_choice_bijection (r, t, b))) pos) .
    simpl in *.
    now rewrite Hbij.
  - simpl in *. 
    auto.
Qed.



  
Lemma executioner_next_means_alive_next conf :  
  forall g da,
    da_predicat da ->
    path_conf conf ->
    no_collision_conf conf ->
    executioner_means_light_off conf ->
    executed_means_light_on conf ->
    exists_at_less_that_Dp conf ->
    get_alive (conf (Good g)) = true ->
    (exists g', get_alive (round rbg_ila da conf (Good g')) = true /\
               get_ident (conf (Good g)) < get_ident (conf (Good g')) /\
               (dist (get_location (round rbg_ila da conf (Good g))) (get_location (round rbg_ila da conf (Good g')))
                    <= D)%R) ->
    get_alive (round rbg_ila da conf (Good g)) = true.
Proof.
  intros g da Hpred Hpath Hcol Hexecutioner_light Hexecuted_light Hexists Halive Hexecution.
  apply moving_means_alive_next; try auto.
  apply executioner_next_means_moving; try auto; try apply Hexecution.
  apply executed_means_light_on_round; try auto.
  repeat (destruct Hexecution as (?, Hexecution)). 
  exists x.
  repeat split; try auto. 
  rewrite <- 2 ident_preserved; try auto.
Qed. 
  


Lemma exists_at_less_round :   forall conf da,
    da_predicat da ->
    path_conf conf ->
    no_collision_conf conf -> 
    executioner_means_light_off conf ->
    executed_means_light_on conf ->
    exists_at_less_that_Dp conf ->
    exists_at_less_that_Dp (round rbg_ila da conf).      
Proof.
  intros conf da Hpred Hpath Hcol Hexecutioner Hexecuted Hexists.
  assert (Hexecuted_round := executed_means_light_on_round Hpred Hpath Hcol Hexecutioner Hexecuted Hexists).
  assert (Hexecutioner_round := executioner_means_light_off_round Hpred Hpath Hcol Hexecutioner Hexecuted Hexists).
  
  - intros g Halive H_not_0 Hlighted.
    assert (Hexists_backup := Hexists).
    specialize (Hexists g (still_alive_means_alive conf g Hpred Halive)).
    assert (Hlight_on_means := light_on_means_not_moving_before).
    assert (Hpath_backup := Hpath).
    specialize (Hpath g (still_alive_means_alive conf g Hpred Halive)).
    destruct Hpath as [H_0| H_exists_g'].
    + rewrite <- ident_preserved, H_0 in H_not_0; try auto.
      omega.
    + destruct H_exists_g' as (g', (Halive_g', (Hdist_g', Hident_g'))).
      assert (Halive' := Halive).
      rewrite round_good_g in Halive; try apply Hpred.
      unfold get_alive in Halive; simpl in Halive.
      unfold upt_aux, map_config in Halive.
      destruct (conf (Good g)) as (pos, ((ide, lig), ali)) eqn : Hconf.
      destruct (upt_robot_dies_b _) eqn : Hbool; simpl in Halive;
        try discriminate.
      assert (Htarget_in := @choose_target_in_spect (obs_from_config
                          (fun id : ident =>
                           ((let (p0, b) := change_frame da conf g in
                             let (r, t) := p0 in
                             comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((let (p0, b) := change_frame da conf g in
                               let (r, t) := p0 in
                               comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (conf (Good g))), snd (conf (Good g))))) _ (reflexivity _)).
      unfold obs_from_config at 2, Spect_ILA at 2 in Htarget_in;
        rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff, Rle_bool_true_iff in Htarget_in;
        try (now intros x y Hxy;
             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy), (get_ident_compat Hxy)).
      destruct Htarget_in as (([g_target | byz], Htarget_spec), (((Hdist_target, Halive_target), Halive_conf), Hident_target));
        try (assert (Hfalse := In_Bnames byz);
             now simpl in *). 
      destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
      destruct (get_light ((comp (bij_rotation r)
                     (comp (bij_translation t)
                        (if b then reflexion else Similarity.id)))
                             (fst (conf (Good g_target))), snd (conf (Good g_target)))) eqn : Hlight_target.
             * unfold executed_means_light_on in *.
               destruct (conf (Good g_target)) as (p_target, ((i_target,l_target), a_target)) eqn : Hconf_target.
               assert (get_alive (round rbg_ila da conf (Good g_target)) = true).
               { rewrite round_good_g; try apply Hpred.
                 unfold get_alive; simpl.
                 unfold upt_aux, map_config.
                 destruct (upt_robot_dies_b _ g_target) eqn : Hbool_target.
                 simpl.
                 assert (Halive_target_r : get_alive (round rbg_ila da conf (Good g_target)) = false).
                 rewrite round_good_g; try apply Hpred.
                 simpl; unfold upt_aux, map_config, get_alive; rewrite Hbool_target, Hconf_target.
                 now simpl.
                 apply robot_dead_means in Halive_target_r.
                 destruct Halive_target_r as [Hfalse|[(g_near,(Hident_near, (Halive_near, Hbool_near))) | Hfar]].
                 -- rewrite Htarget_spec in Halive_target. 
                    unfold get_alive in *; rewrite Hconf_target in *.
                    simpl in *.
                    now rewrite Hfalse in *; discriminate.
                 -- specialize (Hexecutioner g_near da Hpred Halive_near).
                    revert Hexecutioner; intros Hexecutioner.
                    assert ((exists g' : G,
                                get_alive (conf (Good g')) = true /\
                                get_ident (conf (Good g_near)) < get_ident (conf (Good g')) /\
                                (dist (get_location (conf (Good g_near)))
                                      (get_location (conf (Good g'))) <= D)%R)).
                    exists g_target.
                    repeat split.
                    rewrite Htarget_spec in Halive_target; unfold get_alive in *; simpl in *.
                    now rewrite Hconf_target in *; simpl in *.
                    assumption.
                    rewrite Rle_bool_true_iff in *.
                    now rewrite dist_sym.
                    specialize (Hexecutioner H); clear H.
                    assert ((forall g_near : G,
                                get_alive (conf (Good g_near)) = true ->
                                (dist (get_location (conf (Good g_near)))
                                      (get_location (pos, (ide, lig, ali))) <= Dmax)%R ->
                                get_ident (conf (Good g_near)) < get_ident (pos, (ide, lig, ali)) ->
                                get_light (conf (Good g_near)) = true)).
                    intros g0 Halive_0 Hdist_0 Hident_0.
                    assert (Hoff_first := (@light_off_first (obs_from_config
                                                               (fun id : ident =>
                                                                  ((comp (bij_rotation r)
                                                                         (comp (bij_translation t)
                                                                               (if b then reflexion else Similarity.id)))
                                                                     (fst (conf id)), snd (conf id)))
                                                               (Datatypes.id
                                                                  ((comp (bij_rotation r)
                                                                         (comp (bij_translation t)
                                                                               (if b then reflexion else Similarity.id)))
                                                                     (fst (conf (Good g)))), snd (conf (Good g))))) _ (reflexivity _ )).
                    rewrite Htarget_spec in Hoff_first.
                    specialize (Hoff_first Hlight_target).
                    unfold For_all in *.
                    specialize (Hoff_first ((comp (bij_rotation r)
                                                  (comp (bij_translation t)
                                                        (if b then reflexion else Similarity.id)))
                                              (fst (conf (Good g0))), snd (conf (Good g0)))).
                    unfold get_light in *.
                    simpl (snd (fst _)) in *.
                    apply Hoff_first.
                    unfold obs_from_config, Spect_ILA;
                      rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff, Rle_bool_true_iff.
                    repeat split.
                    exists (Good g0); destruct b; reflexivity.
                    rewrite Hconf.
                    unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                    rewrite (frame_dist _ _ (r,t,b)) in Hdist_0.
                    unfold frame_choice_bijection, Frame in *; fold Frame in *; 
                      destruct b; now simpl in *.
                    unfold get_alive in *; now simpl in *.
                    unfold get_alive in *; now simpl in *.
                    rewrite Hconf, Nat.leb_le.
                    destruct b; unfold get_ident in *; simpl in *; omega.
                    
                    intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy), (get_ident_compat Hxy); reflexivity.
                    assert (H_0 : get_ident (pos, (ide, lig, ali)) > 0).
                    {
                      rewrite <- ident_preserved, Hconf in *; auto.
                    }
                    specialize (Hexists H_0 H).
                    clear H.
                    rewrite Hconf_target; simpl.
                    destruct Hexists as (g_exi, (Halive_exi, (Hicent_exi, Hdist_exi))).
                    destruct (Rle_lt_dec (dist p_target pos) Dp).
                    assert (Hexec_near : (dist (get_location (conf (Good g_near))) pos <= Dmax)%R).
                    { 
                      rewrite Rle_bool_true_iff, Hconf_target, dist_sym in Hbool_near.
                      generalize Dmax_6D, D_0.
                      unfold Dp in *.
                      assert (Htri := RealMetricSpace.triang_ineq (get_location (conf (Good g_near))) p_target pos).
                      unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                      simpl (fst _) in Hbool_near.
                      simpl in *; lra.
                    }
                    assert (Hoff_first := @light_off_first (obs_from_config
                                                              (fun id : ident =>
                                                                 ((comp (bij_rotation r)
                                                                        (comp (bij_translation t)
                                                                              (if b then reflexion else Similarity.id)))
                                                                    (fst (conf id)), snd (conf id)))
                                                              (Datatypes.id
                                                                 ((comp (bij_rotation r)
                                                                        (comp (bij_translation t)
                                                                              (if b then reflexion else Similarity.id)))
                                                                    (fst (conf (Good g)))), snd (conf (Good g)))) _ (reflexivity _)).
                    rewrite Htarget_spec in Hoff_first.
                    unfold For_all, get_light in *; simpl (snd (fst _)) in *.
                    specialize (Hoff_first Hlight_target  (((comp (bij_rotation r)
                                                                  (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                                              (fst (conf (Good g_near))), snd (conf (Good g_near))))).
                    rewrite Hoff_first in Hexecutioner; try discriminate.
                    { unfold obs_from_config, Spect_ILA.
                      rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff, Rle_bool_true_iff.
                      repeat split.
                      exists (Good g_near); destruct b; reflexivity.
                      rewrite Hconf.
                      
                      rewrite (frame_dist _ _ (r,t,b)) in Hexec_near.
                      unfold frame_choice_bijection, Frame in *; fold Frame in *; 
                        destruct b; now simpl in *.
                      unfold get_alive in *; now simpl in *.
                      unfold get_alive in *; rewrite Hconf in *; simpl in *; assumption.
                      rewrite Hconf, Nat.leb_le.
                      assert (Htarget_lower := target_lower).
                   specialize (Htarget_lower  (obs_from_config
                      (fun id : ident =>
                       ((comp (bij_rotation r)
                           (comp (bij_translation t)
                              (if b then reflexion else Similarity.id)))
                          (fst (conf id)), snd (conf id)))
                      (Datatypes.id
                         ((comp (bij_rotation r)
                             (comp (bij_translation t)
                                (if b then reflexion else Similarity.id)))
                            (fst (conf (Good g)))), snd (conf (Good g))))
                 ((comp (bij_rotation r)
                     (comp (bij_translation t)
                        (if b then reflexion else Similarity.id)))
                    (fst (p_target, (i_target, l_target, a_target))),
                 snd (p_target, (i_target, l_target, a_target))) ((comp (bij_rotation r)
         (comp (bij_translation t) (if b then reflexion else Similarity.id)))
        (fst (conf (Good g))), snd (conf (Good g)))).
                   rewrite Hconf in Htarget_lower.
                   assert (get_ident (conf (Good g_target)) < get_ident (conf (Good g))).
                   unfold get_ident in *; simpl (fst _) in *; rewrite Hconf, Hconf_target; apply Htarget_lower.
                   unfold obs_from_config, Spect_ILA.
                   rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff.
                   repeat split.
                   exists (Good g).
                   now rewrite Hconf.
                   unfold Datatypes.id.
                   generalize (dist_same ((comp (bij_rotation r)
                                                (comp (bij_translation t) (if b then reflexion else Similarity.id))) pos)), Dmax_6D, D_0;
                     rewrite Rle_bool_true_iff.
                   intro Hdist_0.
                   simpl in Hdist_0; simpl.
                   rewrite Hdist_0.
                   lra.
                   simpl in *; assumption.
                   simpl in *; assumption.
                   rewrite Nat.leb_le. unfold get_ident; simpl; omega.
                   intros x y Hxy.
                   rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                   rewrite (get_alive_compat Hxy).
                   rewrite (get_ident_compat Hxy).
                   reflexivity.
                   destruct Hpred as (Horigin, ?).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   unfold frame_choice_bijection, Frame, Datatypes.id in *.
                   rewrite <- Horigin.
                   rewrite Hchange.
                   unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                   rewrite Hconf; simpl. destruct b; simpl; reflexivity.
                   rewrite <- Htarget_spec, Hconf.
                   reflexivity.
                   transitivity (get_ident (conf (Good g_target))).
                   unfold get_ident in *; simpl in *; omega.
                   unfold get_ident in *; rewrite Hconf in *; simpl in *; omega.
                   intros x y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy), (get_ident_compat Hxy); reflexivity.
                    }
                    assert (Hclose_first := @light_close_first (obs_from_config
                                                                  (fun id : ident =>
                                                                     ((comp (bij_rotation r)
                                                                            (comp (bij_translation t)
                                                                                  (if b then reflexion else Similarity.id)))
                                                                        (fst (conf id)), snd (conf id)))
                                                                  (Datatypes.id
                                                                     ((comp (bij_rotation r)
                                                                            (comp (bij_translation t)
                                                                                  (if b then reflexion else Similarity.id)))
                                                                        (fst (conf (Good g)))), snd (conf (Good g)))) _ (reflexivity _)).
                    rewrite Htarget_spec in Hclose_first.
                    unfold For_all, get_light in *; simpl (snd (fst _)) in *.
                    specialize (Hclose_first Hlight_target).
                    assert ((dist (0, 0)
                                  (get_location
                                     ((comp (bij_rotation r)
                                            (comp (bij_translation t)
                                                  (if b then reflexion else Similarity.id)))
                                        (fst (p_target, (i_target, l_target, a_target))),
                                      snd (p_target, (i_target, l_target, a_target)))) > Dp)%R).
                    { clear Hclose_first.
                      destruct Hpred as (Horigin, _).
                      specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                      revert Horigin; intros Horigin.
                      rewrite Hconf in *;
                        unfold get_location, State_ILA, OnlyLocation, AddInfo,
                        get_location, Datatypes.id in *.
                      rewrite <- Horigin.
                      clear Horigin.
                      rewrite (frame_dist _ _ (r,t,b)) in r0.
                      rewrite dist_sym.
                      rewrite Hchange.
                      unfold frame_choice_bijection, Frame in *;
                        destruct b; simpl in *; lra.
                    }                   
                    specialize (Hclose_first H ((comp (bij_rotation r)
                                                      (comp (bij_translation t)
                                                            (if b then reflexion else Similarity.id)))
                                                  (fst (conf (Good g_exi))), snd (conf (Good g_exi))));
                      clear H.
                    apply Rgt_not_le in Hclose_first.
                    destruct Hclose_first.
                    destruct Hpred as (Horigin, _).
                    specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                    revert Horigin; intros Horigin.
                    rewrite Hconf in *;
                      unfold get_location, State_ILA, OnlyLocation, AddInfo,
                      get_location, Datatypes.id in *.
                    rewrite <- Horigin.
                    clear Horigin.
                    rewrite (frame_dist _ _ (r,t,b)) in Hdist_exi.
                    revert Hdist_exi; intros Hdist_exi.
                    rewrite Hchange.
                    unfold frame_choice_bijection, Frame in *;
                      destruct b; simpl in *; lra.
                    unfold obs_from_config, Spect_ILA.
                    rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff, Rle_bool_true_iff.
                    repeat split.
                    exists (Good g_exi); destruct b; reflexivity.
                    rewrite Hconf.
                    rewrite (frame_dist _ _ (r,t,b)) in Hdist_exi.
                    unfold frame_choice_bijection, Frame in *; fold Frame in *; 
                      destruct b; unfold Dp in *; generalize Dmax_6D, D_0;
                        revert Hdist_exi; intros Hdist_exi;
                          rewrite dist_sym;
                          unfold get_location, State_ILA, OnlyLocation, AddInfo,
                          get_location, Datatypes.id in *;
                          simpl in *; lra.
                    unfold get_alive in *; now simpl in *.
                    unfold get_alive in *; rewrite Hconf in *; simpl in *; assumption.
                    rewrite Hconf, Nat.leb_le.
                    unfold get_ident in *; simpl in *;
                      omega.
                    intros x y Hxy.
                    rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                    rewrite (get_alive_compat Hxy).
                    rewrite (get_ident_compat Hxy).
                    reflexivity.
                 -- specialize (Hpath_backup g_target).
                    revert Hpath_backup; intro Hpath_backup.
                    rewrite <- Halive_target, Htarget_spec in Hpath_backup.
                    unfold get_alive at 1 2 in Hpath_backup.
                    rewrite Hconf_target in Hpath_backup;
                      simpl (snd (snd _)) in Hpath_backup.
                    specialize (Hpath_backup (reflexivity _)).
                    destruct Hpath_backup as [Hfalse| (g_near,(Halive_near, (Hdist_near, Hident_near)))].
                    assert (Halive_target_round : get_alive (round rbg_ila da conf (Good g_target)) = false).
                    {
                      rewrite round_good_g; try auto.
                      simpl.
                      unfold upt_aux, map_config; rewrite Hbool_target.
                      unfold get_alive; simpl.
                      now rewrite Hconf_target; simpl.
                    }
                    rewrite (ident_0_alive (round rbg_ila da conf) g_target) in Halive_target_round.
                    discriminate.
                    rewrite <- ident_preserved; try auto.
                    now rewrite Hconf_target.
                    rewrite Halive_target in Halive_near.
                    rewrite Hconf_target in *.
                    specialize (Hfar g_near Hident_near Halive_near).
                    rewrite negb_true_iff, Rle_bool_false_iff in Hfar.
                    destruct Hfar.
                    lra.
                 -- apply Hpred.
                 -- rewrite Hconf_target.
                    simpl.
                    rewrite Htarget_spec in Halive_target.
                    unfold get_alive in Halive_target; now simpl in *.
               }

               exists g_target.
               
               repeat split.
               -- assumption.
               -- rewrite <- 2 ident_preserved.
                  assert (Hlower_target := target_lower).
                  specialize (@Hlower_target (obs_from_config
                          (fun id : ident =>
                           ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (conf (Good g)))), snd (conf (Good g))))).
                  assert (In (((comp (bij_rotation r)
                            (comp (bij_translation t)
                               (if b then reflexion else Similarity.id)))
                           (fst (conf (Good g))), snd (conf (Good g))))
                           (obs_from_config
                       (fun id : ident =>
                        ((comp (bij_rotation r)
                            (comp (bij_translation t)
                               (if b then reflexion else Similarity.id)))
                           (fst (conf id)), snd (conf id)))
                       (Datatypes.id
                          ((comp (bij_rotation r)
                              (comp (bij_translation t)
                                 (if b then reflexion else Similarity.id)))
                             (fst (conf (Good g)))), snd (conf (Good g))))).
                  { unfold obs_from_config, Spect_ILA.
                    rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff, Rle_bool_true_iff.
                    repeat split.
                    exists (Good g); destruct b; reflexivity.
                    rewrite Hconf.
                    simpl in *.
                    destruct b; replace (sqrt _) with (sqrt 0) by (f_equal; lra);
                      rewrite sqrt_0; generalize Dmax_6D D_0; lra.
                    unfold get_alive in *; rewrite Hconf in *; now simpl in *.
                    unfold get_alive in *; rewrite Hconf in *; simpl in *; assumption.
                    rewrite Hconf, Nat.leb_le. unfold get_ident; simpl; omega.
                    intros x y Hxy.
                    rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                    rewrite (get_alive_compat Hxy).
                    rewrite (get_ident_compat Hxy).
                    reflexivity.
                  }
                  specialize (Hlower_target (choose_target
                   (obs_from_config
                      (fun id : ident =>
                       ((comp (bij_rotation r)
                           (comp (bij_translation t)
                              (if b then reflexion else Similarity.id)))
                          (fst (conf id)), snd (conf id)))
                      (Datatypes.id
                         ((comp (bij_rotation r)
                             (comp (bij_translation t)
                                (if b then reflexion else Similarity.id)))
                            (fst (conf (Good g)))), snd (conf (Good g))))) _ H0); clear H0.
                  rewrite (get_ident_compat Htarget_spec) in Hlower_target.
                  unfold get_ident in *; rewrite Hconf_target;
                    simpl (snd (fst _)) in *; apply Hlower_target.
                  destruct Hpred as (Horigin, _).
                  specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                  revert Horigin; intros Horigin.
                  rewrite Hconf in *;
                    unfold get_location, State_ILA, OnlyLocation, AddInfo,
                    get_location, Datatypes.id in *.
                  rewrite <- Horigin.
                  rewrite Hchange.
                  unfold frame_choice_bijection, Frame; fold Frame; destruct b;

                  reflexivity.
                  reflexivity.
                  apply Hpred.
                  apply Hpred.
               -- destruct (round rbg_ila da conf (Good g)) as (pos_round, ((ident_round, light_round), alive_round)) eqn : Hconf_round.
                  assert (Hround_equiv : round rbg_ila da conf (Good g) == (pos_round, ((ident_round, light_round), alive_round))) by now rewrite Hconf_round. 
                  rewrite round_good_g in Hround_equiv; try apply Hpred.
                  simpl in Hround_equiv.
                  destruct Hround_equiv as (Hpos_round, Hsnd_round).
                  unfold upt_aux, map_config in *. rewrite Hchange, Hbool in *.
                  rewrite Hconf in *.
                  unfold rbg_fnc in *.
                  destruct (get_light ((round rbg_ila da conf (Good g_target)))) eqn : Hlight_target_round.
                  ++
                    
                    set (new_pos := choose_new_pos _ _) in *.
                    assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
                    destruct Hchoose_correct as (Hdist_dp, Hdist_d).
                    destruct (move_to _) eqn : Hmove.
                     ** simpl in Hsnd_round.
                       assert (retraction
                 (comp (bij_rotation r)
                    (comp (bij_translation t)
                          (if b then reflexion else Similarity.id)))
                               new_pos ==
               pos_round).
                       rewrite <- Hpos_round.
                       destruct b; now simpl in *.
                       
                       specialize (Hlighted g_target H).
                       revert Hlighted; intro Hlighted.
                       assert (Hsome := move_to_Some_zone Hmove).
                       rewrite <- Inversion in H0.
                       
                       assert ((dist (get_location (round rbg_ila da conf (Good g_target)))
                (get_location (pos_round, (ident_round, light_round, alive_round)))) <= Dmax)%R.
                       assert (Hdist_round_target := dist_round_max_d g_target Hpred Hpath_backup).
                       rewrite <- Halive_target in Hdist_round_target at 1. 
                       rewrite Htarget_spec, Hconf_target in Hdist_round_target.
                       unfold get_alive in Hdist_round_target.
                       simpl (snd (snd _)) in *.        
                       specialize (Hdist_round_target (reflexivity _)).
                       unfold equiv, bool_Setoid, eq_setoid in Hdist_round_target.
                       rewrite Rle_bool_true_iff in Hdist_round_target.
                       unfold get_location, State_ILA, OnlyLocation, AddInfo,
                    get_location, Datatypes.id in *.
                       rewrite <- H0 in Hdist_dp. 
                       assert (Htri := RealMetricSpace.triang_ineq (fst (round rbg_ila da conf (Good g_target))) p_target pos_round).
                       assert (dist p_target pos_round <= Dp)%R.
                       {
                         rewrite (@frame_dist _ _ (r,t,b)).
                         unfold frame_choice_bijection, Frame.
                         rewrite dist_sym.
                         destruct b; rewrite (RelationPairs.fst_compat _ _ _ _ Htarget_spec) in Hdist_dp; simpl in *; lra. }
                       assert(dist (fst (round rbg_ila da conf (Good g_target))) p_target <= D)%R.
                       {
                         rewrite dist_sym.
                         simpl in *; apply Hdist_round_target.
                       }
                       transitivity (dist (fst (round rbg_ila da conf (Good g_target))) p_target +
          dist p_target pos_round)%R.
                       simpl in *; apply Htri.
                       transitivity (dist (fst (round rbg_ila da conf (Good g_target))) p_target + Dp)%R.
                       lra.
                       transitivity (D + Dp)%R.
                       lra.
                       unfold Dp.
                       lra.
                       rewrite <- H0 in Hdist_dp.
                       assert (Hlight_target_simp : l_target = true) by now simpl in *.
                       revert Hlighted; intro Hlighted.
                       specialize (Hlighted H1).
                       assert (Htarget_lower := target_lower).
                       assert (get_light (round rbg_ila da conf (Good g_target)) = true).
                       {
                         apply Hlighted.
                         specialize (Htarget_lower (@obs_from_config _ _ _ _ Spect_ILA
               (fun id : ident =>
                              ((comp (bij_rotation r)
                                  (comp (bij_translation t)
                                     (if b then reflexion else Similarity.id)))
                                 (fst (conf id)), snd (conf id)))
                             (Datatypes.id
                                ((comp (bij_rotation r)
                                    (comp (bij_translation t)
                                       (if b then reflexion else Similarity.id)))
                                   (fst (pos, (ide, lig, ali)))), snd (pos, (ide, lig, ali))))  
                                    (
              ((comp (bij_rotation r)
                  (comp (bij_translation t)
                     (if b then reflexion else Similarity.id)))
                 (fst (conf (Good g_target))), snd (conf (Good g_target)))) (
              ((comp (bij_rotation r)
                  (comp (bij_translation t)
                     (if b then reflexion else Similarity.id)))
                 (fst (conf (Good g))), snd (conf (Good g))))).
                         rewrite <- Hconf_round.
                         rewrite <- 2 ident_preserved.
                         rewrite Hconf_target, Hconf in *.
                         unfold get_ident in *.
                         simpl (fst (fst( snd _))) in *.
                         apply Htarget_lower.
                         unfold obs_from_config, Spect_ILA.
                         rewrite make_set_spec, filter_InA, config_list_InA.
                         split.
                         exists (Good g).
                         rewrite Hconf.
                         destruct b; simpl;
                           try now repeat split.
                         rewrite 3 andb_true_iff, Rle_bool_true_iff.
                         repeat split.
                         rewrite dist_same.
                         generalize D_0, Dmax_6D; lra.
                         now simpl.
                         unfold get_alive in *; simpl in *; assumption.
                         rewrite Nat.leb_le. unfold get_ident; simpl; omega.
                         intros x y Hxy.
                         rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                         rewrite (get_alive_compat Hxy).
                         rewrite (get_ident_compat Hxy).
                         reflexivity.
                         destruct Hpred as (Hpred1, (Hpred2, Hpred3)).
                         unfold change_frame_origin in Hpred1.
                         rewrite <- (Hpred1 conf g (r,t,b)).
                         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id.
                         destruct b; simpl;
                         rewrite Hconf;
                         now simpl.
                         auto.
                         revert Htarget_spec; intro Htarget_spec.
                         rewrite  <- Htarget_spec.
                         f_equiv.
                         apply Hpred.
                         apply Hpred.
                       }
                       assert (get_location (round rbg_ila da conf (Good g_target)) == get_location (conf (Good g_target))).
                       {
                         symmetry.
                         apply Hlight_on_means.                         
                         apply Hpred.
                         apply Hpath_backup.
                         apply H.
                         apply H2.
                       }
                       rewrite H3.
                       assert ((dist
                  ((comp (bij_rotation r)
                      (comp (bij_translation t)
                         (if b then reflexion else Similarity.id))) pos_round)
                  (fst
                     (choose_target
                        (obs_from_config
                           (fun id : ident =>
                            ((comp (bij_rotation r)
                                (comp (bij_translation t)
                                   (if b then reflexion else Similarity.id)))
                               (fst (conf id)), snd (conf id)))
                           (Datatypes.id
                              ((comp (bij_rotation r)
                                  (comp (bij_translation t)
                                     (if b then reflexion else Similarity.id)))
                                 (fst (pos, (ide, lig, ali)))), snd (pos, (ide,lig,ali)))))) <= Dp)%R <->
                               (dist
                  ((comp (bij_rotation r)
                      (comp (bij_translation t)
                         (if b then reflexion else Similarity.id))) pos_round)
                  (fst
                     ((comp (bij_rotation r)
                     (comp (bij_translation t)
                        (if b then reflexion else Similarity.id)))
                    (fst (p_target, (i_target, l_target, a_target))),
                 snd (p_target, (i_target, l_target, a_target)))) <= Dp)%R).
                       f_equiv.
                       revert Htarget_spec; intros Htarget_spec.
                       rewrite (dist_compat _ _ (reflexivity _) _ _ (fst_compat Htarget_spec)).
                       f_equiv.
                       assert ((dist
          ((comp (bij_rotation r)
              (comp (bij_translation t) (if b then reflexion else Similarity.id)))
             pos_round)
          (fst
             ((comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                (fst (p_target, (i_target, l_target, a_target))),
             snd (p_target, (i_target, l_target, a_target)))) <= Dp)%R).
                       { destruct H4.
                         unfold Loc, location, make_Location in *;
                         unfold reflexion, Similarity.id in *; destruct b; simpl in *;
                           specialize (H4 (Rlt_le _ _ Hdist_dp));
                         apply H4.
                       }
                       clear H4.
                       rewrite Hconf_target.
                       rewrite (frame_dist _ _ (r,t,b)).
                       unfold frame_choice_bijection, Frame.
                       destruct b; simpl in *; auto;
                       unfold Datatypes.id;
                       auto.

                     **  rewrite <- Hconf_round in Halive'.
                         simpl in Hsnd_round.
                         assert (Hlight_round : get_light (round rbg_ila da conf (Good g)) = true).
                         {
                           rewrite Hconf_round; unfold get_light; simpl.
                           intuition.
                         }
                         assert (Hlight_on_round := Hlight_on_means conf g da Hpred Hpath_backup Halive' Hlight_round).
                         assert (Hlight_on_round_target := Hlight_on_means conf g_target da Hpred Hpath_backup H Hlight_target_round).
                         assert (Hnear_exists : (forall g_near : G,
             get_alive (conf (Good g_near)) = true ->
             (dist (get_location (conf (Good g_near)))
                (get_location (pos, (ide, lig, ali))) <= Dmax)%R ->
             get_ident (conf (Good g_near)) < get_ident (pos, (ide, lig, ali)) ->
             get_light (conf (Good g_near)) = true)).
                         intros g_near Halive_near Hdist_near Hident_near.
                         assert (Hlight_off_first := light_off_first Htarget_spec Hlight_target).
                         specialize (Hlight_off_first ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id))) (fst (conf (Good g_near))), snd (conf (Good g_near)))).
                         assert ((((comp (bij_rotation r)
                          (comp (bij_translation t)
                             (if b then reflexion else Similarity.id)))
                         (fst (conf (Good g_near))), snd (conf (Good g_near)))
                      ∈ obs_from_config
                          (fun id : ident =>
                           ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (pos, (ide, lig, ali)))), snd (pos, (ide,lig,ali))))%set).
                         unfold obs_from_config, Spect_ILA.
                         rewrite make_set_spec, filter_InA, config_list_InA.
                         split.
                         exists (Good g_near).
                         reflexivity.
                         rewrite 3 andb_true_iff, Rle_bool_true_iff.
                         repeat split.
                         rewrite (frame_dist _ _  (r,t,b)) in Hdist_near. 
                         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in Hdist_near.                                             destruct b; simpl in *;
                         apply Hdist_near.
                         unfold get_alive in *; simpl in *; assumption.
                         unfold get_alive in *; rewrite Hconf in *; simpl in *; assumption.
                         rewrite Nat.leb_le.
                         unfold get_ident in *; simpl in *; omega.
                         intros x y Hxy.
                         rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                         rewrite (get_alive_compat Hxy).
                         rewrite (get_ident_compat Hxy).
                         reflexivity.
                         specialize (Hlight_off_first H0); clear H0.
                         simpl in Hlight_off_first.
                         now unfold get_light in *; simpl in *.
                         rewrite <- Hconf_round, <- ident_preserved, Hconf in H_not_0; auto.
                         specialize (Hexists H_not_0 Hnear_exists).
                         revert Hexists; intros Hexists.
                         destruct (Rgt_ge_dec (dist (get_location (pos_round, (ident_round, light_round, alive_round)))
     (get_location (round rbg_ila da conf (Good g_target)))) Dp).
                         assert (Hlight_close := light_close_first Htarget_spec Hlight_target).
                         exfalso.
                         destruct Hexists as (g_false, (Halive_false, (Hident_false, Hdist_false))).
                         assert (Hdist_dp_target : (dist (0, 0)
                    (get_location
                       ((comp (bij_rotation r)
                           (comp (bij_translation t)
                              (if b then reflexion else Similarity.id)))
                          (fst (p_target, (i_target, l_target, a_target))),
                       snd (p_target, (i_target, l_target, a_target)))) > Dp)%R).
                         {
                           unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location.
                           assert (Hinv := Inversion (frame_choice_bijection (r,t,b))).
                           destruct Hpred as (Horigin,_).
                           revert Horigin; intro Horigin.
                           specialize (Horigin conf g (r,t,b) Hchange).
                           rewrite <- Horigin.
                           assert (
                               (Datatypes.id
                                  (fst
                                     ((comp (bij_rotation r)
               (comp (bij_translation t) (if b then reflexion else Similarity.id)))
              (fst (p_target, (i_target, l_target, a_target))),
            snd (p_target, (i_target, l_target, a_target))))) ==
                                    (frame_choice_bijection (r,t,b)) (get_location (conf (Good g_target))))%R.
                           unfold frame_choice_bijection, Frame. destruct b; simpl;
                           unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location;
                           rewrite Hconf_target;
                           now simpl.
                           destruct b; rewrite (dist_compat _ _ (reflexivity _) _ _ H0);
                           rewrite <- frame_dist;
                           rewrite Hlight_on_round, Hlight_on_round_target;
                           now rewrite Hconf_round.
                         }
                         specialize (Hlight_close Hdist_dp_target).
                         specialize (Hlight_close ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id))) (fst (conf (Good g_false))), snd (conf (Good g_false)))).
                          assert ((((comp (bij_rotation r)
                          (comp (bij_translation t)
                             (if b then reflexion else Similarity.id)))
                         (fst (conf (Good g_false))), snd (conf (Good g_false)))
                      ∈ obs_from_config
                          (fun id : ident =>
                           ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (pos, (ide, lig, ali)))), snd (pos, (ide,lig,ali))))%set).
                         unfold obs_from_config, Spect_ILA.
                         rewrite make_set_spec, filter_InA, config_list_InA.
                         split.
                         exists (Good g_false).
                         reflexivity.
                         rewrite 3 andb_true_iff, Rle_bool_true_iff.
                         repeat split.
                         rewrite (frame_dist _ _  (r,t,b)) in Hdist_false. 
                         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in Hdist_false.
                         rewrite dist_sym.
                         destruct b; simpl in *; unfold Dp in *;
                         generalize D_0, Dmax_6D; lra.
                         unfold get_alive in *; simpl in *; assumption.
                         unfold get_alive in *; rewrite Hconf in *; simpl in *; assumption.
                         rewrite Nat.leb_le.
                         unfold get_ident in *; simpl in *; omega.
                         intros x y Hxy.
                         rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                         rewrite (get_alive_compat Hxy).
                         rewrite (get_ident_compat Hxy).
                         reflexivity.
                         specialize (Hlight_close H0); clear H0.
                         absurd (dist (get_location (pos, (ide, lig, ali)))
                                      (get_location (conf (Good g_false))) <= Dp)%R .
                         apply Rgt_not_le.
                         destruct Hpred as (Horigin,_).
                         revert Horigin; intro Horigin.
                         specialize (Horigin conf g (r,t,b) Hchange).
                         rewrite Hconf in Horigin.
                         rewrite <- Horigin in Hlight_close.
                         
                         assert (
                               (Datatypes.id
                                  (fst
                                     ((comp (bij_rotation r)
               (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                        (fst (conf (Good g_false))),
                               snd (conf (Good g_false))))) ==
                                    (frame_choice_bijection (r,t,b)) (get_location (conf (Good g_false))))%R.
                           unfold frame_choice_bijection, Frame. destruct b; simpl;
                           unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location;
                           now simpl.
                           destruct b; rewrite (dist_compat _ _ (reflexivity _) _ _ H0), <- frame_dist in Hlight_close;
                             assumption.
                           apply Hdist_false.
                           apply Rge_le.
                           apply r0.
                  ++ specialize (Hlighted g_target).
                     absurd (get_light (round rbg_ila da conf (Good g_target)) = true).
                     intro. 
                     now rewrite H0 in *.
                     apply Hlighted; try apply H; try (now unfold get_ident in *; simpl in *; assumption).
                     **
                       destruct (move_to _) eqn : Hmove.
                       --- assert (Hmove_some := move_to_Some_zone Hmove).
                           simpl in Hsnd_round.
                           
                           assert (dist (get_location (conf (Good g_target))) (get_location (round rbg_ila da conf (Good g_target))) <= D)%R.
                           {
                             rewrite <- Rle_bool_true_iff.
                             rewrite dist_round_max_d; auto.
                             rewrite (get_alive_compat Htarget_spec) in Halive_target.
                             unfold get_alive in *; rewrite Hconf_target;
                               simpl in *; auto.
                           }
                           
                           set (new_pos := choose_new_pos _ _) in *.
                           assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
                           destruct Hchoose_correct as (Hdist_choose_dp, Hdist_chose_d).
                           assert (Hdist_dp: (dist pos_round p_target <= Dp)%R).
                           {
                             assert ( Hdist_t_dp: (dist new_pos (fst (((comp (bij_rotation r)
                                                                       (comp (bij_translation t)
                                                                             (if b then reflexion else Similarity.id)))
                                                                   (fst (p_target, (i_target, l_target, a_target))),
                                                                 snd (p_target, (i_target, l_target, a_target))))) = (dist new_pos
                                                                                                                           (fst
                                                                                                                              (choose_target
                                                                                                                                 (obs_from_config
                                                                                                                                    (fun id : ident =>
                                                                                                                                       ((comp (bij_rotation r)
                                                                                                                                              (comp (bij_translation t)
                                                                                                                                                    (if b then reflexion else Similarity.id)))
                                                                                                                                          (fst (conf id)), snd (conf id)))
                                                                                                                                    (Datatypes.id
                                                                                                                                       ((comp (bij_rotation r)
                                                                                                                                              (comp (bij_translation t)
                                                                                                                                                    (if b then reflexion else Similarity.id)))
                                                                                                                                          (fst (pos, (ide, lig, ali)))), snd (pos, (ide, lig, ali))))))))%R).
                             f_equiv.
                             now rewrite (fst_compat Htarget_spec).
                             assert ((dist new_pos (fst (((comp (bij_rotation r)
                                                          (comp (bij_translation t)
                                                                (if b then reflexion else Similarity.id)))
                                                      (fst (p_target, (i_target, l_target, a_target))),
                                                    snd (p_target, (i_target, l_target, a_target))))) <= Dp)%R).
                             rewrite Hdist_t_dp.
                             destruct b; apply (Rlt_le _ _ Hdist_choose_dp).
                             rewrite <- Hpos_round.
                             rewrite (frame_dist _ _ (r,t,b)).
                             unfold frame_choice_bijection, Frame. 
                             destruct b; rewrite section_retraction; simpl in *; lra.
                           }
                           rewrite Hconf_target in H0;
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                           simpl (fst _) in *.
                           rewrite dist_sym.
                           assert (Htri := RealMetricSpace.triang_ineq pos_round p_target (fst (round rbg_ila da conf (Good g_target)))).
                           unfold Dp in *; generalize D_0, Dmax_6D. 
                           intros.
                           transitivity (dist pos_round p_target +
                                         dist p_target (fst (round rbg_ila da conf (Good g_target))))%R.
                           assumption.
                           transitivity (Dmax - D +dist p_target (fst (round rbg_ila da conf (Good g_target))))%R.
                           lra.
                           transitivity (Dmax - D + D)%R.
                           apply Rplus_le_compat_l.
                           assumption.
                           lra.
                       --- 
                         assert (Hlight_close := light_close_first Htarget_spec Hlight_target).
                         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                        destruct (Rle_lt_dec (dist (0, 0)%R
                    (fst
                       ((comp (bij_rotation r)
                           (comp (bij_translation t)
                              (if b then reflexion else Similarity.id)))
                          (fst (p_target, (i_target, l_target, a_target))),
                       snd (p_target, (i_target, l_target, a_target))))) Dp)%R.
                        simpl (fst _) in Hpos_round.
                        assert (Hpos_round' : retraction
                 (comp (bij_rotation r)
                    (comp (bij_translation t)
                       (if b then reflexion else Similarity.id))) 
                 (0%R, 0%R) == pos_round) by (now destruct b; rewrite Hpos_round).
                        rewrite <- Inversion in Hpos_round'.
                        rewrite <- Hpos_round' in r0.
                        assert (Hframe := frame_dist pos_round p_target (r,t,b)).
                        unfold frame_choice_bijection, Frame in Hframe.
                        assert (Htarg_d := dist_round_max_d g_target Hpred Hpath_backup).
                        assert (get_alive (conf (Good g_target)) == true).
                        rewrite (get_alive_compat Htarget_spec) in Halive_target.
                        unfold get_alive in *; rewrite Hconf_target; now simpl in *.
                        specialize (Htarg_d H0); clear H0.
                        unfold equiv, bool_Setoid, eq_setoid in Htarg_d.
                        rewrite Rle_bool_true_iff in Htarg_d.
                        rewrite dist_sym.
                        simpl (fst _).
                        assert (Htri := RealMetricSpace.triang_ineq pos_round p_target (fst (round rbg_ila da conf (Good g_target)))).
                        unfold Dp in *; generalize D_0, Dmax_6D. 
                        intros.
                        transitivity (dist pos_round p_target +
                                      dist p_target (fst (round rbg_ila da conf (Good g_target))))%R.
                        assumption.
                        transitivity (Dmax - D +dist p_target (fst (round rbg_ila da conf (Good g_target))))%R.
                        apply Rplus_le_compat.
                        destruct b; rewrite <- Hframe in r0; apply r0.
                        lra.
                        transitivity (Dmax - D + D)%R.
                        apply Rplus_le_compat_l.
                        unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                        rewrite Hconf_target in *; simpl (fst _) in Htarg_d.
                        assumption.
                        lra.
                        apply Rlt_gt in r0.
                        specialize (Hlight_close r0).
                        assert (Hnear_exists : (forall g_near : G,
             get_alive (conf (Good g_near)) = true ->
             (dist (get_location (conf (Good g_near)))
                (get_location (pos, (ide, lig, ali))) <= Dmax)%R ->
             get_ident (conf (Good g_near)) < get_ident (pos, (ide, lig, ali)) ->
             get_light (conf (Good g_near)) = true)).
                         intros g_near Halive_near Hdist_near Hident_near.
                         assert (Hlight_off_first := light_off_first Htarget_spec Hlight_target).
                         specialize (Hlight_off_first ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id))) (fst (conf (Good g_near))), snd (conf (Good g_near)))).
                         assert ((((comp (bij_rotation r)
                          (comp (bij_translation t)
                             (if b then reflexion else Similarity.id)))
                         (fst (conf (Good g_near))), snd (conf (Good g_near)))
                      ∈ obs_from_config
                          (fun id : ident =>
                           ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (pos, (ide, lig, ali)))), snd (pos, (ide,lig,ali))))%set).
                         unfold obs_from_config, Spect_ILA.
                         rewrite make_set_spec, filter_InA, config_list_InA.
                         split.
                         exists (Good g_near).
                         reflexivity.
                         rewrite 3 andb_true_iff, Rle_bool_true_iff.
                         repeat split.
                         rewrite (frame_dist _ _  (r,t,b)) in Hdist_near. 
                         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in Hdist_near.                         
                         destruct b; simpl in *;
                         apply Hdist_near.
                         unfold get_alive in *; simpl in *; assumption.
                         unfold get_alive in *; simpl in *; assumption.
                         rewrite Nat.leb_le.
                         unfold get_ident in *; simpl in *; omega.
                         intros x y Hxy.
                         rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                         rewrite (get_alive_compat Hxy).
                         rewrite (get_ident_compat Hxy).
                         reflexivity.
                         specialize (Hlight_off_first H0); clear H0.
                         simpl in Hlight_off_first.
                         now unfold get_light in *; simpl in *.
                         rewrite <- Hconf_round, <- ident_preserved, Hconf in H_not_0; auto.
                         specialize (Hexists H_not_0 Hnear_exists).
                         revert Hexists; intros Hexists.
                         exfalso.
                         destruct Hexists as (g_false, (Halive_false, (Hident_false, Hdist_false))).
                         specialize (Hlight_close ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id))) (fst (conf (Good g_false))), snd (conf (Good g_false)))).
                          assert ((((comp (bij_rotation r)
                          (comp (bij_translation t)
                             (if b then reflexion else Similarity.id)))
                         (fst (conf (Good g_false))), snd (conf (Good g_false)))
                      ∈ obs_from_config
                          (fun id : ident =>
                           ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (pos, (ide, lig, ali)))), snd (pos, (ide, lig, ali))))%set).
                         unfold obs_from_config, Spect_ILA.
                         rewrite make_set_spec, filter_InA, config_list_InA.
                         split.
                         exists (Good g_false).
                         reflexivity.
                         rewrite 3 andb_true_iff, Rle_bool_true_iff.
                         repeat split.
                         rewrite (frame_dist _ _  (r,t,b)) in Hdist_false. 
                         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in Hdist_false.
                         rewrite dist_sym.
                         destruct b; simpl in *; unfold Dp in *;
                         generalize D_0, Dmax_6D; lra.
                         unfold get_alive in *; simpl in *; assumption.
                         unfold get_alive in *; simpl in *; assumption.
                         rewrite Nat.leb_le.
                         unfold get_ident in *; simpl in *; omega.
                         intros x y Hxy.
                         rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                         rewrite (get_alive_compat Hxy).
                         rewrite (get_ident_compat Hxy).
                         reflexivity.
                         specialize (Hlight_close H0); clear H0.
                         absurd (dist (get_location (pos, (ide, lig, ali)))
                                      (get_location (conf (Good g_false))) <= Dp)%R .
                         apply Rgt_not_le.
                         destruct Hpred as (Horigin,_).
                         revert Horigin; intro Horigin.
                         specialize (Horigin conf g (r,t,b) Hchange).
                         rewrite Hconf in Horigin.
                         rewrite <- Horigin in Hlight_close.
                         
                         assert (
                               (Datatypes.id
                                  (fst
                                     ((comp (bij_rotation r)
               (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                                        (fst (conf (Good g_false))),
                               snd (conf (Good g_false))))) ==
                                    (frame_choice_bijection (r,t,b)) (get_location (conf (Good g_false))))%R.
                           unfold frame_choice_bijection, Frame. destruct b; simpl;
                           unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location;
                           now simpl.
                           destruct b; rewrite (dist_compat _ _ (reflexivity _) _ _ H0), <- frame_dist in Hlight_close;
                             assumption.
                           apply Hdist_false.
                     **
                       rewrite <- Hconf_round.
                       rewrite <- 2 ident_preserved.

                       assert  (Htarget_lower := @target_lower (@obs_from_config _ _ _ _ Spect_ILA
               (fun id : ident =>
                              ((comp (bij_rotation r)
                                  (comp (bij_translation t)
                                     (if b then reflexion else Similarity.id)))
                                 (fst (conf id)), snd (conf id)))
                             (Datatypes.id
                                ((comp (bij_rotation r)
                                    (comp (bij_translation t)
                                       (if b then reflexion else Similarity.id)))
                                   (fst (pos, (ide, lig, ali)))), snd (pos, (ide, lig,ali))))  
                                    (
              ((comp (bij_rotation r)
                  (comp (bij_translation t)
                     (if b then reflexion else Similarity.id)))
                 (fst (conf (Good g_target))), snd (conf (Good g_target)))) (
              ((comp (bij_rotation r)
                  (comp (bij_translation t)
                     (if b then reflexion else Similarity.id)))
                 (fst (conf (Good g))), snd (conf (Good g))))).
                         rewrite Hconf_target, Hconf in *.
                         unfold get_ident in *.
                         simpl (fst (fst( snd _))) in *.
                         apply Htarget_lower.
unfold obs_from_config, Spect_ILA.
                         rewrite make_set_spec, filter_InA, config_list_InA.
                         split.
                         exists (Good g).
                         rewrite Hconf.
                         destruct b; simpl;
                           try now repeat split.
                         rewrite 3 andb_true_iff, Rle_bool_true_iff.
                         repeat split.
                         rewrite dist_same.
                         generalize D_0, Dmax_6D; lra.
                         now simpl.
                         simpl in *; assumption.
                         rewrite Nat.leb_le.
                         unfold get_ident in *; simpl in *; omega.
                         intros x y Hxy.
                         rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                         rewrite (get_alive_compat Hxy).
                         rewrite (get_ident_compat Hxy).
                         reflexivity.
                         destruct Hpred as (Hpred1, (Hpred2, Hpred3)).
                         unfold change_frame_origin in Hpred1.
                         rewrite <- (Hpred1 conf g (r,t,b)).
                         unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id.
                         destruct b; simpl;
                         rewrite Hconf;
                         now simpl.
                         auto.
                         revert Htarget_spec; intro Htarget_spec.
                         rewrite  <- Htarget_spec.
                         f_equiv.
                         apply Hpred.
                         apply Hpred.
             * destruct ((round rbg_ila da conf (Good g))) as (pos_round, ((ident_round, light_round), alive_round)) eqn : Hconf_round.
               assert (Hconf_round' : round rbg_ila da conf (Good g) ==
                                      (pos_round, (ident_round, light_round, alive_round))) by now rewrite Hconf_round.
               rewrite round_good_g in Hconf_round'; try apply Hpred.
               simpl in Hconf_round'.
               unfold rbg_fnc in Hconf_round'.
               destruct (move_to _) eqn : Hmove_to.
               ** exists g_target.
                  repeat split.
               ++ rewrite round_good_g.
                  destruct ((round rbg_ila da conf (Good g_target))) as
                      (pos_target_round, ((ident_target_round, light_target_round), alive_target_round)) eqn : Hconf_target_round.
                  assert (Hconf_target_round' :  round rbg_ila da conf (Good g_target) ==
                                                 (pos_target_round,
                                                  (ident_target_round, light_target_round, alive_target_round))) by now rewrite Hconf_target_round.
                  rewrite round_good_g in Hconf_target_round'.
                  simpl.
                  simpl in Hconf_target_round'.
                  unfold upt_aux, map_config in *.
                  unfold get_alive; destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target. simpl. 
                  simpl in Hconf_target_round'.
                  destruct (upt_robot_dies_b _ g_target) eqn : Hdies_target.
                  -- rewrite (get_alive_compat Htarget_spec) in Halive_target.
                     unfold get_light in Hlight_target; simpl in Hlight_target.
                     unfold get_alive in Halive_target; simpl in Halive_target.
                     simpl in Hconf_target_round'.
                     destruct Hconf_target_round' as (Hpos_target_round, (Hident_target_round, (Hlight_target_round, Halive_target_round))).
                     revert Hexecuted; intro Hexecuted.
                     specialize (Hexecuted g_target da Hpred).
                     unfold get_alive in Hexecuted.
                     rewrite Hconf_target, Hconf_target_round in Hexecuted.
                     simpl in Hexecuted.
                     specialize (Hexecuted Halive_target (symmetry Halive_target_round)).
                     unfold get_light in *; simpl in Hexecuted.
                     rewrite Hexecuted in *; discriminate.
                  -- simpl.
                     rewrite (get_alive_compat Htarget_spec) in Halive_target.
                     unfold get_alive in *; simpl in Halive_target.
                     assumption.
                  -- apply Hpred.
                  -- apply Hpred.
              ++ rewrite <- Hconf_round, <- 2 (ident_preserved conf _ Hpred).
                 assert (Htarget_lower := @target_lower                 
                 (obs_from_config
                          (fun id : ident =>
                           ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (conf (Good g)))), snd (conf (Good g))))
                         ((comp (bij_rotation r)
                        (comp (bij_translation t)
                           (if b then reflexion else Similarity.id)))
                            (fst (conf (Good g_target))), snd (conf (Good g_target)))
                         ((comp (bij_rotation r)
                        (comp (bij_translation t)
                           (if b then reflexion else Similarity.id)))
                       (fst (conf (Good g))), snd (conf (Good g)))).
                 unfold get_ident in *.
                 destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
                 rewrite Hconf in *.
                 simpl (fst _) in Htarget_lower.
                 simpl.
                 apply Htarget_lower.
                 unfold obs_from_config, Spect_ILA.
                 rewrite make_set_spec, filter_InA, config_list_InA.
                 split.
                 exists (Good g).
                 rewrite Hconf.
                 destruct b; simpl;
                   try now repeat split.
                 rewrite 3 andb_true_iff, Rle_bool_true_iff.
                 repeat split.
                 rewrite dist_same.
                 generalize D_0, Dmax_6D; lra.
                 now simpl.
                 unfold get_alive in *; simpl in *; assumption.
                 rewrite Nat.leb_le.
                 unfold get_ident in *; simpl in *; omega.
                 intros x y Hxy.
                 rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                 rewrite (get_alive_compat Hxy).
                 rewrite (get_ident_compat Hxy).
                 reflexivity.
                 destruct Hpred as (Hpred1, (Hpred2, Hpred3)).
                 unfold change_frame_origin in Hpred1.
                 rewrite <- (Hpred1 conf g (r,t,b)).
                 unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id.
                 destruct b; simpl;
                   rewrite Hconf;
                   now simpl.
                 auto.
                 revert Htarget_spec; intro Htarget_spec.
                 rewrite  <- Htarget_spec.
                 f_equiv.
              ++ rewrite <- Hconf_round, round_good_g; try apply Hpred.
                  destruct ((round rbg_ila da conf (Good g_target))) as
                      (pos_target_round, ((ident_target_round, light_target_round), alive_target_round)) eqn : Hconf_target_round.
                  assert (Hconf_target_round' :  round rbg_ila da conf (Good g_target) ==
                                                 (pos_target_round,
                                                  (ident_target_round, light_target_round, alive_target_round))) by now rewrite Hconf_target_round.
                  rewrite round_good_g in Hconf_target_round'; try apply Hpred.
                  simpl (get_location _).
                  simpl in Hconf_target_round'.
                  unfold upt_aux, map_config in *.
                  unfold get_alive; destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target. simpl (Datatypes.id _). 
                  simpl in Hconf_target_round'.
                  destruct (upt_robot_dies_b _ g_target) eqn : Hdies_target.
                  -- rewrite (get_alive_compat Htarget_spec) in Halive_target.
                     unfold get_light in Hlight_target; simpl in Hlight_target.
                     unfold get_alive in Halive_target; simpl in Halive_target.
                     simpl in Hconf_target_round'.
                     destruct Hconf_target_round' as (Hpos_target_round, (Hident_target_round, (Hlight_target_round, Halive_target_round))).
                     revert Hexecuted; intro Hexecuted.
                     specialize (Hexecuted g_target da Hpred).
                     unfold get_alive in Hexecuted.
                     rewrite Hconf_target, Hconf_target_round in Hexecuted.
                     simpl in Hexecuted.
                     specialize (Hexecuted Halive_target (symmetry Halive_target_round)).
                     unfold get_light in *; simpl in Hexecuted.
                     rewrite Hexecuted in *; discriminate.
                  -- 
                     assert (Hmove_some := move_to_Some_zone Hmove_to).
                     destruct Hconf_target_round' as (Hpos_target_round, (Hident_target_round, (Hlight_target_round, Halive_target_round))).
                     rewrite Hchange in *.
                     rewrite Hbool in *.
                     (* faire attention on a mixé round g_target et round g *)
                     unfold rbg_fnc.
                     unfold path_conf in Hpath_backup.
                     assert (get_light (round rbg_ila da conf (Good g_target)) = true).
                     {
                       apply (Hlighted g_target).
                       rewrite Hconf_target_round.
                       unfold get_alive; simpl.
                       rewrite <- Halive_target_round.
                       rewrite (get_alive_compat Htarget_spec) in Halive_target.
                       unfold get_alive in Halive_target; simpl in *; auto.
                       (** round g = l -> dist l (g_target) <= Dp (Hmove_some)
                            -> dist g_target (round g_target) <= D ->
                        bon*)
                       assert (Htri := RealMetricSpace.triang_ineq (get_location (round rbg_ila da conf (Good g_target))) (get_location (conf (Good g_target))) (get_location (round rbg_ila da conf (Good g)))).
                       rewrite <- Hconf_round.
                       assert (Hdist_round_target: (dist (get_location (round rbg_ila da conf (Good g_target))) (get_location (conf (Good g_target))) <= D)%R).
                       {
                         rewrite dist_sym, <- Rle_bool_true_iff;
                         apply dist_round_max_d;
                         auto.
                         assert (Ht_alive := choose_target_alive Htarget_spec).
                         rewrite Hconf_target in *; unfold get_alive in *; now simpl in *.
                       }
                       assert( Hdist_target_round_g : (dist (get_location (conf (Good g_target)))
            (get_location (round rbg_ila da conf (Good g))) <= Dp)%R).
                       { rewrite round_good_g; auto.
                         simpl (get_location _).
                         unfold upt_aux, map_config; rewrite Hchange, Hbool.
                         unfold rbg_fnc. rewrite Hmove_to.
                         set (new_pos := choose_new_pos _ _) in *.
                         assert (Hchoose_correct := choose_new_pos_correct (reflexivity new_pos)).
                         rewrite (frame_dist _ _ (r,t,b)).
                         rewrite Hconf.
                         simpl (fst _).
                         unfold frame_choice_bijection, Frame, Datatypes.id.
                         rewrite section_retraction.
                         rewrite dist_sym.
                         destruct b; rewrite (fst_compat Htarget_spec) in Hchoose_correct;
                           rewrite Hconf_target in *; simpl in *; lra.
                         }
                       unfold Dp in *; generalize Dmax_6D, D_0.
                       lra. 
                       rewrite <- Hconf_round,  <- 2 ident_preserved.
                       assert (Htarget_lower := @target_lower                 
                 (obs_from_config
                          (fun id : ident =>
                           ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf id)), snd (conf id)))
                          (Datatypes.id
                             ((comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id)))
                                (fst (conf (Good g)))), snd (conf (Good g))))
                         ((comp (bij_rotation r)
                        (comp (bij_translation t)
                           (if b then reflexion else Similarity.id)))
                            (fst (conf (Good g_target))), snd (conf (Good g_target)))
                         ((comp (bij_rotation r)
                        (comp (bij_translation t)
                           (if b then reflexion else Similarity.id)))
                       (fst (conf (Good g))), snd (conf (Good g)))).
                 unfold get_ident in *.
                 rewrite Hconf, Hconf_target in *.
                 simpl (fst _) in Htarget_lower.
                 simpl.
                 apply Htarget_lower.
                 unfold obs_from_config, Spect_ILA.
                 rewrite make_set_spec, filter_InA, config_list_InA.
                 split.
                 exists (Good g).
                 rewrite Hconf.
                 destruct b; simpl;
                   try now repeat split.
                 rewrite 3 andb_true_iff, Rle_bool_true_iff.
                 repeat split.
                 rewrite dist_same.
                 generalize D_0, Dmax_6D; lra.
                 now simpl.
                 simpl in *; assumption.
                 rewrite Nat.leb_le. unfold get_ident; simpl; omega.
                 intros x y Hxy.
                 rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                 rewrite (get_alive_compat Hxy).
                 rewrite (get_ident_compat Hxy).
                 reflexivity.
                 destruct Hpred as (Hpred1, (Hpred2, Hpred3)).
                 unfold change_frame_origin in Hpred1.
                 rewrite <- (Hpred1 conf g (r,t,b)).
                 unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id.
                 destruct b; simpl;
                   rewrite Hconf;
                   now simpl.
                 auto.
                 revert Htarget_spec; intro Htarget_spec.
                 rewrite  <- Htarget_spec.
                 f_equiv.
                 apply Hpred.
                 apply Hpred.
                     }
                     rewrite Hconf in *.
                     rewrite Hmove_to.
                     specialize (Hlight_on_means conf g_target da Hpred Hpath_backup).
                     rewrite Hconf_target_round in Hlight_on_means.
                     unfold get_alive in Hlight_on_means;
                       simpl (snd _) in Hlight_on_means;
                       rewrite <- Halive_target_round in Hlight_on_means;
                       rewrite (get_alive_compat Htarget_spec) in Halive_target;
                       unfold get_alive in Halive_target;
                       simpl in Halive_target;
                       specialize (Hlight_on_means Halive_target).
                     rewrite Hconf_target_round in H; specialize (Hlight_on_means H).
                     unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in Hlight_on_means.
                     revert Hlight_on_means; intro Hlight_on_means.
                     simpl in Hlight_on_means.
                     rewrite <- Hlight_on_means.
                     (* en retravaillant Hmove_Some *)
                     simpl (fst _).
                     simpl (choose_new_pos _ _) in *.
                     revert Htarget_spec; intro Htarget_spec.
                     destruct Htarget_spec as (Htarget_spec_pos, _).
                     set (new_pos := choose_new_pos _ _) in *.
                     assert (Hchoose_correct := choose_new_pos_correct (reflexivity new_pos)).
                     rewrite (frame_dist _ _ (r,t,b)).
                     simpl (fst _).
                     unfold frame_choice_bijection, Frame, Datatypes.id.
                     rewrite section_retraction.
                     destruct b;
                       rewrite Htarget_spec_pos in Hchoose_correct; rewrite Hconf_target in *; simpl in *;  lra. 
                    ** assert (Hmove_None := move_to_None Hmove_to).
                       rewrite Hchange in Hmove_None.
                       specialize (Hmove_None (((comp (bij_rotation r)
                            (comp (bij_translation t)
                               (if b then reflexion else Similarity.id)))
                                                  (fst (round rbg_ila da conf (Good g)))))).
                       assert (Hsame_pos : get_location (round rbg_ila da conf (Good g)) = get_location (conf (Good g))).
                       {
                         rewrite round_good_g; try auto.
                         simpl.
                         unfold upt_aux, map_config in *; rewrite Hchange, Hbool in *.
                         unfold rbg_fnc; rewrite Hmove_to.
                         destruct Hpred as (Horigin,_).
                         revert Horigin; intro Horigin.
                         specialize (Horigin (conf) g (r,t,b) Hchange).
                         rewrite Hconf in *.
                         simpl (fst _) .
                         unfold frame_choice_bijection, Frame in Horigin.
                         rewrite <- Horigin.
                         rewrite retraction_section.
                         now cbn.
                       }
                       destruct Hmove_None as (other,(Hother_spect, Hmove_other)).
                       -- destruct Hpred as (Horigin,_).
                          revert Horigin; intro Horigin.
                          specialize (Horigin (conf) g (r,t,b) Hchange).
                          rewrite Hconf in Horigin.
                          cbn in Hsame_pos.
                          unfold Datatypes.id in *.
                          rewrite Hsame_pos.
                          unfold frame_choice_bijection, Frame in Horigin.
                          rewrite <- Horigin.
                          rewrite Hconf.
                          unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location.
                          unfold Datatypes.id.
                          destruct b; rewrite dist_same; generalize D_0; lra.
                       -- unfold obs_from_config, Spect_ILA, map_config in Hother_spect.
                          rewrite make_set_spec, filter_InA, config_list_InA in Hother_spect.
                          rewrite 3 andb_true_iff, Rle_bool_true_iff in Hother_spect.
                          destruct Hother_spect as (([g_other|b_other],Hother_spec),
                                                    (((Hother_Dmax, Hother_alive), Hother_alive'), Hother_ident)).
                          destruct (get_alive (round rbg_ila da conf (Good g_other)))
                                   eqn : Halive_other_round.
                          ++ exists g_other.
                             repeat split; try auto.
                             rewrite Hother_spec in Hother_ident.
                             rewrite <- Hconf_round.
                             rewrite <- 2 ident_preserved; try auto.
                             unfold get_ident in *; simpl in Hother_ident.
                             rewrite Nat.leb_le in Hother_ident.
                             destruct Hmove_other as (Hmove_other, Hdist_other_round_2D).
                             destruct Hmove_other as (other1, (Hother_in,(Hother_pos, Hother_ident'))). 
                             revert Hcol; intro Hcol.
                             unfold no_collision_conf in Hcol.
                             unfold obs_from_config, Spect_ILA, map_config in Hother_in.
                             rewrite make_set_spec, filter_InA, config_list_InA in Hother_in.
                             rewrite 3 andb_true_iff in Hother_in.
                             destruct Hother_in as (([g_other'|byz], Hother1_spec), (((Hother1_dist,Hother1_alive),Hother1_aliveg), Hother1_ident));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in *).                              
                             assert (Hident_g : g_other' = g).
                             {
                               destruct (Geq_dec g g_other'); try auto.
                               specialize (Hcol _ _ n0).
                               destruct Hcol.
                               rewrite Hconf in *; simpl in *; auto.
                               rewrite Hother1_spec in Hother1_alive; unfold get_alive in *;
                                 simpl in *;
                                 auto. 
                               rewrite Hother1_spec in Hother_pos.
                               assert (fst (round rbg_ila da conf (Good g)) = fst (conf (Good g))).
                               {
                                 unfold get_location, State_ILA, OnlyLocation, AddInfo in *;
                                   unfold get_location, Datatypes.id in *. 
                                 auto.
                               }
                               rewrite H in Hother_pos.

                               rewrite (frame_dist _ _ (r,t,b)).
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                               rewrite Hother_pos. 
                               destruct b; apply dist_same.
                             }
                             assert (get_ident (other) < get_ident (other1)).
                             unfold get_ident in *; auto.
                             rewrite Hother_spec, Hother1_spec in H.
                             unfold get_ident in H; simpl in H.
                             now rewrite <- Hident_g.
                             intros x y Hxy.
                             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                             rewrite (get_alive_compat Hxy).
                             rewrite (get_ident_compat Hxy).
                             reflexivity.
                             rewrite (fst_compat Hother_spec) in Hother_Dmax.
                             destruct Hmove_other.
                             rewrite Hother_spec in H0.
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                             assert (dist (fst (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))) <= 3 * D)%R.
                             unfold map_config in *.
                             rewrite Hchange in Hmove_to.
                             set (new_pos := choose_new_pos _ _) in *.
                             assert (Htri_new_pos := RealMetricSpace.triang_ineq (fst (conf (Good g_other))) (retraction (frame_choice_bijection (r,t,b)) new_pos) (fst (round rbg_ila da conf (Good g)))).
                             assert (Hnew_correct := choose_new_pos_correct (reflexivity new_pos)).
                             destruct Hnew_correct as (_,Hdist_new_D).
                             destruct Hpred as (Horigin,_).
                             revert Horigin; intro Horigin.
                             specialize (Horigin (conf) g (r,t,b) Hchange).
                             rewrite Hconf in Horigin.
                             rewrite <- Horigin in Hdist_new_D.
                             assert (Hdist_new_D_aux : (dist (retraction (frame_choice_bijection (r, t, b)) new_pos)
                                                             (fst (round rbg_ila da conf (Good g))) <= D)%R).
                             { assert (Hconf_round_aux : round rbg_ila da conf (Good g) == (pos_round, (ident_round, light_round, alive_round))). 
                               unfold ILA in *. now  rewrite <- Hconf_round.
                               unfold ILA in *.
                               rewrite (fst_compat Hconf_round_aux) in Hsame_pos.
                               rewrite (fst_compat Hconf_round_aux).
                               rewrite Hsame_pos.
                               rewrite Hconf.
                               rewrite (frame_dist _ _ (r,t,b)).
                               rewrite section_retraction.
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in Hdist_new_D.
                               generalize D_0; simpl in *; lra. 
                             }
                             assert (Hdist_other_new : (dist (fst (conf (Good g_other)))
                    (retraction (frame_choice_bijection (r, t, b)) new_pos) <= 2*D)%R).
                             {
                               rewrite (frame_dist _ _ (r,t,b)), section_retraction.
                               unfold frame_choice_bijection, Frame;
                                 destruct b; simpl in *; lra.
                             }
                             generalize D_0; simpl in *; lra.
                             assert (Dp > 4*D)%R.
                             {
                               generalize Dmax_6D, D_0. unfold Dp. lra.
                             }
                             assert (Htri := RealMetricSpace.triang_ineq (fst (round rbg_ila da conf (Good g_other))) (fst (conf (Good g_other)))  (fst (pos_round, (ident_round, light_round, alive_round)))). 
                             transitivity (dist (fst (round rbg_ila da conf (Good g_other))) (fst (conf (Good g_other))) +
          dist (fst (conf (Good g_other)))  (fst (pos_round, (ident_round, light_round, alive_round))))%R.
                             auto.
                             rewrite dist_sym at 1; apply Htri.
                             assert (Hdist_round := dist_round_max_d g_other Hpred Hpath_backup).
                             unfold equiv, bool_Setoid, eq_setoid in *;
                               rewrite Rle_bool_true_iff in *.
                             rewrite Hother_spec in Hother_alive; unfold get_alive in *; simpl in Hother_alive.
                             specialize (Hdist_round Hother_alive).
                             rewrite dist_sym in Hdist_round.
                             unfold Dp.
                             Unset Printing All. 
                             unfold ILA in *; rewrite <- Hconf_round.
                             fold Dp.
                             transitivity (D +    dist (fst (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))))%R.
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                             apply Rplus_le_compat_r.
                             apply Hdist_round.
                             transitivity (D + 3*D)%R.
                             apply Rplus_le_compat_l.
                             apply H1.
                             lra.
                          ++ assert (Halive_near := @executed_means_alive_near conf g_other da Hpred).
                             assert (Hother_alive_aux : get_alive (conf (Good g_other)) = true).
                             {
                               rewrite <- Hother_alive.
                               rewrite Hother_spec;
                               unfold get_alive; simpl; auto.
                             }                               
                             revert Hpath_backup; intro Hpath_backup.
                             destruct (nat_eq_eqdec (get_ident (conf (Good g_other))) 0).
                             rewrite (ident_preserved conf g_other Hpred) in e.
                             assert (Hfalse := ident_0_alive (round rbg_ila da conf) g_other e).
                             rewrite Hfalse in *; discriminate.
                             rename c into Hother_else.
                             specialize (Halive_near Hother_alive_aux Hother_else Halive_other_round Hpath_backup).
                             destruct (Hpath_backup g_other Hother_alive_aux).
                             destruct Hother_else.
                             now rewrite H.
                             destruct Halive_near as (g_near, (Hnear_ident, (Hnear_dist, Hnear_alive))).
                             destruct H as (g_0, (Halive_0, (Hdist_0, Hident_0))).
                             exists g_0; repeat split; auto.
                             now rewrite dist_sym.
                             rename H into Hother_path.
                             (*si near marche aps, le bourreau de near marche, mais aussi near ne devrait aps mourrir: il est bourreau donc il bouge   *)



(* je voudrais un axiom qui dit que pour chaque configuration, soit c'est la première, où tout est bon, soit il existe une DA qui permet d'y acceder par un round. Si j'ai ça, alors je peux avoir light_off_means_alive_next car en vrai, la prop d'avant marche sur 3 round: si on est light_off, c'est qu'au round -1, on n'avait personne trop pret ni trop loins, et donc personne ne peut faire en sorte que l'on meurt au round . à tout round, sans avoir à m'inquiéter d'avoir 3 round dans mes lemmes de continuités.

                              *)



                             assert (get_alive (round rbg_ila da conf (Good g_near)) = true).
                             {
                               rewrite round_good_g; try auto.
                               simpl.
                               unfold upt_aux.
                               destruct (upt_robot_dies_b _ g_near) eqn : Hbool_near.
                               - assert (Hfalse : get_alive (round rbg_ila da conf (Good g_near)) = false).
                                 rewrite round_good_g; try auto.
                                 simpl.
                                 unfold upt_aux.
                                 rewrite Hbool_near.
                                 unfold get_alive ; simpl.
                                 now destruct (conf (Good g_near)) as (?, ((?,?),?)); simpl.
                                 assert (Hlight_false : get_light (conf (Good g_near)) = true).
                                 apply (Hexecuted g_near da Hpred Hnear_alive Hfalse).
                                 assert (Hlight_true : get_light (conf (Good g_near)) = false).
                                 apply (Hexecutioner g_near da Hpred Hnear_alive).
                                 exists g_other.
                                 repeat split; try auto.
                                 rewrite dist_sym. auto.
                                 rewrite Hlight_true in *.
                                 discriminate.
                               - unfold get_alive in *; 

                                   destruct (conf (Good g_near)) as (?, ((?,?),?)) eqn : Hconf_near.
                                 simpl; auto.
                                 rewrite Hconf_near.
                                 simpl; auto.
                             }
                             exists g_near.
                             repeat split; auto.
                             rewrite <- ident_preserved; auto.
                             transitivity (get_ident (conf (Good g_other))); auto.

                             (* début  *)
                             destruct Hmove_other as ((copy, (Hcopy_spec, (Hcopy_pos, Hcopy_ident))), _).
                             unfold obs_from_config, Spect_ILA in Hcopy_spec.
                             rewrite make_set_spec, filter_InA, config_list_InA in Hcopy_spec.
                             rewrite 3 andb_true_iff, Rle_bool_true_iff in Hcopy_spec.
                             destruct Hcopy_spec as (([g_inf|byz],Hinf_spec), ((Hinf_dist, Hinf_alive), Hinf));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in *).                              
                             rewrite Nat.leb_le in Hinf.
                             rewrite <- Hconf_round, <- ident_preserved; try auto.
                             apply (Nat.lt_le_trans _ (get_ident copy) _).
                             rewrite Hother_spec in Hcopy_ident.
                             unfold get_ident in *; now simpl in *.
                             unfold get_ident in *; now simpl in *.
                             intros x y Hxy.
                             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                             rewrite (get_alive_compat Hxy).
                             rewrite (get_ident_compat Hxy).
                             reflexivity.
                             assert (Hdist_round_g_near := @dist_round_max_d g_near conf da Hpred Hpath_backup Hnear_alive).
                             unfold equiv, bool_Setoid, eq_setoid in Hdist_round_g_near;
                             rewrite Rle_bool_true_iff in Hdist_round_g_near.
                             destruct Hmove_other as (?,Hdist_other).
                             rewrite Hother_spec, dist_sym in Hdist_other.
                             revert Hdist_other; intro Hdist_other.
                                                          assert (dist (fst (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))) <= 3 * D)%R.
                             unfold map_config in *.
                             rewrite Hchange in Hmove_to.
                             set (new_pos := choose_new_pos _ _) in *.
                             assert (Htri_new_pos := RealMetricSpace.triang_ineq (fst (conf (Good g_other))) (retraction (frame_choice_bijection (r,t,b)) new_pos) (fst (round rbg_ila da conf (Good g)))).
                             assert (Hnew_correct := choose_new_pos_correct (reflexivity new_pos)).
                             destruct Hnew_correct as (_,Hdist_new_D).
                             destruct Hpred as (Horigin,_).
                             revert Horigin; intro Horigin.
                             specialize (Horigin (conf) g (r,t,b) Hchange).
                             rewrite Hconf in Horigin.
                             rewrite <- Horigin in Hdist_new_D.
                             assert (Hdist_new_D_aux : (dist (retraction (frame_choice_bijection (r, t, b)) new_pos)
                                                             (fst (round rbg_ila da conf (Good g))) <= D)%R).
                             { assert (Hconf_round_aux : round rbg_ila da conf (Good g) == (pos_round, (ident_round, light_round, alive_round))). 
                               unfold ILA in *. now  rewrite <- Hconf_round.
                               unfold ILA in *.
                               rewrite (fst_compat Hconf_round_aux) in Hsame_pos.
                               rewrite (fst_compat Hconf_round_aux).
                               rewrite Hsame_pos.
                               rewrite Hconf.
                               rewrite (frame_dist _ _ (r,t,b)).
                               rewrite section_retraction.
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                               generalize D_0; simpl in *; lra. 
                             }
                             assert (Hdist_other_new : (dist (fst (conf (Good g_other)))
                    (retraction (frame_choice_bijection (r, t, b)) new_pos) <= 2*D)%R).
                             {
                               rewrite (frame_dist _ _ (r,t,b)), section_retraction.
                               rewrite dist_sym. unfold frame_choice_bijection, Frame;
                                 destruct b; simpl in *; lra.
                             }
                             generalize D_0; simpl in *; lra.
                             rewrite <- Hconf_round.
                             assert (Htri1 := RealMetricSpace.triang_ineq (get_location (round rbg_ila da conf (Good g))) (get_location (conf (Good g_other))) (get_location (conf (Good g_near)))).
                             clear Hdist_other. 
                             assert (Htri': (dist (get_location (round rbg_ila da conf (Good g)))
             (get_location (conf (Good g_near))) <= 4*D)%R).
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                             replace (4*D)%R with (3*D + D)%R by lra.
                             transitivity ((dist (fst (round rbg_ila da conf (Good g))) (fst (conf (Good g_other))) + D)%R); try (now generalize D_0; lra).
                             transitivity (
           dist (fst (round rbg_ila da conf (Good g))) (fst (conf (Good g_other))) +
           dist (fst (conf (Good g_other))) (fst (conf (Good g_near))))%R ;
                             try auto.
                             apply Rplus_le_compat_l.
                             apply Hnear_dist.
                             apply Rplus_le_compat_r.
                             rewrite dist_sym.
                             apply H1.
                             assert (Htri2 := RealMetricSpace.triang_ineq (get_location (round rbg_ila da conf (Good g))) (get_location (conf (Good g_near)))
     (get_location (round rbg_ila da conf (Good g_near)))).
                             unfold Dp.
                             transitivity (4*D + D)%R.
                             transitivity  (dist (get_location (round rbg_ila da conf (Good g)))
             (get_location (conf (Good g_near))) +
           dist (get_location (conf (Good g_near)))
                (get_location (round rbg_ila da conf (Good g_near))))%R.
                             apply Htri2.
                             transitivity ((dist (get_location (round rbg_ila da conf (Good g)))
             (get_location (conf (Good g_near))) + D))%R.
                             apply Rplus_le_compat_l.
                             apply Hdist_round_g_near.
                             apply Rplus_le_compat_r.
                             apply Htri'.
                             generalize Dmax_6D, D_0; lra.

                             (*  fin  *)
                          ++
                            try (assert (Hfalse := In_Bnames b_other);
                                 now simpl in *). 
                          ++ intros x y Hxy.
                             rewrite (fst_compat Hxy).
                             rewrite (get_alive_compat Hxy), (get_ident_compat Hxy).
                             reflexivity.
(*                       -- 
                         (* ce cas là c'est quand il existe une position assez loins des autres robots mais trop loins de la cible. et c'est possible que quand il existes d'autres robots a portées. 
                           comment exprimer ça? 
                           exists x, (forall other!=x, dist other x >= 2D /\ dist x target < Dp /\ 


*)








                                   
                                 assert (Hmoving := @executioner_means_moving conf g_near da).
                             exists g_near.
                             repeat split; try auto.
                             apply moving_means_alive_next
                             rewrite existsb_exists in *.
                             destruct Hmove_other as ((inf, (Hin, (Hpos_eq, Hlower))), Hmove_other).
                             unfold obs_from_config, Spect_ILA in Hin.
                             rewrite make_set_spec, filter_InA, config_list_InA in Hin.
                             rewrite 2 andb_true_iff, Rle_bool_true_iff in Hin.
                             destruct Hin as (([g_inf|byz],Hinf_spec), ((Hinf_dist, Hinf_alive), Hinf));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in * ).
                             rewrite Hinf_spec in Hpos_eq.
                             rewrite existsb_exists in Hinf.
                             destruct Hinf as (inf2, (Hinf_list, Hinf_bool)).
                             rewrite 2 andb_true_iff, R2dec_bool_true_iff in Hinf_bool.
                             assert (get_ident other < get_ident (conf (Good g))).
                             rewrite Nat.leb_le in Hinf_bool.
                             rewrite config_list_spec, in_map_iff in Hinf_list.
                             destruct Hinf_list as ([g_inf'|byz], (Hinf2_spec,Hinf2_in));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in * ).                              
                             assert (g = g_inf').
                             { destruct (Geq_dec g g_inf'); try auto.
                               specialize (Hcol _ _ n0).
                               destruct Hcol.
                               rewrite Hconf in *; simpl in *; auto.
                               rewrite <- Hinf2_spec in Hinf_bool; unfold get_alive in *;
                                 simpl in *;
                                 intuition; auto. 
                               rewrite <- Hinf2_spec in Hinf_bool.
                               rewrite (frame_dist _ _ (r,t,b)).
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                               destruct Hinf_bool as ((Heq_inf, _),_). rewrite Heq_inf. 
                               apply dist_same.
                             }
                             
                             apply (Nat.lt_le_trans _ (get_ident inf)).
                             omega.
                             rewrite <- Hinf2_spec, H in *; unfold get_ident in *; simpl in *.
                             omega.

                             rewrite <- Hconf_round.
                             rewrite <- 2 ident_preserved; try auto.
                             transitivity (get_ident (conf (Good g_other))); try auto.                             
                             rewrite Hother_spec in H.
                             unfold get_ident in *; simpl in *; omega.
intros x y Hxy.
                             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                             rewrite (get_alive_compat Hxy).
                             rewrite (get_ident_compat Hxy).
                             reflexivity.
                             destruct Hmove_other as ((inf, (Hin, (Hpos_eq, Hlower))), Hmove_other).
                             rewrite Hother_spec in Hmove_other.
                             assert (dist (get_location (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))) <= 2*D)%R.
                             rewrite (frame_dist _ _ (r,t,b)). 
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.                             
                             destruct b; simpl in *; lra.
                             assert (Dp > 4*D)%R by .
                             rewrite <- Hconf_round.
                              (* tri ineq avec Hnear_dist (D), H(2D) et dist_max_round_d(D) *).
                             exists g_near.
                             repeat split; try auto.
                             rewrite existsb_exists in *.
                             destruct Hmove_other as ((inf, (Hin, (Hpos_eq, Hlower))), Hmove_other).
                             unfold obs_from_config, Spect_ILA in Hin.
                             rewrite make_set_spec, filter_InA, config_list_InA in Hin.
                             rewrite 2 andb_true_iff, Rle_bool_true_iff in Hin.
                             destruct Hin as (([g_inf|byz],Hinf_spec), ((Hinf_dist, Hinf_alive), Hinf));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in * ).
                             rewrite Hinf_spec in Hpos_eq.
                             rewrite existsb_exists in Hinf.
                             destruct Hinf as (inf2, (Hinf_list, Hinf_bool)).
                             rewrite 2 andb_true_iff, R2dec_bool_true_iff in Hinf_bool.
                             assert (get_ident other < get_ident (conf (Good g))).
                             rewrite Nat.leb_le in Hinf_bool.
                             rewrite config_list_spec, in_map_iff in Hinf_list.
                             destruct Hinf_list as ([g_inf'|byz], (Hinf2_spec,Hinf2_in));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in * ).                              
                             assert (g = g_inf').
                             { destruct (Geq_dec g g_inf'); try auto.
                               specialize (Hcol _ _ n0).
                               destruct Hcol.
                               rewrite Hconf in *; simpl in *; auto.
                               rewrite <- Hinf2_spec in Hinf_bool; unfold get_alive in *;
                                 simpl in *;
                                 intuition; auto. 
                               rewrite <- Hinf2_spec in Hinf_bool.
                               rewrite (frame_dist _ _ (r,t,b)).
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                               destruct Hinf_bool as ((Heq_inf, _),_). rewrite Heq_inf. 
                               apply dist_same.
                             }
                             
                             apply (Nat.lt_le_trans _ (get_ident inf)).
                             omega.
                             rewrite <- Hinf2_spec, H in *; unfold get_ident in *; simpl in *.
                             omega.
                             rewrite <- Hconf_round.
                             rewrite <- 2 ident_preserved; try auto.
                             transitivity (get_ident (conf (Good g_other))); try auto.                             
                             rewrite Hother_spec in H.
                             unfold get_ident in *; simpl in *; omega.
intros x y Hxy.
                             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                             rewrite (get_alive_compat Hxy).
                             rewrite (get_ident_compat Hxy).
                             reflexivity.
                             destruct Hmove_other as ((inf, (Hin, (Hpos_eq, Hlower))), Hmove_other).
                             rewrite Hother_spec in Hmove_other.
                             assert (dist (get_location (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))) <= 2*D)%R.
                             rewrite (frame_dist _ _ (r,t,b)). 
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.                             
                             destruct b; simpl in *; lra.
                             assert (Dp > 4*D)%R by .
                             rewrite <- Hconf_round.
                              (* tri ineq avec Hnear_dist (D), H(2D) et dist_max_round_d(D) *).
                             

                             exists g_near.
                             repeat split; try auto.
                             rewrite existsb_exists in *.
                             destruct Hmove_other as ((inf, (Hin, (Hpos_eq, Hlower))), Hmove_other).
                             unfold obs_from_config, Spect_ILA in Hin.
                             rewrite make_set_spec, filter_InA, config_list_InA in Hin.
                             rewrite 2 andb_true_iff, Rle_bool_true_iff in Hin.
                             destruct Hin as (([g_inf|byz],Hinf_spec), ((Hinf_dist, Hinf_alive), Hinf));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in * ).
                             rewrite Hinf_spec in Hpos_eq.
                             rewrite existsb_exists in Hinf.
                             destruct Hinf as (inf2, (Hinf_list, Hinf_bool)).
                             rewrite 2 andb_true_iff, R2dec_bool_true_iff in Hinf_bool.
                             assert (get_ident other < get_ident (conf (Good g))).
                             rewrite Nat.leb_le in Hinf_bool.
                             rewrite config_list_spec, in_map_iff in Hinf_list.
                             destruct Hinf_list as ([g_inf'|byz], (Hinf2_spec,Hinf2_in));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in * ).                              
                             assert (g = g_inf').
                             { destruct (Geq_dec g g_inf'); try auto.
                               specialize (Hcol _ _ n0).
                               destruct Hcol.
                               rewrite Hconf in *; simpl in *; auto.
                               rewrite <- Hinf2_spec in Hinf_bool; unfold get_alive in *;
                                 simpl in *;
                                 intuition; auto. 
                               rewrite <- Hinf2_spec in Hinf_bool.
                               rewrite (frame_dist _ _ (r,t,b)).
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                               destruct Hinf_bool as ((Heq_inf, _),_). rewrite Heq_inf. 
                               apply dist_same.
                             }
                             
                             apply (Nat.lt_le_trans _ (get_ident inf)).
                             omega.
                             rewrite <- Hinf2_spec, H in *; unfold get_ident in *; simpl in *.
                             omega.
                             rewrite <- Hconf_round.
                             rewrite <- 2 ident_preserved; try auto.
                             transitivity (get_ident (conf (Good g_other))); try auto.                             
                             rewrite Hother_spec in H.
                             unfold get_ident in *; simpl in *; omega.
intros x y Hxy.
                             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                             rewrite (get_alive_compat Hxy).
                             rewrite (get_ident_compat Hxy).
                             reflexivity.
                             destruct Hmove_other as ((inf, (Hin, (Hpos_eq, Hlower))), Hmove_other).
                             rewrite Hother_spec in Hmove_other.
                             assert (dist (get_location (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))) <= 2*D)%R.
                             rewrite (frame_dist _ _ (r,t,b)). 
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.                             
                             destruct b; simpl in *; lra.
                             assert (Dp > 4*D)%R by .
                             rewrite <- Hconf_round.
                             (* tri ineq avec Hnear_dist (D), H(2D) et dist_max_round_d(D) *).


                             
                             rewrite andb_tr
                             
                             assert (Hlight_other : get_light (conf (Good g_other)) = true).
                             unfold executed_means_light_on in *;
                               apply (Hexecuted _ _ Hpred).
                             rewrite Hother_spec in *; unfold get_alive in *; simpl in *; auto.
                             assumption.
                             unfold executioner_means_light_off in Hexecutioner.
                             assert (Hother_alive_aux : get_alive (conf (Good g_other)) = true).
                             {
                               rewrite <- Hother_alive.
                               rewrite Hother_spec;
                               unfold get_alive; simpl; auto.
                             }                               
                             assert (Hexists_other := Hexists_backup g_other Hother_alive_aux).
                             assert (Hpath_aux := Hpath_backup g_other Hother_alive_aux).
                             destruct Hpath_aux.
                             assert (Hfalse := ident_0_alive (round rbg_ila da conf) g_other).
                             rewrite <- ident_preserved in Hfalse; try apply Hpred.
                             specialize (Hfalse H).
                             now rewrite Hfalse in *; discriminate.
                             rewrite round_good_g in Halive_other_round; try apply Hpred.
                             unfold update, UpdFun, upt_aux in Halive_other_round.
                             destruct (upt_robot_dies_b _ g_other) eqn : Hfalse;
                               unfold get_alive in *.
                             unfold upt_robot_dies_b in Hfalse; clear Halive_other_round.
                             rewrite orb_true_iff in Hfalse.
                             destruct Hfalse as [Hnear|Hfar].
                             revert Hnear; intro Hnear.
                             rewrite existsb_exists in Hnear.
                             destruct Hnear as (near, (Hnear_in, Hnear_dist)).
                             rewrite Rle_bool_true_iff in Hnear_dist.
                             rewrite config_list_spec in Hnear_in.
                             rewrite List.filter_In in Hnear_in.
                             rewrite andb_true_iff in Hnear_in.
                             destruct Hnear_in as ( Hnear_in, (Hnear_ident, Hnear_alive)).
                             rewrite in_map_iff in Hnear_in.
                             destruct Hnear_in as ([g_near|byz], (Hnear_spec, Hnear_name));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in * ).            
                             exists g_near.
                             repeat split.
                             +++ assert (Hnear_light : get_light (conf (Good g_near)) = false).
                                 destruct (conf (Good g_near)) as (pos_near, ((ident_near, light_near), alive_near)) eqn : Hconf_near.
                                 rewrite <- Hconf_near.
                                 apply (Hexecutioner g_near da Hpred).
                                 unfold get_alive in *.
                                 rewrite <- Hnear_spec in Hnear_alive.
                                 simpl in Hnear_alive.
                                 auto.
                                 exists g_other.
                                 unfold get_alive in *.
                                 auto.
                                 repeat split; auto. 
                                 unfold get_ident in *;
                                   simpl in Hnear_ident. 
                                 rewrite Nat.ltb_lt in *.
                                 rewrite <- Hnear_spec in Hnear_ident.
                                 simpl in Hnear_ident.
                                 auto.
                                 rewrite <- Hnear_spec in Hnear_dist.
                                 assert (dist (get_location (conf (Good g_near))) (get_location (conf (Good g_other))) = dist
                  (get_location
                     (map_config
                        (lift
                           (existT precondition
                              (frame_choice_bijection (change_frame da conf g_other))
                              (precondition_satisfied da conf g_other))) conf 
                        (Good g_near)))
                  (get_location
                     (map_config
                        (lift
                           (existT precondition
                              (frame_choice_bijection (change_frame da conf g_other))
                              (precondition_satisfied da conf g_other))) conf 
                        (Good g_other)))).
                                 rewrite (frame_dist _ _ ( (change_frame da conf g_other))).
                                 simpl (lift _).
                                 now simpl. 
                                 rewrite H0; apply Hnear_dist.
                                 
                                   
                             simpl in Halive_other_round.
                             destruct (conf (Good g_other)) as (p_other,((i_other, l_other),alive_other)).
                             simpl in Halive_other_round.
                             simpl in Hother_alive_aux.
                             rewrite Halive_other_round in *; discriminate.
                                    (* g_other meurt entre "conf" et "round (conf)". pourquoi c'est pas possible? g_other est allumé a "conf". donc move_to renvoie None. Donc soit il y a des gens tout pres, soit il n'y a personne en vue. ça marche aps avec le "path". 

apres il reste les autres mode de move_to_None. dist_pos_target >Dp *)














                             
                             (* si on recoit Some de move_to, on bouge a moins de Dp de la target, donc comme la target est éteinte, donc elle ne meurt pas, (Hpath et Hlight_off_means_not_near) donc au round suivant elle est allumé (Hlighted) donc elle n'a aps bougé, donc elle est a moins de Dp 

 Si on reçoit None, alors soit il existe un robot trop près, donc ça marche.  *)




                      stop.
      *)
Qed.




Lemma executioner_means_moving :
   forall conf g da da',
    da_predicat da -> da_predicat da' -> path_conf conf -> 
    get_alive (round rbg_ila da' (round rbg_ila da conf) (Good g)) = true ->
    
    executed_means_light_on conf ->
    no_collision_conf conf ->
    executioner_means_light_off conf ->
    exists_at_less_that_Dp conf ->
    (exists g', get_alive (round rbg_ila da conf (Good g')) = true /\
               get_ident (round rbg_ila da conf (Good g)) < get_ident (round rbg_ila da conf (Good g')) /\
               (dist (get_location (round rbg_ila da conf (Good g))) (get_location (round rbg_ila da conf (Good g')))
                <= D)%R) ->
    get_location (conf (Good g)) <> get_location (round rbg_ila da conf (Good g)).
Proof.
  intros conf g da da' Hpred Hpred' Hpath Halive Hex_light Hcoll Hexec_off Hexists_at (g', (Halive_exec, (Hident_exec, Hdist_exec))).
  assert (Halive_r' : get_alive (round rbg_ila da' (round rbg_ila da conf) (Good g')) = false).
  { rewrite dist_sym in Hdist_exec.
    apply (still_alive_means_alive _ _ Hpred') in Halive; try apply Hpred.
    assert (Hrse:= @round_simplify_executioner g' (round rbg_ila da conf) da' g (round rbg_ila da conf (Good g)) Hident_exec Hdist_exec Hpred' (reflexivity _) Halive).
    destruct Hrse as (l,(p,Hr)).
    rewrite Hr.
    now unfold get_alive; simpl.
  }
  assert (Hnot_moving := @executed_means_not_moving (round rbg_ila da conf) da' g' Hpred' Halive_exec Halive_r').
  assert (Hdist_prec : (dist (get_location (conf (Good g))) (get_location (conf (Good g'))) > D)%R).
  { destruct (Rle_lt_dec (dist (get_location (conf (Good g))) (get_location (conf (Good g')))) D).
    rewrite round_good_g in Halive_exec.
    simpl in Halive_exec.
    unfold upt_aux, map_config in *.
    destruct (upt_robot_dies_b _) eqn : Hbool.
    unfold get_alive in *; simpl in *.
    destruct ((conf (Good g'))) as (?,((?,?),?)); simpl in *; discriminate.
    unfold get_alive in Halive_exec; simpl in Halive_exec.
    clear Halive_exec.
    unfold upt_robot_dies_b in Hbool.
    rewrite orb_false_iff in Hbool.
    destruct Hbool as (Hexists, _).
    rewrite <- negb_true_iff, forallb_existsb, forallb_forall in Hexists.
    specialize (Hexists (((let (p, b) := change_frame da conf g' in
                         let (r, t) := p in
                         comp (bij_rotation r)
                           (comp (bij_translation t)
                                 (if b then reflexion else Similarity.id)))
                            (fst (conf (Good g)))), snd (conf (Good g)))).
    
    assert (@List.In (prod R2 ILA)
                    (@pair R2 ILA
                       (
                          match
                            @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                              (prod R2 light) (prod (prod R R2) bool) bool bool
                              robot_choice_RL Frame Choice inactive_choice_ila da
                              conf g' return (@bijection R2 R2_Setoid)
                          with
                          | pair p b =>
                              match p return (@bijection R2 R2_Setoid) with
                              | pair r t =>
                                  @comp R2 R2_Setoid (bij_rotation r)
                                    (@comp R2 R2_Setoid
                                       (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                       match b return (@bijection R2 R2_Setoid) with
                                       | true =>
                                           @sim_f R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES)) reflexion
                                       | false =>
                                           @sim_f R2 R2_Setoid R2_EqDec VS
                                             (@Normed2Metric R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Euclidean2Normed R2 R2_Setoid
                                                   R2_EqDec VS ES))
                                             (@Similarity.id R2 R2_Setoid R2_EqDec
                                                VS
                                                (@Normed2Metric R2 R2_Setoid
                                                   R2_EqDec VS
                                                   (@Euclidean2Normed R2 R2_Setoid
                                                      R2_EqDec VS ES)))
                                       end)
                              end
                          end (@fst R2 ILA (conf (@Good Identifiers g))))
                       (@snd R2 ILA (conf (@Good Identifiers g))))
                    (@List.filter (prod R2 ILA)
                       (fun elt : prod R2 ILA =>
                        andb
                          (Nat.ltb (get_ident elt)
                             (get_ident
                                (@pair R2 ILA
                                   (@section R2 R2_Setoid
                                      match
                                        @change_frame (prod R2 ILA) Loc State_ILA
                                          Identifiers (prod R2 light)
                                          (prod (prod R R2) bool) bool bool
                                          robot_choice_RL Frame Choice
                                          inactive_choice_ila da conf g'
                                        return (@bijection R2 R2_Setoid)
                                      with
                                      | pair p b =>
                                          match
                                            p return (@bijection R2 R2_Setoid)
                                          with
                                          | pair r t =>
                                              @comp R2 R2_Setoid 
                                                (bij_rotation r)
                                                (@comp R2 R2_Setoid
                                                   (@bij_translation R2 R2_Setoid
                                                      R2_EqDec VS t)
                                                   (@sim_f R2 R2_Setoid R2_EqDec VS
                                                      (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                                      match
                                                       b
                                                       return
                                                       (@similarity R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                                      with
                                                      | true => reflexion
                                                      | false =>
                                                       @Similarity.id R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                                      end))
                                          end
                                      end (@fst R2 ILA (conf (@Good Identifiers g'))))
                                   (@snd R2 ILA (conf (@Good Identifiers g'))))))
                          (get_alive elt))
                       (@config_list Loc (prod R2 ILA) State_ILA Identifiers
                          (fun id : @ident Identifiers =>
                           @pair R2 ILA
                             (@section R2 R2_Setoid
                                match
                                  @change_frame (prod R2 ILA) Loc State_ILA Identifiers
                                    (prod R2 light) (prod (prod R R2) bool) bool
                                    bool robot_choice_RL Frame Choice
                                    inactive_choice_ila da conf g'
                                  return (@bijection R2 R2_Setoid)
                                with
                                | pair p b =>
                                    match p return (@bijection R2 R2_Setoid) with
                                    | pair r t =>
                                        @comp R2 R2_Setoid 
                                          (bij_rotation r)
                                          (@comp R2 R2_Setoid
                                             (@bij_translation R2 R2_Setoid R2_EqDec
                                                VS t)
                                             (@sim_f R2 R2_Setoid R2_EqDec VS
                                                (@Normed2Metric R2 R2_Setoid
                                                   R2_EqDec VS
                                                   (@Euclidean2Normed R2 R2_Setoid
                                                      R2_EqDec VS ES))
                                                match
                                                  b
                                                  return
                                                    (@similarity R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES)))
                                                with
                                                | true => reflexion
                                                | false =>
                                                    @Similarity.id R2 R2_Setoid
                                                      R2_EqDec VS
                                                      (@Normed2Metric R2 R2_Setoid
                                                       R2_EqDec VS
                                                       (@Euclidean2Normed R2
                                                       R2_Setoid R2_EqDec VS ES))
                                                end))
                                    end
                                end (@fst R2 ILA (conf id))) 
                             (@snd R2 ILA (conf id)))))).
    { rewrite filter_In, config_list_spec, in_map_iff.
      split.
      - exists (Good g).
        split; try apply In_names.
        destruct (change_frame da conf g') as ((ro,t),b).
        now destruct b.
      - rewrite andb_true_iff.
        split.
        rewrite <- 2 ident_preserved in Hident_exec; try apply Hpred.
        unfold get_ident in *; simpl in *.
        now rewrite Nat.ltb_lt.
        do 2 apply still_alive_means_alive in Halive; try apply Hpred; try apply Hpred'.
        unfold get_alive in *; simpl in *; auto.
    }
    specialize (Hexists H).
    clear H.
    unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
    simpl (fst _) in Hexists.
    destruct (change_frame _) as ((ro,t),b) eqn : Hchange.
    assert (Hframe := frame_dist (fst (conf (Good g))) (fst (conf (Good g'))) (ro, t, b)).
    unfold frame_choice_bijection, Frame in Hframe.
    destruct b; simpl in *; rewrite <- Hframe in Hexists; rewrite negb_true_iff, Rle_bool_false_iff in *; auto; lra. 
    apply Hpred.
    lra.
  }
  assert (Hdist : (dist (get_location (conf (Good g'))) (get_location (round rbg_ila da conf (Good g'))) <= D)%R).
  {
    rewrite <- Rle_bool_true_iff.
    apply dist_round_max_d.
    apply Hpred.
    apply Hpath.
    now apply still_alive_means_alive in Halive_exec.
  }
  assert (Hex_light_round := executed_means_light_on_round).
  specialize (Hex_light_round conf da Hpred Hpath Hcoll Hexec_off Hex_light Hexists_at).
  specialize (Hex_light_round g' da' Hpred' Halive_exec Halive_r').
  assert ( (get_location (round rbg_ila da conf (Good g'))) == (get_location (conf (Good g'))))%R by (symmetry; apply (light_on_means_not_moving_before g' Hpred Hpath Halive_exec Hex_light_round)).
  
  set (x := (get_location (conf (Good g')))) in *;
    set (y := (get_location (round rbg_ila da conf (Good g')))) in *;
    set (u := get_location (conf (Good g))) in *;
    set (v := get_location (round rbg_ila da conf (Good g))) in *.
  rewrite H in *.
  assert (dist u v > 0)%R.
  { assert (Htri := RealMetricSpace.triang_ineq u v x ).
    lra. }  
  intro Hfalse.
  rewrite Hfalse in H0; rewrite R2_dist_defined_2 in H0.
  lra.
Qed.




Lemma round_target_alive :
  forall conf da,
    da_predicat da ->
    path_conf conf->
    no_collision_conf conf ->
    executioner_means_light_off conf ->
    executed_means_light_on conf ->
    exists_at_less_that_Dp conf ->
    target_alive conf ->
    target_alive (round rbg_ila da conf).
Proof.
  intros conf da Hpred Hpath Hcoll Hexecutioner_off Hexecuted_on Hexists_at Ht_alive g Hn_0 Halive.
  unfold target_alive in *.
  rewrite <- (ident_preserved conf g Hpred) in Hn_0.
  specialize (Ht_alive g Hn_0 (still_alive_means_alive conf g Hpred Halive)).
  assert (Halive_bis := Halive).
  rewrite round_good_g in Halive; try apply Hpred.
  simpl in Halive.
  unfold upt_aux, map_config in Halive.
  destruct (conf (Good g)) as (pos,((ident, light), alive)) eqn : Hconf.
  destruct (upt_robot_dies_b _) eqn : Hbool.
  - unfold get_alive in Halive; now simpl in Halive.
  - unfold rbg_fnc in Halive.   
    set (new_pos := choose_new_pos _ _) in *.
    destruct (move_to _) eqn : Hmove.
    + assert (Hchoose_correct := @choose_new_pos_correct _ _ new_pos (reflexivity _)).
      destruct Hchoose_correct as (Hdist_choose_dp, Hdist_chose_d).
      assert (Hmove_Some := move_to_Some_zone Hmove).
      set (target := choose_target _) in *.
      assert (Htarget_in_spect := @choose_target_in_spect _ target (reflexivity _)).
      specialize (Hmove_Some _ Htarget_in_spect).
      unfold obs_from_config, Spect_ILA in Htarget_in_spect.
      rewrite make_set_spec, filter_InA, config_list_InA in Htarget_in_spect.
      * rewrite 3 andb_true_iff, Rle_bool_true_iff in Htarget_in_spect.
        destruct Htarget_in_spect as (([g_target|b_target],Htarget_spec),
                                      (((Htarget_Dmax, Htarget_alive), Htarget_aux), Htarget_ident));
          try (assert (Hfalse := In_Bnames b_target);
               now simpl in * ).
        (* si target est allumé, tous els robots visibles sont allumés, et il exists donc un robot à moins de Dp (cf Hexists_at). donc target est à moins de Dp, donc elle sera vivante au tours prochain car:
   elle est éteinte donc elle ne bouge pas.
   elle ne peux pas mourrir car son bourreau potentiel serait à moins de D de elle, or un bourreau est éteint, et donc est à plus de Dmax de nous. donc le bourreau doit etre à plus de D de target, contradiction.


    si target est étiente, elle ne meurt aps au prochain tour (executed_mean_light_on) donc comme on à Hdist_Dp, on a dist new_pos (round ... g_target) <= Dmax.

         *)
        destruct (get_light target) eqn : Htarget_light.
        -- assert (Hall_lighted := @light_off_first _ target (reflexivity _) Htarget_light).
           assert (Hless_that_Dp := Hexists_at).
           specialize (Hexists_at g (still_alive_means_alive conf g Hpred Halive_bis)).
           revert Hexists_at; intro Hexists_at.
           assert (Hforall_lighted : (forall g_near,
                                          get_alive (conf (Good g_near)) = true ->
                                      (dist (get_location (conf (Good g_near))) (get_location (conf (Good g))) <= Dmax)%R ->
                get_ident (conf (Good g_near)) < get_ident (conf (Good g)) ->
                get_light (conf (Good g_near)) = true)).
           {
             unfold For_all in Hall_lighted.
             intros g_near Halive_near Hdist_near Hident_near.
             destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
             specialize (Hall_lighted ((comp (bij_rotation r)
                           (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                          (fst (conf (Good g_near))), snd (conf (Good g_near)))).
             apply Hall_lighted.
             unfold obs_from_config, Spect_ILA.
             rewrite make_set_spec, filter_InA, config_list_InA, 3 andb_true_iff, Rle_bool_true_iff.
             repeat split.
             exists (Good g_near).
             destruct b; reflexivity.
             rewrite (frame_dist _ _ (r,t,b)) in Hdist_near.
             unfold frame_choice_bijection, Frame in Hdist_near. unfold Datatypes.id in *.
             simpl (_ ∘ _) in Hdist_near.
             rewrite Hconf in Hdist_near.
             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
             destruct b; simpl in *; lra.
             unfold get_alive in *; now simpl in *.
             repeat rewrite andb_true_iff.
             unfold get_alive in *; now simpl in *.
             
             rewrite Nat.leb_le, <-Hconf .
             unfold get_ident in *; simpl in *.
             omega.
             intros x y Hxy.
             rewrite (fst_compat Hxy).
             rewrite (get_alive_compat Hxy), (get_ident_compat Hxy).
             reflexivity.
           }
           assert (H_not_0 : get_ident (pos, (ident, light, alive)) > 0). 
           {
             
             rewrite (Nat.neq_0_lt_0 _) in Hn_0.
             unfold get_ident in *; simpl in *; omega.

           }
           rewrite Hconf in *.
           specialize (Hexists_at H_not_0 Hforall_lighted).
           assert (Hexists_at_less_Dp := Hexists_at).
                     
           destruct Hexists_at.

           assert (Hlight_close := @light_close_first _ target (reflexivity _) Htarget_light).
           (* par rapprot à notre position ACTUELE elle est à moins de Dp. *) 
           assert (dist (0,0) (get_location target) <= Dp)%R.
           destruct (Rle_dec (dist (0,0) (@get_location Loc _ _ target))%R Dp); try auto.
           specialize (Hlight_close (Rnot_le_gt _ _ n0)).
           destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
           specialize (Hlight_close ((comp (bij_rotation r)
                           (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                          (fst (conf (Good x))), snd (conf (Good x)))).
           assert (Hfalse : ~ (dist (get_location (conf (Good g))) (get_location (conf (Good x))) <= Dp)%R).
           {
             apply Rgt_not_le.
             rewrite (frame_dist _ _ (r,t,b)).
             assert (Hpred_bis := Hpred).
             revert Hpred; intro Hpred; destruct Hpred as (Horigin,_).
             specialize (Horigin conf g (r,t,b) Hchange).
             rewrite Horigin.
             assert (Hin : @In (prod R2 ILA)
                         (@state_Setoid (@make_Location R2 R2_Setoid R2_EqDec) 
                            (prod R2 ILA) State_ILA)
                         (@state_EqDec (@make_Location R2 R2_Setoid R2_EqDec) 
                            (prod R2 ILA) State_ILA)
                         (@FSetList.SetList (prod R2 ILA)
                            (@state_Setoid (@make_Location R2 R2_Setoid R2_EqDec) 
                               (prod R2 ILA) State_ILA)
                            (@state_EqDec (@make_Location R2 R2_Setoid R2_EqDec) 
                               (prod R2 ILA) State_ILA))
                         (@pair R2 ILA
                            (@section R2 R2_Setoid
                               (@comp R2 R2_Setoid (bij_rotation r)
                                  (@comp R2 R2_Setoid
                                     (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                     match b return (@bijection R2 R2_Setoid) with
                                     | true =>
                                         @sim_f R2 R2_Setoid R2_EqDec VS
                                           (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                              (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                           reflexion
                                     | false =>
                                         @sim_f R2 R2_Setoid R2_EqDec VS
                                           (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                              (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                           (@Similarity.id R2 R2_Setoid R2_EqDec VS
                                              (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                 (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES)))
                                     end)) (@fst R2 ILA (conf (@Good Identifiers x))))
                            (@snd R2 ILA (conf (@Good Identifiers x))))
                         (@obs_from_config (prod R2 ILA) Loc State_ILA Identifiers Spect_ILA
                            (fun id : @Identifiers.ident Identifiers =>
                             @pair R2 ILA
                               (@section R2 R2_Setoid
                                  (@comp R2 R2_Setoid (bij_rotation r)
                                     (@comp R2 R2_Setoid
                                        (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                        (@sim_f R2 R2_Setoid R2_EqDec VS
                                           (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                              (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                           match
                                             b
                                             return
                                               (@similarity R2 R2_Setoid R2_EqDec VS
                                                  (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                     (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                                        ES)))
                                           with
                                           | true => reflexion
                                           | false =>
                                               @Similarity.id R2 R2_Setoid R2_EqDec VS
                                                 (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                    (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                                       ES))
                                           end))) (@fst R2 ILA (conf id)))
                               (@snd R2 ILA (conf id)))
                            (@Datatypes.id R2
                               (@section R2 R2_Setoid
                                  (@comp R2 R2_Setoid (bij_rotation r)
                                     (@comp R2 R2_Setoid
                                        (@bij_translation R2 R2_Setoid R2_EqDec VS t)
                                        (@sim_f R2 R2_Setoid R2_EqDec VS
                                           (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                              (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS ES))
                                           match
                                             b
                                             return
                                               (@similarity R2 R2_Setoid R2_EqDec VS
                                                  (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                     (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                                        ES)))
                                           with
                                           | true => reflexion
                                           | false =>
                                               @Similarity.id R2 R2_Setoid R2_EqDec VS
                                                 (@Normed2Metric R2 R2_Setoid R2_EqDec VS
                                                    (@Euclidean2Normed R2 R2_Setoid R2_EqDec VS
                                                       ES))
                                           end)))
                                  (@fst R2 ILA
                                     (@pair R2 ILA pos
                                        (@pair (prod identifiants NoCollisionAndPath.light) NoCollisionAndPath.alive
                                           (@pair identifiants NoCollisionAndPath.light ident light) alive)))), snd (pos, (ident,light,alive))))).
             unfold obs_from_config, Spect_ILA.
             rewrite make_set_spec, filter_InA.
             rewrite (@config_list_InA Loc _ State_ILA), 3 andb_true_iff, Rle_bool_true_iff.
             repeat split.
             exists (Good x).
             destruct b; reflexivity.
             rewrite (frame_dist _ _ (r,t,b)) in H.
             unfold frame_choice_bijection, Frame in H. unfold Datatypes.id in *.
             simpl (_ ∘ _) in H.
             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
             destruct b; unfold Dp in H; generalize Dmax_6D, D_0; rewrite dist_sym; simpl in *; lra.
             unfold get_alive in *; now simpl in *.
             unfold get_alive in *; now simpl in *.
             rewrite Nat.leb_le.
             rewrite Hconf in *.
             unfold get_ident in *; simpl in *.
             omega.
             intros x' y Hxy.
             rewrite (fst_compat Hxy).
             rewrite (get_alive_compat Hxy), (get_ident_compat Hxy).
             reflexivity.
             specialize (Hlight_close Hin).
             simpl in *; destruct b; apply Hlight_close.
           }
           destruct H as (?,(?,?)); rewrite Hconf in *; contradiction.
           exists g_target.
           repeat split.
           ++ destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
              rewrite round_good_g; try apply Hpred.
              simpl.
              unfold upt_aux, map_config.
              destruct (upt_robot_dies_b _ g_target) eqn : Hbool_target.
              ** assert (Halive_target_round :
                           get_alive (round rbg_ila da conf (Good g_target)) = false).
                 { rewrite round_good_g; try apply Hpred.
                   simpl.
                   unfold upt_aux, map_config.
                   now rewrite Hbool_target, Hconf_target; unfold get_alive; simpl.
                 }
                 assert ( Hsame_pos_round_target :
                            get_location (conf (Good g_target))
                            == get_location (round rbg_ila da conf (Good g_target))).
                 { apply executed_means_not_moving; try auto.
                   rewrite Htarget_spec in Htarget_alive.
                   unfold get_alive in *; rewrite Hconf_target; now simpl.
                 }
                 unfold upt_robot_dies_b in Hbool_target.
                 rewrite orb_true_iff in Hbool_target.
                 destruct Hbool_target as [Htoo_close_so_lighted|Htoo_far_but_path_conf].

                 
(* target dead -> executed means not moving /\ executioner_means_moving -> executioner_means_light_off (???????)-> contradiction avec Hall_lighted.
target est vivant apres le round car elle est à moins de Dp, et que tous les autres robots visibles sont allumés, donc   *)
                 rewrite existsb_exists in *.
                 destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
            destruct Htoo_close_so_lighted as (too_close, (Hin_too_close, Hdist_too_close)).
            +++ unfold executioner_means_light_off in *.
               rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff in Hin_too_close.
               destruct Hin_too_close as (([g_too_close | byz], (Hspec_too_close, Hnames_too_close)), (Hident_too_close, Halive_too_close));
                 try (assert (Hfalse := In_Bnames byz);
                      now simpl in *).
                   specialize (Hexecutioner_off g_too_close da Hpred).
                   rewrite <- Hspec_too_close in Halive_too_close.
                   unfold get_alive in *.
                   simpl (snd (snd _)) in *.
                   specialize (Hexecutioner_off Halive_too_close).
                   assert (Hex : (exists g' : G,
                    snd (snd (conf (Good g'))) = true /\
                    get_ident (conf (Good g_too_close)) < get_ident (conf (Good g')) /\
                    (dist (get_location (conf (Good g_too_close)))
                       (get_location (conf (Good g'))) <= D)%R)).
                   { exists g_target;
                       repeat split; try now simpl.
                     rewrite <- Htarget_alive.
                     destruct Htarget_spec as (_,Htarget_spec_snd).
                     destruct target as (p_t,((i_t,l_t),a_t)).
                     simpl in Htarget_spec_snd; destruct Htarget_spec_snd as (_,(_,Htarget_spec_alive)).
                     rewrite Htarget_spec_alive.
                     now rewrite Hconf_target; simpl.
                     rewrite Nat.ltb_lt in Hident_too_close.
                     rewrite <- Hspec_too_close in Hident_too_close.
                     unfold get_ident in *; simpl in *; auto.
                     rewrite <- Hspec_too_close, Rle_bool_true_iff in Hdist_too_close.
                     unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_too_close.
                     rewrite (frame_dist _ _ (change_frame da conf g_target)).

                     now simpl in *.
                   }
                   specialize (Hexecutioner_off Hex).
                   clear Hex.

                   assert (Hlight_off_first := @light_off_first _ target (reflexivity _) Htarget_light).
                   specialize (Hlight_off_first ((comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf (Good g_too_close))), snd (conf (Good g_too_close)))).
                   unfold equiv, bool_Setoid, eq_setoid in Hlight_off_first.
                   rewrite <- Hlight_off_first, <- Hexecutioner_off.
                   unfold get_light. rewrite Hconf_target. now simpl in *.
                   unfold obs_from_config, Spect_ILA.
                   rewrite make_set_spec, filter_InA, config_list_InA, andb_true_iff.                   repeat split.
                   exists (Good g_too_close).
                   destruct b; reflexivity.
                   rewrite 2 andb_true_iff.
                   rewrite Rle_bool_true_iff.
                   replace (fst
        ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g_too_close))), snd (conf (Good g_too_close))))%R
                     with
                       ((comp (bij_rotation r)
            (comp (bij_translation t) (if b then reflexion else Similarity.id)))
           (fst (conf (Good g_too_close))))%R.
                   unfold Datatypes.id.
                   assert (Hframe := frame_dist (fst (conf (Good g_too_close))) pos ((r,t),b)).
                   unfold frame_choice_bijection, Frame in Hframe.
                   assert (dist (fst (conf (Good g_too_close))) pos <= Dmax)%R.
                   rewrite Rle_bool_true_iff in Hdist_too_close.
                   unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_too_close.
                   rewrite <- Hspec_too_close in Hdist_too_close.
                   assert ((dist (fst (conf (Good g_too_close)))
                                 (fst (conf (Good g_target))) <= D)%R).
                   rewrite (frame_dist _ _ (change_frame da conf g_target)).
                   unfold frame_choice_bijection, Frame, Datatypes.id in *.
                   now simpl; simpl in Hdist_too_close.
                   (*  *)
                   specialize (Hless_that_Dp g).
                   unfold get_alive in Hless_that_Dp.
                     rewrite Hconf, Halive in Hless_that_Dp;
                     simpl (snd (snd _)) in Hless_that_Dp.
                   specialize (Hless_that_Dp (reflexivity _)).
                   destruct (Rle_bool (dist pos (fst (conf (Good g_target)))) Dp) eqn : Hhow_far.
                   rewrite Rle_bool_true_iff, dist_sym in Hhow_far.
                   assert (Hti := RealMetricSpace.triang_ineq (fst (conf (Good g_too_close))) (fst (conf (Good g_target))) pos ).
                   rewrite Hconf_target in Hti at 2.
                   simpl ( (fst _)) in Hti.
                   rewrite dist_sym in H1.
                   generalize (D_0), Dmax_6D.
                   unfold Dp in *.
                   rewrite Hconf_target in *; simpl (fst _) in *.
                   rewrite dist_sym in H1.
                   lra.
                   rewrite Rle_bool_false_iff in Hhow_far.
                   revert H0; intro H0.
                   destruct Hhow_far.
                   destruct Hpred as (Horigin, _).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   revert Horigin; intros Horigin.
                   rewrite <- Horigin, Htarget_spec in H0.
                   rewrite (frame_dist _ _ (r,t,b)).
                   unfold frame_choice_bijection, Frame in *.
                   fold Frame in *. rewrite Hchange in *.
                   rewrite Hconf_target, Hconf in *.
                   unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.
                   now destruct b; simpl in *.
                   split ; try (destruct b; now rewrite <- Hframe).
                   unfold get_alive; simpl in *; auto. 
                   now simpl in *. 
                   rewrite Nat.leb_le.
                   transitivity (get_ident (conf (Good g_target))).
                   rewrite Nat.ltb_lt, <- Hspec_too_close in Hident_too_close.
                   unfold get_ident in *; simpl in *; omega.
                   destruct Hpred as (Horigin, ?).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   revert Horigin; intro Horigin.
                   set (spect := obs_from_config _ _) in *.
                   assert (Htarget_ident' := @target_lower spect target).
                   specialize (Htarget_ident' (((frame_choice_bijection (change_frame da conf g)) (get_location (conf (Good g))) ), snd(conf (Good g)))).
                   rewrite Htarget_spec in Htarget_ident'.
                   rewrite Hconf_target, Hconf in *.
                   apply Nat.lt_le_incl.
                   unfold get_ident in *; simpl in *; apply Htarget_ident'.
                   unfold spect.
                   rewrite Hchange.
                   unfold obs_from_config, Spect_ILA.
                   rewrite make_set_spec, filter_InA, (@config_list_InA Loc _ State_ILA), 3 andb_true_iff, Rle_bool_true_iff.
                   repeat split.
                   exists (Good g).
                   destruct b; rewrite Hconf; simpl; repeat split; reflexivity.
                   unfold Datatypes.id.
                   
                   generalize (dist_same ((comp (bij_rotation r)
                                                (comp (bij_translation t) (if b then reflexion else Similarity.id))) pos)), Dmax_6D, D_0;
                     
                   intro Hdist_0.
                   
                   simpl in Hdist_0; simpl.
                   destruct b; simpl in *; rewrite Hdist_0.
                   lra.
                   lra.
                   unfold get_alive; simpl in *; assumption.
                   unfold get_alive; simpl in *; assumption.
                   rewrite Nat.leb_le.
                   reflexivity.
                   intros x1 y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy). 
                   assert (Hcompat := get_ident_compat Hxy).
                   rewrite Hcompat.
                   reflexivity.
                   rewrite Hchange in *.
                   rewrite <- Horigin.                     
                   destruct b; auto.
                   fold target.
                   apply Htarget_spec.
                   intros x1 y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy). 
                   assert (Hcompat := get_ident_compat Hxy).
                   rewrite Hcompat.
                   reflexivity.
                      +++
                        specialize (Hpath g_target).
                        assert (get_alive (conf (Good g_target)) == true).
                        rewrite <- Htarget_alive.
                        rewrite Htarget_spec.
                        rewrite Hconf_target.
                        unfold get_alive; now simpl.
               simpl in H1.
               specialize (Hpath H1); clear H1.
               destruct Hpath as [Hident_0|Hpath_backup].
               rewrite (ident_preserved _ _ Hpred) in Hident_0.
               assert (get_alive (round rbg_ila da conf (Good g_target)) = true).
               apply ident_0_alive; intuition.
               rewrite H1 in *; discriminate.
               rewrite forallb_existsb, forallb_forall in Htoo_far_but_path_conf.
               destruct Hpath_backup as (g_too_close, (Halive_close,( Hdist_close, Hident_close))). 
               specialize (Htoo_far_but_path_conf
                             ((((let (p, b) := change_frame da conf g_target in
                                 let (r, t) := p in
                                 comp (bij_rotation r)
                               (comp (bij_translation t)
                                  (if b then reflexion else Similarity.id)))
                              (fst (conf (Good g_too_close))), snd (conf (Good g_too_close)))))).
               rewrite negb_true_iff, Rle_bool_false_iff in Htoo_far_but_path_conf.
               destruct Htoo_far_but_path_conf.
               rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff.
               repeat split.
               *** exists (Good g_too_close).
                  split.
                  destruct (change_frame da conf g_target) as (?,b0); destruct b0;
                    now simpl.
                  apply In_names.
               *** rewrite Nat.ltb_lt.
                  unfold get_ident in *; simpl in Hident_close; simpl.
                  auto.
               *** rewrite <- Halive_close.
                  now unfold get_alive; simpl.
               *** rewrite dist_sym, (frame_dist _ _ (change_frame da conf g_target)) in Hdist_close.
                  unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                  unfold frame_choice_bijection, Frame in Hdist_close; fold Frame in *.
                  revert Hdist_close; intros Hdist_close.
                  destruct (change_frame _ _ g_target) as ((r_f, t_f), b_f)
                                                         eqn : Hchange_far.
                  now destruct b_f; simpl in *.
                      ** unfold get_alive in *; simpl.
                         rewrite Hconf_target.
                         simpl.
                         rewrite <- Htarget_alive.
                         destruct Htarget_spec as (_,Htarget_spec_snd).
                         destruct target as (p_t,((i_t,l_t),a_t)).
                         simpl in Htarget_spec_snd; destruct Htarget_spec_snd as (_,(_,Htarget_spec_alive)).
                         simpl.
                         rewrite Htarget_spec_alive.
                         reflexivity.
                      ++ rewrite <- 2 ident_preserved; try apply Hpred.
                         destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
                         destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
                         set (spect := obs_from_config _ _) in *.
                     assert (Htarget_ident' := @target_lower spect target).
                     specialize (Htarget_ident' (((frame_choice_bijection (change_frame da conf g)) (get_location (conf (Good g))) ), snd(conf (Good g)))).
                     rewrite Htarget_spec in Htarget_ident'.
                     rewrite  Hconf in *.
                     unfold get_ident in *; simpl in *; apply Htarget_ident'.
                     unfold spect.
                     rewrite Hchange.
                     unfold obs_from_config, Spect_ILA.
                     rewrite make_set_spec, filter_InA, (@config_list_InA Loc _ State_ILA), 3 andb_true_iff, Rle_bool_true_iff.
                     repeat split.
                     exists (Good g).
                     destruct b; rewrite Hconf; simpl; repeat split; reflexivity.
                     unfold Datatypes.id.
                   
                   generalize (dist_same ((comp (bij_rotation r)
                                                (comp (bij_translation t) (if b then reflexion else Similarity.id))) pos)), Dmax_6D, D_0;
                     
                   intro Hdist_0.
                   
                   simpl in Hdist_0; simpl.
                   destruct b; simpl in *; rewrite Hdist_0.
                   lra.                        
                   lra.

                   unfold get_alive; simpl in *; assumption.
                   unfold get_alive; simpl in *; assumption.
                   rewrite Nat.leb_le.
                   reflexivity.
                   intros x1 y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy). 
                   assert (Hcompat := get_ident_compat Hxy).
                   rewrite Hcompat.
                   reflexivity.
                   rewrite Hchange in *.
                   destruct Hpred as (Horigin, ?).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   revert Horigin; intro Horigin.
                   rewrite <- Horigin.
                   rewrite Hconf.
                   unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                   unfold frame_choice_bijection. 
                   rewrite Hchange.
                   simpl; destruct b; reflexivity.
                   fold target.
                   apply Htarget_spec.
                      ++
                        revert Hdist_choose_dp; intros Hdist_choose_dp.
                        rewrite round_good_g at 1; try apply Hpred.
                        simpl (get_location _) at 1.
                        unfold upt_aux, map_config.
                        rewrite Hbool.
                        unfold rbg_fnc.
                        destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
                        rewrite Hconf.
                        fold target new_pos.
                        rewrite Hmove.
                        simpl (fst _).
                        assert (Hdist_choose_dp_aux : (dist ((retraction
           (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos))
                                                           (retraction
           (comp (bij_rotation r)
              (comp (bij_translation t) (if b then reflexion else Similarity.id))) (get_location target)) < Dp)%R).
                        rewrite (frame_dist _ _ (r,t,b)).
                        unfold frame_choice_bijection, Frame.
                        destruct b; rewrite 2 section_retraction;
                        assumption.
                        unfold Datatypes.id in *.
                        rewrite Htarget_spec in Hdist_choose_dp_aux.
                        unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_choose_dp_aux.
                        assert (Hret_sec := retraction_section (frame_choice_bijection (r,t,b)) (fst (conf (Good g_target)))).
                        unfold frame_choice_bijection, Frame in Hret_sec.
                        assert (Hdist_choose_dp' : (dist (retraction
                              (comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id))) new_pos) (fst (conf (Good g_target))) < Dp)%R).
                        rewrite <- Hret_sec.
                        destruct b; simpl in *; apply Hdist_choose_dp_aux.
                        assert (Hti := RealMetricSpace.triang_ineq  (retraction
        (comp (bij_rotation r)
           (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos)
                                                                    (fst (conf (Good g_target))) (get_location (round rbg_ila da conf (Good g_target)))).
                        assert ((dist
           (retraction
              (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos)
           (get_location (round rbg_ila da conf (Good g_target))) <=
  Dp +
         dist (fst (conf (Good g_target))) (get_location (round rbg_ila da conf (Good g_target))))%R).
                        lra.
                        assert ((dist
          (retraction
             (comp (bij_rotation r)
                (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos)
          (get_location (round rbg_ila da conf (Good g_target)))) <= Dp + D)%R.
                        assert (Hdist_round := @dist_round_max_d g_target conf da Hpred Hpath).
                        assert (get_alive (conf (Good g_target)) == true).
                      rewrite <- Htarget_alive.
                     destruct Htarget_spec as (_,Htarget_spec_snd).
                     destruct target as (p_t,((i_t,l_t),a_t)).
                     simpl in Htarget_spec_snd.
                     destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
                     destruct Htarget_spec_snd as (_,(_,Htarget_spec_alive)).
                     rewrite Htarget_spec_alive.
                     simpl; auto.
                     specialize (Hdist_round H2).
                     unfold equiv, bool_Setoid, eq_setoid in Hdist_round.
                     rewrite Rle_bool_true_iff in Hdist_round.
                     unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in *.
                     generalize D_0.
                     transitivity (Dp + dist (fst (conf (Good g_target))) (fst (round rbg_ila da conf (Good g_target))))%R.
                     apply H1.
                     apply Rplus_le_compat_l.
                     apply Hdist_round. 
                     unfold Dp in *.
                     replace (Dmax) with (Dmax - D + D)%R by lra.
                     cbn in *.
                     changeR2.
                     destruct b; apply H2.

                      -- 
                        exists g_target.
                        assert (Htarget_alive' : get_alive (conf (Good g_target)) = true).
                        {
                          rewrite <- Htarget_alive.
                          destruct Htarget_spec as (_,Htarget_spec_snd).
                          destruct target as (p_t,((i_t,l_t),a_t)).
                          simpl in Htarget_spec_snd.
                          destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
                          destruct Htarget_spec_snd as (_,(_,Htarget_spec_alive)).
                          rewrite Htarget_spec_alive.
                          simpl; auto.

                        }
                        repeat split.
                        ++ apply light_off_means_alive_next; try auto.
                           rewrite <- Htarget_light.
                           destruct Htarget_spec as (_,Htarget_spec_snd).
                           destruct target as (p_t,((i_t,l_t),a_t)).
                           simpl in Htarget_spec_snd.
                           destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
                           destruct Htarget_spec_snd as (_,(Htarget_spec_light,_)).
                           rewrite Htarget_spec_light.
                           simpl; auto.
                        ++ 
rewrite <- 2 ident_preserved; try apply Hpred.
                         destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
                         destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
                         set (spect := obs_from_config _ _) in *.
                     assert (Htarget_ident' := @target_lower spect target).
                     specialize (Htarget_ident' (((frame_choice_bijection (change_frame da conf g)) (get_location (conf (Good g))) ), snd(conf (Good g)))).
                     rewrite Htarget_spec in Htarget_ident'.
                     rewrite  Hconf in *.
                     unfold get_ident in *; simpl in *; apply Htarget_ident'.
                     unfold spect.
                     rewrite Hchange.
                     unfold obs_from_config, Spect_ILA.
                     rewrite make_set_spec, filter_InA, (@config_list_InA Loc _ State_ILA), 3 andb_true_iff, Rle_bool_true_iff.
                     repeat split.
                     exists (Good g).
                     destruct b; rewrite Hconf; simpl; repeat split; reflexivity.
                     unfold Datatypes.id.
                   
                   generalize (dist_same ((comp (bij_rotation r)
                                                (comp (bij_translation t) (if b then reflexion else Similarity.id))) pos)), Dmax_6D, D_0;
                     
                   intro Hdist_0.
                   
                   simpl in Hdist_0; simpl.
                   destruct b; simpl in *; rewrite Hdist_0.
                   lra.                        
                   lra.

                   unfold get_alive; simpl in *; assumption.
                   unfold get_alive; simpl in *; assumption.
                   rewrite Nat.leb_le.
                   reflexivity.
                   intros x1 y Hxy; rewrite (RelationPairs.fst_compat _ _ _ _ Hxy), (get_alive_compat Hxy). 
                   assert (Hcompat := get_ident_compat Hxy).
                   rewrite Hcompat.
                   reflexivity.
                   rewrite Hchange in *.
                   destruct Hpred as (Horigin, ?).
                   specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                   revert Horigin; intro Horigin.
                   rewrite <- Horigin.
                   rewrite Hconf.
                   unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                   unfold frame_choice_bijection. 
                   rewrite Hchange.
                   simpl; destruct b; reflexivity.
                   fold target.
                   apply Htarget_spec.
                   ++
                        revert Hdist_choose_dp; intros Hdist_choose_dp.
                        rewrite round_good_g at 1; try apply Hpred.
                        simpl (get_location _) at 1.
                        unfold upt_aux, map_config.
                        rewrite Hbool.
                        unfold rbg_fnc.
                        destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
                        rewrite Hconf.
                        fold target new_pos.
                        rewrite Hmove.
                        simpl (fst _).
                        assert (Hdist_choose_dp_aux : (dist ((retraction
           (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos))
                                                           (retraction
           (comp (bij_rotation r)
              (comp (bij_translation t) (if b then reflexion else Similarity.id))) (get_location target)) < Dp)%R).
                        rewrite (frame_dist _ _ (r,t,b)).
                        unfold frame_choice_bijection, Frame.
                        destruct b; rewrite 2 section_retraction;
                        assumption.
                        unfold Datatypes.id in *.
                        rewrite Htarget_spec in Hdist_choose_dp_aux.
                        unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in Hdist_choose_dp_aux.
                        assert (Hret_sec := retraction_section (frame_choice_bijection (r,t,b)) (fst (conf (Good g_target)))).
                        unfold frame_choice_bijection, Frame in Hret_sec.
                        assert (Hdist_choose_dp' : (dist (retraction
                              (comp (bij_rotation r)
                                 (comp (bij_translation t)
                                    (if b then reflexion else Similarity.id))) new_pos) (fst (conf (Good g_target))) < Dp)%R).
                        rewrite <- Hret_sec.
                        destruct b; simpl in *; apply Hdist_choose_dp_aux.
                        assert (Hti := RealMetricSpace.triang_ineq  (retraction
        (comp (bij_rotation r)
           (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos)
                                                                    (fst (conf (Good g_target))) (get_location (round rbg_ila da conf (Good g_target)))).
                        assert ((dist
           (retraction
              (comp (bij_rotation r)
                 (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos)
           (get_location (round rbg_ila da conf (Good g_target))) <=
  Dp +
         dist (fst (conf (Good g_target))) (get_location (round rbg_ila da conf (Good g_target))))%R).
                        lra.
                        assert ((dist
          (retraction
             (comp (bij_rotation r)
                (comp (bij_translation t) (if b then reflexion else Similarity.id))) new_pos)
          (get_location (round rbg_ila da conf (Good g_target)))) <= Dp + D)%R.
                        assert (Hdist_round := @dist_round_max_d g_target conf da Hpred Hpath).
                        assert (get_alive (conf (Good g_target)) == true).
                      rewrite <- Htarget_alive.
                     destruct Htarget_spec as (_,Htarget_spec_snd).
                     destruct target as (p_t,((i_t,l_t),a_t)).
                     simpl in Htarget_spec_snd.
                     destruct (conf (Good g_target)) as (pos_target, ((ident_target, light_target), alive_target)) eqn : Hconf_target.
                     destruct Htarget_spec_snd as (_,(_,Htarget_spec_alive)).
                     rewrite Htarget_spec_alive.
                     simpl; auto.
                     specialize (Hdist_round H0).
                     unfold equiv, bool_Setoid, eq_setoid in Hdist_round.
                     rewrite Rle_bool_true_iff in Hdist_round.
                     unfold get_location, State_ILA, AddInfo, OnlyLocation, get_location, Datatypes.id in *.
                     generalize D_0.
                     transitivity (Dp + dist (fst (conf (Good g_target))) (fst (round rbg_ila da conf (Good g_target))))%R.
                     apply H.
                     apply Rplus_le_compat_l.
                     apply Hdist_round. 
                     unfold Dp in *.
                     replace (Dmax) with (Dmax - D + D)%R by lra.
                     cbn in *.
                     changeR2.
                     destruct b; apply H0.
                      * intros x y Hxy.
                        rewrite (fst_compat Hxy).
                        rewrite (get_alive_compat Hxy), (get_ident_compat Hxy).
                        reflexivity.
                      +
                        assert (Hdist_same : get_location (conf (Good g)) == get_location (round rbg_ila da conf (Good g))).
                        {
                          rewrite round_good_g; try auto.
                          simpl (get_location _).
                          unfold upt_aux, map_config; rewrite Hbool.
                          unfold rbg_fnc.
                          unfold new_pos in *;
                            destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
                          rewrite Hconf, Hmove.
                          destruct Hpred as (Horigin, ?).
                          specialize (Horigin conf g (change_frame da conf g) (reflexivity _)).
                          revert Horigin; intro Horigin.
                          rewrite <- Horigin.
                          rewrite Hconf.
                          unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                          rewrite Hchange.
                          assert (Hret_sec := retraction_section (frame_choice_bijection (r,t,b)) (fst (conf (Good g)))).
                          unfold frame_choice_bijection, Frame in Hret_sec.
                          rewrite Hconf in Hret_sec.
                          rewrite <- Hret_sec.
                          destruct b; simpl in *; auto. 
                        }
                        assert (Hmove_None := move_to_None Hmove).
                        destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
                       
                       specialize (Hmove_None (((comp (bij_rotation r)
                            (comp (bij_translation t)
                               (if b then reflexion else Similarity.id)))
                                                  (fst (round rbg_ila da conf (Good g)))))).
                       assert (Hsame_pos : get_location (round rbg_ila da conf (Good g)) = get_location (conf (Good g))).
                       {
                         rewrite round_good_g; try auto.
                         simpl.
                         unfold upt_aux, map_config; rewrite Hchange, Hbool in *.
                         unfold rbg_fnc; unfold new_pos in *; rewrite Hconf, Hmove.
                         destruct Hpred as (Horigin,_).
                         revert Horigin; intro Horigin.
                         specialize (Horigin (conf) g (r,t,b) Hchange).
                         rewrite Hconf in *.
                         simpl (fst _) .
                         unfold frame_choice_bijection, Frame in Horigin.
                         rewrite <- Horigin.
                         rewrite retraction_section.
                         now cbn.
                       }
                       destruct Hmove_None as (other,(Hother_spect, Hmove_other)).
                       -- destruct Hpred as (Horigin,_).
                          revert Horigin; intro Horigin.
                          specialize (Horigin (conf) g (r,t,b) Hchange).
                          rewrite Hconf in Horigin.
                          cbn in Hsame_pos.
                          unfold Datatypes.id in *.
                          rewrite Hsame_pos.
                          unfold frame_choice_bijection, Frame in Horigin.
                          rewrite <- Horigin.
                          rewrite Hconf.
                          unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location.
                          unfold Datatypes.id.
                          destruct b; rewrite dist_same; generalize D_0; lra.
                       -- unfold obs_from_config, Spect_ILA in Hother_spect.
                          rewrite make_set_spec, filter_InA, config_list_InA in Hother_spect.
                          rewrite 3 andb_true_iff, Rle_bool_true_iff in Hother_spect.
                          destruct Hother_spect as (([g_other|b_other],Hother_spec),
                                                    (((Hother_Dmax, Hother_alive), Hother_alive_g), Hother_ident)).
                          destruct (get_alive (round rbg_ila da conf (Good g_other)))
                                   eqn : Halive_other_round.
                          ++ exists g_other.
                             repeat split; try auto.
                             rewrite Hother_spec in Hother_ident.
                             rewrite <- 2 ident_preserved; try auto.
                             unfold get_ident in *; simpl in Hother_ident.
                             rewrite Nat.leb_le in Hother_ident.
                             destruct Hmove_other as (Hmove_other, Hdist_other_round_2D).
                             destruct Hmove_other as (other1, (Hother_in,(Hother_pos, Hother_ident'))). 
                             revert Hcoll; intro Hcoll.
                             unfold no_collision_conf in Hcoll.
                             unfold obs_from_config, Spect_ILA, map_config in Hother_in.
                             rewrite make_set_spec, filter_InA, config_list_InA in Hother_in.
                             rewrite 3 andb_true_iff in Hother_in.
                             destruct Hother_in as (([g_other'|byz], Hother1_spec), (((Hother1_dist,Hother1_alive),Hother1_aliveg), Hother1_ident));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in *).                              
                             assert (Hident_g : g_other' = g).
                             {
                               destruct (Geq_dec g g_other'); try auto.
                               specialize (Hcoll _ _ n0).
                               destruct Hcoll.
                               rewrite Hconf in *; simpl in *; auto.
                               rewrite Hother1_spec in Hother1_alive; unfold get_alive in *;
                                 simpl in *;
                                 auto. 
                               rewrite Hother1_spec in Hother_pos.
                               assert (fst (round rbg_ila da conf (Good g)) = fst (conf (Good g))).
                               {
                                 unfold get_location, State_ILA, OnlyLocation, AddInfo in *;
                                   unfold get_location, Datatypes.id in *. 
                                 auto.
                               }
                               rewrite H in Hother_pos.

                               rewrite (frame_dist _ _ (r,t,b)).
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                               rewrite Hother_pos. 
                               destruct b; apply dist_same.
                             }
                             assert (get_ident (other) < get_ident (other1)).
                             unfold get_ident in *; auto.
                             rewrite Hother_spec, Hother1_spec in H.
                             unfold get_ident in H; simpl in H.
                             now rewrite <- Hident_g.
                             intros x y Hxy.
                             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                             rewrite (get_alive_compat Hxy).
                             rewrite (get_ident_compat Hxy).
                             reflexivity.
                             rewrite (fst_compat Hother_spec) in Hother_Dmax.
                             destruct Hmove_other.
                             rewrite Hother_spec in H0.
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                             assert (dist (fst (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))) <= 3 * D)%R.
                             unfold map_config in *.
                             assert (Htri_new_pos := RealMetricSpace.triang_ineq (fst (conf (Good g_other))) (retraction (frame_choice_bijection (r,t,b)) new_pos) (fst (round rbg_ila da conf (Good g)))).
                             assert (Hnew_correct := choose_new_pos_correct (reflexivity new_pos)).
                             destruct Hnew_correct as (_,Hdist_new_D).
                             destruct Hpred as (Horigin,_).
                             revert Horigin; intro Horigin.
                             specialize (Horigin (conf) g (r,t,b) Hchange).
                             rewrite Hconf in Horigin.
                             rewrite <- Horigin in Hdist_new_D.
                             assert (Hdist_new_D_aux : (dist (retraction (frame_choice_bijection (r, t, b)) new_pos)
                                                             (fst (round rbg_ila da conf (Good g))) <= D)%R).
                             { unfold ILA in *.
                               unfold State_ILA in *.
                               rewrite <- Hdist_same.
                               rewrite Hconf.
                               rewrite (frame_dist _ _ (r,t,b)).
                               rewrite section_retraction.
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in Hdist_new_D.
                               generalize D_0; simpl in *; lra. 
                             }
                             assert (Hdist_other_new : (dist (fst (conf (Good g_other)))
                    (retraction (frame_choice_bijection (r, t, b)) new_pos) <= 2*D)%R).
                             {
                               rewrite (frame_dist _ _ (r,t,b)), section_retraction.
                               unfold frame_choice_bijection, Frame;
                                 destruct b; simpl in *; lra.
                             }
                             generalize D_0; simpl in *; lra.
                             assert (Dp > 4*D)%R.
                             {
                               generalize Dmax_6D, D_0. unfold Dp. lra.
                             }
                             assert (Htri := RealMetricSpace.triang_ineq (fst (round rbg_ila da conf (Good g_other))) (fst (conf (Good g_other)))  (fst (round rbg_ila da conf (Good g)))). 
                             transitivity (dist (fst (round rbg_ila da conf (Good g_other))) (fst (conf (Good g_other))) +
          dist (fst (conf (Good g_other)))  (fst (round rbg_ila da conf (Good g))))%R.
                             auto.
                             rewrite dist_sym at 1; apply Htri.
                             assert (Hdist_round := dist_round_max_d g_other Hpred Hpath).
                             unfold equiv, bool_Setoid, eq_setoid in *;
                               rewrite Rle_bool_true_iff in *.
                             rewrite Hother_spec in Hother_alive; unfold get_alive in *; simpl in Hother_alive.
                             specialize (Hdist_round Hother_alive).
                             rewrite dist_sym in Hdist_round.
                             transitivity (D +    dist (fst (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))))%R.
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
                             apply Rplus_le_compat_r.
                             apply Hdist_round.
                             transitivity (D + 3*D)%R.
                             apply Rplus_le_compat_l.
                             apply H1.
                             generalize Dmax_6D, D_0.
                             lra.
                          ++ assert (Halive_near := @executed_means_alive_near conf g_other da Hpred).
                             assert (Hother_alive_aux : get_alive (conf (Good g_other)) = true).
                             {
                               rewrite <- Hother_alive.
                               rewrite Hother_spec;
                               unfold get_alive; simpl; auto.
                             }                               
                             revert Hpath; intro Hpath_backup.
                             destruct (nat_eq_eqdec (get_ident (conf (Good g_other))) 0).
                             rewrite (ident_preserved conf g_other Hpred) in e.
                             assert (Hfalse := ident_0_alive (round rbg_ila da conf) g_other e).
                             rewrite Hfalse in *; discriminate.
                             rename c into Hother_else.
                             specialize (Halive_near Hother_alive_aux Hother_else Halive_other_round Hpath_backup).
                             destruct (Hpath_backup g_other Hother_alive_aux).
                             destruct Hother_else.
                             now rewrite H.
                             destruct Halive_near as (g_near, (Hnear_ident, (Hnear_dist, Hnear_alive))).
                             destruct H as (g_0, (Halive_0, (Hdist_0, Hident_0))).
                             exists g_0; repeat split; auto.
                             now rewrite dist_sym.
                             rename H into Hother_path.
                             (*si near marche aps, le bourreau de near marche, mais aussi near ne devrait aps mourrir: il est bourreau donc il bouge   *)



(* je voudrais un axiom qui dit que pour chaque configuration, soit c'est la première, où tout est bon, soit il existe une DA qui permet d'y acceder par un round. Si j'ai ça, alors je peux avoir light_off_means_alive_next car en vrai, la prop d'avant marche sur 3 round: si on est light_off, c'est qu'au round -1, on n'avait personne trop pret ni trop loins, et donc personne ne peut faire en sorte que l'on meurt au round . à tout round, sans avoir à m'inquiéter d'avoir 3 round dans mes lemmes de continuités.

                              *)



                             assert (get_alive (round rbg_ila da conf (Good g_near)) = true).
                             {
                               rewrite round_good_g; try auto.
                               simpl.
                               unfold upt_aux, map_config.
                               destruct (upt_robot_dies_b _ g_near) eqn : Hbool_near.
                               - assert (Hfalse : get_alive (round rbg_ila da conf (Good g_near)) = false).
                                 rewrite round_good_g; try auto.
                                 simpl.
                                 unfold upt_aux, map_config.
                                 rewrite Hbool_near.
                                 unfold get_alive ; simpl.
                                 now destruct (conf (Good g_near)) as (?, ((?,?),?)); simpl.
                                 assert (Hlight_false : get_light (conf (Good g_near)) = true).
                                 apply (Hexecuted_on g_near da Hpred Hnear_alive Hfalse).
                                 assert (Hlight_true : get_light (conf (Good g_near)) = false).
                                 apply (Hexecutioner_off g_near da Hpred Hnear_alive).
                                 exists g_other.
                                 repeat split; try auto.
                                 rewrite dist_sym. auto.
                                 rewrite Hlight_true in *.
                                 discriminate.
                               - unfold get_alive in *; 
                                   destruct (conf (Good g_near)) as (?, ((?,?),?)) eqn : Hconf_near;
                                   simpl; auto.
                             }
                             exists g_near.
                             repeat split; auto.
                             rewrite <- ident_preserved; auto.
                             transitivity (get_ident (conf (Good g_other))); auto.
                             destruct Hmove_other as ((copy, (Hcopy_spec, (Hcopy_pos, Hcopy_ident))), _).
                             unfold obs_from_config, Spect_ILA in Hcopy_spec.
                             rewrite make_set_spec, filter_InA, config_list_InA in Hcopy_spec.
                             rewrite 3 andb_true_iff, Rle_bool_true_iff in Hcopy_spec.
                             destruct Hcopy_spec as (([g_inf|byz],Hinf_spec), ((Hinf_dist, Hinf_alive), Hinf));
                               try (assert (Hfalse := In_Bnames byz);
                                    now simpl in *).                              
                             rewrite Nat.leb_le in Hinf.
                             rewrite <- ident_preserved; try auto.
                             apply (Nat.lt_le_trans _ (get_ident copy) _).
                             rewrite Hother_spec in Hcopy_ident.
                             unfold get_ident in *; now simpl in *.
                             rewrite Hconf in *.
                             unfold get_ident in *; now simpl in *.
                             intros x y Hxy.
                             rewrite (RelationPairs.fst_compat _ _ _ _ Hxy).
                             rewrite (get_alive_compat Hxy).
                             rewrite (get_ident_compat Hxy).
                             reflexivity.
                             assert (Hdist_round_g_near := @dist_round_max_d g_near conf da Hpred Hpath_backup Hnear_alive).
                             unfold equiv, bool_Setoid, eq_setoid in Hdist_round_g_near;
                             rewrite Rle_bool_true_iff in Hdist_round_g_near.
                             destruct Hmove_other as (?,Hdist_other).
                             rewrite Hother_spec, dist_sym in Hdist_other.
                             revert Hdist_other; intro Hdist_other.
                                                          assert (dist (fst (conf (Good g_other))) (fst (round rbg_ila da conf (Good g))) <= 3 * D)%R.
                             unfold map_config in *.
                             assert (Htri_new_pos := RealMetricSpace.triang_ineq (fst (conf (Good g_other))) (retraction (frame_choice_bijection (r,t,b)) new_pos) (fst (round rbg_ila da conf (Good g)))).
                             assert (Hnew_correct := choose_new_pos_correct (reflexivity new_pos)).
                             destruct Hnew_correct as (_,Hdist_new_D).
                             destruct Hpred as (Horigin,_).
                             revert Horigin; intro Horigin.
                             specialize (Horigin (conf) g (r,t,b) Hchange).
                             rewrite Hconf in Horigin.
                             rewrite <- Horigin in Hdist_new_D.
                             assert (Hdist_new_D_aux : (dist (retraction (frame_choice_bijection (r, t, b)) new_pos)
                                                             (fst (round rbg_ila da conf (Good g))) <= D)%R).
                             { unfold ILA in *.
                               unfold State_ILA in *.
                               rewrite <- Hdist_same.
                               rewrite Hconf.
                               rewrite (frame_dist _ _ (r,t,b)).
                               rewrite section_retraction.
                               unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in Hdist_new_D.
                               left. apply Hdist_new_D. 
                             }
                             assert (Hdist_other_new : (dist (fst (conf (Good g_other)))
                    (retraction (frame_choice_bijection (r, t, b)) new_pos) <= 2*D)%R).
                             {
                               rewrite (frame_dist _ _ (r,t,b)), section_retraction.
                               rewrite dist_sym.
                               unfold frame_choice_bijection, Frame;
                                 destruct b; simpl in *; lra.
                             }
                             generalize D_0; simpl in *; lra.
                             assert (Dp > 4*D)%R.
                             {
                               generalize Dmax_6D, D_0. unfold Dp. lra.
                             }
                             unfold Dp in *. 
                             assert (Htri1 := RealMetricSpace.triang_ineq (get_location (round rbg_ila da conf (Good g))) (get_location (conf (Good g_other))) (get_location (conf (Good g_near)))).
                             clear Hdist_other. 
                             assert (Htri': (dist (get_location (round rbg_ila da conf (Good g)))
             (get_location (conf (Good g_near))) <= 4*D)%R).
                             unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id in *.
                             replace (4*D)%R with (3*D + D)%R by lra.
                             transitivity ((dist (fst (round rbg_ila da conf (Good g))) (fst (conf (Good g_other))) + D)%R); try (now generalize D_0; lra).
                             transitivity (
           dist (fst (round rbg_ila da conf (Good g))) (fst (conf (Good g_other))) +
           dist (fst (conf (Good g_other))) (fst (conf (Good g_near))))%R ;
                             try auto.
                             apply Rplus_le_compat_l.
                             apply Hnear_dist.
                             apply Rplus_le_compat_r.
                             rewrite dist_sym.
                             apply H1.
                             assert (Htri2 := RealMetricSpace.triang_ineq (get_location (round rbg_ila da conf (Good g))) (get_location (conf (Good g_near)))
     (get_location (round rbg_ila da conf (Good g_near)))).
                             unfold Dp.
                             transitivity (4*D + D)%R.
                             transitivity  (dist (get_location (round rbg_ila da conf (Good g)))
             (get_location (conf (Good g_near))) +
           dist (get_location (conf (Good g_near)))
                (get_location (round rbg_ila da conf (Good g_near))))%R.
                             apply Htri2.
                             transitivity ((dist (get_location (round rbg_ila da conf (Good g)))
             (get_location (conf (Good g_near))) + D))%R.
                             apply Rplus_le_compat_l.
                             apply Hdist_round_g_near.
                             apply Rplus_le_compat_r.
                             apply Htri'.
                             generalize Dmax_6D, D_0; lra.
                          ++
                            try (assert (Hfalse := In_Bnames b_other);
                                 now simpl in *). 
                          ++ intros x y Hxy.
                             rewrite (fst_compat Hxy).
                             rewrite (get_alive_compat Hxy), (get_ident_compat Hxy).
                             reflexivity.
Qed.



Lemma path_round :
  forall conf da,
    da_predicat da ->
    path_conf conf ->
    no_collision_conf conf ->
    executioner_means_light_off conf ->
    executed_means_light_on conf ->
    exists_at_less_that_Dp conf ->
    path_conf (round rbg_ila da conf).
Proof.
  intros conf da Hpred Hpath Hcoll Hexecutioner_off Hexecuted_on Hexists_at.
  unfold path_conf in *.
  assert (target_alive conf).
  { unfold target_alive.
    intros g0 Hn0 Halive0.
    specialize (Hpath g0 Halive0).
    destruct Hpath.
    intuition.
    destruct H as (g', (Hpath_alive,( Hpath_Dmax, Hpath_ident))).
    exists g'.
    repeat split; simpl in *; auto;try lra.  
  }
  assert (Ht_alive := round_target_alive Hpred Hpath Hcoll Hexecutioner_off Hexecuted_on Hexists_at H).
  unfold target_alive in Ht_alive.
  intros g' Halive_r'.
  specialize (Ht_alive g').
  destruct (nat_eq_eqdec ( get_ident (round rbg_ila da conf (Good g'))) 0).
  left; now simpl in *.
  specialize (Ht_alive c Halive_r').
  right.
  destruct (Ht_alive) as (?,(?,(?,?))).
  exists x; repeat split; simpl in *; auto.  
Qed.




Lemma executioner_means_light_off_init : forall conf,
    config_init_pred conf ->
    executioner_means_light_off conf.
Proof.
  intros conf Hconf_pred.
  intros g da Hpred Halive Hexecutioner.
  destruct Hconf_pred as (?,(?,?)).
  destruct (conf (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  specialize (H0 (Good g)).
  rewrite Hconf in H0.
  now simpl.
Qed.

Lemma executed_means_light_on_init : forall conf,
    config_init_pred conf ->
    executed_means_light_on conf.
Proof.
  intros conf Hconf_pred.
  intros g da Hpred Halive Halive_round.
  assert (Halive_round' := Halive_round).
  rewrite round_good_g in Halive_round; try auto.
  simpl in *.
  destruct (conf (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  unfold upt_aux, map_config in *.
  unfold get_alive in *.
  rewrite Hconf in *.
  destruct (upt_robot_dies_b _) eqn : Hbool;
    try (simpl in *; rewrite Halive in *; discriminate).
  simpl in *.
  unfold upt_robot_dies_b in *.
  destruct Hconf_pred as (?,(?,?)).
  unfold config_init_lower, config_init_not_close in *.
  specialize (H (Good g)); specialize (H1(Good g)).
  rewrite Hconf in *.
  rewrite orb_true_iff in Hbool; destruct Hbool as [Hex|Hneg].
  + rewrite existsb_exists in Hex.
    destruct Hex as (rila, (Hin,Hex)).
    rewrite filter_In in Hin.
    rewrite config_list_spec in Hin.
    destruct Hin as (Hin, Hident').
    rewrite in_map_iff in Hin.
    destruct Hin as ([g_other|byz], (Hother_spec, Hin));
      try (assert (Hfalse := In_Bnames byz);
           now simpl in *).                              
    specialize (H1 (Good g_other)).
    rewrite <- Hother_spec in Hex.
    destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
    rewrite Rle_bool_true_iff in Hex.
    destruct (conf (Good g_other)) as (p_other,((i_other, l_other), a_other)) eqn : Hconf_other.
    simpl (fst _) in Hex.
    rewrite (frame_dist _ _ (r,t,b)) in H1. 
    unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
    rewrite dist_sym in H1.
    destruct b; simpl in *; lra.
  + destruct H as [H_0| Hnot_far].     
    auto.
    assert (get_alive (round rbg_ila da conf (Good g)) = true).
    apply ident_0_alive.
    rewrite <- ident_preserved; auto.
    rewrite Hconf; unfold get_ident; now simpl.
    unfold get_alive in *; rewrite H in *; discriminate.
    rewrite forallb_existsb, forallb_forall in Hneg.
    destruct Hnot_far as ([g_other|byz], Hnot_far);
      try (assert (Hfalse := In_Bnames byz);
           now simpl in *).
    destruct (conf (Good g_other)) as (p_other,((i_other, l_other), a_other)) eqn : Hconf_other.
    destruct (change_frame da conf g) as ((r,t),b) eqn : Hchange.
    specialize (Hneg ((comp (bij_rotation r)
                      (comp (bij_translation t) (if b then reflexion else Similarity.id)))
                     (fst (conf (Good g_other))), snd (conf (Good g_other)))).
    rewrite negb_true_iff, Rle_bool_false_iff in Hneg.
    destruct Hneg.
    rewrite filter_In, config_list_spec, in_map_iff, andb_true_iff.
    repeat split.
    exists (Good g_other); try auto.
    split; try auto.
    destruct b; rewrite Hconf_other; now simpl.
    apply In_names.
    unfold get_ident in *; simpl in *.
    now rewrite Hconf_other, Nat.ltb_lt. 
    now rewrite Hconf_other; unfold get_alive; simpl in *; auto.
    rewrite Hconf_other.
    simpl (fst _).
    destruct Hnot_far as (?,(?,Hpos)).
    rewrite (frame_dist _ _ (r,t,b)) in Hpos.
    unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, frame_choice_bijection, Frame, Datatypes.id in *.
    rewrite dist_sym.
    destruct b; simpl in *; lra.
Qed.

Lemma exists_at_less_that_Dp_init : forall conf,
    config_init_pred conf ->
    exists_at_less_that_Dp conf.
Proof.
  intros conf (Hlower, (Hoff, Hnot_close)) g Halive Hall_lighted Hall.
  destruct (conf (Good g)) as (pos, ((ident, light), alive)) eqn : Hconf.
  specialize (Hlower (Good g)).
  rewrite Hconf in Hlower.
  destruct Hlower as [Hfalse|([g_other|byz],Hlower)];
    try (unfold get_alive in *; now simpl in *);
    try (assert (Hfalse := In_Bnames byz);
         now simpl in *).
  unfold get_ident in *; simpl in *; omega.                                           
  destruct (conf (Good g_other)) as (p_other, ((i_other, l_other), a_other)) eqn : Hconf_other.
  specialize (Hall g_other).
  assert (Hfalse : get_light (conf (Good g_other)) = true).
  {
    apply Hall; rewrite Hconf_other; unfold get_alive, get_ident; try now simpl.
    unfold get_location, State_ILA, OnlyLocation, AddInfo, get_location, Datatypes.id.
    rewrite dist_sym; simpl in *; lra.
  }
  specialize (Hoff (Good g_other)).
  rewrite Hconf_other in *.
  unfold get_light in *; simpl in *; rewrite Hoff in *; discriminate.
Qed.

Definition NoCollAndPath e := 
    Stream.forever (Stream.instant (fun conf => no_collision_conf conf /\ path_conf conf )) e.

Instance no_collision_conf_compat : Proper (equiv ==> equiv) no_collision_conf.
Proof.
  intros x y Hxy.
  unfold no_collision_conf.
  split; intros.
  rewrite <- (get_alive_compat (Hxy (Good g))) in *.
  rewrite <- (get_alive_compat (Hxy (Good g'))) in *.
  specialize (H g g' H0 H1 H2).
  rewrite <- (get_location_compat _ _ (Hxy (Good g))). 
  rewrite <- (get_location_compat _ _ (Hxy (Good g'))). 
  apply H.
  rewrite (get_alive_compat (Hxy (Good g))) in *.
  rewrite (get_alive_compat (Hxy (Good g'))) in *.
  specialize (H g g' H0 H1 H2).
  rewrite (get_location_compat _ _ (Hxy (Good g))). 
  rewrite (get_location_compat _ _ (Hxy (Good g'))). 
  apply H.
Qed.

Instance path_conf_compat : Proper (equiv ==> equiv) path_conf.
Proof.
  intros x y Hxy.
  unfold path_conf.
  split; intros.
  rewrite <- (get_alive_compat (Hxy (Good g))) in *.
  specialize (H g H0).
  destruct H as [H|(g',(Halive,(Hdist,Hident)))].
  now left; rewrite (get_ident_compat (Hxy (Good g))) in *.
  right.
  exists g'.
  rewrite (Hxy (Good g)) in *.
  rewrite (Hxy (Good g')) in *.
  auto.
  rewrite (get_alive_compat (Hxy (Good g))) in *.
  specialize (H g H0).
  destruct H as [H|(g',(Halive,(Hdist,Hident)))].
  now left; rewrite (get_ident_compat (Hxy (Good g))) in *.
  right.
  exists g'.
  rewrite (Hxy (Good g)) in *.
  rewrite (Hxy (Good g')) in *.
  auto.
Qed.

Definition conf_pred conf :=
  no_collision_conf conf /\ path_conf conf /\
  executed_means_light_on conf /\ executioner_means_light_off conf /\
  exists_at_less_that_Dp conf.
                    

Parameter config_init : config.
Axiom config_init_pred_true : config_init_pred config_init.

Lemma validity:
  forall(demon : demon_ila_type) conf,
    conf_pred conf ->
    demon_ILA demon ->
  NoCollAndPath (execute rbg_ila demon conf).
Proof.
  cofix Hcoind. constructor.
  simpl.
  split.
  now destruct H.
  now destruct H.
  assert (Hexec_tail := @execute_tail (R2*ILA)%type Loc State_ILA _ Spect_ILA).
  rewrite Hexec_tail.
  apply (Hcoind (Stream.tl demon)).
  unfold conf_pred in *; repeat split; 
  destruct H as (?,(?,(?,(?,?)))); destruct H0.
  apply no_collision_cont; try auto.
  apply path_round; try auto.
  apply executed_means_light_on_round; try auto.
  apply executioner_means_light_off_round; try auto.
  apply exists_at_less_round; try auto.
  destruct H0. 
  apply H1.
Qed.

Lemma validity_conf_init:
  forall demon, demon_ILA demon ->
                NoCollAndPath (execute rbg_ila demon config_init).
Proof.
  intros.
  apply validity.
  repeat split; generalize config_init_pred_true; intros.
  now apply no_collision_init.
  now apply paht_conf_init.
  now apply executed_means_light_on_init.
  now apply executioner_means_light_off_init.
  now apply exists_at_less_that_Dp_init.
  auto.
Qed.

(* on  a une base, qui envoie des robots : exists g, get_location (conf (Good g)) = (0,0)%R /\ get_alive (conf (Good g)) = true /\ (forall g', get_alive (conf (Good g')) -> get_ident (conf (Good g)) >= get_ident (conf (Good g'))).

ceci ne marche pas comme ça, car il reste le problème de l'élimination sur la base, et le fait que la base en elle même ne puisse pas bouger.

a voir une autre fois

 on veut prouver qu'il existe toujours un robot à moins de Dp de (0,0). donc il faut en faire sortir de la base.
  *)
