Require Import moremaps.
Require Import FSets.
Require Import FMaps.
Require Import moreZ.

Require Import FSetFacts.
Require Import FMapFacts.



(** Model : 
 * ATOM
 * Strong global multiplicity
 *)


(** * Types and basic modules for state modelling *)

Definition robot:=nat.
Definition tick:=nat.

(** Positions are unlimited going left or right. *)
Definition position := Z.

(** Mapping from robots to 'alpha. *)
Module MapRobots := FMapList.Make(Nat_as_OT).
Module MapRobotsFacts := Facts(MapRobots).
Module MapRobotsProps := Properties(MapRobots).

(** Mapping from positions to 'alpha. *)
Module MapPos := FMapList.Make(Z_as_OT).
Module Import PosFacts := Facts(MapPos).
Module Import PosProps := Properties(MapPos).
(* Module Import RobFacts := Facts(MapRobots). *)
(* Module Import RobProps := Properties(MapRobots). *)
Module Import moremaps := MapMorphisms(Nat_as_OT)(MapRobots).
Module Import moremappred := MorePredicate(MapRobots).

(** Sets of robots. *)
Module Robotset := FSetList.Make(Nat_as_OT).


(* ** States and configurations  *)

(** A configuration is what good robots can see: a number of robots on
    each position (mapping from positions to a number of robots), but robots are
    indistinguishable. Each robot having its own referential, each robot sees a
    different configuration. *)
Definition configuration : Type := MapPos.t nat.


(** A state is the actual state of the network. It is the mapping from
    positions to robots together with the set of baaaad robots (tm) among
    them. *)
Record state : Type := { robots: MapRobots.t position;
                         bad:  Robotset.t }.

Definition empty_configuration:configuration := MapPos.empty _ .
Definition empty_state:state := {| robots := @MapRobots.empty position ; 
                                   bad := Robotset.empty
                                |} .

(** Going from state to configuration by losing all information about robots
    (robots numbers and badness information). *)

Definition accumulate_robot_at_pos (r:robot) (p:position) (acc:configuration) :=
  let oldnum := MapPos.find p acc in
    match oldnum with
      | None => MapPos.add p 1 acc
      | Some n => MapPos.add p (n + 1) acc
    end.


Definition state_to_config (s:state) :=   (* fold = fold_right *)
  (MapRobots.fold accumulate_robot_at_pos s.(robots) empty_configuration).

Definition is_bad (s:state) r:Prop := (Robotset.In r (s.(bad))).
Definition is_good (s:state) r:Prop := ~ is_bad s r.
Definition dec_is_bad (s:state) r:bool := (Robotset.mem r (s.(bad))).
Definition dec_is_good (s:state) r:bool := negb (dec_is_bad s r).

(* [ ~ is_bad s r <-> is_good s r ] is trivial by definition but this one comes
   from decidability of In: ~ is_good is actually ~~ is_false). *)
Lemma bad_is_not_good: forall r s, ~ is_good s r <-> is_bad s r.
Proof.
  intros r s.
  unfold is_good.
  split.
  - intros H.
    apply Decidable.not_not in H.
    + assumption.
    + red.
      unfold is_bad.
      unfold Robotset.In, Robotset.MSet.In, Robotset.MSet.Raw.In.
      generalize (@InA_dec nat (@eq nat) eq_nat_dec r (Robotset.MSet.this (bad s))).
      intros H0.
      destruct H0;auto.
  - tauto.
Qed.

Lemma dec_is_bad_ok : forall r s, is_bad s r <-> dec_is_bad s r = true.
Proof.
  intros r s.
  split;intro h.
  - apply Robotset.mem_1.
    assumption.
  - apply Robotset.mem_2.
    assumption.
Qed.

Lemma dec_is_good_ok : forall r s, is_good s r <-> dec_is_good s r = true.
Proof.
  intros r s.
  split;intro h.
  - unfold dec_is_good.
    apply Is_true_eq_true.
    apply negb_prop_intro.
    intro.
    apply Is_true_eq_true in H.
    rewrite <- dec_is_bad_ok in H.
    contradiction.
  - intro abs.
    rewrite -> dec_is_bad_ok in abs.
    unfold dec_is_good in h.
    apply (no_fixpoint_negb (dec_is_bad s r)).
    transitivity true;auto.
Qed.


Lemma not_in_bad_is_good s r : ~ (Robotset.In r (bad s)) -> is_good s r.
Proof.
  intros H.
  assumption.
Qed.

Lemma not_in_bad_is_good_2 s r : is_good s r -> ~ (Robotset.In r (bad s)).
Proof.
  intros H.
  assumption.
Qed.


(** * Building the set of good robots. This is basically a diff between a map and
    a set. *)
Definition good_robots (s:state): MapRobots.t position :=
  (MapRobotsProps.filter (fun rbt _ => dec_is_good s rbt) s.(robots)).

(* À savoir: In x y = (exists e , MapsTo x e y.
  (bon strictement parlant c'est un "Raw.MapsTo" très moche mais c'est
  convertible). *)

(** ** Main property of [good_robots]. *)
Lemma is_good_mapsto : forall s r p,
                         MapRobots.MapsTo r p (robots s) /\ is_good s r
                         <-> MapRobots.MapsTo r p (good_robots s).
Proof.
  intros s r p.
  generalize (@MapRobotsProps.filter_iff position (fun rbt _ => dec_is_good s rbt) _ (robots s) r p).
  intros h.
  setoid_rewrite <- dec_is_good_ok in h.
  destruct h.
  split.
  - intros (h, h').
    apply H0.
    auto.
  - intros H1.
    apply H.
    auto.
Qed.

(** ** Derived properties of [good_robots]. *)

Lemma MapsTo_In: forall s r p, (MapRobots.MapsTo r p (robots s))
                               -> (MapRobots.In r (robots s)).
Proof.
  intros s r p H.
  exists p;auto.
Qed.

Print Scope type_scope.

Lemma is_good_in_good s r :
  MapRobots.In r (robots s) /\ is_good s r <->
  (MapRobots.In r (good_robots s)).
Proof.
  split.
  - intros (h,h').
    destruct h.
    exists x.
    apply is_good_mapsto;auto.

  - intros h.
    assert (exists p, MapRobots.MapsTo r p (good_robots s)).
    + destruct h.
      exists x.
      auto.
    + destruct H.
      apply is_good_mapsto in H.
      destruct H.
      split; auto.
      apply MapsTo_In with x;auto.
Qed.



Definition all_robotsset (s:state): Robotset.t :=
  (MapRobots.fold
     (fun rbt _ acc => (Robotset.add rbt acc))
     s.(robots) Robotset.empty).


(** Global (timed) state *)

(** The scheduler may return a different result at different time, We thus
    need a notion of timed state as an input to the scheduler. *)
Record timed_state:Type := { thestate: state ;  thetick: tick }.

(** [scheduler tck s] returns the set of robots that should move at tick [tck]
    in state [s]. *)
Definition scheduler:Type := timed_state -> Robotset.t.

(** A transition "function". TODO XU. *)

Definition transition:Type := configuration -> position -> position -> Prop.

(** A bad transition function [f] is such that [f r s n] returns the new asolute
    position of a (bad) robot [r] from position [n] in _state_ [s]. *)
Definition bad_transition:Type := robot -> timed_state -> position -> position -> Prop.

(** The global transition function describes the way the whole system evolves,
    given a a transition function, a bad transition function, a timed state and
    an scheduler. *)

(* in transition ts -> ts_res, robot r should go from p to np when following transition given by sch, t, tb. *)
Inductive trans (sch:scheduler) (t:transition) (ts:timed_state)
                (r:robot) (p:position) (h:MapRobots.MapsTo r p (ts.(thestate).(robots))): position -> Prop  :=
| bad_moving : Robotset.In r (sch ts)
               -> is_bad (ts.(thestate)) r
               -> forall np, trans sch t ts r p h np
| good_moving: Robotset.In r (sch ts)
               -> is_good (ts.(thestate)) r
               -> forall np, t (state_to_config (ts.(thestate))) p np -> trans sch t ts r p h np
| not_moving: ~ Robotset.In r (sch ts) ->  trans sch t ts r p h p.

(* J'ajoute la relation entre les ticks, brutalement *)

Definition global_transition (sch:scheduler) (t:transition) (ts:timed_state)(nts:timed_state) : Prop :=
(ts.(thetick) = nts.(thetick) + 1) /\ 
  moremappred.For_all
    (fun r p =>
       forall h : MapRobots.MapsTo r p (ts.(thestate).(robots)),
       forall np, (MapRobots.MapsTo r np (nts.(thestate).(robots))) -> trans sch t ts r p h np )
    (ts.(thestate).(robots)).
           

(** * Results on the distinction between bad/good robots. *)
(** USEFUL ? *)

(** Equivalence relation defined by forgetting badness information. *)
Definition badness_equiv (c c':state) : Prop :=  MapRobots.Equal c.(robots) c'.(robots).

Add Morphism accumulate_robot_at_pos
             with signature eq ==> eq ==> eq ==> eq
  as accumulate_robot_morphism.
Proof.
  intros y y0 y1.
  reflexivity.
Qed.


Add Morphism accumulate_robot_at_pos
             with signature eq ==> eq ==> MapPos.Equal ==> MapPos.Equal
  as accumulate_robot_morphism2.
Proof.
  intros y y0 x y1 H.
  unfold accumulate_robot_at_pos.
  setoid_rewrite H.
  destruct (MapPos.find (elt:=nat) y0 y1).
  - rewrite H.
    reflexivity.
  - rewrite H.
    reflexivity.
Qed.



(** We can rewrite two [badness_equiv]alent maps inside [state_to_config]
    and obtain an equivalent mapping. *)
Add Morphism state_to_config
             with signature badness_equiv ==> MapPos.Equal
  as state_to_config_morphism.
Proof.
  intros x y H.
  unfold badness_equiv, state_to_config, MapPos.Equal in *.
  intros y0.
  apply PosFacts.find_m_Proper.
  - reflexivity.
  - eapply moremaps.MP.fold_Equal;auto.
    repeat progress red.
    intros x0 y1 H0 x1 y2 H1 x2 y3 H2 y4.
    subst.
    rewrite H2.
    reflexivity.
Qed.


(** Stronger result: We actually obtain exactly the same mapping. *)
Add Morphism state_to_config
             with signature badness_equiv ==> eq
  as state_to_config_morphism2.
Proof.
  intros x y H.
  unfold badness_equiv, state_to_config, MapPos.Equal in *.
  apply moremaps.MP.fold_Equal;auto.
  repeat progress red.
  intros x0 y0 H0 x1 y1 H1 x2 y2 H2.
  subst.
  apply accumulate_robot_morphism;auto.
Qed.



(** Indistinguishability of badness_equivalent states from the (good) transition
    point of view. This is also an example of use of previous mapping (see
    [rewrite] below.) *)
Lemma badness_irrelevance:
  forall (sch:scheduler) (t:transition) (s s':state),
    Proper (MapPos.Equal ==> eq ==> eq) t -> 
    badness_equiv s s' ->
    badness_equiv s' s ->
    forall p:position,
      (t (state_to_config s) p) = (t (state_to_config s') p).
Proof.
  intros sch t s s' H H0 H1 p.
  rewrite H0.
  reflexivity.
Qed.


(** * Fairness of the scheduler *)

(** Scheduler [sch] is fair for a good and a bad transition function [t] and
    [tb], a timed state [s,tck] and a robot [r] iff iterating [global_transition
    sch t tb s tck r] eventually reaches a state where [sch] choses [r] to move. *)
Inductive fair_for (sch:scheduler) (t:transition)
                   (ts:timed_state) r :=
(** [r] moves at first step *)
| fair1 : Robotset.In r (sch ts) -> fair_for sch t ts r 
(** recursive case: we reach (s',tck') in one step, and [sch] is fair from there. *)
| fair2 : forall ts', global_transition sch t ts ts' -> 
                      fair_for sch t ts' r -> fair_for sch t ts r.

(** [sch,t,tb] is fair if it is fair on every state, every tick and every
    robot. *)
Definition fairness (sch:scheduler) (t:transition) :=
  forall ts r, MapRobots.In r ts.(thestate).(robots) ->  fair_for sch t ts r.

Require Import Wellfounded.

Lemma refl_no_acc : forall A (R:A -> A -> Prop) x, R x x -> ~ Acc R x.
Proof.
  intros A R x H.  
  intro abs.
  induction abs.
  apply (H1 x);auto.
Qed.

Definition good_stacked (s:state) (p:position) :=
  moremappred.For_all (fun rbt i => i = p) (good_robots s).

(* Without loss of generality we could have fixed sch to the "always everyone"
   scheduler. *)

Definition get_all_robots s :=
  MapRobots.fold (fun r p acc => Robotset.add r acc) 
                 (s.(thestate).(robots)) 
                 (Robotset.empty).

(* The scheduler that choses everyone everytime. *)
Definition sch_always:scheduler := fun s => get_all_robots s. 


(* FIXME: il faut simplement dire que si on les goods sont empilés alors la
   transition ne les déplace plus (indépendemment des bads, du tick et du
   scheduler). *)
XXXX
(* Chelou car le scheduler peut ne choisir que certains robots, donc les autres
   sont forcés de ne pas bouger? Par ailleurs est-ce-que le tick doit vraiment
   être quantifié ou bien seulement les tick après une certaine date?
 *)
Definition stable_stacked t (mr:MapRobots.t position) p :=
  forall tck (b:Robotset.t) ts' sch,
    let s := {| robots := mr ; bad := b |} in
    let ts := {| thestate := s ; thetick := tck|} in
    good_stacked s p ->
    global_transition sch t ts ts' ->
    (good_stacked (ts'.(thestate)) p).


Definition solution (s:timed_state) (t:transition) (p:position) := 
  good_stacked (s.(thestate)) p /\ stable_stacked t s p.


(* XU *)

(* foireux sur les quantifications, ici je force tb Ã  Ãªtre la mÃªme partout *)
Inductive leadsto_solution2 (s:timed_state) (t:transition) :=
| now : forall (ps:position), solution s t ps -> leadsto_solution2 s t
(* Ici on parenthèse pour que tous les successeurs soient ok *)
| later : (forall (s':timed_state), 
            global_transition sch_always t s s' -> leadsto_solution2 s' t) -> leadsto_solution2 s t.

Definition inhabited (c:configuration) p:Prop := MapPos.In p c.

Lemma split_good_not_sol :
  forall (s:timed_state) (c:configuration) t p p' ps r r', 
    c = (state_to_config (s.(thestate))) -> 
    p' <> p -> 
    inhabited c p -> inhabited c p' ->
    is_good s.(thestate) r -> 
    (MapRobots.MapsTo r p s.(thestate).(robots)) ->
    is_good s.(thestate) r' -> 
    (MapRobots.MapsTo r' p' s.(thestate).(robots)) ->
    (solution s t ps) ->  
    False.
Proof.
  intros s c t p p' ps r r' config pos_dif pos1 pos2 r_good r_at_p
         r'_good r'_at_p' t_sol_ps.
  subst.

  intros .
  destruct t_sol_ps as (ps_goodstack, ps_stable).
  unfold good_stacked,For_all in ps_goodstack.
  absurd (p'=p).
  - assumption.
  - transitivity ps.
    + eapply ps_goodstack with r'.
      apply is_good_mapsto;auto.
    + symmetry.
      eapply ps_goodstack with r.
      apply is_good_mapsto;auto.
Qed.


Definition is_max_good (m:state) x:Prop :=
  moremappred.For_all (fun rbt n => (n <= x)%Z /\ is_good m rbt) (m.(robots)). 


Definition is_min_good (m:state) x:Prop :=
  moremappred.For_all (fun rbt n => (x <= n)%Z /\ is_good m rbt) (m.(robots)). 

(* Versions decidables, à remettre et prouver compatible si nécessaire.

Definition is_max_good (m:state) x :=
  MapRobotsProps.for_all
                (fun rbt n => if (Z_le_dec n x)
                              then dec_is_good m rbt
                              else false)
                (m.(robots)). 

Definition is_min_good (m:state) x :=
  MapRobotsProps.for_all
                (fun rbt n => if (Z_le_dec x n)
                              then dec_is_good m rbt
                              else false)
                (m.(robots)). 
 *)

Definition good_diameter (s:state) (diam:position) :=
  exists max , exists min, is_max_good s max /\ is_min_good s min /\ diam = (max - min)%Z.



Definition cautious (t:transition) :=
  forall sch ts ts' d d',
    good_diameter (ts.(thestate)) d ->
    good_diameter (ts'.(thestate)) d' ->
    global_transition sch t ts ts' ->
    (ts'.(thetick) = (ts.(thetick)+1)) /\ (d' <= d)%Z.


Lemma always_fair t : fairness sch_always t.
Proof.
Admitted.

Definition stable_stacked2 t (s:timed_state) p :=
  forall s', good_stacked (s.(thestate)) p -> global_transition sch_always t s s' -> good_stacked (s'.(thestate)) p.

Lemma stable_stacked_wlog: forall sch t,
                             fairness sch t
                             -> forall s p, stable_stacked2 t s p <-> stable_stacked t s p.
Proof.
  
Admitted.


Lemma nosol_schalways_move :
  forall s s' t,
    (forall p, solution s t p -> False) ->
    (* t is deterministic *)
    leadsto_solution2 s t  ->
    global_transition sch_always t s s' ->
    s.(thestate) = s'.(thestate) -> False.
Proof.
  destruct s; destruct s'.
  intros t nosol determ gbtrans.
  simpl in *.
  decompose [and] gbtrans;clear gbtrans.


  Lemma immobile : forall t ts ts' ,
                     global_transition sch_always t ts ts' -> 
                     ts.(thestate) = ts'.(thestate) ->
                     exists ts'', global_transition sch_always t ts' ts'' /\ 
                                  ts'.(thestate) = ts''.(thestate).
  Proof.
    intros t ts ts' H H0.
    exists {| thestate := ts'.(thestate); thetick := ts'.(thetick)+1 |}.
    simpl.
    split;auto.
    unfold global_transition in *.
    decompose [and] H;clear H.
    split.
    - reflexivity.
    - split.
      + reflexivity.
      + intros r p h np H.
        assert (peqnp:p=np). (* tout ça pour ça! *)
        eapply MapRobotsFacts.MapsTo_fun;eauto.
        subst np.
        assert (h' : MapRobots.MapsTo r p (robots (thestate ts))).
        * rewrite H0.
          assumption.
        * specialize (H4 r p h').
          simpl in H; clear H.
          specialize (H4 p h).
          { destruct H4.
            - constructor 1.
              + unfold sch_always, get_all_robots.
                rewrite <- H0.
                apply H.
              + rewrite <- H0.
                assumption.
            - constructor 2.
              + unfold sch_always, get_all_robots.
                rewrite <- H0.
                apply H.
              + rewrite <- H0.
                assumption.
              + rewrite <- H0.
                assumption.
            - constructor 3.
              unfold sch_always, get_all_robots.
              rewrite <- H0.
              apply H.
          }
  Qed.


ICI  

  unfold global_transition in X.
  cbv zeta iota in X.
  destruct X.
  induction X;intros.
  - apply (nosol ps).
    assumption.
  - subst.
    apply H with (s':= global_transition sch_always t tb s).
    + reflexivity.
    + intros p H0.
      destruct H0.
      unfold solution in H0.
      rewrite <- H1 in H0.
      assert (stable_stacked t  s p).
      * admit. (* lemme *)
      * apply (nosol p).
        split;auto.
    + assumption.
    + 
        
      intuition.
        
    +


    set (g:=(global_transition sch_always t tb s)) in *.
    apply IHX.
    + admit.
    + intros ti tj c p.
      auto.
    + admit. (* lemme *)
    + reflexivity.
Qed.


Lemma global_trans_determ :
  forall (ti tj : tick) (c : configuration) (p : position),
    t c p ti = t c p tj
 -> global_transition sch_always t tb g = g.
            Proof.
              #
            Qed.


    setoid_rewrite <- H2 in IHX .
    setoid_rewrite <- H2 in IHX .


.
  assert(h:s=s').
  destruct s; destruct s';simpl in *.

  rewrite 

  intros.
  induction X.
  elim e ; intros.
  apply (nosol x) ; exact H1.
  (* putain mais c'est quoi cette hypothÃ¨se ? *)
  (* Ã§a peut pas marcher dans le but 3 les ticks diffÃ¨rent de 1 ! *)
  apply IHX.
  intros.
  rewrite e in H.
  rewrite H in H1.
  destruct  H1.
  assert (good_stacked (thestate s) p).
  rewrite <- H0 in H1 ; assumption.
  assert (stable_stacked t s p).
  rewrite <- stable_stacked_wlog in*.
  unfold stable_stacked2 in *.
  rewrite H0.
  intros.
  Check (H2 tb0 s'1 H1).
  (* lÃ  c'est dÃ©jÃ  mort *) 
  assert (thestate (global_transition sch_always t tb0 s') = (thestate (global_transition sch_always t tb0 s))).
  rewrite (tdet_schalways_sameconf_samemove t tb0 s s') ; try reflexivity.
  assumption.
  rewrite H0 ; reflexivity.
  rewrite H5 in H6.

(*---*)
Admitted.

(* TODO Show that there is at least one when there are more than 2 robots *)

Lemma split_conf_not_sol : forall (s:timed_state) (c:configuration) 
                                  t p p' ps, 
                             c = (state_to_config (s.(thestate))) -> 
                             p' <> p -> 
                             inhabited c p -> inhabited c p' ->
                             (solution s t ps) ->  
                             False.
Proof.
  intros.
  assert (exists sgs rg rg', 
            c = state_to_config (thestate sgs) /\  
            (MapRobots.find rg sgs.(thestate).(robots) = Some p) /\ 
            (MapRobots.find rg' sgs.(thestate).(robots) = Some p') /\
            (solution sgs t ps) -> False).
  


  Lemma XXX : forall s,
                MapRobots.cardinal ((s.(thestate)).(robots)) <= 2 * Robotset.cardinal ((s.(thestate)).(bad))
                -> forall t,
                     cautious t -> 
                     forall p, solution s t p -> False.
  Proof.
    intros s H t H0 p H1.
    unfold solution in *.
    destruct H1.
    unfold good_stacked, stable_stacked in *.
    pose (sch := fun ts:timed_state => all_robotsset s.(thestate)).
    Check cautious.
    TODO.
    

  Qed.
Admitted.


(* 
 *** Local Variables: ***
 *** coq-prog-name: "coqtop" ***
 *** fill-column: 80 ***
 *** End: ***
 *)