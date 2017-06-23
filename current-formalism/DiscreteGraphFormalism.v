(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain , R. Pelle                 *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Set Automatic Coercions Import. (* coercions are available as soon as functor application *)
Require Import Reals.
Require Import Psatz.
Require Import Omega.
Require Import Equalities.
Require Import Morphisms.
Require Import Decidable.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
(* Require Import Pactole.CommonFormalism. *)
Require Import Pactole.CommonGraphFormalism.
Require Import Pactole.Isomorphism.
Require Import Pactole.CommonIsoGraphFormalism.
Require MMapWeakList. (* to build an actual implementation of multisets *)
Require Import Utf8_core.
Require Import Arith_base.
Require Import SetoidList.
Require MMultisetInterface.
Require MMultisetExtraOps.
Require MMultisetWMap.
Require Import MMaps.MMapInterface.
Require Import MMultiset.MMultisetInterface.
Require Import MMultiset.MMultisetExtraOps.
Require Pactole.MMultiset.MMultisetFacts.
Require Stream.
(* Record graph_iso :=  *)


Module DGF (Graph : GraphDef)
           (N : Size)
           (Names : Robots(N))
           (LocationA : LocationADef(Graph))
           (MkInfoA : InfoSig(Graph)(LocationA))
           (ConfigA : Configuration (LocationA)(N)(Names)(MkInfoA.Info))
           (Import Iso : Iso(Graph) (LocationA))
           (MMapWL : WSfun)
           (Mraw : (FMultisetsOn)(LocationA))
           (M : MMultisetExtra(LocationA)(Mraw)).
  
  
  (** For spectra *)
  Module View : DecidableType with Definition t := ConfigA.t with Definition eq := ConfigA.eq.
    Definition t := ConfigA.t.
    Definition eq := ConfigA.eq.
    Definition eq_equiv := ConfigA.eq_equiv.
    Definition eq_dec := ConfigA.eq_dec.
  End View.



  (* They come from the common part as they are shared by AGF and DGF. *)
  Module InfoA := MkInfoA.Info.
  Module Location := LocationA.
  Module Info := InfoA.
  Module Config := ConfigA.
  
  (* FIXME: Factor it with MultisetSpectrum.v *)
  Module Spect <: Spectrum(Location)(N)(Names)(Info)(Config). 

    Instance Loc_compat : Proper (Config.eq_RobotConf ==> Location.eq) Config.loc.
    Proof. intros [] [] []. now cbn. Qed.

    Instance info_compat : Proper (Config.eq_RobotConf ==> Info.eq) Config.info.
    Proof. intros [] [] [] *. now cbn. Qed.

    (** Definition of spectra as multisets of locations. *)
    Notation "m1  ≡  m2" := (M.eq m1 m2) (at level 70).
    Notation "m1  ⊆  m2" := (M.Subset m1 m2) (at level 70).
    Notation "m1  [=]  m2" := (M.eq m1 m2) (at level 70, only parsing).
    Notation "m1  [c=]  m2" := (M.Subset m1 m2) (at level 70, only parsing).

    Lemma eq_refl_left : forall e A (a b:A), (if Location.eq_dec e e then a else b) = a.
    Proof.
      intros e A a b.
      destruct (Location.eq_dec e e).
      - reflexivity.
      - elim n.
        reflexivity.
    Qed.


    (** **  Building multisets from lists  **)

    Definition multiset l := M.from_elements (List.map (fun x => (x, 1)) l).

    Lemma multiset_nil : multiset List.nil [=] M.empty.
    Proof. reflexivity. Qed.

    Lemma multiset_cons : forall x l, multiset (x :: l) [=] M.add x 1 (multiset l).
    Proof. reflexivity. Qed.

    Lemma multiset_empty : forall l, multiset l [=] M.empty <-> l = List.nil.
    Proof.
      intro l. unfold multiset. rewrite M.from_elements_empty.
      destruct l; simpl; split; intro H; inversion_clear H; intuition; discriminate.
    Qed.

    Lemma multiset_app : forall l l', multiset (l ++ l') [=] M.union (multiset l) (multiset l').
    Proof. intros. unfold multiset. now rewrite List.map_app, M.from_elements_append. Qed.

    Lemma location_neq_sym: forall x y, ~ Location.eq x y -> ~ Location.eq y x.
    Proof. intros x y H Habs. now symmetry in Habs. Qed.

    Instance multiset_compat : Proper (PermutationA Location.eq ==> M.eq) multiset.
    Proof.
      intros l1 l2 Hl. eapply M.from_elements_compat, PermutationA_map; eauto; refine _; [].
      repeat intro; now split.
    Qed.

    Lemma multiset_PermutationA : forall x l n, M.multiplicity x (multiset l) = n ->
                                                exists l', ~SetoidList.InA Location.eq x l' /\ PermutationA Location.eq l (alls x n ++ l').
    Proof.
      intros x l. induction l; intros n Hin.
      exists List.nil. split. now auto. rewrite multiset_nil, M.empty_spec in Hin. subst n. simpl. reflexivity.
      rewrite multiset_cons in Hin. destruct (Location.eq_dec x a) as [Heq | Heq].
      - setoid_rewrite <- Heq. rewrite <- Heq in Hin. rewrite M.add_spec in Hin. destruct n.
        + rewrite eq_refl_left in Hin.
          omega.
        + rewrite eq_refl_left in Hin.
          rewrite plus_comm in Hin. cbn in Hin. apply eq_add_S in Hin. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
          exists l'. split. assumption. simpl. now constructor.
      - rewrite M.add_other in Hin; auto. apply IHl in Hin. destruct Hin as [l' [Hl1 Hl2]].
        exists (a :: l'). split. intro Hin; inversion_clear Hin; contradiction.
        transitivity (a :: alls x n ++ l'); now constructor || apply (PermutationA_middle _).
    Qed.

    Lemma multiset_alls : forall x n, multiset (alls x n) [=] M.singleton x n.
    Proof.
      intros x n. induction n; simpl.
      + now rewrite M.singleton_0, multiset_nil.
      + rewrite multiset_cons. rewrite IHn. intro y. rewrite M.singleton_spec.
        destruct (Location.eq_dec y x) as [Heq | Heq].
      - rewrite Heq, M.add_spec, M.singleton_spec. destruct (Location.eq_dec x x) as [_ | Helim]. omega. now elim Helim.
      - rewrite M.add_other; auto. rewrite M.singleton_spec. destruct (Location.eq_dec y x); trivial. contradiction.
    Qed.

    Corollary multiset_In : forall x l, M.multiplicity x (multiset l) > 0 <-> SetoidList.InA Location.eq x l.
    Proof.
      intros x l. split; intro Hl.
      + destruct (multiset_PermutationA _ _ _ (eq_refl (M.multiplicity x (multiset l)))) as [l' [Hl' Hperm]].
        rewrite Hperm. rewrite (SetoidList.InA_app_iff _). left. destruct (M.multiplicity x (multiset l)). omega. now left.
      + induction l. now inversion Hl. rewrite multiset_cons. destruct (Location.eq_dec a x) as [Heq | Hneq].
      - rewrite Heq. rewrite M.add_spec. 
        rewrite eq_refl_left.
        omega.
      - apply location_neq_sym in Hneq.
        rewrite M.add_other; trivial. apply IHl. inversion_clear Hl; auto. now elim Hneq.
    Qed.

    Theorem multiset_map : forall f, Proper (Location.eq ==> Location.eq) f ->
                                     forall l, multiset (List.map f l) [=] M.map f (multiset l).
    Proof. intros f Hf l x. unfold multiset. now rewrite List.map_map, M.map_from_elements, List.map_map. Qed.

    Theorem multiset_filter : forall f, Proper (Location.eq ==> Logic.eq) f ->
                                        forall l, multiset (List.filter f l) [=] M.filter f (multiset l).
    Proof.
      intros f Hf l. induction l as [| e l]; simpl.
      + rewrite (@M.filter_compat f Hf (multiset List.nil)), multiset_nil. now rewrite M.filter_empty. now apply multiset_nil.
      + destruct (f e) eqn:Htest.
      - do 2 rewrite multiset_cons. rewrite M.filter_add, Htest, IHl; trivial; reflexivity || omega.
      - rewrite multiset_cons, M.filter_add, Htest, IHl; trivial; reflexivity || omega.
    Qed.

    Theorem cardinal_multiset : forall l, M.cardinal (multiset l) = length l.
    Proof.
      induction l; simpl.
      + now rewrite multiset_nil, M.cardinal_empty.
      + rewrite multiset_cons, M.cardinal_add. apply f_equal, IHl.
    Qed.

    Theorem multiset_spec : forall x l, M.multiplicity x (multiset l) = countA_occ _ Location.eq_dec x l.
    Proof.
      intros x l. induction l; simpl.
      + rewrite multiset_nil. now apply M.empty_spec.
      + rewrite multiset_cons. destruct (Location.eq_dec a x) as [Heq | Hneq].
      - rewrite Heq. rewrite M.add_spec. rewrite IHl.
        rewrite eq_refl_left.
        omega.
      - apply location_neq_sym in Hneq. rewrite M.add_other. now apply IHl. assumption.
    Qed.

    Lemma multiset_remove : forall x l,
        multiset (SetoidList.removeA Location.eq_dec x l) [=] M.remove x (M.multiplicity x (multiset l)) (multiset l).
    Proof.
      intros x l y. induction l as [| a l]; simpl.
      * rewrite multiset_nil. do 2 rewrite M.empty_spec. now rewrite M.remove_0, M.empty_spec.
      * rewrite multiset_cons. destruct (Location.eq_dec y x) as [Hyx | Hyx], (Location.eq_dec x a) as [Hxa | Hxa].
      + rewrite Hyx, Hxa in *. rewrite IHl. setoid_rewrite M.remove_same. setoid_rewrite M.add_same. omega.
      + rewrite Hyx in *. rewrite multiset_cons, M.add_other; auto. rewrite IHl. do 2 rewrite M.remove_same. omega.
      + rewrite Hxa in *. rewrite IHl, M.add_same. repeat rewrite M.remove_other; auto. rewrite M.add_other; auto.
      + rewrite multiset_cons. rewrite M.remove_other; auto. destruct (Location.eq_dec y a) as [Hya | Hya].
      - rewrite Hya in *. do 2 rewrite M.add_same. rewrite IHl. now rewrite M.remove_other.
      - repeat rewrite M.add_other; trivial. rewrite IHl. rewrite M.remove_other; auto.
    Qed.

    Lemma multiset_support : forall x l, SetoidList.InA Location.eq x (M.support (multiset l)) <-> SetoidList.InA Location.eq x l.
    Proof. intros x l. rewrite M.support_spec. unfold M.In. rewrite multiset_spec. apply countA_occ_pos. refine _. Qed.


    (** Building a spectrum from a configuration *)
    Include M.

    (* graph 

Module Type (Spectrum, GraphDef)
     *)

    Definition from_config conf : t := multiset (List.map Config.loc (Config.list conf)).

    Instance from_config_compat : Proper (Config.eq ==> eq) from_config.
    Proof.
      intros conf1 conf2 Hconf x. unfold from_config. do 2 f_equiv.
      apply eqlistA_PermutationA_subrelation, (map_extensionalityA_compat Location.eq_equiv Loc_compat).
      apply Config.list_compat. assumption.
    Qed.

    Definition is_ok s conf := forall l,
        M.multiplicity l s = countA_occ _ Location.eq_dec l (List.map Config.loc (Config.list conf)).

    Theorem from_config_spec : forall conf, is_ok (from_config conf) conf.
    Proof. unfold from_config, is_ok. intros. apply multiset_spec. Qed.

    Lemma from_config_map : forall f, Proper (Location.eq ==> Location.eq) f ->
      forall conf, eq (map f (from_config conf))
                      (from_config (Config.map (fun x => {| Config.loc := f (Config.loc x); Config.info := Config.info x|}) conf)).
    Proof.
      intros f Hf config. unfold from_config. rewrite Config.list_map.
      - now rewrite <- multiset_map, List.map_map, List.map_map.
      - intros ? ? Heq. hnf. split; cbn; try apply Hf; apply Heq.
    Qed.

    Theorem cardinal_from_config : forall conf, cardinal (from_config conf) = N.nG + N.nB.
    Proof. intro. unfold from_config. now rewrite cardinal_multiset, List.map_length, Config.list_length. Qed.

    Property pos_in_config : forall (config : Config.t) id, In (Config.loc (config id)) (from_config config).
    Proof.
      intros conf id. unfold from_config.
      unfold In. rewrite multiset_spec. rewrite (countA_occ_pos _).
      rewrite InA_map_iff; autoclass. exists (conf id). split; try reflexivity; [].
      setoid_rewrite Config.list_InA. now exists id.
    Qed.

    Property from_config_In : forall config l,
        In l (from_config config) <-> exists id, Location.eq (Config.loc (config id)) l.
    Proof.
      intros config l. split; intro Hin.
      + unfold In in Hin. rewrite from_config_spec, (countA_occ_pos _), Config.list_spec in Hin.
        rewrite (InA_map_iff _ _) in Hin; [setoid_rewrite (InA_map_iff _ _) in Hin |]; try autoclass; [].
        destruct Hin as [? [Hl [id [? Hid]]]]. exists id. rewrite <- Hl. now f_equiv.
      + destruct Hin as [id Hid]. rewrite <- Hid. apply pos_in_config.
    Qed.
    
  End Spect.


  Record robogram :=
    {
      pgm :> Spect.t -> Location.t -> Location.t;
      pgm_compat : Proper (Spect.eq ==> Location.eq ==> Location.eq) pgm;
      pgm_range : forall spect lpre,
          exists lpost e, pgm spect lpre = lpost
                          /\ (opt_eq Graph.Eeq (Graph.find_edge lpre lpost) (Some e))
    }.

  (* pgm s l a du dens si l est dans dans s (s[l] > 0)
     si l n'est pas occupée par un robot, on doit revoyer un voisin (à cause de pgm_range). *)
  
  Global Existing Instance pgm_compat.

  Definition req (r1 r2 : robogram) := (Spect.eq ==> Location.eq ==> Location.eq)%signature r1 r2.
  
  Instance req_equiv : Equivalence req.
  Proof.
    split.
    + intros [robogram Hrobogram] x y Heq g1 g2 Hg; simpl. rewrite Hg, Heq. reflexivity.
    + intros r1 r2 H x y Heq g1 g2 Hg. rewrite Hg, Heq.
      unfold req in H.
      now specialize (H y y (reflexivity y) g2 g2 (reflexivity g2)).
    + intros r1 r2 r3 H1 H2 x y Heq g1 g2 Hg.
      specialize (H1 x y Heq g1 g2 Hg). 
      specialize (H2 y y (reflexivity y) g2 g2 (reflexivity g2)).
      now rewrite H1.
  Qed.
  
  (** ** Executions *)
  
  (** Now we can [execute] some robogram from a given configuration with a [demon] *)
  Definition execution := Stream.t Config.t.
 
  Definition eeq : execution -> execution -> Prop := Stream.eq Config.eq.

  Instance eeq_equiv : Equivalence eeq.
  Proof.
    split.
    + coinduction eeq_refl. reflexivity.
    + coinduction eeq_sym. symmetry. now inversion H. now inversion H.
    + coinduction eeq_trans. 
    - inversion H. inversion H0. now transitivity (Stream.hd y).
    - apply (eeq_trans (Stream.tl x) (Stream.tl y) (Stream.tl z)).
      now inversion H. now inversion H0.
  Qed.
  
  Instance eeq_hd_compat : Proper (eeq ==> Config.eq) (@Stream.hd _ ).
  Proof. apply Stream.hd_compat. Qed.
  
  Instance eeq_tl_compat : Proper (eeq ==> eeq) (@Stream.tl _).
  Proof. apply Stream.tl_compat. Qed.
  
  (** ** Demonic schedulers *)
  
  (** A [demonic_action] moves all byz robots as it whishes,
    and sets the referential of all good robots it selects. *)
  Inductive Active_or_Moving := 
  | Moving (dist : bool)                   (* moving ratio, le cas "false" facilite l'équivalence entre les modèles. *)
  | Active (sim : Iso.t).                  (* change of referential *)

  Definition Aom_eq (a1 a2: Active_or_Moving) :=
    match a1, a2 with
    | Moving d1, Moving d2 => d1 = d2
    | Active sim1, Active sim2 =>Iso.eq sim1 sim2
    | _, _ => False
    end.
    
  Instance Active_compat : Proper (Iso.eq ==> Aom_eq) Active.
  Proof. intros ? ? ?. auto. Qed.
  
  (* as Active give a function, Aom_eq is not reflexive. It's still symmetric and transitive.*)
  Instance Aom_eq_Symmetric : Symmetric Aom_eq.
  Proof.
    intros x y H. unfold Aom_eq in *. destruct x, y; auto.
    now symmetry.
  Qed.
  
  Instance Aom_eq_Transitive : Transitive Aom_eq.
  Proof.
    intros [] [] [] H12 H23; unfold Aom_eq in *; congruence || easy || auto.
    now rewrite H12, H23.
  Qed.

(* on a besoin de Rconfig car ça permet de faire la conversion d'un modèle à l'autre *)
  
  Record demonic_action :=
    {
      relocate_byz : Names.B -> Config.RobotConf;
      step : Names.ident -> Config.RobotConf -> Active_or_Moving;
      step_delta : forall g Rconfig sim,
          Aom_eq (step (Good g) Rconfig) (Active sim) ->
          Location.eq Rconfig.(Config.loc) Rconfig.(Config.info).(Info.target);
      step_compat : Proper (eq ==> Config.eq_RobotConf ==> Aom_eq) step
    }.
  Set Implicit Arguments.
  
  Definition da_eq (da1 da2 : demonic_action) :=
    (forall id config, (Aom_eq)%signature (da1.(step) id config) (da2.(step) id config)) /\
    (forall b : Names.B, Config.eq_RobotConf (da1.(relocate_byz) b) (da2.(relocate_byz) b)).
  
  Instance da_eq_equiv : Equivalence da_eq.
  Proof.
    split.
    + split; intuition. now apply step_compat.
    + intros da1 da2 [Hda1 Hda2]. split; repeat intro; try symmetry; auto.
    + intros da1 da2 da3 [Hda1 Hda2] [Hda3 Hda4].
      split; intros; try etransitivity; eauto.
  Qed.
  
  Instance step_da_compat : Proper (da_eq ==> eq ==> Config.eq_RobotConf ==> Aom_eq) step.
  Proof.
    intros da1 da2 [Hd1 Hd2] p1 p2 Hp x y Hxy. subst.
    etransitivity.
    - apply Hd1.
    - apply (step_compat da2); auto.
  Qed.
  
  Instance relocate_byz_compat : Proper (da_eq ==> Logic.eq ==> Config.eq_RobotConf) relocate_byz.
  Proof. intros [] [] Hd p1 p2 Hp. subst. destruct Hd as [H1 H2]. simpl in *. apply (H2 p2). Qed.
  
  Lemma da_eq_step_Moving : forall da1 da2,
      da_eq da1 da2 -> 
      forall id config r,
        Aom_eq (step da1 id config) (Moving r) <-> 
        Aom_eq (step da2 id config) (Moving r).
  Proof.
    intros da1 da2 Hda id config r.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
    split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step; reflexivity || elim Hopt_eq; now auto.
  Qed.

  Lemma da_eq_step_Active : forall da1 da2,
      da_eq da1 da2 -> 
      forall id config sim,
        Aom_eq (step da1 id config) (Active sim) <-> 
        Aom_eq (step da2 id config) (Active sim).
  Proof.
    intros da1 da2 Hda id config sim.
    assert (Hopt_eq := step_da_compat Hda (reflexivity id) (reflexivity config)).
    split; intro Hidle;rewrite Hidle in Hopt_eq ; destruct step;
      reflexivity || elim Hopt_eq; now intros; simpl.
  Qed.
  
  (** A [demon] is just a stream of [demonic_action]s. *)
  Definition demon := Stream.t demonic_action.
  
  Definition deq (d1 d2 : demon) : Prop := Stream.eq da_eq d1 d2.
  
  Instance deq_equiv : Equivalence deq.
  Proof. apply Stream.eq_equiv, da_eq_equiv. Qed.
  
  Instance demon_hd_compat : Proper (deq ==> da_eq) (@Stream.hd _) :=
  Stream.hd_compat _.
  
  Instance demon_tl_compat : Proper (deq ==> deq) (@Stream.tl _) :=
    Stream.tl_compat _.
  
  (** [round r da conf] return the new configuration of robots (that is a function
    giving the configuration of each robot) from the previous one [conf] by applying
    the robogram [r] on each spectrum seen by each robot. [da.(demonic_action)]
    is used for byzantine robots. *)
  (* TODO: Should we keep the Moving/Active disctinction?
         We could use :
         1) bool in da, 2 states for robots (Loc / MoveTo)
         2) 3 states in da (Compute, Move, Wait), 2 states for robots *)
  Global Notation "s ⁻¹" := (Iso.inverse s) (at level 99).

  Definition round (r : robogram) (da : demonic_action) (config : Config.t) : Config.t :=
    (** for a given robot, we compute the new configuration *)
    fun id =>
      let rconf := config id in
      let pos := rconf.(Config.loc) in
      match da.(step) id rconf with (** first see whether the robot is activated *)
      | Moving false => rconf
      | Moving true =>
        match id with
        | Good g =>
          let tgt := rconf.(Config.info).(Info.target) in
          {| Config.loc := tgt ; Config.info := rconf.(Config.info) |}
        | Byz b => rconf
        end
      | Active sim => (* g is activated with similarity [sim (conf g)] and move ratio [mv_ratio] *)
        match id with
        | Byz b => da.(relocate_byz) b (* byzantine robot are relocated by the demon *)
        | Good g =>
          let local_config := Config.map (Config.app sim) config in
          let local_target := (r (Spect.from_config local_config) (Config.loc (local_config (Good g)))) in
          let target := (sim⁻¹).(Iso.sim_V) local_target in
(* This if is unnecessary: with the invariant on da: inside rconf, loc = target *)
(*           if (Location.eq_dec (target) pos) then rconf else *)
          {| Config.loc := pos ; 
             Config.info := {| Info.source := pos ; Info.target := target|} |}
        end
      end.
  
  Instance round_compat : Proper (req ==> da_eq ==> Config.eq ==> Config.eq) round.
  Proof.
    intros r1 r2 Hr da1 da2 Hda conf1 conf2 Hconf id.
    unfold req in Hr.
    unfold round.
    assert (Hrconf : Config.eq_RobotConf (conf1 id) (conf2 id)). 
    apply Hconf.
    assert (Hstep := step_da_compat Hda (reflexivity id) Hrconf).
    assert (Hsim: Aom_eq (step da1 id (conf1 id)) (step da1 id (conf2 id))).
    apply step_da_compat; try reflexivity.
    apply Hrconf.
    destruct (step da1 id (conf1 id)) eqn : He1, (step da2 id (conf2 id)) eqn:He2;
      destruct (step da1 id (conf2 id)) eqn:He3, id as [ g| b]; try now elim Hstep.
    + unfold Aom_eq in *.
      rewrite Hstep.
      destruct dist0.
      f_equiv;
        apply Hrconf.
      apply Hrconf.
    + unfold Aom_eq in *.
      rewrite Hstep.
      destruct dist0; apply Hrconf.
    + assert (Location.eq (((Iso.sim_V (sim ⁻¹))
            (r1 (Spect.from_config (Config.map (Config.app sim) conf1))
                (Config.loc (Config.map (Config.app sim) conf1 (Good g))))))
                          (((Iso.sim_V (sim0 ⁻¹))
            (r2 (Spect.from_config (Config.map (Config.app sim0) conf2))
                (Config.loc (Config.map (Config.app sim0) conf2 (Good g))))))).
      f_equiv.
      simpl in Hstep.
      f_equiv.
      f_equiv.
      apply Hstep.
      apply Hr. now repeat f_equiv.
      apply Config.map_compat.
      apply Config.app_compat.
      apply Hstep.
      apply Hconf.
(*       destruct (Location.eq_dec
         ((Iso.sim_V (sim ⁻¹))
            (r1 (Spect.from_config (Config.map (Config.app sim) conf1))
               (Config.loc (Config.map (Config.app sim) conf1 (Good g)))))
         (Config.loc (conf1 (Good g)))),
       (Location.eq_dec
         ((Iso.sim_V (sim0 ⁻¹))
            (r2 (Spect.from_config (Config.map (Config.app sim0) conf2))
               (Config.loc (Config.map (Config.app sim0) conf2 (Good g)))))
         (Config.loc (conf2 (Good g)))).
      now apply Hconf. *)
      repeat split; simpl; f_equiv; try apply Hconf; [|].
      - now f_equiv.
      - apply Hr. repeat (f_equiv; trivial). now do 2 f_equiv.
    + rewrite Hda. now destruct (Hconf (Byz b)).
  Qed.
  
  
  (** [execute r d conf] returns an (infinite) execution from an initial global
    configuration [conf], a demon [d] and a robogram [r] running on each good robot. *)
  Definition execute (r : robogram): demon -> Config.t -> execution :=
    cofix execute d conf :=
      Stream.cons conf (execute (Stream.tl d) (round r (Stream.hd d) conf)).
  
  (** Decomposition lemma for [execute]. *)
  Lemma execute_tail : forall (r : robogram) (d : demon) (conf : Config.t),
      Stream.tl (execute r d conf) = execute r (Stream.tl d) (round r (Stream.hd d) conf).
  Proof. intros. destruct d. reflexivity. Qed.
  
  Instance execute_compat : Proper (req ==> deq ==> Config.eq ==> eeq) execute.
  Proof.
    intros r1 r2 Hr.
    cofix proof. constructor. simpl. assumption.
    apply proof; clear proof. now inversion H. apply round_compat; trivial. inversion H; assumption.
  Qed.

  (** ** Fairness *)

  (* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
       changer execution en un (execute r d config) 
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
*)
  
  (** A [demon] is [Fair] if at any time it will later activate any robot. *)
  Inductive LocallyFairForOne g (d : demon) r e : Prop :=
  | ImmediatelyFair :
      (exists conf,
        eeq (execute r d conf) e) -> 
      (exists sim,
          Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e)
                                                  (Good g))) (Active sim))
      → LocallyFairForOne g d r e
  | LaterFair :
      (exists conf,
        eeq (execute r d conf) e) -> 
      (exists dist,
          Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e) (Good g)))
                 (Moving dist))
      → LocallyFairForOne g (Stream.tl d) r (Stream.tl e)
      → LocallyFairForOne g d r e.
  
  CoInductive Fair (d : demon) r e : Prop :=
    AlwaysFair : (∀ g, LocallyFairForOne g d r e) →
                 Fair (Stream.tl d) r (Stream.tl e) →
                 Fair d r e.
  
  (** [Between g h d] means that [g] will be activated before at most [k]
    steps of [h] in demon [d]. *)
  Inductive Between g h (d : demon) r e: nat -> Prop :=
  | kReset : forall k,
      (exists conf,
        eeq (execute r d conf) e) -> 
      (exists sim, Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e) (Good g)))
                          (Active sim))
      -> Between g h d r e k 
  | kReduce : forall k,
      (exists conf,
        eeq (execute r d conf) e) -> 
      (exists dist, Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e)
                                                            (Good g)))
                           (Moving dist))
      -> (exists sim, Aom_eq (step (Stream.hd d) (Good h) ((Stream.hd e)
                                                              (Good h)))
                             (Active sim))
      -> Between g h (Stream.tl d) r (Stream.tl e) k -> Between g h d r e (S k)
  | kStall : forall k,
      (exists conf,
        eeq (execute r d conf) e) -> 
      (exists dist, Aom_eq (step (Stream.hd d) (Good g) ((Stream.hd e)
                                                            (Good g)))
                           (Moving dist)) -> 
      (exists dist, Aom_eq (step (Stream.hd d) (Good h) ((Stream.hd e)
                                                            (Good h)))
                           (Moving dist)) ->
      Between g h (Stream.tl d) r (Stream.tl e) k -> Between g h d r e k.

  (* k-fair: every robot g is activated within at most k activation of any other robot h *)
  CoInductive kFair k (d : demon) r e: Prop :=
    AlwayskFair : (forall g h, Between g h d r e k) ->
                  kFair k (Stream.tl d)r  (Stream.tl e) ->
                  kFair k d r e.

  Lemma LocallyFairForOne_compat_aux : forall g d1 d2 e1 e2 r1 r2,
      deq d1 d2 -> eeq e1 e2 -> req r1 r2 -> 
      LocallyFairForOne g d1 r1 e1 -> LocallyFairForOne g d2 r2 e2.
  Proof.
    intros g da1 da2 e1 e2 r1 r2 Hda He Hr Hfair.
    revert da2 Hda e2 He r2 Hr. induction Hfair; intros da2 Hda.
    + constructor 1.
      destruct H.
      exists x.
      now rewrite <- He, <- Hr, <- Hda.
      destruct H0.
      exists x.
      rewrite <- He.
      rewrite da_eq_step_Active; try eassumption. now f_equiv.
    + constructor 2.
      destruct H.
      exists x.
      now rewrite <- He, <- Hr, <- Hda.
      destruct H0.
      exists x.
      rewrite <- He.
      rewrite da_eq_step_Moving; try eassumption. now f_equiv.
      apply IHHfair;
      now f_equiv.
  Qed.

  Instance LocallyFairForOne_compat : Proper (eq ==> deq ==> req ==> eeq ==> iff) LocallyFairForOne.
  Proof.
    repeat intro. subst. split; intro; now eapply LocallyFairForOne_compat_aux; eauto. Qed.

  Lemma Fair_compat_aux : forall d1 d2 e1 e2 r1 r2,
      deq d1 d2 -> eeq e1 e2 -> req r1 r2 -> Fair d1 r1 e1 -> Fair d2 r2 e2.
  Proof.
    cofix be_fair. intros d1 d2 e1 e2 r1 r2 Hdeq Heeq Hreq Hfair.
    destruct Hfair as [Hnow Hlater]. constructor.
    + intros. now rewrite <- Hdeq, <- Heeq, <- Hreq.
    + eapply be_fair; try eassumption; now f_equiv.
  Qed.

  Instance Fair_compat : Proper (deq ==> req ==> eeq ==> iff) Fair.
  Proof. repeat intro. split; intro; now eapply Fair_compat_aux; eauto. Qed.

  Lemma Between_compat_aux : forall g h k d1 d2 r1 r2 e1 e2,
      deq d1 d2 -> eeq e1 e2 -> req r1 r2 ->
      Between g h d1 r1 e1 k -> Between g h d2 r2 e2 k.
  Proof.
    intros g h k d1 d2 r1 r2 e1 e2 Hdeq Heeq Hreq bet.
    revert d2 Hdeq e2 Heeq r2 Hreq. induction bet; intros d2 Hdeq e2 Heeq.
    + constructor 1.
      destruct H.
      exists x.
      now rewrite <- Heeq, <- Hreq, <- Hdeq.
      destruct H0.
      exists x.
      rewrite <- Heeq.
      rewrite <- da_eq_step_Active; try eassumption. now f_equiv.
    + constructor 2.
    - destruct H; exists x; now rewrite <- Heeq, <- Hreq, <- Hdeq.
    - destruct H0; exists x; rewrite <- Heeq;
        rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
    - destruct H1; exists x; rewrite <- Heeq;
        rewrite <- da_eq_step_Active; try eassumption. now f_equiv.
    - apply IHbet; now f_equiv.
    + constructor 3.
    - destruct H; exists x; now rewrite <- Heeq, <- Hreq, <- Hdeq.
    - destruct H0; exists x; rewrite <- Heeq;
        rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
    - destruct H1; exists x; rewrite <- Heeq;
        rewrite <- da_eq_step_Moving; try eassumption. now f_equiv.
    - apply IHbet; now f_equiv.
  Qed.

  Instance Between_compat : Proper (eq ==> eq ==> deq ==> req ==> eeq ==> eq ==> iff) Between.
  Proof. repeat intro. subst. split; intro; now eapply Between_compat_aux; eauto. Qed.

  Lemma kFair_compat_aux : forall k d1 d2 r1 r2 e1 e2,
      deq d1 d2 -> req r1 r2 -> eeq e1 e2 -> kFair k d1 r1 e1 -> kFair k d2 r2 e2.
  Proof.
    cofix be_fair. intros k d1 d2 e1 e2 r1 r2 Hdeq Hreq Heeq Hkfair.
    destruct Hkfair as [Hnow Hlater]. constructor.
    + intros. now rewrite <- Hdeq, <- Heeq, <- Hreq.
    + eapply be_fair; try eassumption; now f_equiv.
  Qed.

  Instance kFair_compat : Proper (eq ==> deq ==> req ==> eeq ==> iff) kFair.
  Proof. repeat intro. subst. split; intro; now eapply kFair_compat_aux; eauto. Qed.

  Lemma Between_LocallyFair : forall g (d : demon) h r e k,
      Between g h d r e k -> LocallyFairForOne g d r e.
  Proof.
    intros g h d r e k Hg. induction Hg.
    now constructor 1.
    now constructor 2.
    now constructor 2.
  Qed.

  (** A robot is never activated before itself with a fair demon! The
    fairness hypothesis is necessary, otherwise the robot may never be
    activated. *)
  Lemma Between_same :
    forall g (d : demon) k r e, LocallyFairForOne g d r e -> Between g g d r e k.
  Proof.
    intros g d r e k Hd. induction Hd.
    now constructor 1.
    now constructor 3.
  Qed.

  (** A k-fair demon is fair. *)
  Theorem kFair_Fair : forall k (d : demon) r e, kFair k d r e -> Fair d r e.
  Proof.
    coinduction kfair_is_fair.
    destruct H as [Hbetween H]. intro. apply Between_LocallyFair with g k.
    now apply Hbetween.
    apply (kfair_is_fair k). now destruct H.
  Qed.

  (** [Between g h d k] is monotonic on [k]. *)
  Lemma Between_mon : forall g h (d : demon) r e k,
      Between g h d r e k -> forall k', (k <= k')%nat -> Between g h d r e k'.
  Proof.
    intros g h d r e k Hd. induction Hd; intros k' Hk.
    now constructor 1.
    destruct k'.
    now inversion Hk.
    constructor 2; assumption || now (apply IHHd; omega).
    constructor 3; assumption || now (apply IHHd; omega).
  Qed.

  (** [kFair k d] is monotonic on [k] relation. *)
  Theorem kFair_mon : forall k (d: demon) r e,
      kFair k d r e -> forall k', (k <= k')%nat -> kFair k' d r e.
  Proof.
    coinduction fair; destruct H.
    - intros. now apply Between_mon with k.
    - now apply (fair k).
  Qed.

  Theorem Fair0 : forall d r e,
      (exists conf,
          eeq (execute r d conf) e) -> 
      kFair 0 d r e->
      forall g h,
        (exists dist,
            Aom_eq ((Stream.hd d).(step) (Good g) ((Stream.hd e) (Good g))) (Moving dist))
        <-> exists dist,
          Aom_eq ((Stream.hd d).(step) (Good h) ((Stream.hd e) (Good h))) (Moving dist).
  Proof.
    intros d r e Hconf Hd g h. destruct Hd as [Hd _]. split; intro H.
    assert (Hg := Hd g h). inversion Hg. destruct H1, H.
    rewrite H in H1; now simpl in *.
    destruct H2; exists x. assumption.
    assert (Hh := Hd h g). inversion Hh. destruct H1, H.
    rewrite H in H1; now simpl in *.
    destruct H2; exists x. assumption.
  Qed.

  (** ** Full synchronicity

  A fully synchronous demon is a particular case of fair demon: all good robots
  are activated at each round. In our setting this means that the demon never
  return a null reference. *)


  (* (** A demon is fully synchronous for one particular good robot g at the first *)
   (*     step. *) *)
  (*   Inductive FullySynchronousForOne g d:Prop := *)
  (*     ImmediatelyFair2: *)
  (*       (step (Stream.hd d) g) ≠ None →  *)
  (*       FullySynchronousForOne g d. *)

  Definition StepSynchronism d e r : Prop := forall g,
      (exists conf,
          eeq (execute r d conf) e) -> 
      exists aom,
        ((exists sim, Aom_eq aom (Active sim)) \/ Aom_eq aom (Moving true)) /\
        step (Stream.hd d) (Good g) ((Stream.hd e) (Good g)) = aom .
  
  (** A demon is fully synchronous if it is fully synchronous for all good robots
    at all step. *)
  CoInductive FullySynchronous d r e := 
    NextfullySynch:
      StepSynchronism d e r
      → FullySynchronous (Stream.tl d) r (Stream.tl e)
      → FullySynchronous d r e.
  
End DGF.
