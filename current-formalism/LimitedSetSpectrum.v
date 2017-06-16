(**************************************************************************)
(*   Mechanised Framework for Local Interactions & Distributed Algorithms *)
(*   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            *)
(*   PACTOLE project                                                      *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(**************************************************************************)
(**   Mechanised Framework for Local Interactions & Distributed Algorithms 

   C. Auger, P. Courtieu, L. Rieg, X. Urbain                            

   PACTOLE project                                                      
                                                                        
   This file is distributed under the terms of the CeCILL-C licence     
                                                                        *)
(**************************************************************************)

Require Import Utf8_core.
Require Import SetoidList.
Require Import Rbase.
Require Import Pactole.Preliminary.
Require Import Pactole.Robots.
Require Import Pactole.Configurations.
Require Import Pactole.RealMetricSpace.
Require Pactole.SetSpectrum.


Module Type Radius.
  Parameter radius : R.
End Radius.


Module Make (Loc : RealMetricSpace) (* for the distance *)
            (N : Size)
            (R : Radius)
            (Names : Robots.Robots(N))
            (Info : DecidableTypeWithApplication(Loc))
            (Config : Configuration(Loc)(N)(Names)(Info)) <: Spectrum (Loc)(N)(Names)(Info)(Config).

Module M := SetSpectrum.Make(Loc)(N)(Names)(Info)(Config).

Notation "m1  ≡  m2" := (M.eq m1 m2) (at level 70).
Notation "m1  [=]  m2" := (M.eq m1 m2) (at level 70, only parsing).


(** Building a spectrum from a configuration *)

(** Inclusion is not possible because M has the same signature and we want to restrict the functions. *)
Definition t := M.t.
Definition eq := M.eq.
Definition eq_equiv := M.eq_equiv.
Definition eq_dec := M.eq_dec.
Definition In := M.In.


Definition from_config conf : t :=
  M.M.filter (fun x => Rle_bool (Loc.dist x Loc.origin) R.radius) (M.set (map Config.loc (Config.list conf))).

Instance from_config_compat : Proper (Config.eq ==> eq) from_config.
Proof.
intros conf1 conf2 Hconf x. unfold from_config.
f_equiv. apply M.MProp.MP.Dec.F.filter_ext.
+ intros y z Hyz. rewrite Hyz. reflexivity.
+ intro. reflexivity.
+ apply M.set_compat, (@PermutationA_map _ _ Config.eq_RobotConf Loc.eq),
        eqlistA_PermutationA_subrelation, Config.list_compat;
  autoclass; apply Config.loc_compat.
Qed.

Definition is_ok s conf := forall l,
  In l s <-> (Loc.dist l Loc.origin <= R.radius)%R /\ exists id : Names.ident, Loc.eq l (Config.loc (conf id)).

Theorem from_config_spec : forall conf, is_ok (from_config conf) conf.
Proof.
unfold from_config, is_ok. intros. rewrite M.M.filter_spec, Rle_bool_true_iff.
+ rewrite M.set_spec, InA_map_iff; autoclass; []. setoid_rewrite Config.list_InA. split.
  - intros [[rc [Heq Hin]] ?]. split; trivial; [].
    destruct Hin as [id Hid]. exists id. now rewrite <- Hid, Heq.
  - intros [? [id Hid]]. split; trivial; [].
    exists (conf id). rewrite Hid. split; try reflexivity; []. now exists id.
+ intros x y Hxy. now rewrite Hxy.
Qed.

End Make.
