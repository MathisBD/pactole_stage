Require Export SetoidDec.
Require Export Pactole.Util.Coqlib.
Require Export Pactole.Util.Ratio.
Require Pactole.Util.Stream.
Require Pactole.Util.Lexprod.
Require Export Pactole.Core.Robots.
Require Export Pactole.Core.RobotInfo.
Require Export Pactole.Core.Configurations.
Require Export Pactole.Spectra.Definition.
Require Export Pactole.Core.Formalism.

Remove Hints eq_setoid : Setoid.

(** For simplicity, we gather into one definition all the classes that must be instanciated
    in order to define a complete and working environment. *)
Class GlobalDefinitions := {
  (* Number of good and Byzantine robots *)
  glob_nG : nat;
  glob_nB : nat;
  (** The space in which robots evolve *)
  glob_Loc :> Location;
  (** The state of robots (must contain at least the current location) *)
  glob_info : Type;
  glob_State :> @State glob_Loc glob_info;
  (** The spectrum: what robots can see from their surroundings *)
  glob_spect :> @Spectrum _ _ glob_State (Robots.Robots glob_nG glob_nB);
  (** The output type of robograms: some information that we can use to get a target location *)
  glob_Trobot : Type;
  glob_robot_choice :> robot_choice glob_Trobot;
  (** The frame decision made by the demon, used to build the frame change *)
  glob_Tframe : Type;
  glob_frame_choice :> frame_choice glob_Tframe;
  (** The influence of the demon on the state update of robots, when active *)
  glob_Tactive : Type;
  glob_update_choice :> update_choice glob_Tactive;
  (** The influence of the demon on the state update of robots, when inactive *)
  glob_Tinactive : Type;
  glob_inactive_choice :> inactive_choice glob_Tinactive;
  (** How a robots state is updated:
      - if active, using the result of the robogram and the decision from the demon
      - if inactive, using only the decision from the demon *)
  glob_update_function :> @update_function _ _ glob_State (Robots.Robots glob_nG glob_nB) _ _ _
                            glob_robot_choice glob_frame_choice glob_update_choice;
  glob_inactive_function :> @inactive_function _ _ glob_State (Robots.Robots glob_nG glob_nB) _
                              glob_inactive_choice
  }.

Global Instance GlobRobots `(GlobalDefinitions) : Names := Robots.Robots glob_nG glob_nB.