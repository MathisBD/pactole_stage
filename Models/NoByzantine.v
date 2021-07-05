Require Import SetoidClass.
Require Import Pactole.Core.Identifiers.
Require Import Pactole.Core.State.
Require Import Pactole.Core.Configuration.

(** To use these results, just provide an instance of the [NoByzantine] class. *)

Section NoByzantine.

Context `{Names}.
Context `{St : State}.

Class NoByzantine := { nB_eq_0 : nB = 0 }.

Context {NoByz : NoByzantine}.
(** There is no byzantine robot so we can simplify properties
    about identifiers and configurations. *)
Lemma no_byz : forall (id : ident) P, (forall g, P (Good g)) -> P id.
Proof using NoByz.
intros [g | b] P HP.
+ apply HP.
+ assert (Hnil : Bnames = nil) by now rewrite <- List.length_zero_iff_nil, Bnames_length, nB_eq_0.
  elim (@List.in_nil _ b). rewrite <- Hnil. apply In_Bnames.
Qed.

Lemma no_byz_eq : forall config1 config2 : configuration,
  (forall g, config1 (Good g) == config2 (Good g)) -> config1 == config2.
Proof using NoByz.
intros config1 config2 Heq id. apply (no_byz id). intro g. apply Heq.
Qed.

End NoByzantine.
