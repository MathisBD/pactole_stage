Require Import Morphisms.
Require Import Rbase.
Require Import Psatz.
Require Import SetoidDec.
Require Import SetoidClass.
Require Import Pactole.Util.Preliminary.

(** A ratio (of some quantity). *)
Definition ratio := {x : R | 0 <= x <= 1}%R.

Definition proj_ratio : ratio -> R := @proj1_sig _ _.

Instance proj_ratio_compat : Proper (@equiv _ sig_Setoid ==> equiv) proj_ratio.
Proof. intros ? ? Heq. apply Heq. Qed.

Coercion proj_ratio : ratio >-> R.

Definition ratio_0 : ratio.
Proof. refine (exist _ 0%R _). abstract lra. Defined.

Definition ratio_1_2 : ratio.
Proof. refine (exist _ (1/2)%R _). abstract lra. Defined.

Definition ratio_1 : ratio.
Proof. refine (exist _ 1%R _). abstract lra. Defined.

(* A trajectory seen as a path inside the space. *)
(* FIXME: I should use typeclasses to avoid rthe explicit parameter T.
          Otherwise, path cannot be used as a target class for coercions. *)
Record path T `{Setoid T}:= {
  path_f :> ratio -> T;
  path_compat :> Proper (equiv ==> equiv) path_f }.
Arguments path_f {T} {_} _ _.

Instance path_Setoid T {S : Setoid T} : Setoid (path T) := { equiv := fun x y => path_f x == y }.
Proof. split.
+ intro. reflexivity.
+ intros ? ? ?. now symmetry.
+ intros ? ? ? ? ?. etransitivity; eauto.
Defined.

Instance path_full_compat {T} `(Setoid T): Proper (equiv ==> equiv ==> equiv) path_f.
Proof.
intros p p' Hp x y Hxy. transitivity (path_f p y).
- now apply path_compat.
- apply Hp.
Qed.

Definition lift_path {T U} `{Setoid T, Setoid U} (f : T -> U)
                     {Hf : Proper (equiv ==> equiv) f} (p : path T) : path U.
refine (Build_path _ _ (fun x => f (p x)) _).
Proof. intros x y Hxy. now apply Hf, path_compat. Defined.
Arguments lift_path T U _ _ f _ p /.

Instance lift_path_compat {T U} {HT : Setoid T} {HU : Setoid U}
  : forall f (Hf : Proper (equiv ==> equiv) f), Proper (equiv ==> equiv) (@lift_path T U HT HU f Hf).
Proof. repeat intro. simpl. auto. Qed.

Lemma lift_path_extensionality_compat {T U} {HT : Setoid T} {HU : Setoid U} :
  forall (f g : T -> U) (Hf : Proper (equiv ==> equiv) f) (Hg : Proper (equiv ==> equiv) g),
  (equiv ==> equiv)%signature f g ->
  (equiv ==> equiv)%signature (lift_path f) (lift_path g).
Proof. intros f g Hf Hg Hfg p p' Hp x. simpl. apply Hfg, Hp. Qed.