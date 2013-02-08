Require Export ZArith.

Lemma Z_eq_dec_true_to_Prop a b:
  (if Z.eq_dec a b then true else false) = true <-> a = b.
Proof.
  destruct (Z.eq_dec a b);split;auto.
  intro abs.
  inversion abs.
Qed.

Lemma Z_eq_dec_false_to_Prop a b :
  (if Z.eq_dec a b then true else false) = false <-> a <> b.
Proof.
  destruct (Z.eq_dec a b);split;auto.
  intro abs.
  inversion abs.
  intro abs;contradiction.
Qed.
