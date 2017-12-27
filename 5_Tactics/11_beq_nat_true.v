Require Import Arith.

Search (_ =? _).

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  destruct n.
  - (* zero *) intros m. intros eq1. destruct m.
    + (* zero *) reflexivity.
    + (* S m *) apply beq_nat_true. exact eq1.
  - (* S n *) intros m. intros eq1. destruct m.
    + (* zero *) inversion eq1.
    + (* S m *) apply beq_nat_true. exact eq1.
Qed.