Require Import Arith.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n. (* more general I.H. by not intro-ing m *)
    + destruct m.
      - reflexivity.
      - reflexivity.
    + destruct m.
      - reflexivity.
      - apply IHn.
Qed.