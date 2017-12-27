(*
Give a careful informal proof of beq_nat_true, being as explicit as possible about quantifiers.

Theorem beq_nat_true : forall n m, beq_nat n m = true -> n = m.
Proof by cases:

Assume n = zero: forall m, beq_nat 0 m = true -> 0 = m.
  Assume m = zero: beq_nat 0 0 = true -> 0 = 0. we just apply beq_nat_true in this case.

  Assume m = S m': beq_nat 0 (S m') = true -> 0 = (S m'). we just apply beq_nat_true in this case.

Assume n = S n'
  Assume m = zero: beq_nat (S n') 0 = true -> (S n') = 0. we have
    beq_nat n' 0 = true -> n' = 0 we just apply beq_nat_true in this case.

  Assume m = S m': beq_nat (S n') (S m') = true -> (S n') = (S m'). we just apply beq_nat_true in this case.

*)