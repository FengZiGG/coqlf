(*
Give an informal proof of this lemma that corresponds to your formal proof above:
Theorem: For any nats n m, beq_nat n m = beq_nat m n.
Proof: We will proof the theorem with induction on n.

Base case: forall m, beq_nat 0 m = beq_nat m 0. This is true by definition for beq_nat (case O, S _ and S _ O)

Inductive step: Assume that forall m, beq_nat n m = beq_nat m n.
Now, to prove forall m, beq_nat (S n) m = beq_nat m (S n), we'll consider two cases for m:
m: O: beq_nat (S n) O = beq_nat O (S n), which is true by definition for beq_nat
m: S m: beq_nat (S n) (S m) = beq_nat (S m) (S n). Now we can use the I.H. to conclude our proof.

We've shown that for all n, forall m, beq_nat n m = beq_nat m n.
*)
