(*
Definition plus: n = 0 + n, S(m) + n = S(m + n).
Lemma fancy_lemma: n + S m = S (m + n).

Theorem: Addition is commutative. For any n m, n + m = m + n.

Proof: We will prove the theorem by induction on n.

Base case:      n = 0:     0 + m = m + 0. This follows directly from the definition of +.

Inductive step: n = k + 1: Assuming k + m = m + k, we need to show that S k + m = m + S k.

(* goal *) Sk + m   = m + Sk
(* plus *) Sk + m   = S(k + m)
(* i.h. *) S(k + m) = S(m + k)
(* f.l. *) S(m + k) = m + Sk

Thus, addition is commutative. Qed.

*)

(*
Definition beq_nat(0, 0) = T
           beq_nat(0, m) = F (m > 0)
           beq_nat(n, 0) = F (n > 0)
           beq_nat(n, m) = beq_nat(n - 1, m - 1)

Theorem: true = beq_nat n n for any n.
Proof: We will prove the theorem by induction on n.

Base case: n = 0: true = beq_nat 0 0. This follows by definition of beq_nat
Inductive step: n = k + 1: Assuming true = beq_nat k k, we need to prove that true = beq_nat (k + 1) (k + 1).
If we expand beq_nat (k + 1) (k + 1) by definition, we get that it's equal to beq_nat k k, which is true by I.H.

Qed.

*)
Require Import PeanoNat.

Check beq_nat.