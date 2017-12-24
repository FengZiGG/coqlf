(* In addition to this definition, there are 2 more rules:
1. nat is injective, i.e. S n = S m -> n = m
2. All constructors are disjoint (i.e. there doesn't exist n s.t. S n = O)
*)
Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

(* inversion will generate all equations that it can infer from the rules above *)
Theorem test : forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m eq1.
  inversion eq1.
  reflexivity.
Qed.

Require Import List.
Import ListNotations.

Check cons.

Theorem inversion_ex2 : forall (n m : nat),
  n = m ->
  cons n nil = cons m nil.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.

Theorem inversion_ex2' : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
(*  rewrite H. (* ??? *) *)
  inversion H as [Hnm]. reflexivity.
Qed.