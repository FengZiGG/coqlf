Require Import List.
Import ListNotations.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [ q ; o ] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly3 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [ q ; o ] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite (eq2 n m eq1).
  reflexivity.
Qed.
