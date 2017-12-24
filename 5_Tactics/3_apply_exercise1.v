Require Import List.
Import ListNotations.

Search rev.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' eq1.
  rewrite eq1.
  symmetry.
(*  exact (rev_involutive l'). *)
  apply rev_involutive.
Qed.
