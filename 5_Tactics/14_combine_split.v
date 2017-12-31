Require Import List.
Import ListNotations.

Check split.
Compute split [(1, 2) ; (3, 4)].

Check combine.
Compute combine [1 ; 3] [2 ; 4].


Lemma woot : forall X Y t (r : list (X * Y)) x y, t = r -> (x, y) :: t = (x, y) :: r.
  intros. rewrite H. reflexivity.
Qed.

Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
(*  intros X Y l l1 l2 eq1. (* need to generalize the I.H. *) *)
  intros X Y l.
  induction l as [ | (x, y) l]. (* unfold the list for easier rewrite *)
  - (* nil *) intros l1 l2 eq1. inversion eq1. reflexivity.
  - (* cons n l *) simpl. destruct (split l).
    + (* case (l0, l1) *)
      intros l2 l3 eq1.
      inversion eq1. (* use the fact that x :: l0 = l2 and y :: l1 = l3 *)
      simpl. (* simplify to move out the params from combine *)
      apply woot. (* use our fancy lemma to simplify combine expr *)
      apply IHl. (* apply conclusion to finish with refl *)
      reflexivity.
Qed.
