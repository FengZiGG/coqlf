(*
apply L in H gives us a form of "forward reasoning": from L1 -> L2
and a hypothesis matching L1, it produces a hypothesis matching L2.

By contrast, apply L is "backward reasoning": it says that if we know L1 -> L2
and we are trying to prove L2, it suffices to prove L1.
*)

(* Hint: use plus_n_Sm *)
Check plus_n_Sm.

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
  intros n m eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].

  - (* zero *) intros m eq1. destruct m.
    + (* zero *) reflexivity.
    + (* S m  *) inversion eq1. (* contra *)
  - (* S n *) intros m eq1. destruct m.
    + (* zero *) inversion eq1. (* contra *)
    + (* S m *) apply eq_remove_S.
      (* At this point we have IHn': a -> b, and goal is b. We apply
      IHn' to change the goal *)
      apply IHn'.
      simpl in eq1. inversion eq1.
      rewrite <- plus_n_Sm in H0. rewrite <- plus_n_Sm in H0. inversion H0.
      reflexivity.
Qed.
