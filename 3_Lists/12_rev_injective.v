Load "8_list_exercises.v".

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros rev_l1_eq_rev_l2.
  induction l1.
  - (* base *) rewrite <- rev_involutive. rewrite <- rev_l1_eq_rev_l2. simpl. reflexivity.
  - (* i.h. *) rewrite <- rev_involutive. rewrite <- rev_l1_eq_rev_l2. rewrite -> rev_involutive. reflexivity.
Qed.

