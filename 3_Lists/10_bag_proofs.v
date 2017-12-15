Load "5_bag_more_functions.v".

Theorem count_member_nonzero : forall (s : bag), Nat.leb 1 (count 1 (cons 1 s)) = true.
Proof.
  simpl. intros proof_bag. reflexivity.
Qed.

Theorem ble_n_Sn : forall n, Nat.leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_decreases_count: forall (s : bag), Nat.leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros.
  induction s.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. case (Nat.eqb n 0) eqn:Hn.
    + (* n == 0 *) simpl. rewrite ble_n_Sn. reflexivity.
    + (* n != 0 *) simpl. rewrite Hn. rewrite IHs. reflexivity.
Qed.