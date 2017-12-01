Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  (* use assert instead of rewriting lemma plus_O_n *)
  assert (H : 0 + n = n).
  {
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Axiom plus_comm : forall m n : nat, m + n = n + m.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite <- plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.

Theorem plus_rearrange_mytry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm n should do the trick! *)
  rewrite <- (plus_comm n).
  reflexivity.
Qed.

Theorem plus_rearrange_their_try : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : m + n = n + m).
  { rewrite plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.