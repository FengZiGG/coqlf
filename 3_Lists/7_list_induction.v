Load MyLists.

Theorem app_assoc : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite <- IHl1. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil      => nil
  | cons h t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof.
  reflexivity.
Qed.

Example test_rev2: rev nil = nil.
Proof.
  reflexivity.
Qed.

Lemma my_fancy_lemma : forall l1 l2 : natlist, length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2.
  induction l1.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHl1. reflexivity.
Qed.

Require Import PeanoNat.

Search (S _ = _ + 1).
Search (_ + 1 = S _).
Check Nat.add_1_r.

Lemma testlemma : forall n : nat, n + 1 = S n.
Proof.
  intros n.
  induction n.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHn. reflexivity.
Qed.

Axiom plus_comm : forall m n : nat, m + n = n + m.

Theorem rev_length_mytry : forall l : natlist, length (rev l) = length l.
Proof.
  intros l.
  induction l.
  - (* base *) simpl. reflexivity.
(*  - (* i.h. *) simpl. rewrite -> my_fancy_lemma, plus_comm. simpl. rewrite IHl. reflexivity. *)
  - (* i.h. *) simpl. rewrite -> my_fancy_lemma. simpl. rewrite -> IHl. exact (Nat.add_1_r (length l)).
Qed.