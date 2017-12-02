Require Import Nat.

Theorem plus_O_n : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n.
  induction n.
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n.
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. exact IHn.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  - (* base *) unfold add. reflexivity.
  - (* i.h. *) simpl. rewrite IHn. reflexivity.
Qed.

Lemma fancy_lemma : forall n m : nat, n + S m = S (m + n).
Proof.
  intros n m.
  induction n.
  - (* base *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* i.h. *) rewrite <- plus_n_Sm. simpl. rewrite <- plus_n_Sm. rewrite <- IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction m.
  - (* base *) simpl. exact (plus_O_n n).
  - (* i.h. *) simpl. exact (fancy_lemma n m).
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction p.
  - (* base *) rewrite plus_O_n. rewrite plus_O_n. reflexivity.
  - (* i.h. *) rewrite <- plus_n_Sm. rewrite fancy_lemma. rewrite plus_comm. rewrite IHp. rewrite plus_n_Sm. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O    => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | S (S n) => evenb n
    | S n => false
    | 0 => true
end.

Require Import Bool.
Search (negb (negb _) = _).
Print negb.
Print negb_involutive.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) rewrite IHn. rewrite negb_involutive. simpl. reflexivity.
Qed.

(* Briefly explain the difference between the tactics destruct and induction. *)
(* When we use destruct to analyze cases, we don't have hypothesis to re-use on the subterms, unlike induction. *)
