Module NatPlayground.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition not_b (a : bool) :=
  match a with
  | true => false
  | false => true
  end.

Definition blt_nat (n m : nat) : bool := andb (leb n m) (not_b (beq_nat n m)).


Example test_blt_nat1: (blt_nat 2 2) = false.
Proof.
reflexivity.
Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof.
reflexivity.
Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof.
reflexivity.
Qed.

Theorem simple_minmax : forall n m, n <= m -> min n m <= max n m.
Proof.
  intros.
  rewrite min_l.
  rewrite max_r.
  assumption. assumption. assumption.
Qed.

End NatPlayground.

