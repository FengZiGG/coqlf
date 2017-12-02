Load MyLists.

Search (nat -> nat -> bool).

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | []        => 0
  | cons x s' => match (Nat.eqb x v) with
                | true  => 1 + (count v s')
                | false => count v s'
                end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
  simpl.
  reflexivity.
Qed.

Definition add (v:nat) (s:bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Definition member (v:nat) (s:bag) : bool := negb (Nat.leb (count v s) 0).

Example test_member1: member 1 [1;4;1] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof.
  simpl.
  reflexivity.
Qed.