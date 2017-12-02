Load "4_bag_functions".

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | []        => []
  | cons x s' => match (Nat.eqb x v) with
                 | true  => s'
                 | false => cons x (remove_one v s')
                 end
  end.

Example test_remove_one1 : count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_remove_one2 : count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_remove_one3 : count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_remove_one4 : count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | []        => []
  | cons x s' => match (Nat.eqb x v) with
                 | true  => remove_all v s'
                 | false => cons x (remove_all v s')
                 end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | []         => true
  | cons x s1' => match (member x s2) with
                  | true  => subset s1' (remove_one x s2)
                  | false => false
                  end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof.
  simpl.
  reflexivity.
Qed.
