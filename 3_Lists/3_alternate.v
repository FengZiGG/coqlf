Load MyLists.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | []         => l2
  | cons x l1' => match l2 with
                  | []         => cons x (alternate l1' l2)
                  | cons y l2' => cons x (cons y (alternate l1' l2'))
                  end
  end.

Example test_alternate1 : alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
  simpl.
  reflexivity.
Qed.

Example test_alternate2 : alternate [1] [4;5;6] = [1;4;5;6].
Proof.
  simpl.
  reflexivity.
Qed.

Example test_alternate3 : alternate [1;2;3] [4] = [1;4;2;3].
Proof.
  simpl.
  reflexivity.
Qed.

Example test_alternate4 : alternate [] [20;30] = [20;30].
Proof.
  simpl.
  reflexivity.
Qed.

