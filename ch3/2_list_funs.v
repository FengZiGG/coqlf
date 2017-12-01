Load MyLists.
(* list_funs exercises *)

Check natlist.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | [ ]       => []
  | cons 0 l' => (nonzeros l')
  | cons x l' => cons x (nonzeros l')
  end.

Example test_nonzeros : nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
  simpl.
  reflexivity.
Qed.

Search (nat -> bool).

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | []        => []
  | cons x l' => match (Nat.odd x) with
                 | true  => cons x (oddmembers l')
                 | false => oddmembers l'
                 end
  end.

Example test_oddmembers : oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  simpl.
  reflexivity.
Qed.

Definition countoddmembers (l:natlist) : nat := length (oddmembers l).

Example test_countoddmembers1 : countoddmembers [1;0;3;1;4;5] = 4.
Proof.
  unfold countoddmembers.
  simpl.
  reflexivity.
Qed.

Example test_countoddmembers2 : countoddmembers [0;2;4] = 0.
Proof.
  unfold countoddmembers.
  simpl.
  reflexivity.
Qed.

Example test_countoddmembers3 : countoddmembers nil = 0.
Proof.
  unfold countoddmembers.
  simpl.
  reflexivity.
Qed.