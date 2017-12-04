Load "MyLists".

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None    => d
  end.

Definition hd_error (l:natlist) : natoption :=
  match l with
  | []         => None
  | (cons x _) => Some x
  end.

Example test_hd_error1 : hd_error [] = None.
Proof.
  simpl. reflexivity.
Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof.
  simpl. reflexivity.
Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof.
  simpl. reflexivity.
Qed.

