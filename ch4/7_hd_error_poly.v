Load "4_more_poly_exercises.v".

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | S m' => false
         end
  | S n' => match m with
            | 0 => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | (cons x _) => Some x
  end.


Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof.
  simpl. reflexivity.
Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof.
  simpl. reflexivity.
Qed.