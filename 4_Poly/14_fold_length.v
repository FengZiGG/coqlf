Load "13_fold_types_different.v".

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Fixpoint list_length {x : Type} (l : list x) :=
  match l with
  | nil       => 0
  | cons _ l' => 1 + list_length l'
  end.

Example test_fold_length1 : fold_length [4;7;0] = 3.

Theorem fold_length_correct : forall X (l : list X), fold_length l = list_length l.
Proof.
  intros x l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite <- IHl. reflexivity.
Qed.
