Load "4_more_poly_exercises.v".

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | cons (x, y) l' => (cons x (fst (split l')), cons y (snd (split l')))
  end.

Example test_split : split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  simpl. reflexivity.
Qed.
