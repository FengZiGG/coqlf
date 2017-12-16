Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
