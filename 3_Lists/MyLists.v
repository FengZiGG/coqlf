Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist. (* cons is product type *)

(* natlist is union of nil and cons *)

Definition bag := natlist.

Compute (cons 1 (cons 2 (cons 3 nil))).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Compute [ 1 ; 2 ; 3 ].

Fixpoint repeat (n count : nat) :=
  match count with
  | 0         => [ ]
  | S count'  => cons n (repeat n count')
  end.

Compute repeat 1 10.

Fixpoint length (l:natlist) : nat :=
  match l with
  | [ ]         => 0
  | (cons _ n') => 1 + (length n')
  end.

Compute length [ 1 ; 2 ; 3 ].

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [ ]          => l2
  | (cons x l1') => (cons x (app l1' l2))
  end.

Compute app [ 1 ; 2 ; 3 ] [ 4 ; 5 ; 6 ].

Notation "x ++ y" := (app x y).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.


Definition hd' (default:nat) (l:natlist) : nat :=
  match l with
  | []         => default
  | (cons x _) => x
  end.

Definition tl' (l:natlist) : natlist :=
  match l with
  | [] => []
  | (cons _ y)  => y
  end.

Compute hd' 123 [ 1 ; 2 ; 3 ].
Compute hd' 123 [ ].
Compute tl' [ 1 ; 2 ; 3 ].
