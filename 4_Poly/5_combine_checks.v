Load "4_more_poly_exercises.v".

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

(*
It is easy at first to get (x,y) and X*Y confused. Remember that (x,y) is
a value built from two other values, while X*Y is a type built from two
other types. If x has type X and y has type Y, then (x,y) has type X*Y.
*)

Check pair 1 2.
Check prod nat nat.

Definition fst {X Y : Type} (p : X * Y) :=
  match p with
  | pair x _ => x
  end.

Definition snd {X Y : Type} (p : X * Y) :=
  match p with
  | pair _ y => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Compute combine [ 1 ; 3 ; 5 ] [ 2 ; 4 ; 6 ].

(* What is the type of combine (i.e., what does Check @combine print?) *)
(* The type is: combine: forall X Y : Type, list X -> list Y -> list X * Y *)
Check @combine.
Check combine.

(* What does `Compute (combine [1;2] [false;false;true;true]).` print? *)
(* It will print [ (1, false); (2, false) ] *)
Compute (combine [1;2] [false;false;true;true]).