Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Check bool_cons. (* bool_cons : bool -> boollist -> boollist *)
Compute bool_cons true bool_nil.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check cons. (* cons : forall X : Type, X -> list X -> list X *)
Compute cons bool true (nil bool).

Check list.

(*
A comment on dependent types
Note that this is different from polymorphism which includes the type as an argument.
*)
Check cons nat.
Check cons bool.

Definition is_nil (X : Type) (l : list X) :=
  match l with
  | nil _ => true
  | _     => false
  end.

Fixpoint list_length (x : Type) (l : list x) :=
  match l with
  | nil _       => 0
  | cons _ _ l' => 1 + list_length x l'
  end.

Compute list_length bool (cons bool true (nil bool)).


Check cons _ 1 (cons _ 2 (nil _)).

(*
This powerful facility means we don't always have to write explicit
type annotations everywhere, although explicit type annotations are
still quite useful as documentation and sanity checks, so we will
continue to use them most of the time.
*)

(*
The Arguments directive specifies the name of the function
(or constructor) and then lists its argument names, with curly
braces around any arguments to be treated as implicit. (If some
arguments of a definition don't have a name, as is often the case
for constructors, they can be marked with a wildcard pattern _.)
*)
Arguments nil {X}.
Arguments cons {X}.
Arguments list_length {x} l.

Compute cons 1 (cons 2 nil).
Compute list_length (cons 1 (cons 2 nil)).

(*
Alternatively, we can declare an argument to be implicit when defining
the function itself, by surrounding it in curly braces instead of parens.
*)
Fixpoint list_length' {x : Type} (l : list x) :=
  match l with
  | nil       => 0
  | cons _ l' => 1 + list_length' l'
  end.

Check list_length'.

Compute list_length' (cons 1 (cons 2 nil)).

Definition cool_pair {X : Type} (x y : X) := fun a => if (Nat.eqb a 1) then x else y.

Compute ((cool_pair 10 20) 1).
Compute ((cool_pair 10 20) 2).