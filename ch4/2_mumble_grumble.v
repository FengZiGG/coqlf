Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(*
Which of the following are well-typed elements of grumble X for some type X?
*)
(* Check d (b a 5). (* isn't because the type X is not passed *) *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). (* isn't because (b c 0) isn't bool *) *)
Check c.