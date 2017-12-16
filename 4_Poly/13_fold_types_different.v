Load "list.v".

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil    => b
  | h :: t => f h (fold f t b)
  end.

Compute fold (fun x y => x + y) [1;2;3] 0.
Check fold (fun x y => x + y) [1;2;3] 0. (* X = Y *)

Compute fold cons [1;2;3] []. (* X = nat, Y = list nat *)
Check fold cons [1;2;3] [].
Check cons.