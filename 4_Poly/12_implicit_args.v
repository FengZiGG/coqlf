Load "list.v".

Fixpoint filter (X:Type) (test: X -> bool) (l:list X) : (list X) :=
  match l with
  | []      => []
  | x :: l' => if test x then x :: filter X test l' else filter X test l'
  end.

Fixpoint map (X Y:Type) (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map X Y f t)
  end.

Compute filter nat (fun x => Nat.eqb x 1) [1; 2; 3].
Compute map nat nat (fun x => x + 1) [4; 5; 6].
Compute map nat bool (fun x => Nat.eqb x 1) [1; 2; 3; 1].
