Load "list.v".

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Compute map (fun n => [n;n;n]) [1;5;4].

Fixpoint flat {X:Type} (l:list (list X)) : list X :=
  match l with
  | []        => []
  | cons x l' => app x (flat l')
  end.

Compute flat (map (fun n => [n;n;n]) [1;5;4]).

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) := flat (map f l).

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
  simpl. reflexivity.
Qed.