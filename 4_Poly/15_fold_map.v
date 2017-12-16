Load "13_fold_types_different.v".

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Check fold.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => cons (f x) y) l [].

Theorem fold_map_is_map : forall X Y (f : X -> Y) l, map f l = fold_map f l.
Proof.
  intros x y f l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHl. reflexivity.
Qed.