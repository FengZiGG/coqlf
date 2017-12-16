Load "4_more_poly_exercises.v".

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1 : map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof.
  reflexivity.
Qed.

Lemma very_useful : forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
  map f (l ++ [x]) = map f l ++ [f x].
Proof.
  intros X Y f l x.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite -> IHl. reflexivity. 
Qed.

(* map and rev commute *)
(*
if a(l) = map f l and b(l) = rev l, then a(b(l)) = map f (rev l) and b(a(l)) = rev (map f l)
In this case, * represents function composition.
*)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros x y f l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite <- IHl. rewrite very_useful. reflexivity.
Qed.