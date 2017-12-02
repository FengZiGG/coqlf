Load MyLists.

Fixpoint even_members (l:natlist) : natlist :=
  match l with
  | []        => []
  | cons x l' => match (Nat.even x) with
                 | true  => cons x (even_members l')
                 | false => even_members l'
                 end
  end.

Fixpoint has_odd (l:natlist) :=
  match l with
  | []        => false
  | cons x l' => match (Nat.even x) with
                 | false => true
                 | true  => has_odd l'
                 end
  end.

Compute even_members [ 1 ; 2 ; 3 ].

(* This is a unit test *)
Example asdf : has_odd (even_members [ 1 ; 2 ; 3 ] ) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(* This is a proof (doesn't check a specific value, but checks for all possible values *)
Theorem even_members_list_only_even : (forall l : natlist, has_odd (even_members l) = false).
Proof.
  intros l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. case (Nat.even n) eqn:Hn. (* case with save hypothesis *)
    + (* case for odd numbers  *) simpl. rewrite Hn. rewrite IHl. reflexivity.
    + (* case for even numbers *) exact IHl.
Qed.