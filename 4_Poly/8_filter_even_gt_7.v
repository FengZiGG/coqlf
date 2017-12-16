Load "list.v".

Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : (list X) :=
  match l with
  | []      => []
  | x :: l' => if test x then x :: filter test l' else filter test l'
  end.

Require Import PeanoNat.

Search (nat -> bool).

Definition filter_even_gt7 (l : list nat) : list nat := filter (fun x => andb (7 <=? x) (Nat.even x)) l.

Compute filter_even_gt7 [8 ; 9 ; 10 ; 11].

Example test_filter_even_gt7_1 : filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
  simpl. reflexivity.
Qed.

Example test_filter_even_gt7_2 : filter_even_gt7 [5;2;6;19;129] = [].
Proof.
  simpl. reflexivity.
Qed.
