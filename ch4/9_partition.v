Load "8_filter_even_gt_7.v".

Require Import PeanoNat.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X := pair (filter test l) (filter (fun x => negb (test x)) l).

Check pair.
Search (nat -> bool).

Example test_partition1: partition Nat.odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
  simpl. reflexivity.
Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
  simpl. reflexivity.
Qed.
