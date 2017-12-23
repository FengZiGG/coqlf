Load "list.v".

Require Import PeanoNat.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if Nat.eqb n O then Some a else nth_error l' (pred n)
     end.

(* Write an informal proof of the following theorem: *)
(* forall X n l, length l = n -> @nth_error X l n = None *)

(*
Suppose l is an arbitrary list, and assume that n is the length of the list.
We prove the claim by induction on l.

For the base case, we have that nth_error [] 0 = None, which is correct.

For the inductive step, we assume that nth_error xs n = None holds.

To prove the x:xs case, first note that length x:xs = 1 + length xs, in other words 1 + n.

For proving that nth_error x:xs n' = None, by the a :: l' definition of nth_error we can
rewrite nth_error xs n (since n' > 0). But, by I.H. this is exactly None.
*)