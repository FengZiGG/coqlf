Require Import List.
Import ListNotations.

Example inversion_ex_6 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] -> y :: l = z :: j -> x = z.
Proof.
  intros X x y z l j eq1 eq2.
(*
If we use inversion on eq1, Coq notices that the goal we are
working on is impossible, and therefore removes it from further consideration.
This is an instance of a logical principle known as the principle of explosion,
which asserts that a contradictory hypothesis entails anything
*)
  inversion eq1.
Qed.
