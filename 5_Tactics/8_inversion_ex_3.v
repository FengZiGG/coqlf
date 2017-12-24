Require Import List.
Import ListNotations.

Example inversion_ex_3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1.
  inversion eq2.
  symmetry.
  exact H0.
Qed.