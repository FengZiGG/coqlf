Require Import Arith.
Require Import List.
Import ListNotations.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l eq1.
  (* Bring back n to the quantifier for a more general IH *)
  generalize dependent n.
  induction l.
    - (* nil *) simpl. intros n eq2. reflexivity.
    - (* cons n l' *) intros n eq2. simpl. destruct n.
      + (* zero *) inversion eq2. (* length cons n l = 0 is contra *)
      + (* S n *) simpl. apply IHl. inversion eq2. reflexivity. 
Qed.