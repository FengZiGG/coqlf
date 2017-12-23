Definition nat := forall X : Type, (X -> X) -> X -> X.

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Definition three : nat := @doit3times.

(* Used defs from https://en.wikipedia.org/wiki/Church_encoding#Table_of_functions_on_Church_numerals *)
Definition succ (n : nat) : nat := fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : nat) : nat := fun (X : Type) (f : X -> X) (x : X) => m X f (n X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 : plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : nat) : nat := fun (X : Type) (f : X -> X) (x : X) => m X (n X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three two = plus (mult two (mult two two)) one. 
Proof. reflexivity. Qed.
Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.