Load "10_map_rev.v".

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  unfold prod_uncurry.
  unfold prod_curry.
  simpl.
  reflexivity.
Qed.


Lemma wat : forall (X Y : Type) (p : X * Y), (fst p, snd p) = p.
Proof.
  intros X Y p.
  destruct p. (* destructure *)
  simpl.
  reflexivity.
Qed.

Lemma wat' : forall (X Y : Type) (p : X * Y), (fst p, snd p) = p.
Proof.
  intros X Y p.
  case p. (* case analysis on the p : prod *)
  (* the only case is that it's a pair since it's the only constructor for prod *)
  intros proof_x proof_y.
  simpl.
  reflexivity.
Qed.

Print pair.
Print prod.

Check wat.
Search (forall (X Y : Type) (p : X * Y), (fst p, snd p) = p).

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  unfold prod_uncurry.
  unfold prod_curry.
  rewrite wat.
  reflexivity.
Qed.
