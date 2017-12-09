Inductive a_tag : Type :=
  | Tag : nat -> a_tag.

Check Tag 3.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem beq_refl : forall x : nat, true = beq_nat x x.
Proof.
  intros x.
  induction x.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHx. reflexivity.
Qed.

Definition beq_tag (a b : a_tag) : bool :=
  match a, b with
  | Tag a', Tag b' => beq_nat a' b'
  end.

Compute eq 1 2.

Compute beq_tag (Tag 2) (Tag 5).
Compute beq_tag (Tag 5) (Tag 5).

Theorem beq_tag_refl : forall x, true = beq_tag x x.
Proof.
  intros x.
  simpl.
  unfold beq_tag.
  case x.
  - (* match b with Tag b' => beq_nat a' b', but a' = b' because of beq_tag x x *)
  exact beq_refl.
Qed.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : a_tag -> nat -> partial_map -> partial_map.

Definition update (d : partial_map)
                  (x : a_tag) (value : nat)
                  : partial_map :=
  record x value d.

Definition test  := update empty (Tag 1) 2.
Definition test' := update test (Tag 3) 4.
Compute test'.

Inductive natoption : Type :=
  | None : natoption
  | Some : nat -> natoption.

Fixpoint find (x : a_tag) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_tag x y
                     then Some v
                     else find x d'
  end.

Compute find (Tag 1) test'.
Compute find (Tag 2) test'.
Compute find (Tag 3) test'.
Compute find (Tag 4) test'.
Compute find (Tag 5) test'.


Theorem update_eq : forall (d : partial_map) (x : a_tag) (v: nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.
  rewrite <- beq_tag_refl.
  reflexivity.
Qed.


Theorem update_neq : forall (d : partial_map) (x y : a_tag) (o: nat),
    beq_tag x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros beq_tag_x_neq_y.
  simpl.
  rewrite beq_tag_x_neq_y.
  reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(*
How many elements does the type baz have?
Since the inductive definition does not have a base case, we have 0 elements.
We can't construct any elements.
*)

(*
Found this after my answer:
https://cs.stackexchange.com/questions/29365/baz-num-elts-exercise-from-software-foundations?answertab=votes#tab-top

There's a bijection between baz and False.
*)

Definition injective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => forall x1 x2, f1 x1 = f1 x2 -> x1 = x2.
Definition surjective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => forall x1, exists x2, f1 x2 = x1.
Definition bijective : forall {t1 t2}, (t1 -> t2) -> Prop := fun t1 t2 f1 => injective f1 /\ surjective f1.

Theorem baz_False : baz -> False.
Proof.
  induction 1. exact IHbaz. exact IHbaz.
Qed.

Goal exists f1 : baz -> False, bijective f1.
Proof.
  exists baz_False. unfold bijective, injective, surjective. firstorder.
  assert (H2 := baz_False x1). firstorder.
  assert (H2 := x1). firstorder.
Qed.
