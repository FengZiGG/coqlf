Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X}.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X:Type), forall l:list X, l ++ [] = l.
Proof.
  intros x l.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite IHl. reflexivity.
Qed.

Search (_ = _ + 0).

Lemma app_length : forall (X:Type) (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros x l1 l2.
  induction l1.
  - (* base *) simpl. reflexivity.
  - (* i.h. *) simpl. rewrite <- IHl1. reflexivity.
Qed.
