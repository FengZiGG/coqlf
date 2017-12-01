Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 2 3). (* pair 2 3 : natprod *)

Definition fst' ( p : natprod ) :=
  match p with
  | pair x y => x
  end.

Definition snd' ( p : natprod ) :=
  match p with
  | pair x y => y
  end.

Definition swap' ( p : natprod ) :=
  match p with
  | pair x y => pair y x
  end.


(* Since pairs are used quite a bit, it is nice to be able to write
them with the standard mathematical notation (x,y) instead of pair x y. *)
Notation "( x , y )" := (pair x y).

Check (2, 5).

Compute (fst' (2, 3)).
Compute (snd' (4, 5)).
Compute (swap' (6, 7)).

Theorem surjective_pairing' : forall (n m : nat), (n,m) = (fst' (n, m), snd' (n, m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod), p = (fst' p, snd' p).
Proof.
  intros p.
  destruct p. (* We have to expose the structure of p so that we can simpl *)
  simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod), (snd' p, fst' p) = swap' p.
Proof.
  intros p.
  destruct p.
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod), fst' (swap' p) = snd' p.
Proof.
  intros p.
  rewrite <- snd_fst_is_swap.
  simpl.
  reflexivity.
Qed.