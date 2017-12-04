Load "MyLists".

Require Import PeanoNat.

Fixpoint find_n_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil       => 42 (* arbitrary! *)
  | cons a l' => match Nat.eqb a n with
               | true  => a
               | false => find_n_bad l' n
               end
  end.

Example find_n_bad_1 : find_n_bad [ 1 ; 2 ; 3 ] 1 = 1.
Proof.
  simpl. reflexivity.
Qed.

Example find_n_bad_2 : find_n_bad [ 1 ; 2 ; 3 ] 2 = 2.
Proof.
  simpl. reflexivity.
Qed.

Example find_n_bad_3 : find_n_bad [ 1 ; 2 ; 3 ] 42 = 42.
Proof.
  reflexivity.
Qed.

Example find_n_bad_4 : find_n_bad [ 1 ; 2 ; 3 ; 42 ] 42 = 42.
Proof.
  reflexivity.
Qed.

(* If we can find_n_bad we don't know if 42 exists in the list, or it's a value returned as a result that
   it doesn't exist in the list. Maybe to the rescue! *)

Inductive Maybe : Type :=
  | Just : nat -> Maybe
  | None : Maybe.

Compute Just 3.
Compute None.

Fixpoint find_n_good (l:natlist) (n:nat) : Maybe :=
  match l with
  | nil       => None (* arbitrary! *)
  | cons a l' => match Nat.eqb a n with
               | true  => Just a
               | false => find_n_good l' n
               end
  end.

Example find_n_good_1 : find_n_good [ 1 ; 2 ; 3 ] 1 = Just 1.
Proof.
  reflexivity.
Qed.

Example find_n_good_2 : find_n_good [ 1 ; 2 ; 3 ] 2 = Just 2.
Proof.
  reflexivity.
Qed.

Example find_n_good_3 : find_n_good [ 1 ; 2 ; 3 ] 42 = None.
Proof.
  reflexivity.
Qed.

Example find_n_good_4 : find_n_good [ 1 ; 2 ; 3 ; 42 ] 42 = Just 42.
Proof.
  reflexivity.
Qed.

(* The function below pulls the nat out of a Maybe, returning a supplied default in the None case. *)

Definition maybe_elim (d : nat) (o : Maybe) : nat :=
  match o with
  | Just n' => n'
  | None    => d
  end.

Compute maybe_elim 3 (Just 4).
Compute maybe_elim 4 None.