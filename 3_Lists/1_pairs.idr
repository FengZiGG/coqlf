data Natprod : Type where
    Pair : Nat -> Nat -> Natprod

total fst' : Natprod -> Nat
fst' (Pair x _) = x

total snd' : Natprod -> Nat
snd' (Pair _ x) = x

total swap' : Natprod -> Natprod
swap' (Pair x y) = Pair y x

total surjective_pairing' : (n, m : Nat) -> Pair n m = Pair (fst' (Pair n m)) (snd' (Pair n m))
surjective_pairing' n m = Refl

total snd_fst_is_swap : (p : Natprod) -> Pair (snd' p) (fst' p) = swap' p
-- snd_fst_is_swap p = Refl
-- use the following to simulate Coq's 'destruct'
snd_fst_is_swap (Pair a b) = Refl

total fst_swap_is_snd : (p : Natprod) -> fst' (swap' p) = snd' p
fst_swap_is_snd p = rewrite sym (snd_fst_is_swap p) in Refl
