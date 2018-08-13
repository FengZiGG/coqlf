plus_O_n : (n : Nat) -> 0 + n = n
plus_O_n n = Refl

mult_0_plus' : (n, m : Nat) -> (0 + n) * m = n * m
mult_0_plus' n m = Refl

postulate plus_comm : (m, n : Nat) -> m + n = n + m

plus_rearrange : (n, m, p, q : Nat) -> (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange n m p q = rewrite plus_comm n m in Refl

total sym' : (a = b) -> (b = a)
sym' Refl = Refl
