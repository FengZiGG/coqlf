beq_nat : Nat -> Nat -> Bool
beq_nat Z Z           = True
beq_nat Z (S m')      = False
beq_nat (S n') Z      = False
beq_nat (S n') (S m') = beq_nat n' m'

leb : Nat -> Nat -> Bool
leb Z _           = True
leb (S n') Z      = False
leb (S n') (S m') = leb n' m'

not_b : Bool -> Bool
not_b True  = False
not_b False = True

blt_nat : Nat -> Nat -> Bool
blt_nat n m = (leb n m) && (not_b (beq_nat n m))

test_blt_nat1 : (blt_nat 2 2) = False
test_blt_nat1 = Refl

test_blt_nat2 : (blt_nat 2 4) = True
test_blt_nat2 = Refl

test_blt_nat3 : (blt_nat 4 2) = False
test_blt_nat3 = Refl

postulate min_l : (n : Nat) -> (m : Nat) -> LTE n m -> minimum n m = n
postulate max_r : (n : Nat) -> (m : Nat) -> LTE n m -> maximum n m = m

simple_minmax : (n : Nat) -> (m : Nat) -> LTE n m -> LTE (minimum n m) (maximum n m)
simple_minmax n m lte_n_m = rewrite (min_l n m lte_n_m) in rewrite (max_r n m lte_n_m) in lte_n_m
