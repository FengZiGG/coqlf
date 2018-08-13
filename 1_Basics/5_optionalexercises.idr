andb : Bool -> Bool -> Bool
andb True True = True
andb _ _       = False

total andb_true_elim2 : (b : Bool) -> (c : Bool) -> andb b c = True -> c = True
andb_true_elim2 b     True  b_and_c = rewrite (sym b_and_c) in Refl
andb_true_elim2 True  False b_and_c = rewrite (sym b_and_c) in Refl
andb_true_elim2 False False b_and_c = rewrite (sym b_and_c) in Refl

beq_nat : Nat -> Nat -> Bool
beq_nat Z Z           = True
beq_nat Z (S m')      = False
beq_nat (S n') Z      = False
beq_nat (S n') (S m') = beq_nat n' m'

zero_nbeq_plus_1 : (n : Nat) -> beq_nat 0 (n + 1) = False
zero_nbeq_plus_1 Z      = Refl
zero_nbeq_plus_1 (S n') = Refl

testfact : (n : Nat) -> Nat
testfact Z = 1
testfact n = n * (testfact (pred n))

testfact' : (n : Nat) -> Nat
testfact' Z      = 1
testfact' (S n') = (S n') * (testfact' n')
