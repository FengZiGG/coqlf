total identity_fn_applied_twice : (b : Bool) -> (f : Bool -> Bool) -> ((x : Bool) -> f x = x) -> (f (f b) = b)
identity_fn_applied_twice b f f_id = rewrite (f_id b) in rewrite (f_id b) in Refl

andb : Bool -> Bool -> Bool
andb True True = True
andb _ _       = False

orb : Bool -> Bool -> Bool
orb True _ = True
orb _ True = True
orb _ _    = False

andb_eq_orb : (b : Bool) -> (c : Bool) -> andb b c = orb b c -> b = c
andb_eq_orb b     c     andb_is_orb = rewrite andb_eq_orb b c andb_is_orb in Refl

data BinaryNat : Type where
    O : BinaryNat
    E : BinaryNat -> BinaryNat
    D : BinaryNat -> BinaryNat

incr : BinaryNat -> BinaryNat
incr O         = E O
incr (E n)     = D n
incr (D (E n)) = D (D n)
incr (D n)     = D (E n)

BinToNat : BinaryNat -> Nat
BinToNat O = Z
BinToNat (E n) = 1 + BinToNat n
BinToNat (D n) = 2 + BinToNat n

test_bin_incr1 : BinToNat O = 0
test_bin_incr1 = Refl

test_bin_incr2 : BinToNat (incr O) = 1
test_bin_incr2 = Refl

test_bin_incr3 : BinToNat (incr (incr O)) = 2
test_bin_incr3 = Refl

test_bin_incr4 : BinToNat (incr (incr (incr O))) = 3
test_bin_incr4 = Refl

test_bin_incr5 : BinToNat (incr (incr (incr (incr O)))) = 4
test_bin_incr5 = Refl
