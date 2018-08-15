import MyLists

nonzeros : Natlist -> Natlist
nonzeros Nil = Nil
nonzeros (Cons Z l') = nonzeros l'
nonzeros (Cons x l') = Cons x (nonzeros l')

test_nonzeros : nonzeros (Cons Z (Cons 1 (Cons Z (Cons 2 (Cons 3 (Cons Z (Cons Z Nil))))))) = (Cons 1 (Cons 2 (Cons 3 Nil)))
test_nonzeros = Refl

even : (n : Nat) -> Bool
even (S (S n')) = even n'
even (S n')     = False
even Z          = True

oddmembers : Natlist -> Natlist
oddmembers Nil          = Nil
oddmembers (Cons x l') = case (even x) of
                             True => oddmembers l'
                             _    => Cons x (oddmembers l')

test_oddmembers : oddmembers (Cons Z (Cons 1 (Cons Z (Cons 2 (Cons 3 (Cons Z (Cons Z Nil))))))) = (Cons 1 (Cons 3 Nil))
test_oddmembers = Refl

countoddmembers : Natlist -> Nat
countoddmembers l = length (oddmembers l)

test_countoddmembers1 : countoddmembers (Cons 1 (Cons Z (Cons 3 (Cons 1 (Cons 4 (Cons 5 Nil)))))) = 4
test_countoddmembers1 = Refl

test_countoddmembers2 : countoddmembers (Cons Z (Cons 2 (Cons 4 Nil))) = Z
test_countoddmembers2 = Refl

test_countoddmembers3 : countoddmembers Nil = Z
test_countoddmembers3 = Refl
