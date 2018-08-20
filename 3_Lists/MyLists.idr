module MyLists

public export
data Natlist : Type where
    Nil : Natlist
    Cons : Nat -> Natlist -> Natlist

public export
total
repeat : Nat -> Nat -> Natlist
repeat _ Z          = []
repeat n (S count') = Cons n (repeat n count')

public export
total
length : Natlist -> Nat
length []          = Z
length (Cons _ n') = 1 + (length n')

public export
total
app : Natlist -> Natlist -> Natlist
app [] l2           = l2
app (Cons x l1') l2 = Cons x (app l1' l2)

test_app1 : app (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 4 (Cons 5 Nil)) = (Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 5 Nil)))))
test_app1 = Refl

test_app2 : app Nil (Cons 4 (Cons 5 Nil)) = Cons 4 (Cons 5 Nil)
test_app2 = Refl

test_app3 : app (Cons 1 (Cons 2 (Cons 3 Nil))) Nil = (Cons 1 (Cons 2 (Cons 3 Nil)))
test_app3 = Refl

public export
total
hd' : Nat -> Natlist -> Nat
hd' default Nil  = default
hd' _ (Cons x _) = x

public export
total
tl' : Natlist -> Natlist
tl' Nil        = Nil
tl' (Cons _ x) = x

public export
total
app_assoc : (l1, l2, l3 : Natlist) -> (app (app l1 l2) l3) = (app l1 (app l2 l3))
app_assoc Nil l2 l3          = Refl
app_assoc (Cons x l1') l2 l3 = let IH = app_assoc l1' l2 l3 in rewrite IH in Refl

public export
total
rev : Natlist -> Natlist
rev Nil         = Nil
rev (Cons x l') = app (rev l') (Cons x Nil)
