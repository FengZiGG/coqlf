import MyLists

total alternate : Natlist -> Natlist -> Natlist
alternate Nil l2                    = l2
alternate (Cons x l1') Nil          = Cons x (alternate l1' Nil)
alternate (Cons x l1') (Cons y l2') = Cons x (Cons y (alternate l1' l2'))

test_alternate1 : alternate (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 4 (Cons 5 (Cons 6 Nil))) = (Cons 1 (Cons 4 (Cons 2 (Cons 5 (Cons 3 (Cons 6 Nil))))))
test_alternate1 = Refl

test_alternate2 : alternate (Cons 1 Nil) (Cons 4 (Cons 5 (Cons 6 Nil))) = (Cons 1 (Cons 4 (Cons 5 (Cons 6 Nil))))
test_alternate2 = Refl

test_alternate3 : alternate (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 4 Nil) = (Cons 1 (Cons 4 (Cons 2 (Cons 3 Nil))))
test_alternate3 = Refl

test_alternate4 : alternate Nil (Cons 20 (Cons 30 Nil)) = (Cons 20 (Cons 30 Nil))
test_alternate4 = Refl
