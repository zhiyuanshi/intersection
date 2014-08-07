module CurryHoward where

-- (A \/ B ) -> C   |-   (A -> C) /\ (B -> C)
disjun :: (Either a b -> c) -> (a -> c, b -> c)
disjun f = (f . Left, f . Right)

-- (A -> C) /\ (B -> C)   |-   (A \/ B) -> C
disjun' :: (a -> c, b -> c) -> Either a b -> c
disjun' (f, g) c = case c of
                     Left x  -> f x
                     Right y -> g y

-- (A /\ B ) -> C   |-   (A -> C) \/ (B -> C)
conjun :: ((a, b) -> c) -> Either (a -> c) (b -> c)
conjun f = Left (\x -> f (x, undefined))
-- Alternatively,
-- conjun g = Right (\y -> g (undefined, y))

-- (A -> C) \/ (B -> C)   |-   (A /\ B) -> C
conjun' :: Either (a-> c) (b -> c) -> (a, b) -> c
conjun' d = case d of
              Left f  -> \(x, _y) -> f x
              Right g -> \(_x, y) -> g y