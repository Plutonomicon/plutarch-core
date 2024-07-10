{-# LANGUAGE UndecidableInstances #-}

import Data.Kind (Type)

-- find what is in xs and not in ys and vice versa,
-- out is what is in xs but not in ys,
-- and remainder is what is in ys but not in xs
class FindDiff (xs :: [Type]) (ys :: [Type]) (remainder :: [Type]) (out :: [Type]) | xs ys -> remainder out

instance FindDiff '[] ys ys '[]

class FindDiff1 (x :: Type) (ys :: [Type]) (prev_out :: [Type]) (remainder :: [Type]) (out :: [Type]) | x ys prev_out -> remainder out
instance FindDiff1 x '[] prev_out '[] (x : prev_out)
instance FindDiff1 x (x : ys) prev_out ys prev_out
instance {-# OVERLAPPABLE #-} (FindDiff1 x ys prev_out remainder out, remainder' ~ y : remainder) => FindDiff1 x (y : ys) prev_out remainder' out
instance (FindDiff xs ys prev_remainder prev_out, FindDiff1 x prev_remainder prev_out remainder out) => FindDiff (x : xs) ys remainder out

data F (x :: [Type])

type XS = '[Int, Bool, Bool, String, Bool, Bool, Char, Char, Char, Bool, Bool, Bool]
type YS = '[[Char], Char, Bool, Char, Bool, Maybe ()]

z :: FindDiff XS YS remainder out => F remainder
z = undefined

w :: F _
w = z
