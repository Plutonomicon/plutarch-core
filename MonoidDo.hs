module MonoidDo ((MonoidDo.>>)) where

(>>) :: Semigroup a => a -> a -> a
(>>) = (<>)
