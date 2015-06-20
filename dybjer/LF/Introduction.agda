module LF.Introduction where

Id-set : Set → Set
Id-set = λ X → X

id : {X : Set} -> X -> X
id x = x

-- id : (X : Set) → X → X
-- id _ x = x

-- id = λ X x -> x
-- id = λ _ x -> x
