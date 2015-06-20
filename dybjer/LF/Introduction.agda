module LF.Introduction where

Id-set : Set → Set
Id-set = λ X → X

id : {X : Set} -> X -> X
id x = x

-- id : (X : Set) → X → X
-- id _ x = x

-- id = λ X x -> x
-- id = λ _ x -> x

-- C-SPC = give (complete expression in hole)
-- C-r =  refine

_∘_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
(g ∘ f) x = g (f x)
