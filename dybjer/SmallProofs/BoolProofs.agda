module SmallProofs.BoolProofs where

open import IType.Bool
open import IType.Nat
open import MLTT.PropositionalLogic
open import MLTT.MLTT renaming (r to refl)

-- proving equality of two boolean expressions

notnotI : (b : Bool) → I Bool b (not (not b))
notnotI true = refl
notnotI false = refl

-- notnotI x = if x then refl else refl

-- Now prove the same equality as above using So

_<==>_ : Bool → Bool → Bool
true <==> true = true
true <==> false = false
false <==> true = false
false <==> false = true

sonotnot : (b : Bool) → So (b <==> not (not b))
sonotnot true = ⊤-intro
sonotnot false = ⊤-intro




_⊃b_ : Bool → Bool → Bool
true ⊃b true = true
true ⊃b false = false
false ⊃b true = true
false ⊃b false = true


-- I have no idea what I'm proving, but it type checks...
-- Okay... ⊤-intro just proves everything?
em : (b : Bool) -> So (b || (not b))
-- em true = ||-intro true (not true) ⊤-intro
-- em false = ||-intro true (not true) ⊤-intro
em true = ⊤-intro
em false = ⊤-intro


dm : (a b : Bool) → So ((not (a && b)) <==> ((not a) || (not b)))
dm true true = ⊤-intro
dm true false = ⊤-intro
dm false true = ⊤-intro
dm false false = ⊤-intro

-- don't ask me why this doesn't work with [a ↦ n]....
Pred : Nat → Set
Pred zero     = Bool
Pred (succ a) = Bool → (Pred a)

-- i have no fucking clue
-- taut : (a : Nat) -> Pred a -> Bool
-- taut zero     p = p
-- taut (succ a) p = taut a (p {!!})


-- ¬¬¬P → ¬P
a : {P : Set} -> (((P -> ⊥) -> ⊥) -> ⊥) -> (P -> ⊥)
a l = {!!} -- λ z → l (λ z₁ → z₁ z) -- proof by C-c C-a

-- ¬(P ∨ Q) ↔ ¬P&¬Q
-- ok, I know ∨ is a sum type, but what is that in Agda?

