module IType.Bool where

open import IType.Nat

data Bool : Set where
  true  : Bool
  false : Bool

-- Note that Agda has a standard library where many common types and functions are defined

not : Bool -> Bool
not true = false
not false = true

-- In Agda we have unicode and can for example write → for -> and ¬ for not: 

¬ : Bool → Bool
¬ = not

-- The names of unicode characters used by Agda are often the same as the names used in latex.

-- In Agda, we can write programs by gradual refinement, 
-- where we write ? for an unknown part of the program.
-- The ? becomes { - } when type-checked (a "hole").
-- Holes can be filled in either by writing a complete expression in the hole and doing ^C^SPC
-- or by writing a partial expression in the whole and doing ^C^R (refine)
-- or by writing the top level function and doing ^C^R

-- Exercise: write the following function by gradual refinement:

¬¬ : Bool → Bool
¬¬ b = ¬ (¬ b)

-- Agda can also create complete case analysis (pattern matching) automatically 
-- by writing the pattern variable in a hole and do ^C^C

-- Exercise: write not by gradual refinement and case analysis

-- This is how you declare an infix operator:

_&&_ : Bool → Bool → Bool
b && true  = b
b && false = false

_||_ : Bool → Bool → Bool
true || true = true
false || true = true
true || false = true
false || false = false

-- It is a special case of mixfix declarations:

if_then_else_ : {C : Set} → Bool → C → C → C
if true  then y else z = y
if false then y else z = z

-- You can compute ("normalize") closed expressions by writing ^C^N and then write the expression afterwards.

-- Exercise: compute a few expressions!

eqNat : Nat → Nat → Bool
eqNat zero zero = true
eqNat zero (succ n) = false
eqNat (succ m) zero = false
eqNat (succ m) (succ n) = eqNat m n

isZero : Nat → Bool
isZero n = natrec true (λ x y → false) n

help : (Nat → Bool) → Nat → Bool
help f zero = false
help f (succ n) = f n

eqNat' : Nat → Nat → Bool
eqNat' zero = isZero
eqNat' (succ m) = help (eqNat' m)

open import MLTT.PropositionalLogic

So : Bool → Set
So true  = ⊤
So false = ⊥

||-intro : (b c : Bool) → So b → So (b || c)
||-intro true true ⊤-intro = ⊤-intro
||-intro true false ⊤-intro = ⊤-intro
||-intro false c ()

refleqNat : (n : Nat) → So (eqNat n n)
refleqNat zero = ⊤-intro
refleqNat (succ n) = refleqNat n

_<_ : Nat → Nat → Bool
m < zero = false
zero < succ n = true
succ m < succ n = m < n
