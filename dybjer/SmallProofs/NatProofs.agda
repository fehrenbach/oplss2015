module SmallProofs.NatProofs where

open import IType.Nat
open import IType.Bool
open import MLTT.PropositionalLogic
open import MLTT.MLTT renaming (r to refl) hiding (_+_; n)

cong : {A B : Set} → {a a' : A} → (f : A → B) → I A a a' → I B (f a) (f a')
cong f refl = refl

-- proving associativity of plus using pattern matching

associativity-plus : (m n p : Nat) → I Nat ((m + n) + p) (m + (n + p))
associativity-plus m n zero = refl
associativity-plus m n (succ p) = cong succ (associativity-plus m n p)

-- the induction axiom is a dependently typed combinator for primitive recursion (by Curry-Howard)
-- use R from MLTT

natind : {C : Nat -> Set} -> C zero -> ((n : Nat) -> C n -> C (succ n)) -> (n : Nat) -> C n
natind base step zero     = base
natind base step (succ n) = step n (natind base step n)

-- proving associativity using the induction axiom

associativity-plus-ind : (m n p : Nat) → I Nat ((m + n) + p) (m + (n + p))
associativity-plus-ind m n p = natind {λ p → I Nat ((m + n) + p) (m + (n + p))} refl ((λ q r → cong succ r))  p

-- note that the two proofs are essentially the same! 
-- Pattern matching provides "syntactic sugar" for primitive recursion, 
-- but also possibility for more general recursion schemes than primitive recursion

_∸_ : Nat → Nat → Nat
zero ∸ _ = zero
succ m ∸ zero = succ m
succ m ∸ succ n = m ∸ n

_^_ : Nat → Nat → Nat
m ^ 0 = 1
m ^ succ n = m * (m ^ n)

-- natrec : {A : Set} -> A -> (Nat -> A -> A) -> Nat -> A
-- natrec base step zero = base
-- natrec base step (succ n) = step n (natrec base step n)

pow : Nat -> Nat -> Nat
pow m n = natrec 1 (λ n r -> r * m) n

_==_ : Nat -> Nat -> Bool
zero == zero = true
zero == succ m = false
succ n == zero = false
succ n == succ m = n == m

