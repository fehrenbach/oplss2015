intuitionistic type theory (aka Martin-Löf type theory 1986)

intensional

logical framework based

1. LF = dependently typed lambda-calculus with a universe `Set` of small types

   ```
A : Set
-------
A type

a ::= x | λ x → a | a a | Set | (x:a) → a

Γ ⊢ a type  Γ, x:a ⊢ b type
---------------------------
Γ ⊢ (x:a) → b type

Γ ⊢ A : Set  Γ, x:A ⊢ B : Set
-----------------------------
Γ ⊢ (x:a) → B : Set

Γ ⊢ a type  Γ, x:a ⊢ B : Set
---------------------------- (impredicative)
Γ ⊢ (x:a) → B : Set
```

2. inductive types `Set`


"Swedish school"
----------------
(Martin-Löf and students)

focus on foundations

dependently typed fb (Agda: Novell, Danielson, Abel)


Coq
---
formalization of mathematics

software verification
