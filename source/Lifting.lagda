Martin Escardo 25th October 2018.

The type of partial elements of a type (or lifting). Constructions and
properties of lifting are discussed in other modules.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Lifting (𝓣 : Universe) where

open import UF-Subsingletons hiding (⊥)

𝓛 : 𝓤 ̇ → 𝓣 ⁺ ⊔  𝓤 ̇
𝓛 X = Σ \(P : 𝓣 ̇ ) → (P → X) × is-prop P

is-defined : {X : 𝓤 ̇ } → 𝓛 X → 𝓣 ̇
is-defined (P , φ , i) = P

-- size test

test : {X : 𝓤 ̇ } → (α : 𝓛 X → Ω 𝓥) → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
test {𝓤} {𝓥} {X} α = Σ \(l : 𝓛 X) → ((α l) holds) × is-defined l

-- test' : {X : 𝓤 ̇ } → (α : 𝓛 X → Ω 𝓥) → 𝓛 X
-- test' {𝓤} {𝓥} {X} α = {!!} -- test , {!!}

𝓟 : 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓟 X = X → Ω 𝓣

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 X → 𝓣 ̇
x ∈ A = A x holds

test'' : {X : 𝓤 ̇ } → (α : 𝓟 X → Ω 𝓥) → X → 𝓣 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
test'' {𝓤} {𝓥} {X} α x = Σ \(A : 𝓟 X) → (x ∈ A) × ((α A) holds)

--

being-defined-is-a-prop : {X : 𝓤 ̇ } (l : 𝓛  X) → is-prop (is-defined l)
being-defined-is-a-prop (P , φ , i) = i

value : {X : 𝓤 ̇ } (l : 𝓛  X) → is-defined l → X
value (P , φ , i) = φ

\end{code}

The "total" elements of 𝓛 X:

\begin{code}

η : {X : 𝓤 ̇ } → X → 𝓛 X
η x = 𝟙 , (λ _ → x) , 𝟙-is-prop

\end{code}

Its "undefined" element:

\begin{code}

⊥ : {X : 𝓤 ̇ } → 𝓛 X
⊥ = 𝟘 , unique-from-𝟘 , 𝟘-is-prop

\end{code}
