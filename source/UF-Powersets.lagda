Tom de Jong
17-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Powersets where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

𝓟 : (𝓣 : Universe) → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓟 𝓣 X = X → Ω 𝓣

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 𝓣 X → 𝓣 ̇
x ∈ A = A x holds

∈-is-a-prop : {X : 𝓤 ̇ } (A : 𝓟 𝓣 X) (x : X)
            → is-prop (x ∈ A)
∈-is-a-prop A x = holds-is-prop (A x)

𝕋 : {X : 𝓤 ̇ } → 𝓟 𝓣 X → 𝓣 ⊔ 𝓤 ̇
𝕋 {𝓤} {𝓣} {X} A = Σ \(x : X) → x ∈ A

_⊆_ : {X : 𝓤 ̇ } → 𝓟 𝓣 X → 𝓟 𝓣 X → 𝓤 ⊔ 𝓣 ̇
_⊆_ {𝓤} {𝓣} {X} A B = (x : X) → x ∈ A → x ∈ B

⊆-is-a-prop : {X : 𝓤 ̇ }
            → funext 𝓤 𝓣 → funext 𝓣 𝓣
            → (A B : 𝓟 𝓣 X)
            → is-prop (A ⊆ B)
⊆-is-a-prop fe fe' A B = Π-is-prop fe
                         (λ x → Π-is-prop fe'
                         (λ _ → ∈-is-a-prop B x))

⊆-reflexivity : {X : 𝓤 ̇ } (A : 𝓟 𝓣 X) → A ⊆ A
⊆-reflexivity A x = id

⊆-transitivity : {X : 𝓤 ̇ } (A B C : 𝓟 𝓣 X)
               → A ⊆ B → B ⊆ C → A ⊆ C
⊆-transitivity A B C i j x a = j x (i x a)

⊆-antisymmetry : propext 𝓣 → funext 𝓤 (𝓣 ⁺) → funext 𝓣 𝓣
               → {X : 𝓤 ̇ } (A B : 𝓟 𝓣 X)
               → A ⊆ B → B ⊆ A → A ≡ B
⊆-antisymmetry {𝓤} {𝓣} pe fe fe' {X} A B i j = dfunext fe γ
 where
  γ : (x : X) → A x ≡ B x
  γ x = to-subtype-≡ (λ _ → being-a-prop-is-a-prop fe') ϕ
   where
    ϕ : x ∈ A ≡ x ∈ B
    ϕ = pe (∈-is-a-prop A x) (∈-is-a-prop B x) (i x) (j x)

𝕤 : {X : 𝓤 ̇ } → is-set X → X → 𝓟 𝓤 X
𝕤 i x = λ y → ((x ≡ y) , i)

\end{code}
