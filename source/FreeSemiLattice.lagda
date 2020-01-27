Tom de Jong
27-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module FreeSemiLattice where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
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

⊆-reflexivity : {X : 𝓤 ̇ } {A : 𝓟 𝓣 X} → A ⊆ A
⊆-reflexivity x = id

⊆-transitivity : {X : 𝓤 ̇ } {A B C : 𝓟 𝓣 X}
               → A ⊆ B → B ⊆ C → A ⊆ C
⊆-transitivity i j x a = j x (i x a)

⊆-antisymmetry : propext 𝓣 → funext 𝓤 (𝓣 ⁺) → funext 𝓣 𝓣
               → {X : 𝓤 ̇ } {A B : 𝓟 𝓣 X}
               → A ⊆ B → B ⊆ A → A ≡ B
⊆-antisymmetry {𝓤} {𝓣} pe fe fe' {X} {A} {B} i j = dfunext fe γ
 where
  γ : (x : X) → A x ≡ B x
  γ x = to-subtype-≡ (λ _ → being-a-prop-is-a-prop fe') ϕ
   where
    ϕ : x ∈ A ≡ x ∈ B
    ϕ = pe (∈-is-a-prop A x) (∈-is-a-prop B x) (i x) (j x)

𝕤 : {X : 𝓤 ̇ } → is-set X → X → 𝓟 𝓣 X
𝕤 i x = λ y → {!x ≡ y!} , {!!}

open import UF-PropTrunc

module KuratowskiFinite
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt
 open import UF-ImageAndSurjection
 open ImageAndSurjection pt

 open import Fin

 is-Kuratowski-finite : 𝓤 ̇ → 𝓤 ̇
 is-Kuratowski-finite X = ∃ \(n : ℕ) → Σ \(e : Fin n → X) → is-surjection e

 being-Kuratowski-finite-is-a-prop : {X : 𝓤 ̇ }
                                   → is-prop (is-Kuratowski-finite X)
 being-Kuratowski-finite-is-a-prop = ∥∥-is-a-prop

 𝓚 : (𝓣 : Universe) → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓚 𝓣 X = Σ \(A : 𝓟 𝓣 X) → is-Kuratowski-finite (𝕋 A)

 ⟨_⟩ : {X : 𝓤 ̇ } → 𝓚 𝓣 X → 𝓟 𝓣 X
 ⟨_⟩ = pr₁

 κ : {X : 𝓤 ̇ } → (A : 𝓚 𝓣 X) → is-Kuratowski-finite (𝕋 ⟨ A ⟩)
 κ = pr₂

 _∈ₖ_ : {X : 𝓤 ̇ } → X → 𝓚 𝓣 X → 𝓣 ̇
 x ∈ₖ A = x ∈ ⟨ A ⟩

 ∈ₖ-is-a-prop : {X : 𝓤 ̇ } (A : 𝓚 𝓣 X) (x : X)
            → is-prop (x ∈ₖ A)
 ∈ₖ-is-a-prop A x = ∈-is-a-prop ⟨ A ⟩ x

 _⊆ₖ_ : {X : 𝓤 ̇ } → 𝓚 𝓣 X → 𝓚 𝓣 X → 𝓤 ⊔ 𝓣 ̇
 A ⊆ₖ B = ⟨ A ⟩ ⊆ ⟨ B ⟩

 ⊆ₖ-is-a-prop : {X : 𝓤 ̇ }
              → funext 𝓤 𝓣 → funext 𝓣 𝓣
              → (A B : 𝓚 𝓣 X)
              → is-prop (A ⊆ₖ B)
 ⊆ₖ-is-a-prop fe fe' A B = ⊆-is-a-prop fe fe' ⟨ A ⟩ ⟨ B ⟩

 ⊆ₖ-reflexivity : {X : 𝓤 ̇ } {A : 𝓚 𝓣 X} → A ⊆ₖ A
 ⊆ₖ-reflexivity {𝓤} {𝓣} {X} {A} = ⊆-reflexivity {𝓤} {𝓣} {X} {⟨ A ⟩}

 ⊆ₖ-transitivity : {X : 𝓤 ̇ } {A B C : 𝓚 𝓣 X}
                 → A ⊆ₖ B → B ⊆ₖ C → A ⊆ₖ C
 ⊆ₖ-transitivity {𝓤} {𝓣} {X} {A} {B} {C} =
  ⊆-transitivity {𝓤 } {𝓣} {X} {⟨ A ⟩} {⟨ B ⟩} {⟨ C ⟩}

 ⊆ₖ-antisymmetry : propext 𝓣 → funext 𝓤 (𝓣 ⁺) → funext 𝓣 𝓣
                 → {X : 𝓤 ̇ } {A B : 𝓚 𝓣 X}
                 → A ⊆ₖ B → B ⊆ₖ A → A ≡ B
 ⊆ₖ-antisymmetry {𝓤} {𝓣} pe fe fe' {X} {A} {B} i j = to-subtype-≡ ϕ ψ
  where
   ϕ : (A : 𝓟 𝓤 X) → is-prop (is-Kuratowski-finite (𝕋 A))
   ϕ _ = being-Kuratowski-finite-is-a-prop
   ψ : ⟨ A ⟩ ≡ ⟨ B ⟩
   ψ = ⊆-antisymmetry pe fe fe' i j

 𝕤ₖ : {X : 𝓤 ̇ } → X → 𝓚 𝓣 X
 𝕤ₖ x = {!!} , {!!}

\end{code}
