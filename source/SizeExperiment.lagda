\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons hiding (⊥)
open import UF-Equiv
open import UF-Size

module SizeExperiment where

module Setup
       (𝓤 𝓥 𝓣 : Universe) -- 𝓥 is our notion of smallness
       (P : 𝓤 ̇ )
       (_⊑_ : P → P → 𝓣 ̇ )
       (sv : (p q : P) → is-prop (p ⊑ q))
       (⊤ : P)
       (⊤-is-top : (x : P) → x ⊑ ⊤)
      where

-- For now, we just consider small predicates on P, so not necessarily
-- proposition valued (i.e. subsets) and not necessarily ideals.

 𝓢 : 𝓣 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓤 ̇
 𝓢 = Σ \(S : P → 𝓣 ̇ ) → (Σ S) has-size 𝓥

 ↓ : P → 𝓤 ⊔ 𝓣 ̇
 ↓ p = Σ \(x : P) → x ⊑ p

 ↓-size-requirement : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ↓-size-requirement = (p : P) → (↓ p) has-size 𝓥

 ↓-size-requirement-implies-Resizing : ↓-size-requirement → P has-size 𝓥
 ↓-size-requirement-implies-Resizing ↓sr = S , ≃-comp ϕ ψ
  where
   S : 𝓥 ̇
   S = pr₁ (↓sr ⊤)
   ϕ : S ≃ ↓ ⊤
   ϕ = pr₂ (↓sr ⊤)
   ψ : ↓ ⊤ ≃ P
   ψ = qinveq f (g , gf , (λ p → refl))
    where
     f : ↓ ⊤ → P
     f = pr₁
     g : P → ↓ ⊤
     g p = p , (⊤-is-top p)
     gf : (y : ↓ ⊤) → g (f y) ≡ y
     gf (p , l) = to-Σ-≡ (refl , sv p ⊤ _ l)

\end{code}

As a particular example of this:

\begin{code}

open import UF-FunExt
open import UF-Subsingletons-FunExt

module _
        (𝓤 𝓥 : Universe)
        (fe : funext 𝓤 𝓤)
       where

 _⊑_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ̇
 P ⊑ Q = P holds → Q holds

 ⊑-sv : (P Q : Ω 𝓤) → is-prop (P ⊑ Q)
 ⊑-sv P Q = Π-is-prop fe (λ p → holds-is-prop Q)

 open Setup (𝓤 ⁺) 𝓥 𝓤 (Ω 𝓤) _⊑_ ⊑-sv ⊤ (λ (P : Ω 𝓤) → unique-to-𝟙)

 ↓-size-requirement-implies-Ω-Resizing : ↓-size-requirement → Ω-Resizing 𝓤 𝓥
 ↓-size-requirement-implies-Ω-Resizing = ↓-size-requirement-implies-Resizing

\end{code}
