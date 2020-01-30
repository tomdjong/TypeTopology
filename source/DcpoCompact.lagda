Tom de Jong, 11 December 2019.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoCompact
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

-- open import UF-Subsingletons hiding (⊥)
-- open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥

approximates : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
approximates 𝓓 x y = (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                   → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
                   → ∃ \(i : I) → x ⊑⟨ 𝓓 ⟩ α i

syntax approximates 𝓓 x y = x ≪⟨ 𝓓 ⟩ y

≪-implies-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y
≪-implies-⊑ 𝓓 {x} {y} a = ∥∥-rec (prop-valuedness 𝓓 x y) γ g
 where
  α : 𝟙{𝓥} → ⟨ 𝓓 ⟩
  α * = y
  γ : (Σ \(i : 𝟙) → x ⊑⟨ 𝓓 ⟩ α i) → x ⊑⟨ 𝓓 ⟩ y
  γ (* , l) = l
  g : ∃ \(i : 𝟙) → x ⊑⟨ 𝓓 ⟩ α i
  g = a 𝟙 α δ (∐-is-upperbound 𝓓 δ *)
   where
    δ : is-Directed 𝓓 α
    δ = (∣ * ∣ , ε)
     where
      ε : (i j : 𝟙)
        → ∃ \(k : 𝟙) →  α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k
      ε * * = ∣ * , reflexivity 𝓓 y , reflexivity 𝓓 y ∣

⊑-≪-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x' x y y' : ⟨ 𝓓 ⟩}
      → x' ⊑⟨ 𝓓 ⟩ x
      → x ≪⟨ 𝓓 ⟩ y
      → y ⊑⟨ 𝓓 ⟩ y'
      → x' ≪⟨ 𝓓 ⟩ y'
⊑-≪-⊑ 𝓓 {x'} {x} {y} {y'} u a v I α δ w = γ
 where
  γ : ∃ \(i : I) → x' ⊑⟨ 𝓓 ⟩ α i
  γ = ∥∥-functor g h
   where
    g : (Σ \(i : I) → x ⊑⟨ 𝓓 ⟩ α i)
      → (Σ \(i : I) → x' ⊑⟨ 𝓓 ⟩ α i)
    g (i , l) = (i , t)
     where
      t = x'  ⊑⟨ 𝓓 ⟩[ u ]
          x   ⊑⟨ 𝓓 ⟩[ l ]
          α i ∎⟨ 𝓓 ⟩
    h : ∃ \(i : I) → x ⊑⟨ 𝓓 ⟩ α i
    h = a I α δ s
     where
      s = y     ⊑⟨ 𝓓 ⟩[ v ]
          y'    ⊑⟨ 𝓓 ⟩[ w ]
          ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

compact : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
compact 𝓓 x = x ≪⟨ 𝓓 ⟩ x

is-a-continuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-continuous-dcpo 𝓓 = (x : ⟨ 𝓓 ⟩)
                       → ∥ (Σ \(I : 𝓥 ̇ )
                           → Σ \(α : I → ⟨ 𝓓 ⟩)
                           → ((i : I) → α i ≪⟨ 𝓓 ⟩ x)
                           × (Σ \(δ : is-Directed 𝓓 α) → ∐ 𝓓 δ ≡ x)) ∥

is-an-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-an-algebraic-dcpo 𝓓 = (x : ⟨ 𝓓 ⟩)
                       → ∥ (Σ \(I : 𝓥 ̇ )
                           → Σ \(α : I → ⟨ 𝓓 ⟩)
                           → ((i : I) → compact 𝓓 (α i))
                           × (Σ \(δ : is-Directed 𝓓 α) → ∐ 𝓓 δ ≡ x)) ∥

algebraicity-implies-continuity : (𝓓 : DCPO {𝓤} {𝓣})
                                → is-an-algebraic-dcpo 𝓓
                                → is-a-continuous-dcpo 𝓓
algebraicity-implies-continuity 𝓓 a x = ∥∥-functor γ (a x)
 where
  γ : (Σ \(I : 𝓥 ̇ )
         → Σ \(α : I → ⟨ 𝓓 ⟩)
         → ((i : I) → compact 𝓓 (α i))
         × Σ (λ δ → ∐ 𝓓 δ ≡ x))
      → Σ \(I : 𝓥 ̇ )
          → Σ \(α : I → ⟨ 𝓓 ⟩)
          → ((i : I) → approximates 𝓓 (α i) x)
          × Σ (λ δ → ∐ 𝓓 δ ≡ x)
  γ (I , α , c , δ , refl) = (I , α , h , δ , refl)
   where
    h : (i : I) → α i ≪⟨ 𝓓 ⟩ x
    h i = ⊑-≪-⊑ 𝓓 u v w
     where
      u : α i ⊑⟨ 𝓓 ⟩ α i
      u = reflexivity 𝓓 (α i)
      v : α i ≪⟨ 𝓓 ⟩ α i
      v = c i
      w : α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
      w = ∐-is-upperbound 𝓓 δ i

\end{code}
