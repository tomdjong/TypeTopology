Tom de Jong
30-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (_≈_)

module FreeDcpoFromPoset-1
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- universe where the index types for directedness
                        -- completeness live
       where

open import Poset fe
open import Dcpo pt fe 𝓥

open PropositionalTruncation pt

module FreeDcpoFromPoset-Setup-1
        {P : 𝓤 ̇ }
        (_≤_ : P → P → 𝓣 ̇ )
        ((is-set-P , ≤-prop-valued ,
          ≤-refl , ≤-trans , ≤-anti) : PosetAxioms.poset-axioms _≤_)
       where

 𝓕 : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 𝓕 = Σ \(I : 𝓥 ̇ ) → Σ \(α : I → P) → is-directed _≤_ α

 _≼_ : 𝓕 → 𝓕 → 𝓥 ⊔ 𝓣 ̇
 (I , α , _) ≼ (J , β , _) = (i : I) → ∃ \(j : J) → α i ≤ β j

 ≼-is-reflexive : (f : 𝓕) → f ≼ f
 ≼-is-reflexive (_ , α , _) i = ∣ i , ≤-refl (α i) ∣

 ≼-is-transitive : (f g h : 𝓕) → f ≼ g → g ≼ h → f ≼ h
 ≼-is-transitive (I , α , _) (J , β , _) (K , γ , _) u v i = do
  (j , m) ← u i
  (k , n) ← v j
  ∣ k , ≤-trans (α i) (β j) (γ k) m n ∣

 ≼-is-prop-valued : (f g : 𝓕) → is-prop (f ≼ g)
 ≼-is-prop-valued f g = Π-is-prop fe (λ i → ∥∥-is-a-prop)

 _≈_ : 𝓕 → 𝓕 → 𝓥 ⊔ 𝓣 ̇
 f ≈ g = f ≼ g × g ≼ f

 ≈-to-≼ : (f g : 𝓕) → f ≈ g → f ≼ g
 ≈-to-≼ f g = pr₁

 ≈-to-≼' : (f g : 𝓕) → f ≈ g → g ≼ f
 ≈-to-≼' f g = pr₂

 ≈-is-reflexive : (f : 𝓕) → f ≈ f
 ≈-is-reflexive f = (≼-is-reflexive f , ≼-is-reflexive f)

 ≈-is-transitive : (f g h : 𝓕) → f ≈ g → g ≈ h → f ≈ h
 ≈-is-transitive f g h (u₁ , v₁) (u₂ , v₂) =
   (≼-is-transitive f g h u₁ u₂) , ≼-is-transitive h g f v₂ v₁

 ≈-is-prop-valued : (f g : 𝓕) → is-prop (f ≈ g)
 ≈-is-prop-valued f g =
  ×-is-prop (≼-is-prop-valued f g) (≼-is-prop-valued g f)

 ≈-is-symmetric : (f g : 𝓕) → f ≈ g → g ≈ f
 ≈-is-symmetric f g (u , v) = (v , u)

\end{code}
