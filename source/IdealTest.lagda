\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module IdealTest
        (pe : propext 𝓤₀)
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index type for directed completeness lives
       where

open PropositionalTruncation pt

open import UF-Subsingletons
-- open import UF-Subsingletons-FunExt
open import DcpoIdeal pt fe 𝓥

open import Two-Properties

Idl𝟚 : 𝓤₁ ̇
Idl𝟚 = Idl _≤₂_ 𝓤₀

Ω₀ : 𝓤₁ ̇
Ω₀ = Ω 𝓤₀

f : Idl𝟚 → Ω₀
f (I , α , ι) = (∃ (\(i : I) → α i ≡ ₁) , ∥∥-is-a-prop)

≤₂-refl : {a : 𝟚} → a ≤₂ a
≤₂-refl = id

g : Ω₀ → Idl𝟚
g P = (𝟙 + (P holds)) , (χ , ι)
 where
  χ : 𝟙 + (P holds) → 𝟚
  χ (inl *) = ₀
  χ (inr p) = ₁
  ι : is-ideal _≤₂_ χ
  ι = u , v
   where
    u : is-directed' _≤₂_ χ
    u = ∣ inl * ∣ , δ
     where
      δ : (i j : 𝟙 + (P holds))
        → ∃ \k → (χ i ≤₂ χ k) × (χ j ≤₂ χ k)
      δ (inl *) (inl *) = ∣ (inl *) , (≤₂-refl , ≤₂-refl) ∣
      δ (inl *) (inr p) = ∣ (inr p) , (₀-bottom , ≤₂-refl) ∣
      δ (inr p) j       = ∣ (inr p) , (≤₂-refl , ₁-top) ∣
    v : is-lower-closed _≤₂_ χ
    v (inl *) ₀ l = ∣ (inl *) , refl ∣
    v (inl *) ₁ l = 𝟘-elim (zero-is-not-one (l refl))
    v (inr p) ₀ l = ∣ (inl *) , refl ∣
    v (inr p) ₁ l = ∣ (inr p) , refl ∣

fg : (P : Ω₀) → f (g P) ≡ P
fg (P , i) = to-Σ-≡ ((pe ∥∥-is-a-prop i a b) , (being-a-prop-is-a-prop fe _ i))
 where
  a : pr₁ (f (g (P , i))) → P
  a s = ∥∥-rec i h s
   where
    h : (Σ \i₂ → pr₁ (pr₂ (g (P , i))) i₂ ≡ ₁) → P
    h (inl * , e) = 𝟘-elim (zero-is-not-one e)
    h (inr p , e) = p
  b : P → pr₁ (f (g (P , i)))
  b p = ∣ (inr p) , refl ∣

gf : (α : Idl𝟚) → g (f α) ≡ α
gf (I , α , ι) = to-Σ-≡ ({!!} , {!!})
 where
  a : (𝟙 + (∃ \i → α i ≡ ₁)) → I
  a (inl *) = {!!}
  a (inr p) = {!!}

\end{code}
