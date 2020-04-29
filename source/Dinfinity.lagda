Tom de Jong, 29 April 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module Dinfinity
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓤 : Universe)
        (pe : propext 𝓤)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓤
open import DcpoBasics pt fe 𝓤
open import DcpoLifting pt fe 𝓤 pe
open import DcpoExponential pt fe 𝓤

𝓓 : ℕ → DCPO⊥ {𝓤 ⁺} {𝓤 ⁺}
𝓓 zero     = 𝓛-DCPO⊥ {𝓤} {𝟙{𝓤}} (props-are-sets 𝟙-is-prop)
𝓓 (succ n) = 𝓓 n ⟹ᵈᶜᵖᵒ⊥ 𝓓 n

𝓓-diagram : (n : ℕ) → DCPO[ 𝓓 n ⁻  , 𝓓 (succ n) ⁻ ]
                    × DCPO[ 𝓓 (succ n) ⁻ , 𝓓 n ⁻   ]
𝓓-diagram zero     = (e₀ , e₀-continuity) , p₀ , p₀-continuity
 where
  e₀ : ⟨ 𝓓 0 ⁻ ⟩ → ⟨ 𝓓 1 ⁻ ⟩
  e₀ x = (λ y → x) , (constant-functions-are-continuous (𝓓 0 ⁻) (𝓓 0 ⁻) x)
  e₀-continuity : is-continuous (𝓓 0 ⁻) (𝓓 1 ⁻) e₀
  e₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → e₀ (α i) ⊑⟨ (𝓓 1 ⁻) ⟩ e₀ (∐ (𝓓 0 ⁻) δ)
    ub i y =  α i          ⊑⟨ 𝓓 0 ⁻ ⟩[ ∐-is-upperbound (𝓓 0 ⁻) δ i ]
              ∐ (𝓓 0 ⁻) δ  ∎⟨ 𝓓 0 ⁻ ⟩
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 1 ⁻))
                  (e₀ (∐ (𝓓 0 ⁻) δ)) (λ x → e₀ (α x))
    lb-of-ubs (g , c) ub y =
     ∐-is-lowerbound-of-upperbounds (𝓓 0 ⁻) δ (g y) (λ i → ub i y)
  p₀ : ⟨ 𝓓 1 ⁻ ⟩ → ⟨ 𝓓 0 ⁻ ⟩
  p₀ (f , c) = f (⊥ (𝓓 0))
  p₀-continuity : is-continuous (𝓓 1 ⁻) (𝓓 0 ⁻) p₀
  p₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → p₀ (α i) ⊑⟨ 𝓓 0 ⁻ ⟩ p₀ (∐ (𝓓 1 ⁻) {I} {α} δ)
    ub i = ∐-is-upperbound (𝓓 1 ⁻) {I} {α} δ i (⊥ (𝓓 0))
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 0 ⁻))
                  (p₀ (∐ (𝓓 1 ⁻) {I} {α} δ)) (λ x → p₀ (α x))
    lb-of-ubs y ub =
     ∐-is-lowerbound-of-upperbounds (𝓓 0 ⁻) ε y ub
      where
       ε : is-Directed (𝓓 0 ⁻) (pointwise-family (𝓓 0 ⁻) (𝓓 0 ⁻) α (⊥ (𝓓 0)))
       ε = pointwise-family-is-directed (𝓓 0 ⁻) (𝓓 0 ⁻) α δ (⊥ (𝓓 0))
𝓓-diagram (succ n) = (e , {!!}) , {!!}
 where
  IH : DCPO[ 𝓓 n ⁻ , 𝓓 (succ n) ⁻ ] × DCPO[ 𝓓 (succ n) ⁻ , 𝓓 n ⁻ ]
  IH = 𝓓-diagram n
  eₙ : ⟪ 𝓓 n ⟫ → ⟪ 𝓓 (succ n) ⟫
  eₙ = underlying-function (𝓓 n ⁻) (𝓓 (succ n) ⁻) (pr₁ IH)
  eₙ-continuity : is-continuous (𝓓 n ⁻) (𝓓 (succ n) ⁻) eₙ
  eₙ-continuity = continuity-of-function (𝓓 n ⁻) (𝓓 (succ n) ⁻) (pr₁ IH)
  pₙ : ⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 n ⟫
  pₙ = underlying-function (𝓓 (succ n) ⁻) (𝓓 n ⁻) (pr₂ IH)
  pₙ-continuity : is-continuous (𝓓 (succ n) ⁻) (𝓓 n ⁻) pₙ
  pₙ-continuity = continuity-of-function (𝓓 (succ n) ⁻) (𝓓 n ⁻) (pr₂ IH)
  e : ⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 (succ (succ n)) ⟫
  e (f , cf) = (eₙ ∘ f ∘ pₙ) ,
               ∘-is-continuous (𝓓 (succ n) ⁻) (𝓓 n ⁻) (𝓓 (succ n) ⁻)
                (f ∘ pₙ) eₙ
                (∘-is-continuous (𝓓 (succ n) ⁻) (𝓓 n ⁻) (𝓓 n ⁻)
                  pₙ f pₙ-continuity cf)
                eₙ-continuity

{- (λ f → (underlying-function {!!} {!!} {!eₙ!} ∘ underlying-function (𝓓 n ⁻) (𝓓 n ⁻) f ∘ underlying-function (𝓓 (succ n) ⁻) (𝓓 n ⁻) pₙ) {!!}) , {!!} -}
        -- DCPO-∘ (𝓓 (succ n) ⁻) {!!} {!!} pₙ
        -- (DCPO-∘ {!!} {!!} {!!} eₙ {!!})

{-
up-and-down : (n : ℕ) → (⟪ 𝓓 n ⟫ → ⟪ 𝓓 (succ n) ⟫)
                      × (⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 n ⟫)
up-and-down zero     = e₀ , p₀
 where
  e₀ : ⟪ 𝓓 0 ⟫ → ⟪ 𝓓 1 ⟫
  e₀ x = (λ y → x) , constant-functions-are-continuous (𝓓 0 ⁻) (𝓓 0 ⁻) x
  p₀ : ⟪ 𝓓 1 ⟫ → ⟪ 𝓓 0 ⟫
  p₀ f = underlying-function (𝓓 0 ⁻) (𝓓 0 ⁻) f (⊥ (𝓓 0))
up-and-down (succ n) = e , {!!}
 where
  IH : (⟪ 𝓓 n ⟫ → ⟪ 𝓓 (succ n) ⟫) × (⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 n ⟫)
  IH = up-and-down n
  eₙ : ? -- ⟪ 𝓓 n ⟫ → ⟪ 𝓓 (succ n) ⟫
  eₙ = underlying-function ? ? (pr₁ IH)
  eₙ-continuity : is-continuous ? ? eₙ
  eₙ-continuity = ?
  pₙ : ⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 n ⟫
  pₙ = pr₂ IH
  e : ⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 (succ (succ n)) ⟫
  e (f , c) = {!!} ∘ f ∘ {!!} , {!!}
-}

\end{code}
