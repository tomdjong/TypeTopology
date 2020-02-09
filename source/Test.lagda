Tom de Jong, 9 February 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Test where

open import UF-Base
open import SpartanMLTT
open import UF-Equiv
open import UF-Retracts
open import UF-Size
open import UF-PropTrunc
open import UF-Embeddings
open import UF-EquivalenceExamples

module _ (pt : propositional-truncations-exist) where
 open PropositionalTruncation pt

 retract-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → (ρ : retract X of Y)
                  → is-embedding (section ρ)
                  → X has-size 𝓥
 retract-has-size {𝓤} {𝓥} {X} {Y} (r , s , ρ) semb =
  (Σ y ꞉ Y , ∥ s (r y) ≡ y ∥) , γ
   where
    γ = (Σ y ꞉ Y , ∥ s (r y) ≡ y ∥) ≃⟨ Σ-cong ψ ⟩
        (Σ y ꞉ Y , fiber s y)       ≃⟨ ≃-sym (sum-of-fibers X Y s) ⟩
        X                           ■
     where
      ψ : (y : Y) → ∥ s (r y) ≡ y ∥ ≃ fiber s y
      ψ y = logically-equivalent-props-are-equivalent
             ∥∥-is-a-prop (semb y)
             f g
       where
        f : ∥ s (r y) ≡ y ∥ → fiber s y
        f = ∥∥-rec (semb y) ϕ
         where
          ϕ : s (r y) ≡ y → fiber s y
          ϕ q = (r y) , q
        g : fiber s y → ∥ s (r y) ≡ y ∥
        g (x , p) = ∣ q ∣
         where
          q = s (r y)     ≡⟨ ap (s ∘ r) (p ⁻¹) ⟩
              s (r (s x)) ≡⟨ ap s (ρ x) ⟩
              s x         ≡⟨ p ⟩
              y           ∎


 retract-of-a-set-has-size' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                  → is-set Y
                                  → retract X of Y
                                  → X has-size 𝓥
 retract-of-a-set-has-size' {𝓤} {𝓥} {X} {Y} i ρ = retract-has-size ρ γ
  where
   γ : is-embedding (section ρ)
   γ = lc-maps-into-sets-are-embeddings (section ρ)
        (sections-are-lc (section ρ)
         ((retraction ρ) , (retract-condition ρ)))
        i

\end{code}
