Tom de Jong

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoSize2
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
        (pe : propext 𝓥)
        (PE : PropExt)
       where

open PropositionalTruncation pt

open import Poset fe
open PosetAxioms

open import Dcpo pt fe 𝓥
open import DcpoLifting pt fe 𝓥 pe
open import Lifting 𝓥
open import LiftingMiscelanea-PropExt-FunExt 𝓥 pe fe

open import UF-Equiv
open import UF-Size

every-pointed-dcpo-has-maximal-element-statement : (𝓤 𝓣 : Universe)
                                                 → (𝓥 ⊔ 𝓤 ⊔ 𝓣) ⁺ ̇
every-pointed-dcpo-has-maximal-element-statement 𝓤 𝓣 =
 (𝓓 : DCPO⊥ {𝓤} {𝓣}) → ∃ x ꞉ ⟪ 𝓓 ⟫ , is-maximal (underlying-order (𝓓 ⁻)) x

open import UF-UniverseEmbedding
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-Embeddings

-- Theorem 2
every-dcpo-has-maximal-element-implies-resizing-Σ : {𝓤 : Universe}
                                                → every-pointed-dcpo-has-maximal-element-statement
                                                   (𝓥 ⁺ ⊔ 𝓤) (𝓥 ⁺ ⊔ 𝓤)
                                                → propositional-resizing 𝓤 𝓥
every-dcpo-has-maximal-element-implies-resizing-Σ {𝓤} M P i =
 ∥∥-rec (prop-has-size-is-a-prop PE (λ _ _ → fe) P i 𝓥) γ (M 𝓛P-DCPO⊥)
  where
   𝓛P-DCPO⊥ : DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⁺ ⊔ 𝓤}
   𝓛P-DCPO⊥ = 𝓛-DCPO⊥ (props-are-sets i)
   γ : (Σ x ꞉ 𝓛 P , is-maximal _⊑'_ x) → P has-size 𝓥
   γ (Q' , Q'-is-max) = Q , ψ
    where
     Q : 𝓥 ̇
     Q = is-defined Q'
     ψ : Q ≃ P
     ψ = logically-equivalent-props-are-equivalent
          (being-defined-is-a-prop Q')
          i (value Q') g
      where
       g : P → Q
       g p = transport is-defined e *
        where
         e : η p ≡ Q'
         e = (Q'-is-max (η p) u) ⁻¹
          where
           u : Q' ⊑' η p
           u q = ⋍-to-≡
                  (logically-equivalent-props-are-equivalent
                   (being-defined-is-a-prop Q')
                   (being-defined-is-a-prop (η p))
                   (λ _ → *) (λ _ → q)
                  , dfunext fe (λ _ → i _ _))

\end{code}
