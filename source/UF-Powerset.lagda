Tom de Jong
17-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Powerset where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt

𝓟 : (X : 𝓤 ̇ ) → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 X → 𝓤 ̇
x ∈ A = A x holds

open import UF-SetTrunc

module _
        (𝓤 : Universe)
        (fe : funext 𝓤 𝓤)
        (pe : propext 𝓤)
        (st : set-truncations-exist)
      where
 open SetTruncation st

 𝓟-∥∥₀-≃ : (X : 𝓤 ̇ ) → 𝓟 X ≃ 𝓟 ∥ X ∥₀
 𝓟-∥∥₀-≃ X = ≃-sym e
  where
   e : 𝓟 ∥ X ∥₀ ≃ 𝓟 X
   e = (∣∣₀-precomp , ∥∥₀-universal-property (Ω-is-a-set fe pe))

\end{code}
