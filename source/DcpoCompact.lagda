Tom de Jong, 11 December 2019.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoCompact
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index type for directed completeness lives
       where

open PropositionalTruncation pt

open import UF-Subsingletons hiding (⊥)
open import UF-Subsingletons-FunExt

-- open import UF-Miscelanea
-- open import NaturalsAddition renaming (_+_ to _+'_)
-- open import NaturalsOrder
-- open import NaturalNumbers-Properties

-- open import Dcpo pt fe 𝓥

module _
       {𝓤 𝓣 : Universe}
       (X : 𝓤 ̇ )
       (_⊑_ : X → X → 𝓣 ̇ )
       (⊑-reflexive : (x : X) → x ⊑ x)
       (⊑-propvalued
       where

 is-compact : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 is-compact c = (I : 𝓥 ̇ ) (α : I → D) (s : D) → is-sup _⊑_ s α
              → c ⊑ s
              → ∃ \(i : I) → c ⊑ α i
  where
   D : 𝓤 ̇
   D = ⟨ 𝓓 ⟩
   _⊑_ = underlying-order 𝓓



\end{code}
