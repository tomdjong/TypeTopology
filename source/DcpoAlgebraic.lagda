Tom de Jong, late February - early March 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module DcpoAlgebraic
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoApproximation pt fe 𝓥
open import DcpoBasis pt fe 𝓥

is-an-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-an-algebraic-dcpo {𝓤} {𝓣} 𝓓 =
 ∃ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) ,
 is-a-basis 𝓓 β × ((b : B) → is-compact 𝓓 (β b))

algebraicity-implies-continuity : (𝓓 : DCPO {𝓤} {𝓣})
                                → is-an-algebraic-dcpo 𝓓
                                → is-a-continuous-dcpo 𝓓
algebraicity-implies-continuity 𝓓 = ∥∥-functor γ
 where
  γ : (Σ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) ,
         is-a-basis 𝓓 β
        × ((b : B) → is-compact 𝓓 (β b)))
    → Σ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , is-a-basis 𝓓 β
  γ (B , β , isb , comp) = B , β , isb

\end{code}
