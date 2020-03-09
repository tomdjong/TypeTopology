Tom de Jong, 7 March 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

open import Dyadic
open import DyadicOrder

module DyadicIdealCompletion
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓤₀
open import DcpoApproximation pt fe 𝓤₀
open import DcpoBasis pt fe 𝓤₀
open import DyadicOrder-PropTrunc pt

open import IdealCompletion pt fe pe 𝓤₀
open import IdealCompletion-Properties pt fe pe 𝓤₀

\end{code}

Having less repetition would be nice.

\begin{code}

open Ideals
 _≺_
 (λ {x} {y} → ≺-is-prop-valued x y)
 (λ {x} {y} {z} → ≺-interpolation₂ x y z)
 ≺-has-no-left-endpoint
 (λ {x} {y} {z} → ≺-is-transitive x y z)

open Idl-Properties
 _≺_
 (λ {x} {y} → ≺-is-prop-valued x y)
 (λ {x} {y} {z} → ≺-interpolation₂ x y z)
 ≺-has-no-left-endpoint
 (λ {x} {y} {z} → ≺-is-transitive x y z)

open SmallIdeals
 _≺_
 (λ {x} {y} → ≺-is-prop-valued x y)
 (λ {x} {y} {z} → ≺-interpolation₂ x y z)
 ≺-has-no-left-endpoint
 (λ {x} {y} {z} → ≺-is-transitive x y z)

\end{code}

\begin{code}

Idl-𝔻 : DCPO {𝓤₁} {𝓤₀}
Idl-𝔻 = Idl-DCPO

Idl-𝔻-is-continuous : is-a-continuous-dcpo Idl-𝔻
Idl-𝔻-is-continuous = Idl-is-continuous

Idl-𝔻-has-no-compact-elements : (I : Idl) → ¬ (is-compact Idl-DCPO I)
Idl-𝔻-has-no-compact-elements I κ = ∥∥-rec 𝟘-is-prop γ g
 where
  γ : ¬ (Σ x ꞉ 𝔻 , x ∈ᵢ I × I ⊑ (↓ x))
  γ (x , x∈I , I⊑↓x) = ≺-to-≢ {x} {x} x≺x refl
   where
    x≺x : x ≺ x
    x≺x = I⊑↓x x x∈I
  g : ∃ x ꞉ 𝔻 , x ∈ᵢ I × I ⊑ (↓ x)
  g = Idl-≪-in-terms-of-⊑ I I κ

\end{code}
