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

open import IdealCompletion pt fe pe 𝓤₀
open import Dcpo pt fe 𝓤₀
open import DyadicOrder-PropTrunc pt

open Ideals
 _≺_
 (λ {x} {y} → ≺-is-prop-valued x y)
 (λ {x} {y} {z} → ≺-interpolation₂ x y z)
 ≺-has-no-left-endpoint
 (λ {x} {y} {z} → ≺-is-transitive x y z)

Idl-𝔻 : DCPO {𝓤₁} {𝓤₀}
Idl-𝔻 = Idl-DCPO


\end{code}
