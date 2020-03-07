Tom de Jong, 6 March 2020

As suggested by Martin Escardo.

No endpoints, density and binary interpolation formulated using ∃.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Dyadic
open import Dyadic-Order
open import UF-PropTrunc

module Dyadic-Order-PropTrunc (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

≺-has-no-left-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , y ≺ x
≺-has-no-left-endpoint x = ∣ ≺-has-no-left-endpoint-Σ x ∣

≺-has-no-right-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , x ≺ y
≺-has-no-right-endpoint x = ∣ ≺-has-no-right-endpoint-Σ x ∣

≺-is-dense : {x y : 𝔻} → x ≺ y → ∃ z ꞉ 𝔻 , x ≺ z × z ≺ y
≺-is-dense {x} {y} x≺y = ∣ ≺-is-dense-Σ x y x≺y ∣

≺-interpolation₂ : (x₀ x₁ y : 𝔻) → x₀ ≺ y → x₁ ≺ y
                 → ∃ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
≺-interpolation₂ x₀ x₁ y x₀≺y x₁≺y = ∣ ≺-interpolation₂-Σ x₀ x₁ y x₀≺y x₁≺y ∣

\end{code}
