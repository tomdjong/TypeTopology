Tom de Jong, 6 March 2020

As suggested by Martin Escardo.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Dyadic
open import Dyadic-Order
open import UF-PropTrunc

module Dyadic-Order-PropTrunc (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 ≺-has-no-left-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , y ≺ x
 ≺-has-no-left-endpoint x = ∣ left x , left-≺ x ∣

 ≺-has-no-right-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , x ≺ y
 ≺-has-no-right-endpoint x = ∣ right x , ≺-right x ∣

 ≺-is-dense : (x y : 𝔻) → x ≺ y → ∃ z ꞉ 𝔻 , x ≺ z × z ≺ y
 ≺-is-dense midpoint (right y) _ = ∣ right (left y) , * , left-≺ y ∣
 ≺-is-dense (left x) midpoint _ = ∣ left (right x) , ≺-right x , * ∣
 ≺-is-dense (left x) (left y) x≺y = do
  z , x≺z , z≺y ← ≺-is-dense x y x≺y
  ∣ left z , x≺z , z≺y ∣
 ≺-is-dense (left x) (right y) _ = ∣ midpoint , * , * ∣
 ≺-is-dense (right x) midpoint = 𝟘-induction
 ≺-is-dense (right x) (left y) = 𝟘-induction
 ≺-is-dense (right x) (right y) x≺y = do
  z , x≺z , z≺y ← ≺-is-dense x y x≺y
  ∣ right z , x≺z , z≺y ∣

\end{code}
