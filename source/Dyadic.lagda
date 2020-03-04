Tom de Jong, 3 March 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import DiscreteAndSeparated
open import One-Properties

module Dyadic where

data 𝔻 : 𝓤₀ ̇ where
  midpoint : 𝔻
  left     : 𝔻 → 𝔻
  right    : 𝔻 → 𝔻

midpoint-is-not-left : {x : 𝔻} → midpoint ≢ left x
midpoint-is-not-left p = 𝟙-is-not-𝟘 (ap f p)
 where
  f : 𝔻 → 𝓤₀ ̇
  f midpoint  = 𝟙
  f (left _)  = 𝟘
  f (right _) = 𝟘

midpoint-is-not-right : {x : 𝔻} → midpoint ≢ right x
midpoint-is-not-right p = 𝟙-is-not-𝟘 (ap f p)
 where
  f : 𝔻 → 𝓤₀ ̇
  f midpoint  = 𝟙
  f (left _)  = 𝟘
  f (right _) = 𝟘

left-is-not-right : {x y : 𝔻} → left x ≢ right y
left-is-not-right p = 𝟙-is-not-𝟘 (ap f p)
 where
  f : 𝔻 → 𝓤₀ ̇
  f midpoint  = 𝟙
  f (left x)  = 𝟙
  f (right x) = 𝟘

left-lc : {x y : 𝔻} → left x ≡ left y → x ≡ y
left-lc = ap f
 where
  f : 𝔻 → 𝔻
  f midpoint = midpoint
  f (left x) = x
  f (right x) = right x

right-lc : {x y : 𝔻} → right x ≡ right y → x ≡ y
right-lc = ap f
 where
  f : 𝔻 → 𝔻
  f midpoint = midpoint
  f (left x) = left x
  f (right x) = x

𝔻-is-discrete : is-discrete 𝔻
𝔻-is-discrete midpoint midpoint = inl refl
𝔻-is-discrete midpoint (left y) = inr midpoint-is-not-left
𝔻-is-discrete midpoint (right y) = inr midpoint-is-not-right
𝔻-is-discrete (left x) midpoint = inr (λ p → midpoint-is-not-left (p ⁻¹))
𝔻-is-discrete (left x) (left y) = cases a b (𝔻-is-discrete x y)
 where
  a : x ≡ y → decidable (left x ≡ left y)
  a = inl ∘ ap left
  b : ¬ (x ≡ y) → decidable (left x ≡ left y)
  b = inr ∘ contrapositive left-lc
𝔻-is-discrete (left x) (right y) = inr left-is-not-right
𝔻-is-discrete (right x) midpoint = inr (λ p → midpoint-is-not-right (p ⁻¹))
𝔻-is-discrete (right x) (left y) = inr (λ p → left-is-not-right (p ⁻¹))
𝔻-is-discrete (right x) (right y) = cases a b (𝔻-is-discrete x y)
 where
  a : x ≡ y → decidable (right x ≡ right y)
  a = inl ∘ ap right
  b : ¬ (x ≡ y) → decidable (right x ≡ right y)
  b = inr ∘ contrapositive right-lc

\end{code}

\begin{code}

_≺_ : 𝔻 → 𝔻 → 𝓤₀ ̇
midpoint ≺ midpoint = 𝟘
left x ≺ midpoint = x ≺ midpoint + (midpoint ≡ x)
right x ≺ midpoint = x ≺ midpoint
midpoint ≺ left y = midpoint ≺ y
left x ≺ left y = x ≺ y
right x ≺ left y = x ≺ midpoint + midpoint ≺ y
midpoint ≺ right y = midpoint ≺ y + (y ≡ midpoint)
left x ≺ right y = (x ≺ midpoint + (midpoint ≡ x)) + (midpoint ≺ y + (y ≡ midpoint))
right x ≺ right y = x ≺ y

left-monotone : {x y : 𝔻} → x ≺ y → left x ≺ left y
left-monotone = id

right-monotone : {x y : 𝔻} → x ≺ y → right x ≺ right y
right-monotone = id


≺-to-≢ : {x y : 𝔻} → x ≺ y → x ≢ y
≺-to-≢ {midpoint} {midpoint}       = 𝟘-induction
≺-to-≢ {midpoint} {left y}   _     = midpoint-is-not-left
≺-to-≢ {midpoint} {right y}  _     = midpoint-is-not-right
≺-to-≢ {left x}   {midpoint} _   p = midpoint-is-not-left (p ⁻¹)
≺-to-≢ {left x}   {left y}   x≺y   = contrapositive left-lc (≺-to-≢ x≺y)
≺-to-≢ {left x}   {right y}  _     = left-is-not-right
≺-to-≢ {right x}  {midpoint} _ p   = midpoint-is-not-right (p ⁻¹)
≺-to-≢ {right x}  {left y}   _ p   = left-is-not-right (p ⁻¹)
≺-to-≢ {right x}  {right y}  x≺y   = contrapositive right-lc (≺-to-≢ x≺y)

{-
≺-to-¬≺-swapped : (x y : 𝔻) → x ≺ y → ¬ (y ≺ x)
≺-to-¬≺-swapped midpoint midpoint = 𝟘-induction
≺-to-¬≺-swapped (midpoint) (left y) mp≺y = cases a b
 where
  a : y ≺ midpoint → 𝟘
  a = ≺-to-¬≺-swapped midpoint y mp≺y
  b : midpoint ≡ y → 𝟘
  b = ≺-to-≢ mp≺y
≺-to-¬≺-swapped midpoint (right y) = cases a b
 where
  a : midpoint ≡ y → ¬ (right y ≺ midpoint)
  a mp≡y y≺mp = ≺-to-≢ y≺mp (mp≡y ⁻¹)
  b : midpoint ≺ y → ¬ (right y ≺ midpoint)
  b = ≺-to-¬≺-swapped midpoint y
≺-to-¬≺-swapped (left x) midpoint leftx≺mp = {!!}
≺-to-¬≺-swapped (left x) (left y) x≺y = ≺-to-¬≺-swapped x y x≺y
≺-to-¬≺-swapped (left x) (right y) = {!!}
≺-to-¬≺-swapped (right x) y = {!!}

≺-is-transitive : {x y z : 𝔻} → x ≺ y → y ≺ z → x ≺ z
≺-is-transitive {midpoint} {y} {midpoint} = {!!}
≺-is-transitive {midpoint} {y} {left z} = {!!}
≺-is-transitive {midpoint} {y} {right z} = {!!}
≺-is-transitive {left x} {y} {z} = {!!}
≺-is-transitive {right x} {y} {z} = {!!}
-}

\end{code}

\begin{code}

{-
left-≺ : (x : 𝔻) → left x ≺ x
left-≺ midpoint  = *
left-≺ (left x)  = left-≺ x
left-≺ (right x) = *

≺-sandwich : (x : 𝔻) → (right (left x) ≺ x) × (x ≺ left (right x))
≺-sandwich midpoint = * , *
≺-sandwich (left x) = {!!} , {!!}
≺-sandwich (right x) = {!!}

≺-right : (x : 𝔻) → x ≺ right x
≺-right midpoint  = *
≺-right (left x)  = *
≺-right (right x) = ≺-right x
-}

\end{code}

\begin{code}

\end{code}

One could (should?) phrase these using ∃ perhaps.

\begin{code}

\end{code}
