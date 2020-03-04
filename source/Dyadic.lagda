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
right x ≺ left y = x ≺ midpoint × midpoint ≺ y
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

≡-to-¬≺ : {x y : 𝔻} → x ≡ y → ¬ (x ≺ y)
≡-to-¬≺ x≡y x≺y = ≺-to-≢ x≺y x≡y

≡-to-¬≺' : {x y : 𝔻} → x ≡ y → ¬ (y ≺ x)
≡-to-¬≺' x≡y y≺x = ≺-to-≢ y≺x (x≡y ⁻¹)

≺-to-¬≺ : (x y : 𝔻) → x ≺ y → ¬ (y ≺ x)
≺-to-¬≺ midpoint midpoint = 𝟘-induction
≺-to-¬≺ midpoint (left y) mp≺y = cases a b
 where
  a : ¬ (y ≺ midpoint)
  a = ≺-to-¬≺ midpoint y mp≺y
  b : midpoint ≢ y
  b = ≺-to-≢ mp≺y
≺-to-¬≺ midpoint (right y) = cases a b
 where
  a : midpoint ≺ y → ¬ (y ≺ midpoint)
  a = ≺-to-¬≺ midpoint y
  b : y ≡ midpoint → ¬ (right y ≺ midpoint)
  b = ≡-to-¬≺
≺-to-¬≺ (left x) midpoint = cases a b
 where
  a : x ≺ midpoint → ¬ (midpoint ≺ left x)
  a = ≺-to-¬≺ x midpoint
  b : midpoint ≡ x → ¬ (midpoint ≺ left x)
  b = ≡-to-¬≺
≺-to-¬≺ (left x) (left y) = ≺-to-¬≺ x y
≺-to-¬≺ (left x) (right y) = cases a b
 where
  a : (x ≺ midpoint) + (midpoint ≡ x) → ¬ (right y ≺ left x)
  a = cases c d
   where
    c : x ≺ midpoint → ¬ (right y ≺ left x)
    c x≺mp (_ , mp≺x) = ≺-to-¬≺ x midpoint x≺mp mp≺x
    d : midpoint ≡ x → ¬ (right y ≺ left x)
    d mp≡x (_ , mp≺x) = ≡-to-¬≺ mp≡x mp≺x
  b : (midpoint ≺ y) + (y ≡ midpoint) → ¬ (right y ≺ left x)
  b = cases c d
   where
    c : midpoint ≺ y → ¬ (right y ≺ left x)
    c mp≺y (y≺mp , _) = ≺-to-¬≺ midpoint y mp≺y y≺mp
    d : y ≡ midpoint → ¬ (right y ≺ left x)
    d y≡mp (y≺mp , _) = ≡-to-¬≺ y≡mp y≺mp
≺-to-¬≺ (right x) midpoint x≺mp = cases a b
 where
  a : midpoint ≺ x → 𝟘
  a = ≺-to-¬≺ x midpoint x≺mp
  b : x ≡ midpoint → 𝟘
  b = ≺-to-≢ x≺mp
≺-to-¬≺ (right x) (left y) (x≺mp , mp≺y) = cases a b
 where
  a : (y ≺ midpoint) + (midpoint ≡ y) → 𝟘
  a = cases c d
   where
    c : y ≺ midpoint → 𝟘
    c = ≺-to-¬≺ midpoint y mp≺y
    d : midpoint ≡ y → 𝟘
    d = ≺-to-≢ mp≺y
  b : (midpoint ≺ x) + (x ≡ midpoint) → 𝟘
  b = cases c d
   where
    c : midpoint ≺ x → 𝟘
    c = ≺-to-¬≺ x midpoint x≺mp
    d : x ≡ midpoint → 𝟘
    d = ≺-to-≢ x≺mp
≺-to-¬≺ (right x) (right y) = ≺-to-¬≺ x y

≺-is-transitive : (x y z : 𝔻) → x ≺ y → y ≺ z → x ≺ z
≺-is-transitive midpoint y midpoint = ≺-to-¬≺ midpoint y
≺-is-transitive (left x) midpoint midpoint = λ _ → 𝟘-induction
≺-is-transitive (left x) (left y) midpoint x≺y = cases a b
 where
  a : y ≺ midpoint → left x ≺ midpoint
  a y≺mp = inl (≺-is-transitive x y midpoint x≺y y≺mp)
  b : midpoint ≡ y → left x ≺ midpoint
  b refl = inl x≺y
≺-is-transitive (left x) (right y) midpoint = cases a b
 where
  a : (x ≺ midpoint) + (midpoint ≡ x)
    → right y ≺ midpoint → left x ≺ midpoint
  a = cases c d
   where
    c : x ≺ midpoint → right y ≺ midpoint → left x ≺ midpoint
    c x≺mp _ = inl x≺mp
    d : midpoint ≡ x → right y ≺ midpoint → left x ≺ midpoint
    d mp≡x _ = inr mp≡x
  b : (midpoint ≺ y) + (y ≡ midpoint)
    → right y ≺ midpoint → left x ≺ midpoint
  b = cases c d
   where
    c : midpoint ≺ y → right y ≺ midpoint → left x ≺ midpoint
    c mp≺y y≺mp = 𝟘-induction (≺-to-¬≺ midpoint y mp≺y y≺mp)
    d : y ≡ midpoint → right y ≺ midpoint → left x ≺ midpoint
    d y≡mp y≺mp = 𝟘-induction (≺-to-≢ y≺mp y≡mp)
≺-is-transitive (right x) midpoint midpoint _ = 𝟘-induction
≺-is-transitive (right x) (left y) midpoint (x≺mp , _) _ = x≺mp
≺-is-transitive (right x) (right y) midpoint = ≺-is-transitive x y midpoint
≺-is-transitive midpoint midpoint (left z) = 𝟘-induction
≺-is-transitive midpoint (left y) (left z) = ≺-is-transitive midpoint y z
≺-is-transitive midpoint (right y) (left z) = cases a b
 where
  a : midpoint ≺ y → right y ≺ left z → midpoint ≺ left z
  a mp≺y (y≺mp , _) = 𝟘-induction (≺-to-¬≺ midpoint y mp≺y y≺mp)
  b : y ≡ midpoint → right y ≺ left z → midpoint ≺ left z
  b y≡mp (y≺mp , _) = 𝟘-induction (≺-to-≢ y≺mp y≡mp)
≺-is-transitive (left x) midpoint (left z) = cases a b
 where
  a : x ≺ midpoint → midpoint ≺ left z → left x ≺ left z
  a = ≺-is-transitive x midpoint z
  b : midpoint ≡ x → midpoint ≺ left z → left x ≺ left z
  b refl = id
≺-is-transitive (left x) (left y) (left z) = ≺-is-transitive x y z
≺-is-transitive (left x) (right y) (left z) = cases a b
 where
  a : (x ≺ midpoint) + (midpoint ≡ x)
    → right y ≺ left z → left x ≺ left z
  a = cases c d
   where
    c : x ≺ midpoint → right y ≺ left z → left x ≺ left z
    c x≺mp (_ , mp≺z) = ≺-is-transitive x midpoint z x≺mp mp≺z
    d : midpoint ≡ x → right y ≺ left z → left x ≺ left z
    d refl = pr₂
  b : (midpoint ≺ y) + (y ≡ midpoint)
    → right y ≺ left z → left x ≺ left z
  b = cases c d
   where
    c : midpoint ≺ y → right y ≺ left z → left x ≺ left z
    c mp≺y (y≺mp , _) = 𝟘-induction (≺-to-¬≺ midpoint y mp≺y y≺mp)
    d : y ≡ midpoint → right y ≺ left z → left x ≺ left z
    d y≡mp (y≺mp , _) = 𝟘-induction (≺-to-≢ y≺mp y≡mp)
≺-is-transitive (right x) midpoint (left z) x≺mp mp≺z = x≺mp , mp≺z
≺-is-transitive (right x) (left y) (left z) (x≺mp , mp≺y) y≺z =
 x≺mp , (≺-is-transitive midpoint y z mp≺y y≺z)
≺-is-transitive (right x) (right y) (left z) x≺y (y≺mp , mp≺z) =
 (≺-is-transitive x y midpoint x≺y y≺mp) , mp≺z
≺-is-transitive midpoint midpoint (right z) = 𝟘-induction
≺-is-transitive midpoint (left y) (right z) mp≺y = cases a b
 where
  a : (y ≺ midpoint) + (midpoint ≡ y) → midpoint ≺ right z
  a = cases c d
   where
    c : y ≺ midpoint → midpoint ≺ right z
    c y≺mp = 𝟘-induction (≺-to-¬≺ y midpoint y≺mp mp≺y)
    d : midpoint ≡ y → midpoint ≺ right z
    d mp≡y = 𝟘-induction (≺-to-≢ mp≺y mp≡y)
  b : (midpoint ≺ z) + (z ≡ midpoint) → midpoint ≺ right z
  b = cases c d
   where
    c : midpoint ≺ z → midpoint ≺ right z
    c = inl
    d : z ≡ midpoint → midpoint ≺ right z
    d = inr
≺-is-transitive midpoint (right y) (right z) = cases a b
 where
  a : midpoint ≺ y → right y ≺ right z → midpoint ≺ right z
  a mp≺y y≺z = inl (≺-is-transitive midpoint y z mp≺y y≺z)
  b : y ≡ midpoint → right y ≺ right z → midpoint ≺ right z
  b refl = inl
≺-is-transitive (left x) midpoint (right z) = cases a b
 where
  a : x ≺ midpoint → midpoint ≺ right z → left x ≺ right z
  a x≺mp _ = inl (inl x≺mp)
  b : midpoint ≡ x → midpoint ≺ right z → left x ≺ right z
  b mp≡x _ = inl (inr mp≡x)
≺-is-transitive (left x) (left y) (right z) x≺y = cases a b
 where
  a : (y ≺ midpoint) + (midpoint ≡ y) → left x ≺ right z
  a = cases c d
   where
    c : y ≺ midpoint → left x ≺ right z
    c y≺mp = inl (inl (≺-is-transitive x y midpoint x≺y y≺mp))
    d : midpoint ≡ y → left x ≺ right z
    d refl = inl (inl x≺y)
  b : (midpoint ≺ z) + (z ≡ midpoint) → left x ≺ right z
  b = cases c d
   where
    c : midpoint ≺ z → left x ≺ right z
    c mp≺z = inr (inl mp≺z)
    d : z ≡ midpoint → left x ≺ right z
    d z≡mp = inr (inr z≡mp)
≺-is-transitive (left x) (right y) (right z) = cases a b
 where
  a : (x ≺ midpoint) + (midpoint ≡ x) →
        right y ≺ right z → left x ≺ right z
  a = cases c d
   where
    c : x ≺ midpoint → right y ≺ right z → left x ≺ right z
    c x≺mp _ = inl (inl x≺mp)
    d : midpoint ≡ x → right y ≺ right z → left x ≺ right z
    d mp≡x _ = inl (inr mp≡x)
  b : (midpoint ≺ y) + (y ≡ midpoint) →
        right y ≺ right z → left x ≺ right z
  b = cases c d
   where
    c : midpoint ≺ y → right y ≺ right z → left x ≺ right z
    c mp≺y y≺z = inr (inl (≺-is-transitive midpoint y z mp≺y y≺z))
    d : y ≡ midpoint → right y ≺ right z → left x ≺ right z
    d refl mp≺z = inr (inl mp≺z)
≺-is-transitive (right x) midpoint (right z) x≺mp = cases a b
 where
  a : midpoint ≺ z → right x ≺ right z
  a = ≺-is-transitive x midpoint z x≺mp
  b : z ≡ midpoint → right x ≺ right z
  b refl = x≺mp
≺-is-transitive (right x) (left y) (right z) (x≺mp , mp≺y) = cases a b
 where
  a : (y ≺ midpoint) + (midpoint ≡ y) → right x ≺ right z
  a = cases c d
   where
    c : y ≺ midpoint → right x ≺ right z
    c y≺mp = 𝟘-induction (≺-to-¬≺ midpoint y mp≺y y≺mp)
    d : midpoint ≡ y → right x ≺ right z
    d mp≡y = 𝟘-induction (≺-to-≢ mp≺y mp≡y)
  b : (midpoint ≺ z) + (z ≡ midpoint) → right x ≺ right z
  b =  cases c d
   where
    c : midpoint ≺ z → right x ≺ right z
    c = ≺-is-transitive x midpoint z x≺mp
    d : z ≡ midpoint → right x ≺ right z
    d refl = x≺mp
≺-is-transitive (right x) (right y) (right z) = ≺-is-transitive x y z

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
