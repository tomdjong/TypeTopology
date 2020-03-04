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

\end{code}

\begin{code}

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

\end{code}

Can this be done with less cases?

At the very least, we should introduce a cases₃ constructions.

\begin{code}

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

≺-is-linear : (x y : 𝔻) → x ≺ y + (x ≡ y) + (y ≺ x)
≺-is-linear midpoint midpoint = inr (inl refl)
≺-is-linear midpoint (left y) = cases a b (≺-is-linear midpoint y)
 where
  a : midpoint ≺ y
    → (midpoint ≺ left y) + (midpoint ≡ left y) + (left y ≺ midpoint)
  a = inl
  b : (midpoint ≡ y) + (y ≺ midpoint)
    → (midpoint ≺ left y) + (midpoint ≡ left y) + (left y ≺ midpoint)
  b = cases c d
   where
    c : midpoint ≡ y
      → (midpoint ≺ left y) + (midpoint ≡ left y) + (left y ≺ midpoint)
    c = inr ∘ inr ∘ inr
    d : y ≺ midpoint
      → (midpoint ≺ left y) + (midpoint ≡ left y) + (left y ≺ midpoint)
    d = inr ∘ inr ∘ inl
≺-is-linear midpoint (right y) = cases a b (≺-is-linear midpoint y)
 where
  a : midpoint ≺ y
    → (midpoint ≺ right y) + (midpoint ≡ right y) + (right y ≺ midpoint)
  a = inl ∘ inl
  b : (midpoint ≡ y) + (y ≺ midpoint)
    → (midpoint ≺ right y) + (midpoint ≡ right y) + (right y ≺ midpoint)
  b = cases c d
   where
    c : midpoint ≡ y
      → (midpoint ≺ right y) + (midpoint ≡ right y) + (right y ≺ midpoint)
    c mp≡y = inl (inr (mp≡y ⁻¹))
    d : y ≺ midpoint
      → (midpoint ≺ right y) + (midpoint ≡ right y) + (right y ≺ midpoint)
    d = inr ∘ inr
≺-is-linear (left x) midpoint = cases a b (≺-is-linear x midpoint)
 where
  a : x ≺ midpoint
    → (left x ≺ midpoint) + (left x ≡ midpoint) + (midpoint ≺ left x)
  a = inl ∘ inl
  b : (x ≡ midpoint) + (midpoint ≺ x)
    → (left x ≺ midpoint) + (left x ≡ midpoint) + (midpoint ≺ left x)
  b = cases c d
   where
    c : x ≡ midpoint
      → (left x ≺ midpoint) + (left x ≡ midpoint) + (midpoint ≺ left x)
    c x≡mp = inl (inr (x≡mp ⁻¹))
    d : midpoint ≺ x
      → (left x ≺ midpoint) + (left x ≡ midpoint) + (midpoint ≺ left x)
    d = inr ∘ inr
≺-is-linear (left x) (left y) = cases a b (≺-is-linear x y)
 where
  a : x ≺ y → (left x ≺ left y) + (left x ≡ left y) + (left y ≺ left x)
  a x≺y = inl x≺y
  b : (x ≡ y) + (y ≺ x)
    → (left x ≺ left y) + (left x ≡ left y) + (left y ≺ left x)
  b = cases c d
   where
    c : x ≡ y → (left x ≺ left y) + (left x ≡ left y) + (left y ≺ left x)
    c x≡y = inr (inl (ap left x≡y))
    d : y ≺ x → (left x ≺ left y) + (left x ≡ left y) + (left y ≺ left x)
    d = inr ∘ inr
≺-is-linear (left x) (right y) = cases a b (≺-is-linear x y)
 where
  a : x ≺ y
    → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
  a x≺y = cases c d (≺-is-linear x midpoint)
   where
    c : x ≺ midpoint
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    c = inl ∘ inl ∘ inl
    d : (x ≡ midpoint) + (midpoint ≺ x)
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    d = cases e f
     where
      e : x ≡ midpoint
        → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
      e x≡mp = inl (inl (inr (x≡mp ⁻¹)))
      f : midpoint ≺ x
        → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
      f mp≺x = inl (inr (inl (≺-is-transitive midpoint x y mp≺x x≺y)))
  b : (x ≡ y) + (y ≺ x)
    → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
  b = cases c d
   where
    c : x ≡ y
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    c refl = cases e f (≺-is-linear x midpoint)
     where
      e : x ≺ midpoint
        → (left x ≺ right x) + (left x ≡ right x) + (right x ≺ left x)
      e = inl ∘ inl ∘ inl
      f : (x ≡ midpoint) + (midpoint ≺ x)
        → (left x ≺ right x) + (left x ≡ right x) + (right x ≺ left x)
      f = cases g h
       where
        g : x ≡ midpoint
          → (left x ≺ right x) + (left x ≡ right x) + (right x ≺ left x)
        g x≡mp = inl (inl (inr (x≡mp ⁻¹)))
        h : midpoint ≺ x
          → (left x ≺ right x) + (left x ≡ right x) + (right x ≺ left x)
        h mp≺x = inl (inr (inl mp≺x))
    d : y ≺ x
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    d y≺x = cases e f (≺-is-linear y midpoint)
     where
      e : y ≺ midpoint
        → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
      e y≺mp = cases g h (≺-is-linear x midpoint)
       where
        g : x ≺ midpoint
          → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
        g = inl ∘ inl ∘ inl
        h : (x ≡ midpoint) + (midpoint ≺ x)
          → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
        h = cases i j
         where
          i : x ≡ midpoint
            → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
          i x≡mp = inl (inl (inr (x≡mp ⁻¹)))
          j : midpoint ≺ x
            → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
          j mp≺x = inr (inr (y≺mp , mp≺x))
      f : (y ≡ midpoint) + (midpoint ≺ y)
        → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
      f = cases g h
       where
        g : y ≡ midpoint
          → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
        g y≡mp = inl (inr (inr y≡mp))
        h : midpoint ≺ y
          → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
        h mp≺y = inl (inr (inl mp≺y))
≺-is-linear (right x) midpoint = cases a b (≺-is-linear x midpoint)
 where
  a : x ≺ midpoint
    → (right x ≺ midpoint) + (right x ≡ midpoint) + (midpoint ≺ right x)
  a = inl
  b : (x ≡ midpoint) + (midpoint ≺ x)
    → (right x ≺ midpoint) + (right x ≡ midpoint) + (midpoint ≺ right x)
  b = cases c d
   where
    c : x ≡ midpoint
      → (right x ≺ midpoint) + (right x ≡ midpoint) + (midpoint ≺ right x)
    c = inr ∘ inr ∘ inr
    d : midpoint ≺ x
      → (right x ≺ midpoint) + (right x ≡ midpoint) + (midpoint ≺ right x)
    d mp≺x = inr (inr (inl mp≺x))
≺-is-linear (right x) (left y) = cases a b (≺-is-linear x y)
 where
  a : x ≺ y
    → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
  a x≺y = cases c d (≺-is-linear y midpoint)
   where
    c : y ≺ midpoint
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    c y≺mp = inr (inr (inl (inl y≺mp)))
    d : (y ≡ midpoint) + (midpoint ≺ y)
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    d = cases e f
     where
      e : y ≡ midpoint
        → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
      e y≡mp = inr (inr (inl (inr (y≡mp ⁻¹))))
      f : midpoint ≺ y
        → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
      f mp≺y = cases g h (≺-is-linear x midpoint)
       where
        g : x ≺ midpoint
          → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
        g x≺mp = inl (x≺mp , mp≺y)
        h : (x ≡ midpoint) + (midpoint ≺ x)
          → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
        h = cases i j
         where
          i : x ≡ midpoint
            → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
          i = inr ∘ inr ∘ inr ∘ inr
          j : midpoint ≺ x
            → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
          j mp≺x = inr (inr (inr (inl mp≺x)))
  b : (x ≡ y) + (y ≺ x)
    → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
  b = cases c d
   where
    c : x ≡ y
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    c refl = cases e f (≺-is-linear x midpoint)
     where
      e : x ≺ midpoint
        → (right x ≺ left x) + (right x ≡ left x) + (left x ≺ right x)
      e x≺mp = inr (inr (inl (inl x≺mp)))
      f : (x ≡ midpoint) + (midpoint ≺ x)
        → (right x ≺ left x) + (right x ≡ left x) + (left x ≺ right x)
      f = cases g h
       where
        g : x ≡ midpoint
          → (right x ≺ left x) + (right x ≡ left x) + (left x ≺ right x)
        g = inr ∘ inr ∘ inr ∘ inr
        h : midpoint ≺ x
          → (right x ≺ left x) + (right x ≡ left x) + (left x ≺ right x)
        h mp≺x = inr (inr (inr (inl mp≺x)))
    d : y ≺ x
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    d y≺x = cases e f (≺-is-linear x midpoint)
     where
      e : x ≺ midpoint
        → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
      e x≺mp = inr (inr (inl (inl (≺-is-transitive y x midpoint y≺x x≺mp))))
      f : (x ≡ midpoint) + (midpoint ≺ x)
        → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
      f = cases g h
       where
        g : x ≡ midpoint
          → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
        g = inr ∘ inr ∘ inr ∘ inr
        h : midpoint ≺ x
          → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
        h mp≺x = inr (inr (inr (inl mp≺x)))
≺-is-linear (right x) (right y) = cases a b (≺-is-linear x y)
 where
  a : x ≺ y
    → (right x ≺ right y) + (right x ≡ right y) + (right y ≺ right x)
  a = inl
  b : (x ≡ y) + (y ≺ x)
    → (right x ≺ right y) + (right x ≡ right y) + (right y ≺ right x)
  b = cases c d
   where
    c : x ≡ y
      → (right x ≺ right y) + (right x ≡ right y) + (right y ≺ right x)
    c x≡y = inr (inl (ap right x≡y))
    d : y ≺ x
      → (right x ≺ right y) + (right x ≡ right y) + (right y ≺ right x)
    d = inr ∘ inr

\end{code}

\begin{code}

left-≺ : (x : 𝔻) → left x ≺ x
left-≺ midpoint  = inr refl
left-≺ (left x)  = left-≺ x
left-≺ (right x) = cases₃ a b c h
 where
  a : x ≺ midpoint → left (right x) ≺ right x
  a = inl ∘ inl
  b : x ≡ midpoint → left (right x) ≺ right x
  b = inr ∘ inr
  c : midpoint ≺ x → left (right x) ≺ right x
  c = inr ∘ inl
  h : (x ≺ midpoint) + (x ≡ midpoint) + (midpoint ≺ x)
  h = ≺-is-linear x midpoint

≺-right : (x : 𝔻) → x ≺ right x
≺-right midpoint  = inr refl
≺-right (left x)  = cases₃ a b c h
 where
  a : x ≺ midpoint → left x ≺ right (left x)
  a = inl ∘ inl
  b : x ≡ midpoint → left x ≺ right (left x)
  b x≡mp = inl (inr (x≡mp ⁻¹))
  c : midpoint ≺ x → left x ≺ right (left x)
  c = inr ∘ inl
  h : (x ≺ midpoint) + (x ≡ midpoint) + (midpoint ≺ x)
  h = ≺-is-linear x midpoint
≺-right (right x) = ≺-right x

\end{code}

\begin{code}

test : (x : 𝔻) → left x ≺ left (right (left x)) × left (right (left x)) ≺ x
test midpoint = {!!} , {!!}
test (left x) = {!!}
test (right x) = {!!}

≺-sandwich : (x : 𝔻)
           → (Σ y ꞉ 𝔻 , left x ≺ y × y ≺ x)
           × (Σ z ꞉ 𝔻 , x ≺ z × z ≺ right x)
≺-sandwich midpoint =
 (right (left midpoint) , inl (inr refl) , inr refl) ,
 (left (right midpoint) , inr refl , inr (inr refl))
≺-sandwich (left x) =
 (left y , lx≺y , y≺x) , left z , {!!} , {!!} -- left z , x≺z , cases₃ a b c (≺-is-linear z midpoint)
  where
   IH : (Σ y ꞉ 𝔻 , left x ≺ y × y ≺ x)
      × (Σ z ꞉ 𝔻 , x ≺ z × z ≺ right x)
   IH = ≺-sandwich x
   y : 𝔻
   y = pr₁ (pr₁ IH)
   lx≺y : left x ≺ y
   lx≺y = pr₁ (pr₂ (pr₁ IH))
   y≺x : y ≺ x
   y≺x = pr₂ (pr₂ (pr₁ IH))
   z : 𝔻
   z = pr₁ (pr₂ IH)
   x≺z : x ≺ z
   x≺z = pr₁ (pr₂ (pr₂ IH))
   z≺rx : z ≺ right x
   z≺rx = pr₂ (pr₂ (pr₂ IH))
   a : z ≺ midpoint → left z ≺ right (left x)
   a = inl ∘ inl
   b : z ≡ midpoint → left z ≺ right (left x)
   b z≡mp = inl (inr (z≡mp ⁻¹))
   c : midpoint ≺ z → left z ≺ right (left x)
   c mp≺z = cases₃ {!!} {!z≺rx!} {!!} (≺-is-linear x midpoint)
≺-sandwich (right x) = {!!}

{-right y , cases₃ a b c (≺-is-linear y midpoint)
 where
  IH : (Σ y ꞉ 𝔻 , left x ≺ y × y ≺ x)
  IH = ≺-sandwich x
  y : 𝔻
  y = pr₁ IH
  lx≺y : left x ≺ y
  lx≺y = pr₁ (pr₂ IH)
  y≺x : y ≺ x
  y≺x = pr₂ (pr₂ IH)
  a : y ≺ midpoint → (left (right x) ≺ right y) × (right y ≺ right x)
  a y≺mp = {!!}
  b : y ≡ midpoint → (left (right x) ≺ right y) × (right y ≺ right x)
  b y≡mp = inr (inr y≡mp) , y≺x
  c : midpoint ≺ y → (left (right x) ≺ right y) × (right y ≺ right x)
  c mp≺y = (inr (inl mp≺y)) , y≺x -}

{-
≺-density : (x y : 𝔻) → x ≺ y → Σ z ꞉ 𝔻 , x ≺ z × z ≺ y
≺-density midpoint midpoint = 𝟘-induction
≺-density midpoint (left y) mp≺y = (pr₁ h) , {!!}
 where
  h : Σ z ꞉ 𝔻 , midpoint ≺ z × z ≺ y
  h = ≺-density midpoint y mp≺y
≺-density midpoint (right y) = {!!}
≺-density (left x) y = {!!}
≺-density (right x) y = {!!}

open import UF-PropTrunc

module _ (pt : propositional-truncations-exist) where
 open PropositionalTruncation pt

 ≺-has-no-lowest-point : (x : 𝔻) → ∃ y ꞉ 𝔻 , y ≺ x
 ≺-has-no-lowest-point x = ∣ (left x) , (left-≺ x) ∣

 ≺-is-dense : (x y : 𝔻) → x ≺ y → ∃ z ꞉ 𝔻 , x ≺ z × z ≺ y
 ≺-is-dense midpoint midpoint = 𝟘-induction
 ≺-is-dense midpoint (left y) mp≺y = {!!}
 ≺-is-dense midpoint (right y) = {!!}
 ≺-is-dense (left x) y = {!!}
 ≺-is-dense (right x) y = {!!}
-}

\end{code}
