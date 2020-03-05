Tom de Jong, 3 March 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import DiscreteAndSeparated
open import One-Properties
open import UF-Miscelanea
open import UF-Subsingletons

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

𝔻-is-a-set : is-set 𝔻
𝔻-is-a-set = discrete-types-are-sets 𝔻-is-discrete

\end{code}

\begin{code}

_≺_ : 𝔻 → 𝔻 → 𝓤₀ ̇
midpoint ≺ midpoint = 𝟘
left x   ≺ midpoint = x ≺ midpoint + (midpoint ≡ x)
right x  ≺ midpoint = x ≺ midpoint
midpoint ≺ left y   = midpoint ≺ y
left x   ≺ left y   = x ≺ y
right x  ≺ left y   = x ≺ midpoint × midpoint ≺ y
midpoint ≺ right y  = midpoint ≺ y + (y ≡ midpoint)
left x   ≺ right y  = (x ≺ midpoint + (midpoint ≡ x)) +
                      (midpoint ≺ y + (y ≡ midpoint))
right x  ≺ right y  = x ≺ y

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
≺-to-≢ {right x}  {midpoint} _   p = midpoint-is-not-right (p ⁻¹)
≺-to-≢ {right x}  {left y}   _   p = left-is-not-right (p ⁻¹)
≺-to-≢ {right x}  {right y}  x≺y   = contrapositive right-lc (≺-to-≢ x≺y)

≺-to-≢' : {x y : 𝔻} → y ≺ x → x ≢ y
≺-to-≢' y≺x p = ≺-to-≢ y≺x (p ⁻¹)

≡-to-¬≺ : {x y : 𝔻} → x ≡ y → ¬ (x ≺ y)
≡-to-¬≺ x≡y x≺y = ≺-to-≢ x≺y x≡y

≡-to-¬≺' : {x y : 𝔻} → x ≡ y → ¬ (y ≺ x)
≡-to-¬≺' x≡y y≺x = ≺-to-≢ y≺x (x≡y ⁻¹)

\end{code}

\begin{code}

≺-is-prop-valued : (x y : 𝔻) → is-prop (x ≺ y)
≺-is-prop-valued midpoint midpoint = 𝟘-is-prop
≺-is-prop-valued midpoint (left y) = ≺-is-prop-valued midpoint y
≺-is-prop-valued midpoint (right y) =
 +-is-prop (≺-is-prop-valued midpoint y) 𝔻-is-a-set ≺-to-≢'
≺-is-prop-valued (left x) midpoint =
 +-is-prop (≺-is-prop-valued x midpoint) 𝔻-is-a-set ≺-to-≢'
≺-is-prop-valued (left x) (left y) = ≺-is-prop-valued x y
≺-is-prop-valued (left x) (right y) = {!!}
{-
 +-is-prop
  (+-is-prop (≺-is-prop-valued x midpoint) 𝔻-is-a-set ≺-to-≢')
  (+-is-prop (≺-is-prop-valued midpoint y) 𝔻-is-a-set ≺-to-≢')
  {!!} -}
≺-is-prop-valued (right x) midpoint = ≺-is-prop-valued x midpoint
≺-is-prop-valued (right x) (left y) =
 ×-is-prop (≺-is-prop-valued x midpoint) (≺-is-prop-valued midpoint y)
≺-is-prop-valued (right x) (right y) = ≺-is-prop-valued x y

\end{code}

\begin{code}

{-
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

\begin{code}

≺-is-transitive : (x y z : 𝔻) → x ≺ y → y ≺ z → x ≺ z
≺-is-transitive midpoint y midpoint = ≺-to-¬≺ midpoint y
≺-is-transitive (left x) midpoint midpoint _ = 𝟘-induction
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

≺-is-linear : (x y : 𝔻) → x ≺ y + (x ≡ y) + (y ≺ x)
≺-is-linear midpoint midpoint = inr (inl refl)
≺-is-linear midpoint (left y) = cases₃ a b c (≺-is-linear midpoint y)
 where
  a : midpoint ≺ y
    → (midpoint ≺ left y) + (midpoint ≡ left y) + (left y ≺ midpoint)
  a = inl
  b : midpoint ≡ y
    → (midpoint ≺ left y) + (midpoint ≡ left y) + (left y ≺ midpoint)
  b = inr ∘ inr ∘ inr
  c : y ≺ midpoint
    → (midpoint ≺ left y) + (midpoint ≡ left y) + (left y ≺ midpoint)
  c = inr ∘ inr ∘ inl
≺-is-linear midpoint (right y) = cases₃ a b c (≺-is-linear midpoint y)
 where
  a : midpoint ≺ y
    → (midpoint ≺ right y) + (midpoint ≡ right y) + (right y ≺ midpoint)
  a = inl ∘ inl
  b : midpoint ≡ y
    → (midpoint ≺ right y) + (midpoint ≡ right y) + (right y ≺ midpoint)
  b mp≡y = inl (inr (mp≡y ⁻¹))
  c : y ≺ midpoint
    → (midpoint ≺ right y) + (midpoint ≡ right y) + (right y ≺ midpoint)
  c = inr ∘ inr
≺-is-linear (left x) midpoint = cases₃ a b c (≺-is-linear x midpoint)
 where
  a : x ≺ midpoint
    → (left x ≺ midpoint) + (left x ≡ midpoint) + (midpoint ≺ left x)
  a = inl ∘ inl
  b : x ≡ midpoint
    → (left x ≺ midpoint) + (left x ≡ midpoint) + (midpoint ≺ left x)
  b x≡mp = inl (inr (x≡mp ⁻¹))
  c : midpoint ≺ x
    → (left x ≺ midpoint) + (left x ≡ midpoint) + (midpoint ≺ left x)
  c = inr ∘ inr
≺-is-linear (left x) (left y) = cases₃ a b c (≺-is-linear x y)
 where
  a : x ≺ y → (left x ≺ left y) + (left x ≡ left y) + (left y ≺ left x)
  a x≺y = inl x≺y
  b : x ≡ y → (left x ≺ left y) + (left x ≡ left y) + (left y ≺ left x)
  b x≡y = inr (inl (ap left x≡y))
  c : y ≺ x → (left x ≺ left y) + (left x ≡ left y) + (left y ≺ left x)
  c = inr ∘ inr
≺-is-linear (left x) (right y) = cases₃ a b c (≺-is-linear x y)
 where
  a : x ≺ y
    → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
  a x≺y = cases₃ d e f (≺-is-linear x midpoint)
   where
    d : x ≺ midpoint
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    d = inl ∘ inl ∘ inl
    e : x ≡ midpoint
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    e x≡mp = inl (inl (inr (x≡mp ⁻¹)))
    f : midpoint ≺ x
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    f mp≺x = inl (inr (inl (≺-is-transitive midpoint x y mp≺x x≺y)))
  b : x ≡ y
    → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
  b refl = cases₃ d e f (≺-is-linear x midpoint)
   where
    d : x ≺ midpoint
      → (left x ≺ right x) + (left x ≡ right x) + (right x ≺ left x)
    d = inl ∘ inl ∘ inl
    e : x ≡ midpoint
      → (left x ≺ right x) + (left x ≡ right x) + (right x ≺ left x)
    e x≡mp = inl (inl (inr (x≡mp ⁻¹)))
    f : midpoint ≺ x
      → (left x ≺ right x) + (left x ≡ right x) + (right x ≺ left x)
    f mp≺x = inl (inr (inl mp≺x))
  c : y ≺ x
    → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
  c y≺x = cases₃ d e f (≺-is-linear y midpoint)
   where
    d : y ≺ midpoint
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    d y≺mp = cases₃ g h k (≺-is-linear x midpoint)
     where
      g : x ≺ midpoint
        → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
      g = inl ∘ inl ∘ inl
      h : x ≡ midpoint
        → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
      h x≡mp = inl (inl (inr (x≡mp ⁻¹)))
      k : midpoint ≺ x
        → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
      k mp≺x = inr (inr (y≺mp , mp≺x))
    e : y ≡ midpoint
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    e y≡mp = inl (inr (inr y≡mp))
    f : midpoint ≺ y
      → (left x ≺ right y) + (left x ≡ right y) + (right y ≺ left x)
    f mp≺y = inl (inr (inl mp≺y))
≺-is-linear (right x) midpoint = cases₃ a b c (≺-is-linear x midpoint)
 where
  a : x ≺ midpoint
    → (right x ≺ midpoint) + (right x ≡ midpoint) + (midpoint ≺ right x)
  a = inl
  b : x ≡ midpoint
    → (right x ≺ midpoint) + (right x ≡ midpoint) + (midpoint ≺ right x)
  b = inr ∘ inr ∘ inr
  c : midpoint ≺ x
    → (right x ≺ midpoint) + (right x ≡ midpoint) + (midpoint ≺ right x)
  c mp≺x = inr (inr (inl mp≺x))
≺-is-linear (right x) (left y) = cases₃ a b c (≺-is-linear x y)
 where
  a : x ≺ y
    → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
  a x≺y = cases₃ d e f (≺-is-linear y midpoint)
   where
    d : y ≺ midpoint
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    d y≺mp = inr (inr (inl (inl y≺mp)))
    e : y ≡ midpoint
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    e y≡mp = inr (inr (inl (inr (y≡mp ⁻¹))))
    f : midpoint ≺ y
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    f mp≺y = cases₃ g h k (≺-is-linear x midpoint)
     where
      g : x ≺ midpoint
        → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
      g x≺mp = inl (x≺mp , mp≺y)
      h : x ≡ midpoint
        → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
      h = inr ∘ inr ∘ inr ∘ inr
      k : midpoint ≺ x
        → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
      k mp≺x = inr (inr (inr (inl mp≺x)))
  b : x ≡ y
    → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
  b refl = cases₃ d e f (≺-is-linear x midpoint)
   where
    d : x ≺ midpoint
      → (right x ≺ left x) + (right x ≡ left x) + (left x ≺ right x)
    d x≺mp = inr (inr (inl (inl x≺mp)))
    e : x ≡ midpoint
      → (right x ≺ left x) + (right x ≡ left x) + (left x ≺ right x)
    e = inr ∘ inr ∘ inr ∘ inr
    f : midpoint ≺ x
      → (right x ≺ left x) + (right x ≡ left x) + (left x ≺ right x)
    f mp≺x = inr (inr (inr (inl mp≺x)))
  c : y ≺ x
    → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
  c y≺x = cases₃ d e f (≺-is-linear x midpoint)
   where
    d : x ≺ midpoint
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    d x≺mp = inr (inr (inl (inl (≺-is-transitive y x midpoint y≺x x≺mp))))
    e : x ≡ midpoint
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    e = inr ∘ inr ∘ inr ∘ inr
    f : midpoint ≺ x
      → (right x ≺ left y) + (right x ≡ left y) + (left y ≺ right x)
    f mp≺x = inr (inr (inr (inl mp≺x)))
≺-is-linear (right x) (right y) = cases₃ a b c (≺-is-linear x y)
 where
  a : x ≺ y
    → (right x ≺ right y) + (right x ≡ right y) + (right y ≺ right x)
  a = inl
  b : x ≡ y
    → (right x ≺ right y) + (right x ≡ right y) + (right y ≺ right x)
  b x≡y = inr (inl (ap right x≡y))
  c : y ≺ x
    → (right x ≺ right y) + (right x ≡ right y) + (right y ≺ right x)
  c = inr ∘ inr

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

≺-density : (x y : 𝔻) → x ≺ y → Σ z ꞉ 𝔻 , x ≺ z × z ≺ y
≺-density midpoint midpoint = 𝟘-induction
≺-density midpoint (left y) mp≺y = left z , mp≺z , z≺y
 where
  IH : Σ z ꞉ 𝔻 , midpoint ≺ z × z ≺ y
  IH = ≺-density midpoint y mp≺y
  z : 𝔻
  z = pr₁ IH
  mp≺z : midpoint ≺ z
  mp≺z = pr₁ (pr₂ IH)
  z≺y : z ≺ y
  z≺y = pr₂ (pr₂ IH)
≺-density midpoint (right y) = cases a b
 where
  a : midpoint ≺ y → Σ z ꞉ 𝔻 , midpoint ≺ z × z ≺ right y
  a mp≺y = y , mp≺y , ≺-right y
  b : y ≡ midpoint → Σ z ꞉ 𝔻 , midpoint ≺ z × z ≺ right y
  b refl = left (right midpoint) , inr refl , inr (inr refl)
≺-density (left x) midpoint = cases a b
 where
  a : x ≺ midpoint → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ midpoint
  a x≺mp = x , left-≺ x , x≺mp
  b : midpoint ≡ x → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ midpoint
  b refl = right (left midpoint) , inl (inr refl) , inr refl
≺-density (left x) (left y) x≺y = left z , x≺z , z≺y
 where
  IH : Σ z ꞉ 𝔻 , x ≺ z × z ≺ y
  IH = ≺-density x y x≺y
  z : 𝔻
  z = pr₁ IH
  x≺z : x ≺ z
  x≺z = pr₁ (pr₂ IH)
  z≺y : z ≺ y
  z≺y = pr₂ (pr₂ IH)
≺-density (left x) (right y) = cases a b
 where
  a : (x ≺ midpoint) + (midpoint ≡ x)
    → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right y
  a = cases c d
   where
    c : x ≺ midpoint → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right y
    c x≺mp = left midpoint , x≺mp , inl (inr refl)
    d : midpoint ≡ x → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right y
    d refl = cases₃ e f g (≺-is-linear y midpoint)
     where
      e : y ≺ midpoint → Σ z ꞉ 𝔻 , left midpoint ≺ z × z ≺ right y
      e y≺mp = cases₃ i j k (≺-is-linear y (left midpoint))
       where
        i : y ≺ left midpoint → Σ z ꞉ 𝔻 , left midpoint ≺ z × z ≺ right y
        i y≺lmp = right (left y) , inl (inr refl) , left-≺ y
        j : y ≡ left midpoint → Σ z ꞉ 𝔻 , left midpoint ≺ z × z ≺ right y
        j refl = right (left (left midpoint)) , inl (inr refl) , inr refl
        k : left midpoint ≺ y → Σ z ꞉ 𝔻 , left midpoint ≺ z × z ≺ right y
        k lmp≺y = y , lmp≺y , ≺-right y
      f : y ≡ midpoint → Σ z ꞉ 𝔻 , left midpoint ≺ z × z ≺ right y
      f refl = midpoint , inr refl , inr refl
      g : midpoint ≺ y → Σ z ꞉ 𝔻 , left midpoint ≺ z × z ≺ right y
      g mp≺y = y , h , ≺-right y
       where
        h : left midpoint ≺ y
        h = ≺-is-transitive (left midpoint) midpoint y (left-≺ midpoint) mp≺y
  b : (midpoint ≺ y) + (y ≡ midpoint)
    → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right y
  b = cases c d
   where
    c : midpoint ≺ y → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right y
    c mp≺y = right midpoint , inr (inr refl) , mp≺y
    d : y ≡ midpoint → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right y
    d refl = cases₃ e f g (≺-is-linear x midpoint)
     where
      e : x ≺ midpoint → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right midpoint
      e x≺mp = left midpoint , x≺mp , inr (inr refl)
      f : x ≡ midpoint → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right midpoint
      f refl = midpoint , inr refl , inr refl
      g : midpoint ≺ x → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right midpoint
      g mp≺x = cases₃ i j k (≺-is-linear x (right midpoint))
       where
         i : x ≺ right midpoint → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right midpoint
         i x≺rmp = x , left-≺ x , x≺rmp
         j : x ≡ right midpoint → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right midpoint
         j refl = left (right (left (right midpoint))) , inr refl , inr (inr refl)
         k : right midpoint ≺ x → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ right midpoint
         k rmp≺x = left (right x) , ≺-right x , inr (inr refl)
≺-density (right x) midpoint x≺mp = right z , x≺z , z≺mp
 where
  IH : Σ z ꞉ 𝔻 , x ≺ z × z ≺ midpoint
  IH = ≺-density x midpoint x≺mp
  z : 𝔻
  z = pr₁ IH
  x≺z : x ≺ z
  x≺z = pr₁ (pr₂ IH)
  z≺mp : z ≺ midpoint
  z≺mp = pr₂ (pr₂ IH)
≺-density (right x) (left y) (x≺mp , mp≺y) = left z , (x≺mp , mp≺z) , z≺y
 where
  IH : Σ z ꞉ 𝔻 , midpoint ≺ z × z ≺ y
  IH = ≺-density midpoint y mp≺y
  z : 𝔻
  z = pr₁ IH
  mp≺z : midpoint ≺ z
  mp≺z = pr₁ (pr₂ IH)
  z≺y : z ≺ y
  z≺y = pr₂ (pr₂ IH)
≺-density (right x) (right y) x≺y = right z , x≺z , z≺y
 where
  IH : Σ z ꞉ 𝔻 , x ≺ z × z ≺ y
  IH = ≺-density x y x≺y
  z : 𝔻
  z = pr₁ IH
  x≺z : x ≺ z
  x≺z = pr₁ (pr₂ IH)
  z≺y : z ≺ y
  z≺y = pr₂ (pr₂ IH)

\end{code}

\begin{code}

open import UF-PropTrunc

module _ (pt : propositional-truncations-exist) where
 open PropositionalTruncation pt

 ≺-has-no-left-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , y ≺ x
 ≺-has-no-left-endpoint x = ∣ left x , left-≺ x ∣

 ≺-has-no-right-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , x ≺ y
 ≺-has-no-right-endpoint x = ∣ right x , ≺-right x ∣

 ≺-is-dense : (x y : 𝔻) → x ≺ y → ∃ z ꞉ 𝔻 , x ≺ z × z ≺ y
 ≺-is-dense x y x≺y = ∣ ≺-density x y x≺y ∣

-}
\end{code}
