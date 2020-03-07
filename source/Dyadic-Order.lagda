Tom de Jong, 3 - 5 March 2020

As suggested by Martin Escardo.

The (usual) order on the dyadic rationals

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import Dyadic
open import UF-Subsingletons

\end{code}

We inductively define an order ≺ on 𝔻 and prove that it is transitive and
linear.

We also show that is is "dense" and "has no endpoints", but formulated using Σ
rather than ∃. Although the proper formulation would use ∃ (to ensure that being
dense and having no endpoints is property, rather than structure), we still
prove the Σ-versions for two reasons:
- we can easily prove them and derive the ∃-versions from them;
- so that this module does not depend on propositional truncation.

\begin{code}

module Dyadic-Order where

\end{code}

We defined ≺ by using the translation (from 𝔻 to (-1,1)) as set out in Dyadic.

\begin{code}

_≺_ : 𝔻 → 𝔻 → 𝓤₀ ̇
midpoint ≺ midpoint = 𝟘
midpoint ≺ left y   = 𝟘
midpoint ≺ right y  = 𝟙
left x   ≺ midpoint = 𝟙
left x   ≺ left y   = x ≺ y
left x   ≺ right y  = 𝟙
right x  ≺ midpoint = 𝟘
right x  ≺ left y   = 𝟘
right x  ≺ right y  = x ≺ y

\end{code}

Monotonicity of left and right holds by definition (so we will never call these
lemmas), but we record them here for clarity.

\begin{code}

left-monotone : {x y : 𝔻} → x ≺ y → left x ≺ left y
left-monotone = id

right-monotone : {x y : 𝔻} → x ≺ y → right x ≺ right y
right-monotone = id

\end{code}

\begin{code}

≺-is-prop-valued : (x y : 𝔻) → is-prop (x ≺ y)
≺-is-prop-valued midpoint  midpoint  = 𝟘-is-prop
≺-is-prop-valued midpoint  (left y)  = 𝟘-is-prop
≺-is-prop-valued midpoint  (right y) = 𝟙-is-prop
≺-is-prop-valued (left x)  midpoint  = 𝟙-is-prop
≺-is-prop-valued (left x)  (left y)  = ≺-is-prop-valued x y
≺-is-prop-valued (left x)  (right y) = 𝟙-is-prop
≺-is-prop-valued (right x) midpoint  = 𝟘-is-prop
≺-is-prop-valued (right x) (left y)  = 𝟘-is-prop
≺-is-prop-valued (right x) (right y) = ≺-is-prop-valued x y

≺-is-transitive : (x y z : 𝔻) → x ≺ y → y ≺ z → x ≺ z
≺-is-transitive midpoint midpoint z = 𝟘-induction
≺-is-transitive midpoint (left y) midpoint = 𝟘-induction
≺-is-transitive midpoint (left y) (left z) = 𝟘-induction
≺-is-transitive midpoint (left y) (right z) = 𝟘-induction
≺-is-transitive midpoint (right y) midpoint _ = id
≺-is-transitive midpoint (right y) (left z) _ = id
≺-is-transitive midpoint (right y) (right z) _ _ = *
≺-is-transitive (left x) midpoint midpoint _ _ = *
≺-is-transitive (left x) midpoint (left z) _ = 𝟘-induction
≺-is-transitive (left x) midpoint (right z) _ = id
≺-is-transitive (left x) (left y) midpoint _ = id
≺-is-transitive (left x) (left y) (left z) = ≺-is-transitive x y z
≺-is-transitive (left x) (left y) (right z) _ = id
≺-is-transitive (left x) (right y) midpoint _ _ = *
≺-is-transitive (left x) (right y) (left z) _ = 𝟘-induction
≺-is-transitive (left x) (right y) (right z) _ _ = *
≺-is-transitive (right x) midpoint z = 𝟘-induction
≺-is-transitive (right x) (left y) z = 𝟘-induction
≺-is-transitive (right x) (right y) midpoint _ = id
≺-is-transitive (right x) (right y) (left z) _ = id
≺-is-transitive (right x) (right y) (right z) = ≺-is-transitive x y z

≺-is-linear : (x y : 𝔻) → x ≢ y → x ≺ y + y ≺ x
≺-is-linear midpoint midpoint p = 𝟘-induction (p refl)
≺-is-linear midpoint (left y) _ = inr *
≺-is-linear midpoint (right y) _ = inl *
≺-is-linear (left x) midpoint _ = inl *
≺-is-linear (left x) (left y) lx≢ly = ≺-is-linear x y x≢y
 where
  x≢y : x ≢ y
  x≢y = contrapositive (ap left) lx≢ly
≺-is-linear (left x) (right y) _ = inl *
≺-is-linear (right x) midpoint _ = inr *
≺-is-linear (right x) (left y) _ = inr *
≺-is-linear (right x) (right y) rx≢ry = ≺-is-linear x y x≢y
 where
  x≢y : x ≢ y
  x≢y = contrapositive (ap right) rx≢ry

\end{code}

Discreteness of 𝔻 and linearity of ≺ imply that ≺ is trichotomous, i.e. for
every x y : 𝔻 , x ≺ y or x ≡ y or y ≺ x holds. The lemmas after
≺-is-trichotomous show that exactly one of these is the case, as witnessed by
trichotomy-is-a-singleton.

\begin{code}

≺-is-trichotomous : (x y : 𝔻) → x ≺ y + (x ≡ y) + (y ≺ x)
≺-is-trichotomous x y = cases a b (𝔻-is-discrete x y)
 where
  a : x ≡ y → (x ≺ y) + (x ≡ y) + (y ≺ x)
  a = inr ∘ inl
  b : (x ≢ y) → (x ≺ y) + (x ≡ y) + (y ≺ x)
  b x≢y = cases c d (≺-is-linear x y x≢y)
   where
    c : x ≺ y → (x ≺ y) + (x ≡ y) + (y ≺ x)
    c = inl
    d : y ≺ x → (x ≺ y) + (x ≡ y) + (y ≺ x)
    d = inr ∘ inr

≺-to-≢ : {x y : 𝔻} → x ≺ y → x ≢ y
≺-to-≢ {midpoint} {midpoint}    = 𝟘-induction
≺-to-≢ {midpoint} {left y}      = 𝟘-induction
≺-to-≢ {midpoint} {right y} _   = midpoint-is-not-right
≺-to-≢ {left x}   {midpoint} _  = (λ p → midpoint-is-not-left (p ⁻¹))
≺-to-≢ {left x}   {left y} x≺y  = contrapositive left-lc (≺-to-≢ x≺y)
≺-to-≢ {left x}   {right y} _   = left-is-not-right
≺-to-≢ {right x}  {midpoint}    = 𝟘-induction
≺-to-≢ {right x}  {left y}      = 𝟘-induction
≺-to-≢ {right x}  {right y} x≺y = contrapositive right-lc (≺-to-≢ x≺y)

≺-to-≢' : {x y : 𝔻} → y ≺ x → x ≢ y
≺-to-≢' y≺x p = ≺-to-≢ y≺x (p ⁻¹)

≡-to-¬≺ : {x y : 𝔻} → x ≡ y → ¬ (x ≺ y)
≡-to-¬≺ x≡y x≺y = ≺-to-≢ x≺y x≡y

≡-to-¬≺' : {x y : 𝔻} → x ≡ y → ¬ (y ≺ x)
≡-to-¬≺' x≡y y≺x = ≺-to-≢ y≺x (x≡y ⁻¹)

≺-to-¬≺ : (x y : 𝔻) → x ≺ y → ¬ (y ≺ x)
≺-to-¬≺ midpoint midpoint    = 𝟘-induction
≺-to-¬≺ midpoint (left y)    = 𝟘-induction
≺-to-¬≺ midpoint (right y) _ = id
≺-to-¬≺ (left x) midpoint _  = id
≺-to-¬≺ (left x) (left y)    = ≺-to-¬≺ x y
≺-to-¬≺ (left x) (right y) _ = id
≺-to-¬≺ (right x) midpoint   = 𝟘-induction
≺-to-¬≺ (right x) (left y)   = 𝟘-induction
≺-to-¬≺ (right x) (right y)  = ≺-to-¬≺ x y

trichotomy-is-a-singleton : {x y : 𝔻} → is-singleton (x ≺ y + (x ≡ y) + y ≺ x)
trichotomy-is-a-singleton {x} {y} =
 pointed-props-are-singletons (≺-is-trichotomous x y) γ
  where
   γ : is-prop (x ≺ y + (x ≡ y) + y ≺ x)
   γ = +-is-prop (≺-is-prop-valued x y) h g
    where
     h : is-prop ((x ≡ y) + y ≺ x)
     h = +-is-prop 𝔻-is-a-set (≺-is-prop-valued y x) ≡-to-¬≺'
     g : x ≺ y → ¬ ((x ≡ y) + y ≺ x)
     g x≺y = cases a b
      where
       a : x ≢ y
       a = ≺-to-≢ x≺y
       b : ¬ (y ≺ x)
       b = ≺-to-¬≺ x y x≺y

\end{code}

Next, we prove that ≺ has no endpoints and is dense (although formulated with Σ,
as explained at the top of this file).

\begin{code}

left-≺ : (x : 𝔻) → left x ≺ x
left-≺ midpoint = *
left-≺ (left x) = left-≺ x
left-≺ (right x) = *

≺-right : (x : 𝔻) → x ≺ right x
≺-right midpoint = *
≺-right (left x) = *
≺-right (right x) = ≺-right x

≺-has-no-left-endpoint-Σ : (x : 𝔻) → Σ y ꞉ 𝔻 , y ≺ x
≺-has-no-left-endpoint-Σ x = left x , left-≺ x

≺-has-no-right-endpoint-Σ : (x : 𝔻) → Σ y ꞉ 𝔻 , x ≺ y
≺-has-no-right-endpoint-Σ x = right x , ≺-right x

≺-is-dense-Σ : (x y : 𝔻) → x ≺ y → Σ z ꞉ 𝔻 , x ≺ z × z ≺ y
≺-is-dense-Σ midpoint (right y) _ = right (left y) , * , left-≺ y
≺-is-dense-Σ (left x) midpoint _ = left (right x) , ≺-right x , *
≺-is-dense-Σ (left x) (left y) x≺y = γ (≺-is-dense-Σ x y x≺y)
 where
  γ : (Σ z ꞉ 𝔻 , x ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , left x ≺ z × z ≺ left y
  γ (z , x≺z , z≺y) = left z , x≺z , z≺y
≺-is-dense-Σ (left x) (right y) _ = midpoint , * , *
≺-is-dense-Σ (right x) midpoint = 𝟘-induction
≺-is-dense-Σ (right x) (left y) = 𝟘-induction
≺-is-dense-Σ (right x) (right y) x≺y = γ (≺-is-dense-Σ x y x≺y)
 where
  γ : (Σ z ꞉ 𝔻 , x ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , right x ≺ z × z ≺ right y
  γ (z , x≺z , z≺y) = right z , x≺z , z≺y

\end{code}

Binary interpolation is a generalisation of density, which can, in our case, be
proved from density using trichotomy of ≺.

We will need this property to construct the (rounded) ideal completion of
(𝔻 , ≺).

\begin{code}

≺-interpolation₂-Σ : (x₀ x₁ y : 𝔻) → x₀ ≺ y → x₁ ≺ y
                   → Σ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
≺-interpolation₂-Σ x₀ x₁ y x₀≺y x₁≺y = cases₃ a b c (≺-is-trichotomous x₀ x₁)
 where
  a : x₀ ≺ x₁ → Σ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
  a x₀≺x₁ = γ (≺-is-dense-Σ x₁ y x₁≺y)
   where
    γ : (Σ z ꞉ 𝔻 , x₁ ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
    γ (z , x₁≺z , z≺y) = z , ≺-is-transitive x₀ x₁ z x₀≺x₁ x₁≺z , x₁≺z , z≺y
  b : x₀ ≡ x₁ → Σ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
  b refl = γ (≺-is-dense-Σ x₁ y x₁≺y)
   where
    γ : (Σ z ꞉ 𝔻 , x₁ ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
    γ (z , x₁≺z , z≺y) = z , x₁≺z , x₁≺z , z≺y
  c : x₁ ≺ x₀ → Σ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
  c x₁≺x₀ = γ (≺-is-dense-Σ x₀ y x₀≺y)
   where
    γ : (Σ z ꞉ 𝔻 , x₀ ≺ z × z ≺ y) → Σ z ꞉ 𝔻 , x₀ ≺ z × x₁ ≺ z × z ≺ y
    γ (z , x₀≺z , z≺y) = z , x₀≺z , ≺-is-transitive x₁ x₀ z x₁≺x₀ x₀≺z , z≺y

\end{code}
