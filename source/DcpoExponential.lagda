\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc hiding (⊥)

module DcpoExponential
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoBasics pt fe 𝓥

module _ (𝓓 : DCPO {𝓤} {𝓣})
         (𝓔 : DCPO {𝓤'} {𝓣'})
       where

 _hom-⊑_ : DCPO[ 𝓓 , 𝓔 ] → DCPO[ 𝓓 , 𝓔 ] → 𝓤 ⊔ 𝓣' ̇
 (f , _) hom-⊑ (g , _) = ∀ d → f d ⊑⟨ 𝓔 ⟩ g d

 pointwise-family : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ]) → ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
 pointwise-family α d i = underlying-function 𝓓 𝓔 (α i) d

 pointwise-family-is-directed : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ])
                                (δ : is-directed _hom-⊑_ α)
                                (d : ⟨ 𝓓 ⟩)
                              → is-directed (underlying-order 𝓔)
                                 (pointwise-family α d)
 pointwise-family-is-directed {I} α δ d =
  (directed-implies-inhabited _hom-⊑_ {I} {α} δ) ,
  λ (i j : I) → ∥∥-functor (h i j) ((directed-implies-weakly-directed _hom-⊑_ {I} {α} δ) i j)
   where
    β : ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
    β = pointwise-family α
    h : (i j : I) → Σ (\(k : I) → α i hom-⊑ α k × α j hom-⊑ α k)
        → Σ (\k → (β d i) ⊑⟨ 𝓔 ⟩ (β d k) × (β d j) ⊑⟨ 𝓔 ⟩ (β d k))
    h i j (k , l , m) = k , l d , m d

 continuous-functions-sup : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ])
                          → is-directed _hom-⊑_ α → DCPO[ 𝓓 , 𝓔 ]
 continuous-functions-sup {I} α δ = f , c
  where
   β : ⟨ 𝓓 ⟩ → I → ⟨ 𝓔 ⟩
   β d = pointwise-family α d
   ε : (d : ⟨ 𝓓 ⟩) → is-directed (underlying-order 𝓔) (β d)
   ε = pointwise-family-is-directed α δ
   f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   f d = ∐ 𝓔 {I} {β d} (ε d)
   c : is-continuous 𝓓 𝓔 f
   c J γ φ = u , v
    where
     u : (j : J) → f (γ j) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
     u j = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (γ j)) (f (∐ 𝓓 φ)) r
      where
       r : (i : I) → underlying-function 𝓓 𝓔 (α i) (γ j) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
       r i = underlying-function 𝓓 𝓔 (α i) (γ j)   ⊑⟨ 𝓔 ⟩[ p ]
             underlying-function 𝓓 𝓔 (α i) (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩[ q ]
             f (∐ 𝓓 φ)                             ∎⟨ 𝓔 ⟩
        where
         p = continuous-implies-monotone 𝓓 𝓔 (α i) (γ j) (∐ 𝓓 φ)
             (∐-is-upperbound 𝓓 φ j)
         q = ∐-is-upperbound 𝓔 (ε (∐ 𝓓 φ)) i
     v : (y : ⟨ 𝓔 ⟩)
       → ((j : J) → f (γ j) ⊑⟨ 𝓔 ⟩ y)
       → f (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ y
     v y l = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (∐ 𝓓 φ)) y r
      where
       r : (i : I) → β (∐ 𝓓 φ) i ⊑⟨ 𝓔 ⟩ y
       r i = sup-is-lowerbound-of-upperbounds (underlying-order 𝓔)
              (continuity-of-function 𝓓 𝓔 (α i) J γ φ) y m
        where
         m : (j : J) → underlying-function 𝓓 𝓔 (α i) (γ j) ⊑⟨ 𝓔 ⟩ y
         m j = underlying-function 𝓓 𝓔 (α i) (γ j) ⊑⟨ 𝓔 ⟩[ m₁ ]
               f (γ j)                             ⊑⟨ 𝓔 ⟩[ m₂ ]
               y                                   ∎⟨ 𝓔 ⟩
          where
           m₁ = ∐-is-upperbound 𝓔 (ε (γ j)) i
           m₂ = l j

infixr 20 _⟹ᵈᶜᵖᵒ_

_⟹ᵈᶜᵖᵒ_ : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'}
        → DCPO {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
𝓓 ⟹ᵈᶜᵖᵒ 𝓔 = DCPO[ 𝓓 , 𝓔 ] , _⊑_ , d
 where
  _⊑_ = 𝓓 hom-⊑ 𝓔
  d : dcpo-axioms _⊑_
  d = (s , p , r , t , a) , c
   where
    s : is-set DCPO[ 𝓓 , 𝓔 ]
    s = subsets-of-sets-are-sets (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (is-continuous 𝓓 𝓔)
        (Π-is-set fe (λ (x : ⟨ 𝓓 ⟩) →  sethood 𝓔))
        (λ {f} → being-continuous-is-a-prop 𝓓 𝓔 f)
    p : (f g : DCPO[ 𝓓 , 𝓔 ]) → is-prop (f ⊑ g)
    p (f , _) (g , _) = Π-is-prop fe
                        (λ (x : ⟨ 𝓓 ⟩) → prop-valuedness 𝓔 (f x) (g x))
    r : (f : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ f
    r (f , _) x = reflexivity 𝓔 (f x)
    t : (f g h : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ g → g ⊑ h → f ⊑ h
    t (f , _) (g , _) (h , _) l m x = transitivity 𝓔 (f x) (g x) (h x)
                                      (l x) (m x)
    a : (f g : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ g → g ⊑ f → f ≡ g
    a f g l m =
     to-Σ-≡
      (dfunext fe
       (λ d → antisymmetry 𝓔
              ((underlying-function 𝓓 𝓔 f) d)
              ((underlying-function 𝓓 𝓔 g) d)
              (l d) (m d)) ,
      being-continuous-is-a-prop 𝓓 𝓔 (underlying-function 𝓓 𝓔 g) _
       (continuity-of-function 𝓓 𝓔 g))
    c : (I : _ ̇) (α : I → DCPO[ 𝓓 , 𝓔 ]) → is-directed _⊑_ α → has-sup _⊑_ α
    c I α δ = (continuous-functions-sup 𝓓 𝓔 α δ) , u , v
     where
      u : (i : I) → α i ⊑ continuous-functions-sup 𝓓 𝓔 α δ
      u i d = ∐-is-upperbound 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d) i
      v : (g : DCPO[ 𝓓 , 𝓔 ])
        → ((i : I) → α i ⊑ g)
        → continuous-functions-sup 𝓓 𝓔 α δ ⊑ g
      v (g , _) l d = ∐-is-lowerbound-of-upperbounds 𝓔
                      (pointwise-family-is-directed 𝓓 𝓔 α δ d)
                      (g d) (λ (i : I) → l i d)

infixr 20 _⟹ᵈᶜᵖᵒ⊥_

_⟹ᵈᶜᵖᵒ⊥_ : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'}
         → DCPO⊥ {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
𝓓 ⟹ᵈᶜᵖᵒ⊥ 𝓔 = (𝓓 ⁻) ⟹ᵈᶜᵖᵒ (𝓔 ⁻) , h
 where
  h : has-least (underlying-order ((𝓓 ⁻) ⟹ᵈᶜᵖᵒ (𝓔 ⁻)))
  h = ((λ _ → ⊥ 𝓔) ,
      constant-functions-are-continuous (𝓓 ⁻) (𝓔 ⁻) (⊥ 𝓔)) ,
      (λ g d → ⊥-is-least 𝓔 (underlying-function (𝓓 ⁻) (𝓔 ⁻) g d))

\end{code}
