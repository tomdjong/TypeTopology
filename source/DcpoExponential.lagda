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
 pointwise-family-is-directed {I} α δ d = a , b
  where
   a : ∥ I ∥
   a = directed-implies-inhabited _hom-⊑_ α δ
   b : is-weakly-directed (underlying-order 𝓔) (pointwise-family α d)
   b i j = do
    (k , l , m) ← directed-implies-weakly-directed _hom-⊑_ α δ i j
    ∣ k , l d , m d ∣

 continuous-functions-sup : {I : 𝓥 ̇} (α : I → DCPO[ 𝓓 , 𝓔 ])
                          → is-directed _hom-⊑_ α → DCPO[ 𝓓 , 𝓔 ]
 continuous-functions-sup {I} α δ = f , c
  where
   ε : (d : ⟨ 𝓓 ⟩) → is-directed (underlying-order 𝓔) (pointwise-family α d)
   ε = pointwise-family-is-directed α δ
   f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
   f d = ∐ 𝓔 (ε d)
   c : is-continuous 𝓓 𝓔 f
   c J β φ = ub , lb-of-ubs
    where
     ub : (j : J) → f (β j) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 φ)
     ub j = f (β j)         ⊑⟨ 𝓔 ⟩[ reflexivity 𝓔 (f (β j)) ]
            ∐ 𝓔 (ε (β j))   ⊑⟨ 𝓔 ⟩[ ∐-is-monotone 𝓔 (ε (β j)) (ε (∐ 𝓓 φ)) h ]
            ∐ 𝓔 (ε (∐ 𝓓 φ)) ⊑⟨ 𝓔 ⟩[ reflexivity 𝓔 (f (∐ 𝓓 φ)) ]
            f (∐ 𝓓 φ)       ∎⟨ 𝓔 ⟩
      where
       h : (i : I) → [ 𝓓 , 𝓔 ]⟨ α i ⟩ (β j) ⊑⟨ 𝓔 ⟩ [ 𝓓 , 𝓔 ]⟨ α i ⟩ (∐ 𝓓 φ)
       h i = continuous-implies-monotone 𝓓 𝓔 (α i) (β j) (∐ 𝓓 φ)
              (∐-is-upperbound 𝓓 φ j)
     lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓔) (f (∐ 𝓓 φ))
                  (f ∘ β)
     lb-of-ubs e l = f (∐ 𝓓 φ)       ⊑⟨ 𝓔 ⟩[ reflexivity 𝓔 (f (∐ 𝓓 φ)) ]
                     ∐ 𝓔 (ε (∐ 𝓓 φ)) ⊑⟨ 𝓔 ⟩[ u ]
                     e               ∎⟨ 𝓔 ⟩
      where
       u = ∐-is-lowerbound-of-upperbounds 𝓔 (ε (∐ 𝓓 φ)) e v
        where
         v : (i : I) → [ 𝓓 , 𝓔 ]⟨ α i ⟩ (∐ 𝓓 φ) ⊑⟨ 𝓔 ⟩ e
         v i = [ 𝓓 , 𝓔 ]⟨ α i ⟩ (∐ 𝓓 φ)             ⊑⟨ 𝓔 ⟩[ l₁ ]
               ∐ 𝓔 (image-is-directed' 𝓓 𝓔 (α i) φ) ⊑⟨ 𝓔 ⟩[ l₂ ]
               e                                    ∎⟨ 𝓔 ⟩
          where
           l₁ = continuous-∐-⊑ 𝓓 𝓔 (α i) φ
           l₂ = ∐-is-lowerbound-of-upperbounds 𝓔 (image-is-directed' 𝓓 𝓔 (α i) φ) e w
            where
             w : (j : J) → [ 𝓓 , 𝓔 ]⟨ α i ⟩ (β j) ⊑⟨ 𝓔 ⟩ e
             w j = [ 𝓓 , 𝓔 ]⟨ α i ⟩ (β j) ⊑⟨ 𝓔 ⟩[ ∐-is-upperbound 𝓔 (ε (β j)) i ]
                   ∐ 𝓔 (ε (β j))          ⊑⟨ 𝓔 ⟩[ reflexivity 𝓔 (f (β j)) ]
                   f (β j)                ⊑⟨ 𝓔 ⟩[ l j ]
                   e                      ∎⟨ 𝓔 ⟩

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
        (Π-is-set fe (λ (x : ⟨ 𝓓 ⟩) → sethood 𝓔))
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

\begin{code}

DCPO-∘-is-continuous₁ : (𝓓 : DCPO {𝓤} {𝓣})
                        (𝓔 : DCPO {𝓤'} {𝓣'})
                        (𝓔' : DCPO {𝓦} {𝓦'})
                        (f : DCPO[ 𝓓 , 𝓔 ])
                      → is-continuous (𝓔 ⟹ᵈᶜᵖᵒ 𝓔') (𝓓 ⟹ᵈᶜᵖᵒ 𝓔') (DCPO-∘ 𝓓 𝓔 𝓔' f)
DCPO-∘-is-continuous₁ 𝓓 𝓔 𝓔' f I α δ = γ
 where
  γ : is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔'))
        (DCPO-∘ 𝓓 𝓔 𝓔' f (∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓔') {I} {α} δ)) (λ x → DCPO-∘ 𝓓 𝓔 𝓔' f (α x))
  γ = transport (λ - → is-sup (underlying-order (𝓓 ⟹ᵈᶜᵖᵒ 𝓔')) - (λ x → DCPO-∘ 𝓓 𝓔 𝓔' f (α x))) (claim ⁻¹) (∐-is-sup (𝓓 ⟹ᵈᶜᵖᵒ 𝓔') {I} {β} ε)
  -- transport {!λ - → is-sup ? - ?!} -- claim ∐-is-sup -- ∐-is-sup {!!} ε
   where
    β : I → ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔' ⟩
    β i = DCPO-∘ 𝓓 𝓔 𝓔' f (α i)
    ε : is-Directed (𝓓 ⟹ᵈᶜᵖᵒ 𝓔') β
    ε = image-is-directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓔') (𝓓 ⟹ᵈᶜᵖᵒ 𝓔') {!!} δ
    claim : DCPO-∘ 𝓓 𝓔 𝓔' f (∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓔') {I} {α} δ)
          ≡ ∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔') {I} {β} ε
    claim = to-subtype-≡ (λ g → being-continuous-is-a-prop 𝓓 𝓔' g)
            (dfunext fe ψ)
     where
      ψ : (x : ⟨ 𝓓 ⟩) → pr₁ (∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓔') {I} {α} δ) (pr₁ f x) ≡
       ∐ 𝓔' (pointwise-family-is-directed 𝓓 𝓔' β ε x)
      ψ x = ∐-independent-of-directedness-witness 𝓔' (pointwise-family-is-directed 𝓔 𝓔' α δ (pr₁ f x)) (pointwise-family-is-directed 𝓓 𝓔' β ε x)


-- ∐-is-sup {!!} (pointwise-family-is-directed {!!} {!!} {!!} {!!} {!!})


\end{code}
