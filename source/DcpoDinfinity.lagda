Tom de Jong, 12 May 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoDinfinity
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓤₀
open import DcpoBasics pt fe 𝓤₀
open import DcpoExponential pt fe 𝓤₀
-- open import DcpoLimits pt fe 𝓤₀ 𝓤₁ 𝓤₁
open import DcpoLimitsSequential pt fe 𝓤₁ 𝓤₁
open import DcpoLifting pt fe 𝓤₀ pe

open import NaturalsOrder
open import NaturalsAddition renaming (_+_ to _+'_)

𝓓⊥ : ℕ → DCPO⊥ {𝓤₁} {𝓤₁}
𝓓⊥ zero     = 𝓛-DCPO⊥ {𝓤₀} {𝟙{𝓤₀}} (props-are-sets 𝟙-is-prop)
𝓓⊥ (succ n) = 𝓓⊥ n ⟹ᵈᶜᵖᵒ⊥ 𝓓⊥ n

𝓓 : ℕ → DCPO {𝓤₁} {𝓤₁}
𝓓 n = pr₁ (𝓓⊥ n)

𝓓-diagram : (n : ℕ)
          → DCPO[ 𝓓 n , 𝓓 (succ n) ]
          × DCPO[ 𝓓 (succ n) , 𝓓 n ]
𝓓-diagram zero = (e₀ , e₀-continuity) , p₀ , p₀-continuity
 where
  e₀ : ⟨ 𝓓 0 ⟩ → ⟨ 𝓓 1 ⟩
  e₀ x = (λ y → x) , (constant-functions-are-continuous (𝓓 0) (𝓓 0) x)
  e₀-continuity : is-continuous (𝓓 0) (𝓓 1) e₀
  e₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → e₀ (α i) ⊑⟨ (𝓓 1) ⟩ e₀ (∐ (𝓓 0) δ)
    ub i y =  α i          ⊑⟨ 𝓓 0 ⟩[ ∐-is-upperbound (𝓓 0) δ i ]
              ∐ (𝓓 0) δ  ∎⟨ 𝓓 0 ⟩
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 1))
                  (e₀ (∐ (𝓓 0) δ)) (λ x → e₀ (α x))
    lb-of-ubs (g , c) ub y =
     ∐-is-lowerbound-of-upperbounds (𝓓 0) δ (g y) (λ i → ub i y)
  p₀ : ⟨ 𝓓 1 ⟩ → ⟨ 𝓓 0 ⟩
  p₀ (f , c) = f (⊥ (𝓓⊥ 0))
  p₀-continuity : is-continuous (𝓓 1) (𝓓 0) p₀
  p₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → p₀ (α i) ⊑⟨ 𝓓 0 ⟩ p₀ (∐ (𝓓 1) {I} {α} δ)
    ub i = ∐-is-upperbound (𝓓 1) {I} {α} δ i (⊥ (𝓓⊥ 0))
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 0))
                  (p₀ (∐ (𝓓 1) {I} {α} δ)) (λ x → p₀ (α x))
    lb-of-ubs y ub =
     ∐-is-lowerbound-of-upperbounds (𝓓 0) ε y ub
      where
       ε : is-Directed (𝓓 0) (pointwise-family (𝓓 0) (𝓓 0) α (⊥ (𝓓⊥ 0)))
       ε = pointwise-family-is-directed (𝓓 0) (𝓓 0) α δ (⊥ (𝓓⊥ 0))
𝓓-diagram (succ n) = (e , e-continuity) , (p , p-continuity)
 where
  IH : DCPO[ 𝓓 n , 𝓓 (succ n) ] × DCPO[ 𝓓 (succ n) , 𝓓 n ]
  IH = 𝓓-diagram n
  eₙ : DCPO[ 𝓓 n , 𝓓 (succ n) ]
  eₙ = pr₁ IH
  pₙ : DCPO[ 𝓓 (succ n) , 𝓓 n ]
  pₙ = pr₂ IH
  e : ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 (succ (succ n)) ⟩
  e f = DCPO-∘₃ (𝓓 (succ n)) (𝓓 n) (𝓓 n) (𝓓 (succ n)) pₙ f eₙ
  e-continuity : is-continuous (𝓓 (succ n)) (𝓓 (succ (succ n))) e
  e-continuity = ∘-is-continuous
                  (𝓓 (succ n))
                  ((𝓓 n) ⟹ᵈᶜᵖᵒ (𝓓 (succ n)))
                  (𝓓 (succ (succ n)))
                  (λ f → DCPO-∘ (𝓓 n) (𝓓 n) (𝓓 (succ n)) f eₙ)
                  (DCPO-∘ (𝓓 (succ n)) (𝓓 n) (𝓓 (succ n)) pₙ)
                  (DCPO-∘-is-continuous₂ (𝓓 n) (𝓓 n) (𝓓 (succ n)) eₙ)
                  (DCPO-∘-is-continuous₁ (𝓓 (succ n)) (𝓓 n)
                   (𝓓 (succ n)) pₙ)
  p : ⟨ 𝓓 (succ (succ n)) ⟩ → ⟨ 𝓓 (succ n) ⟩
  p f = DCPO-∘₃ (𝓓 n) (𝓓 (succ n)) (𝓓 (succ n)) (𝓓 n) eₙ f pₙ
  p-continuity : is-continuous (𝓓 (succ (succ n))) (𝓓 (succ n)) p
  p-continuity = ∘-is-continuous
                  (𝓓 (succ (succ n)))
                  ((𝓓 n) ⟹ᵈᶜᵖᵒ (𝓓 (succ n)))
                  (𝓓 (succ n))
                  (DCPO-∘ (𝓓 n) (𝓓 (succ n)) (𝓓 (succ n)) eₙ)
                  (λ f → DCPO-∘ (𝓓 n) (𝓓 (succ n)) (𝓓 n) f pₙ)
                  (DCPO-∘-is-continuous₁ (𝓓 n) (𝓓 (succ n))
                   (𝓓 (succ n)) eₙ)
                  (DCPO-∘-is-continuous₂ (𝓓 n) (𝓓 (succ n)) (𝓓 n) pₙ)

π' : (n : ℕ) → DCPO[ 𝓓 (succ n) , 𝓓 n ]
π' n = pr₂ (𝓓-diagram n)

π : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 n ⟩
π n = underlying-function (𝓓 (succ n)) (𝓓 n) (π' n)

π-is-continuous : (n : ℕ) → is-continuous (𝓓 (succ n)) (𝓓 n) (π n)
π-is-continuous n = pr₂ (pr₂ (𝓓-diagram n))

ε' : (n : ℕ) → DCPO[ 𝓓 n , 𝓓 (succ n) ]
ε' n = pr₁ (𝓓-diagram n)

ε : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (succ n) ⟩
ε n = underlying-function (𝓓 n) (𝓓 (succ n)) (ε' n)

ε-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (𝓓 (succ n)) (ε n)
ε-is-continuous n = pr₂ (pr₁ (𝓓-diagram n))

π-on-0 : (f : ⟨ 𝓓 0 ⟩ → ⟨ 𝓓 0 ⟩) (c : is-continuous (𝓓 0) (𝓓 0) f)
       → π 0 (f , c) ≡ f (⊥ (𝓓⊥ 0))
π-on-0 f c = refl

π-on-succ : (n : ℕ) (f : ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 (succ n) ⟩)
            (c : is-continuous (𝓓 (succ n)) (𝓓 (succ n)) f)
          → [ 𝓓 n , 𝓓 n ]⟨ π (succ n) (f , c) ⟩ ≡ π n ∘ f ∘ ε n
π-on-succ n f c = refl

π-on-succ' : (n : ℕ) (f : DCPO[ 𝓓 (succ n) , 𝓓 (succ n) ])
           → [ 𝓓 n , 𝓓 n ]⟨ π (succ n) f ⟩
           ≡ π n ∘ [ 𝓓 (succ n) , 𝓓 (succ n) ]⟨ f ⟩ ∘ ε n
π-on-succ' n f = refl

ε-on-0 : (x : ⟨ 𝓓 0 ⟩) → [ 𝓓 0 , 𝓓 0 ]⟨ ε 0 x ⟩ ≡ (λ y → x)
ε-on-0 x = refl

ε-on-succ : (n : ℕ) (f : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 n ⟩) (c : is-continuous (𝓓 n) (𝓓 n) f)
          → [ 𝓓 (succ n) , 𝓓 (succ n) ]⟨ ε (succ n) (f , c) ⟩ ≡ ε n ∘ f ∘ π n
ε-on-succ n f c = refl

ε-section-of-π : (n : ℕ) → π n ∘ ε n ∼ id
ε-section-of-π zero x = refl
ε-section-of-π (succ n) (f , _) = to-continuous-function-≡ (𝓓 n) (𝓓 n) γ
 where
  γ : π n ∘ ε n ∘ f ∘ π n ∘ ε n ∼ f
  γ x = (π n ∘ ε n ∘ f ∘ π n ∘ ε n) x ≡⟨ IH (f (π n (ε n x))) ⟩
        (f ∘ π n ∘ ε n) x             ≡⟨ ap f (IH x) ⟩
        f x                           ∎
   where
    IH : π n ∘ ε n ∼ id
    IH = ε-section-of-π n

επ-deflation : (n : ℕ) (f : ⟨ 𝓓 (succ n) ⟩) → ε n (π n f) ⊑⟨ 𝓓 (succ n) ⟩ f
επ-deflation zero (f , c) x =
 f (⊥ (𝓓⊥ 0)) ⊑⟨ 𝓓 0 ⟩[ m (⊥ (𝓓⊥ 0)) x (⊥-is-least (𝓓⊥ 0) x) ]
 f x          ∎⟨ 𝓓 0 ⟩
  where
   m : is-monotone (𝓓 0) (𝓓 0) f
   m = continuous-implies-monotone (𝓓 0) (𝓓 0) (f , c)
επ-deflation (succ n) (f , c) x =
 {- I would use the ⊑⟨ 𝓓 (succ n) ⟩[ ? ] syntax here, but Agda has trouble
    figuring out some implicit arguments. -}
 transitivity (𝓓 (succ n))
  ((ε n ∘ π n ∘ f ∘ ε n ∘ π n) x) (f (ε n (π n x))) (f x)
  (IH (f (ε n (π n x))))
  (m (ε n (π n x)) x (IH x))
{-
 (ε n ∘ π n ∘ f ∘ ε n ∘ π n) x ⊑⟨ 𝓓 (succ n) ⟩[ IH (f (ε n (π n x)))     ]
 f (ε n (π n x))               ⊑⟨ 𝓓 (succ n) ⟩[ m (ε n (π n x)) x (IH x) ]
 f x                           ∎⟨ 𝓓 (succ n) ⟩ -}
  where
   IH : (g : ⟨ 𝓓 (succ n) ⟩) → ε n (π n g) ⊑⟨ 𝓓 (succ n) ⟩ g
   IH = επ-deflation n
   m : is-monotone (𝓓 (succ n)) (𝓓 (succ n)) f
   m = continuous-implies-monotone (𝓓 (succ n)) (𝓓 (succ n)) (f , c)

open SequentialDiagram
      𝓓
      ε
      π
      επ-deflation
      ε-section-of-π
      ε-is-continuous
      π-is-continuous

α-to-succ : (n : ℕ) → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓 (succ n) ⟩
α-to-succ n f = DCPO-∘₃ (𝓓 n) 𝓓∞ 𝓓∞ (𝓓 n) (ε∞' n) f (π∞' n)

α-to-succ-is-continuous : (n : ℕ)
                        → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 (succ n)) (α-to-succ n)
α-to-succ-is-continuous n = γ
 where
  abstract
   γ = DCPO-∘₃-is-continuous₂ (𝓓 n) 𝓓∞ 𝓓∞ (𝓓 n) (ε∞' n) (π∞' n)

α : (n : ℕ) → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓 n ⟩
α zero     = π 0 ∘ α-to-succ 0
α (succ n) = α-to-succ n

-- Kinda slow, why?
α-is-continuous : (n : ℕ) → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (α n)
α-is-continuous  = γ
 where
  abstract
   γ : (n : ℕ) → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (α n)
   γ zero = ∘-is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 1) (𝓓 0)
             (α-to-succ 0) (π 0)
             (α-to-succ-is-continuous 0) (π-is-continuous 0)
   γ (succ n) = α-to-succ-is-continuous n

α-commutes-with-π : (n : ℕ) → π n ∘ α (succ n) ∼ α n
α-commutes-with-π zero f = refl
α-commutes-with-π (succ n) (f , c) =
 to-continuous-function-≡ (𝓓 n) (𝓓 n) γ
   where
    h : DCPO[ 𝓓 (succ n) , 𝓓 (succ n) ]
    h = DCPO-∘₃ (𝓓 (succ n)) 𝓓∞ 𝓓∞ (𝓓 (succ n))
         (ε∞' (succ n)) (f , c) (π∞' (succ n))
    γ : ([ 𝓓 n , 𝓓 n ]⟨ π (succ n) h ⟩) ∼ π∞ n ∘ f ∘ ε∞ n
    γ x = [ 𝓓 n , 𝓓 n ]⟨ (π (succ n) h) ⟩ x                       ≡⟨ e₁   ⟩
          (π n ∘ [ 𝓓 (succ n) , 𝓓 (succ n) ]⟨ h ⟩ ∘ ε n) x        ≡⟨ refl ⟩
          (π n ∘ π∞ (succ n) ∘ f') x                              ≡⟨ e₂    ⟩
          (π⁺ {n} {succ n} (≤-succ n) ∘ π∞ (succ n) ∘ f') x       ≡⟨ e₃    ⟩
          (π∞ n ∘ f ∘ ε∞ (succ n) ∘ ε n) x                        ≡⟨ e₄    ⟩
          (π∞ n ∘ f ∘ ε∞ (succ n) ∘ ε⁺ {n} {succ n} (≤-succ n)) x ≡⟨ e₅    ⟩
          (π∞ n ∘ f ∘ ε∞ n) x                                     ∎
           where
            f' : ⟨ 𝓓 n ⟩ → ⟨ 𝓓∞ ⟩
            f' = f ∘ ε∞ (succ n) ∘ ε n
            e₁ = happly (π-on-succ' n h) x
            e₂ = π-in-terms-of-π⁺ n (π∞ (succ n) (f' x))
            e₃ = π∞-commutes-with-πs n (succ n) (≤-succ n)
                  (f (ε∞ (succ n) (ε n x)))
            e₄ = ap (π∞ n ∘ f ∘ ε∞ (succ n)) (ε-in-terms-of-ε⁺ n x)
            e₅ = ap (π∞ n ∘ f) (ε∞-commutes-with-εs n (succ n) (≤-succ n) x)

α-commutes-with-π⁺ : (n m : ℕ) (l : n ≤ m) → π⁺ {n} {m} l ∘ α m ∼ α n
α-commutes-with-π⁺ n m l = commute-with-πs-lemma (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                            α α-commutes-with-π n m l

-- α-is-continuous is VERY SLOW to typecheck here. Why?
open DcpoCone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) α α-is-continuous α-commutes-with-π⁺

α∞ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
α∞ = limit-mediating-arrow -- (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) α α-is-continuous α-commutes-with-π⁺

β-from-succ : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
β-from-succ n f = DCPO-∘₃ 𝓓∞ (𝓓 n) (𝓓 n) 𝓓∞ (π∞' n) f (ε∞' n)

β-from-succ-is-continuous : (n : ℕ)
                          → is-continuous (𝓓 (succ n)) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                             (β-from-succ n)
β-from-succ-is-continuous n = DCPO-∘₃-is-continuous₂ 𝓓∞ (𝓓 n) (𝓓 n) 𝓓∞
                               (π∞' n) (ε∞' n)

β : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
-- because of Agda's idiosyncrasies, it's faster to have "ε zero" than "ε 0".
β zero     = β-from-succ 0 ∘ ε zero
β (succ n) = β-from-succ n

-- SLOW
β-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (β n)
β-is-continuous zero = ∘-is-continuous (𝓓 0) (𝓓 1) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                        (ε 0) (β-from-succ 0)
                        (ε-is-continuous 0) (β-from-succ-is-continuous 0)
β-is-continuous (succ n) = β-from-succ-is-continuous n

β-commutes-with-ε : (n : ℕ) → β (succ n) ∘ ε n ∼ β n
β-commutes-with-ε zero x = refl
β-commutes-with-ε (succ n) (f , c) =
 to-continuous-function-≡ 𝓓∞ 𝓓∞ γ
   where
    β₁ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
    β₁ = [ 𝓓∞ , 𝓓∞ ]⟨ β (succ (succ n)) (ε (succ n) (f , c)) ⟩
    β₂ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
    β₂ = [ 𝓓∞ , 𝓓∞ ]⟨ β (succ n) (f , c) ⟩
    γ : β₁ ∼ β₂
    {- It should be possible to prove equality on 𝓓∞ directly (i.e. we shouldn't
       need to boil it down to ⦅ ... ⦆ m, as witnessed by all the
       ap (λ - → ⦅ ... - ⦆ m) in the terms below), but Agda is very slow to typecheck
       otherwise. -}
    γ σ = to-𝓓∞-≡ ψ
     where
      ψ : (m : ℕ) → ⦅ β₁ σ ⦆ m ≡ ⦅ β₂ σ ⦆ m
      ψ m = ⦅ β₁ σ ⦆ m                                                    ≡⟨ refl ⟩
            ⦅ (ε∞ (succ n) ∘ ε n ∘ h) σ ⦆ m                               ≡⟨ e₁   ⟩
            ⦅ (ε∞ (succ n) ∘ ε⁺ {n} {succ n} (≤-succ n) ∘ h) σ ⦆ m        ≡⟨ e₂   ⟩
            ⦅ (ε∞ n ∘ h) σ ⦆ m                                            ≡⟨ refl ⟩
            ⦅ (ε∞ n ∘ f ∘ π n ∘ π∞ (succ n)) σ ⦆ m                        ≡⟨ e₃   ⟩
            ⦅ (ε∞ n ∘ f ∘ π⁺ {n} {succ n} (≤-succ n) ∘ π∞ (succ n)) σ ⦆ m ≡⟨ e₄   ⟩
            ⦅ (ε∞ n ∘ f ∘ π∞ n) σ ⦆ m                                     ≡⟨ refl ⟩
            ⦅ β₂ σ ⦆ m                                                    ∎
       where
        h : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓 n ⟩
        h = f ∘ π n ∘ π∞ (succ n)
        e₁ = ap (λ - → ⦅ ε∞ (succ n) - ⦆ m) (ε-in-terms-of-ε⁺ n (h σ))
        e₂ = ap (λ - → ⦅ - ⦆ m) (ε∞-commutes-with-εs n (succ n) (≤-succ n) (h σ))
        e₃ = ap (λ - → ⦅ ε∞ n (f -) ⦆ m) (π-in-terms-of-π⁺ n (π∞ (succ n) σ))
        e₄ = ap (λ - → ⦅ ε∞ n (f -) ⦆ m) (π∞-commutes-with-πs n (succ n) (≤-succ n) σ)

β-commutes-with-ε⁺ : (n m : ℕ) (l : n ≤ m) → β m ∘ ε⁺ {n} {m} l ∼ β n
β-commutes-with-ε⁺ n m l = commute-with-εs-lemma (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) β
                            β-commutes-with-ε n m l

open DcpoCocone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) β β-is-continuous β-commutes-with-ε⁺

β∞ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
β∞ = colimit-mediating-arrow -- (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) β β-is-continuous β-commutes-with-ε⁺

{-
α∞-after-β∞-is-id : α∞ ∘ β∞ ∼ id
α∞-after-β∞-is-id σ = to-𝓓∞-≡ γ
 where
  γ : (n : ℕ) → ⦅ α∞ (β∞ σ) ⦆ n ≡ ⦅ σ ⦆ n
  γ n = ⦅ α∞ (β∞ σ) ⦆ n ≡⟨ refl ⟩
        α n (β∞ σ) ≡⟨ continuous-∐-≡ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (α n , α-is-continuous n) (colimit-family-is-directed σ) ⟩
        ∐ (𝓓 n) {!!} ≡⟨ {!!} ⟩
        α n (∐ {!!} {ℕ} {colimit-family σ} (colimit-family-is-directed σ)) ≡⟨ {!!} ⟩
--        α n (∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family-is-directed σ)) ≡⟨ {!!} ⟩
        {!!} ∎
-}

{-
β∞-after-α∞-is-id : β∞ ∘ α∞ ∼ id
β∞-after-α∞-is-id φ = to-continuous-function-≡ 𝓓∞ 𝓓∞ γ
 where
  γ : [ 𝓓∞ , 𝓓∞ ]⟨ β∞ (α∞ φ) ⟩ ∼ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩
  γ σ = to-𝓓∞-≡ ψ
   where
    ψ : (n : ℕ) → ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ β∞ (α∞ φ) ⟩ σ ⦆ n ≡ ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ σ ⦆ n
    ψ n = ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ β∞ (α∞ φ) ⟩ σ ⦆ n ≡⟨ {!!} ⟩
--          ⦅ ∐ 𝓓∞ (pointwise-family-is-directed 𝓓∞ 𝓓∞ (colimit-family (α∞ φ)) (colimit-family-is-directed (α∞ φ)) σ) ⦆ n ≡⟨ {!!} ⟩
          ∐ (𝓓 n) (family-at-ith-component-is-directed (pointwise-family 𝓓∞ 𝓓∞ (colimit-family (α∞ φ)) σ) (pointwise-family-is-directed 𝓓∞ 𝓓∞ (colimit-family (α∞ φ)) (colimit-family-is-directed (α∞ φ)) σ) n) ≡⟨ {!!} ⟩
          {!!} ≡⟨ {!!} ⟩
          ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ σ ⦆ n ∎
-}

\end{code}

Experimenting stuff

foo : (n : ℕ) → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (α n)
foo = α-is-continuous

helper : (𝓓 𝓓' 𝓔 𝓔' : DCPO {𝓤₁} {𝓤₁})
         (α₁ : ⟨ 𝓓 ⟩ → ⟨ 𝓓' ⟩)
         (p : 𝓓 ≡ 𝓔) (q : 𝓓' ≡ 𝓔')
       → ⟨ 𝓔 ⟩ → ⟨ 𝓔' ⟩
helper 𝓓₁ 𝓓' .𝓓₁ .𝓓' α₁ refl refl = α₁

transport-is-continuous : (𝓓 𝓓' 𝓔 𝓔' : DCPO {𝓤₁} {𝓤₁})
                          (α₁ : ⟨ 𝓓 ⟩ → ⟨ 𝓓' ⟩)
                          (β₁ : ⟨ 𝓔 ⟩ → ⟨ 𝓔' ⟩)
                          (c : is-continuous 𝓓 𝓓' α₁)
                          (p : 𝓓 ≡ 𝓔) (q : 𝓓' ≡ 𝓔')
                          (r : helper 𝓓 𝓓' 𝓔 𝓔' α₁ p q ≡ β₁)
                        → is-continuous 𝓔 𝓔' β₁
transport-is-continuous 𝓓₁ 𝓓' .𝓓₁ .𝓓' α₁ β₁ c refl refl refl = γ
 where
  abstract
   γ = c

bar : (((n : ℕ) → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (α n)) → 𝟙{𝓤₀}) → 𝟙{𝓤₀}
bar f = f α-is-continuous

open DcpoCone
cone : DcpoCone 𝓤₁ 𝓤₁
𝓔 cone = 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞
f cone = α
(f-cont cone) n = transport-is-continuous
                  (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (𝓔 cone) (𝓓 n)
                  (α n) ((f cone) n) {!γ!} refl refl refl
 where
  γ : is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (α n)
  -- (n : ℕ) → is-continuous (𝓔 cone) (𝓓 n) {!f cone n!}
  γ = α-is-continuous n
  test : (i : ℕ) → is-continuous (𝓔 cone) (𝓓 i) (f cone i) ≡ is-continuous (𝓔 cone) (𝓓 i) (f cone i)
  test i = refl
comm cone = α-commutes-with-π⁺

-- record { 𝓔 = {!!} ; f = {!!} ; f-cont = {!!} ; comm = {!!} }

{-
foo : {!!}
foo = DcpoCone.limit-mediating-arrow (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) α γ α-commutes-with-π⁺
 where
  γ : {!(i : ℕ) → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 i) (α i)!}
  γ = {!!}
-}
