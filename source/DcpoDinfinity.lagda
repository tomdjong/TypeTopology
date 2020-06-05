Tom de Jong, 12 May 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

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

π-exp-to-succ : (n : ℕ) → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓 (succ n) ⟩
π-exp-to-succ n f = DCPO-∘₃ (𝓓 n) 𝓓∞ 𝓓∞ (𝓓 n) (ε∞' n) f (π∞' n)

π-exp-to-succ-is-continuous : (n : ℕ)
                            → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 (succ n))
                               (π-exp-to-succ n)
π-exp-to-succ-is-continuous n =
 DCPO-∘₃-is-continuous₂ (𝓓 n) 𝓓∞ 𝓓∞ (𝓓 n) (ε∞' n) (π∞' n)

π-exp : (n : ℕ) → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓 n ⟩
π-exp zero     = π 0 ∘ π-exp-to-succ 0
π-exp (succ n) = π-exp-to-succ n

π-exp-is-continuous : (n : ℕ) → is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (π-exp n)
π-exp-is-continuous zero = ∘-is-continuous (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 1) (𝓓 0)
                            (π-exp-to-succ 0) (π 0)
                            (π-exp-to-succ-is-continuous 0) (π-is-continuous 0)
π-exp-is-continuous (succ n) = π-exp-to-succ-is-continuous n

π-exp-commutes-with-π : (n : ℕ) → π n ∘ π-exp (succ n) ∼ π-exp n
π-exp-commutes-with-π zero f = refl
π-exp-commutes-with-π (succ n) (f , c) =
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

π-exp-commutes-with-π⁺ : (n m : ℕ) (l : n ≤ m) → π⁺ {n} {m} l ∘ π-exp m ∼ π-exp n
π-exp-commutes-with-π⁺ n m l = commute-with-πs-lemma (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                            π-exp π-exp-commutes-with-π n m l

open DcpoCone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) π-exp π-exp-is-continuous π-exp-commutes-with-π⁺

π-exp∞ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
π-exp∞ = limit-mediating-arrow

π-exp∞' : DCPO[ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ , 𝓓∞ ]
π-exp∞' = limit-mediating-arrow , limit-mediating-arrow-is-continuous

\end{code}

\begin{code}

ε-exp-from-succ : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp-from-succ n f = DCPO-∘₃ 𝓓∞ (𝓓 n) (𝓓 n) 𝓓∞ (π∞' n) f (ε∞' n)

ε-exp-from-succ-is-continuous : (n : ℕ)
                              → is-continuous (𝓓 (succ n)) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                                 (ε-exp-from-succ n)
ε-exp-from-succ-is-continuous n = DCPO-∘₃-is-continuous₂ 𝓓∞ (𝓓 n) (𝓓 n) 𝓓∞
                                   (π∞' n) (ε∞' n)

ε-exp : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp zero     = ε-exp-from-succ 0 ∘ ε 0
ε-exp (succ n) = ε-exp-from-succ n

ε-exp-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp n)
ε-exp-is-continuous zero = ∘-is-continuous (𝓓 0) (𝓓 1) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
                            (ε 0) (ε-exp-from-succ 0)
                            (ε-is-continuous 0) (ε-exp-from-succ-is-continuous 0)
ε-exp-is-continuous (succ n) = ε-exp-from-succ-is-continuous n

ε-exp-commutes-with-ε : (n : ℕ) → ε-exp (succ n) ∘ ε n ∼ ε-exp n
ε-exp-commutes-with-ε zero x = refl
ε-exp-commutes-with-ε (succ n) (f , c) =
 to-continuous-function-≡ 𝓓∞ 𝓓∞ γ
   where
    ε-exp₁ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
    ε-exp₁ = [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp (succ (succ n)) (ε (succ n) (f , c)) ⟩
    ε-exp₂ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
    ε-exp₂ = [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp (succ n) (f , c) ⟩
    γ : ε-exp₁ ∼ ε-exp₂
    γ σ = ε-exp₁ σ                                                ≡⟨ refl ⟩
          (ε∞ (succ n) ∘ ε n ∘ h) σ                               ≡⟨ e₁   ⟩
          (ε∞ (succ n) ∘ ε⁺ {n} {succ n} (≤-succ n) ∘ h) σ        ≡⟨ e₂   ⟩
          (ε∞ n ∘ h) σ                                            ≡⟨ refl ⟩
          (ε∞ n ∘ f ∘ π n ∘ π∞ (succ n)) σ                        ≡⟨ e₃ ⟩
          (ε∞ n ∘ f ∘ π⁺ {n} {succ n} (≤-succ n) ∘ π∞ (succ n)) σ ≡⟨ e₄ ⟩
          (ε∞ n ∘ f ∘ π∞ n) σ                                     ≡⟨ refl ⟩
          ε-exp₂ σ                                                ∎
     where
      h : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓 n ⟩
      h = f ∘ π n ∘ π∞ (succ n)
      e₁ = ap (ε∞ (succ n)) (ε-in-terms-of-ε⁺ n (h σ))
      e₂ = ε∞-commutes-with-εs n (succ n) (≤-succ n) (h σ)
      e₃ = ap (ε∞ n ∘ f) (π-in-terms-of-π⁺ n (π∞ (succ n) σ))
      e₄ = ap (ε∞ n ∘ f) (π∞-commutes-with-πs n (succ n) (≤-succ n) σ)

ε-exp-commutes-with-ε⁺ : (n m : ℕ) (l : n ≤ m) → ε-exp m ∘ ε⁺ {n} {m} l ∼ ε-exp n
ε-exp-commutes-with-ε⁺ n m l = commute-with-εs-lemma (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε-exp
                                ε-exp-commutes-with-ε n m l

open DcpoCocone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε-exp ε-exp-is-continuous ε-exp-commutes-with-ε⁺

ε-exp∞ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp∞ = colimit-mediating-arrow

ε-exp∞' : DCPO[ 𝓓∞ , 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ]
ε-exp∞' = colimit-mediating-arrow , colimit-mediating-arrow-is-continuous

\end{code}

\begin{code}

ε-exp-family : ⟨ 𝓓∞ ⟩ → ℕ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
ε-exp-family σ n = ε-exp (succ n) (⦅ σ ⦆ (succ n))

ε-exp-family-is-directed : (σ : ⟨ 𝓓∞ ⟩)
                         → is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family σ)
ε-exp-family-is-directed σ = ∣ 0 ∣ , γ
 where
  γ : is-weakly-directed (underlying-order (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)) (ε-exp-family σ)
  γ n m = ∥∥-functor g h
   where
    δ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family σ)
    δ = colimit-family-is-directed σ
    h : ∃ k ꞉ ℕ , colimit-family σ (succ n) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k
                × colimit-family σ (succ m) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k
    h = Directed-implies-weakly-directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ (succ n) (succ m)
    g : (Σ k ꞉ ℕ , colimit-family σ (succ n) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k
                 × colimit-family σ (succ m) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ colimit-family σ k)
      → Σ k ꞉ ℕ , ε-exp-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
                × ε-exp-family σ m ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
    g (k , lₙ , lₘ) = k , lₙ' , lₘ'
     where
      lₖ : colimit-family σ k ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
      lₖ = colimit-family-is-monotone σ k (succ k) (≤-succ k)
      lₙ' : ε-exp-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
      lₙ' = transitivity (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
             (ε-exp-family σ n) (colimit-family σ k) (ε-exp-family σ k)
             lₙ lₖ
      lₘ' : ε-exp-family σ m ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ k
      lₘ' = transitivity (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
             (ε-exp-family σ m) (colimit-family σ k) (ε-exp-family σ k)
             lₘ lₖ

ε-exp∞-alt : (σ : ⟨ 𝓓∞ ⟩)
           → ε-exp∞ σ ≡ ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family-is-directed σ)
ε-exp∞-alt σ = antisymmetry (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp∞ σ) (∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂) a b
 where
  δ₁ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family σ)
  δ₁ = colimit-family-is-directed σ
  δ₂ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family σ)
  δ₂ = ε-exp-family-is-directed σ
  a : ε-exp∞ σ ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂
  a = ∐-is-monotone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁ δ₂ γ
   where
    γ : (n : ℕ)
      → colimit-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ n
    γ n = colimit-family-is-monotone σ n (succ n) (≤-succ n)
  b : ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂ ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp∞ σ
  b = ∐-is-lowerbound-of-upperbounds (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₂ (ε-exp∞ σ) γ
   where
    γ : is-upperbound (underlying-order (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞))
         (ε-exp∞ σ) (ε-exp-family σ)
    γ n = ∐-is-upperbound (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁ (succ n)

π-exp-family : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ → ℕ → ⟨ 𝓓∞ ⟩
π-exp-family φ n = ε∞ (succ n) (π-exp (succ n) φ)

π-exp-family-is-directed : (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩)
                         → is-Directed 𝓓∞ (π-exp-family φ)
π-exp-family-is-directed φ = ∣ 0 ∣ , γ
 where
  γ : is-weakly-directed (underlying-order 𝓓∞) (π-exp-family φ)
  γ n m = ∥∥-functor g h
   where
    σ : ⟨ 𝓓∞ ⟩
    σ = π-exp∞ φ
    δ : is-Directed 𝓓∞ (ε∞-family σ)
    δ = ε∞-family-is-directed σ
    h : ∃ k ꞉ ℕ , ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k
                × ε∞-family σ (succ m) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k
    h = Directed-implies-weakly-directed 𝓓∞ δ (succ n) (succ m)
    g : (Σ k ꞉ ℕ , ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k
                 × ε∞-family σ (succ m) ⊑⟨ 𝓓∞ ⟩ ε∞-family σ k)
      → Σ k ꞉ ℕ , π-exp-family φ n ⊑⟨ 𝓓∞ ⟩ π-exp-family φ k
                × π-exp-family φ m ⊑⟨ 𝓓∞ ⟩ π-exp-family φ k
    g (k , lₙ , lₘ) = k , lₙ' , lₘ'
     where
      lₖ : ε∞-family σ k ⊑⟨ 𝓓∞ ⟩ ε∞-family σ (succ k)
      lₖ = ε∞-family-is-monotone σ k (succ k) (≤-succ k)
      lₙ' = π-exp-family φ n     ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (π-exp-family φ n) ]
            ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩[ lₙ ]
            ε∞-family σ k        ⊑⟨ 𝓓∞ ⟩[ lₖ ]
            ε∞-family σ (succ k) ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (π-exp-family φ k) ]
            π-exp-family φ k     ∎⟨ 𝓓∞ ⟩
      lₘ' = π-exp-family φ m     ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (π-exp-family φ m) ]
            ε∞-family σ (succ m) ⊑⟨ 𝓓∞ ⟩[ lₘ ]
            ε∞-family σ k        ⊑⟨ 𝓓∞ ⟩[ lₖ ]
            ε∞-family σ (succ k) ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (π-exp-family φ k) ]
            π-exp-family φ k     ∎⟨ 𝓓∞ ⟩

π-exp∞-alt : (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩)
           → π-exp∞ φ ≡ ∐ 𝓓∞ (π-exp-family-is-directed φ)
π-exp∞-alt φ = σ                              ≡⟨ ∐-of-ε∞s σ ⟩
               ∐ 𝓓∞ (ε∞-family-is-directed σ) ≡⟨ γ ⟩
               ∐ 𝓓∞ (π-exp-family-is-directed φ) ∎
 where
  σ : ⟨ 𝓓∞ ⟩
  σ = π-exp∞ φ
  γ : ∐ 𝓓∞ (ε∞-family-is-directed σ) ≡ ∐ 𝓓∞ (π-exp-family-is-directed φ)
  γ = antisymmetry 𝓓∞ (∐ 𝓓∞ δ₁) (∐ 𝓓∞ δ₂) a b
   where
    δ₁ : is-Directed 𝓓∞ (ε∞-family σ)
    δ₁ = ε∞-family-is-directed σ
    δ₂ : is-Directed 𝓓∞ (π-exp-family φ)
    δ₂ = π-exp-family-is-directed φ
    a : ∐ 𝓓∞ δ₁ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₂
    a = ∐-is-monotone 𝓓∞ δ₁ δ₂ h
     where
      h : (n : ℕ) → ε∞-family σ n ⊑⟨ 𝓓∞ ⟩ π-exp-family φ n
      h n = ε∞-family σ n        ⊑⟨ 𝓓∞ ⟩[ ε∞-family-is-monotone σ n (succ n) (≤-succ n) ]
            ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (ε∞-family σ (succ n)) ]
            π-exp-family φ n     ∎⟨ 𝓓∞ ⟩
    b : ∐ 𝓓∞ δ₂ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₁
    b = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₂ (∐ 𝓓∞ δ₁) h
     where
      h : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₁) (π-exp-family φ)
      h n = π-exp-family φ n     ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (π-exp-family φ n) ]
            ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩[ ∐-is-upperbound 𝓓∞ δ₁ (succ n) ]
            ∐ 𝓓∞ δ₁              ∎⟨ 𝓓∞ ⟩

\end{code}

\begin{code}

π-exp-family-is-monotone : (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩) {n m : ℕ} → n ≤ m
                         → π-exp-family φ n ⊑⟨ 𝓓∞ ⟩ π-exp-family φ m
π-exp-family-is-monotone φ {n} {m} l =
 π-exp-family φ n              ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (π-exp-family φ n) ]
 ε∞-family (π-exp∞ φ) (succ n) ⊑⟨ 𝓓∞ ⟩[ u  ]
 ε∞-family (π-exp∞ φ) (succ m) ⊑⟨ 𝓓∞ ⟩[ reflexivity 𝓓∞ (π-exp-family φ m) ]
 π-exp-family φ m              ∎⟨ 𝓓∞ ⟩
  where
   u = ε∞-family-is-monotone (π-exp∞ φ) (succ n) (succ m) l

π-exp-family-is-monotone' : (φ ψ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩) {n : ℕ}
                          → φ ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ψ
                          → π-exp-family φ n ⊑⟨ 𝓓∞ ⟩ π-exp-family ψ n
π-exp-family-is-monotone' φ ψ {n} l =
 π-exp-family φ n               ⊑⟨ 𝓓∞ ⟩[ u₁ ]
 ε∞ (succ n) (π-exp (succ n) φ) ⊑⟨ 𝓓∞ ⟩[ u₂ ]
 ε∞ (succ n) (π-exp (succ n) ψ) ⊑⟨ 𝓓∞ ⟩[ u₃ ]
 π-exp-family ψ n ∎⟨ 𝓓∞ ⟩
  where
   u₁ = reflexivity 𝓓∞ (ε∞ (succ n) (π-exp (succ n) φ))
   u₂ = continuous-implies-monotone (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ f φ ψ l
    where
     f : DCPO[ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ , 𝓓∞ ]
     f = DCPO-∘ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 (succ n)) 𝓓∞
          (π-exp (succ n) , π-exp-is-continuous (succ n))
          (ε∞' (succ n))
   u₃ = reflexivity 𝓓∞ (ε∞ (succ n) (π-exp (succ n) ψ))

ε-exp-family-is-monotone : (σ : ⟨ 𝓓∞ ⟩) {n m : ℕ} → n ≤ m
                         → ε-exp-family σ n ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ ε-exp-family σ m
ε-exp-family-is-monotone σ {n} {m} l =
 colimit-family-is-monotone σ (succ n) (succ m) l

\end{code}

\begin{code}

ε-exp∞-is-section-of-π-exp∞ : π-exp∞ ∘ ε-exp∞ ∼ id
ε-exp∞-is-section-of-π-exp∞ σ =
 π-exp∞ (ε-exp∞ σ)                                 ≡⟨ ap π-exp∞ (ε-exp∞-alt σ) ⟩
 π-exp∞ (∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁)                       ≡⟨ e₁ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → (π-exp∞ ∘ ε-exp-family σ) n} δ₂   ≡⟨ ∐-family-≡ 𝓓∞ p δ₂ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → ∐ 𝓓∞ {ℕ} {λ m → f n m} (δ₃ n)} δ₄ ≡⟨ e₂ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → ε∞ n (⦅ σ ⦆ n)} δ₅                ≡⟨ (∐-of-ε∞s σ) ⁻¹ ⟩
 σ                                                 ∎
  where
   f : ℕ → ℕ → ⟨ 𝓓∞ ⟩
   f n m = π-exp-family (ε-exp-family σ n) m
   δ₁ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family σ)
   δ₁ = ε-exp-family-is-directed σ
   δ₂ : is-Directed 𝓓∞ (π-exp∞ ∘ ε-exp-family σ)
   δ₂ = image-is-directed' (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ π-exp∞' δ₁
   δ₃ : (n : ℕ) → is-Directed 𝓓∞ (π-exp-family (ε-exp-family σ n))
   δ₃ n = π-exp-family-is-directed (ε-exp-family σ n)
   p : π-exp∞ ∘ ε-exp-family σ ≡ λ n → ∐ 𝓓∞ (δ₃ n)
   p = dfunext fe (λ n → π-exp∞-alt (ε-exp-family σ n))
   δ₄ : is-Directed 𝓓∞ (λ n → ∐ 𝓓∞ (δ₃ n))
   δ₄ = transport (is-Directed 𝓓∞) p δ₂
   δ₅ : is-Directed 𝓓∞ (ε∞-family σ)
   δ₅ = ε∞-family-is-directed σ
   e₁ = continuous-∐-≡ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ π-exp∞' δ₁
   e₂ = antisymmetry 𝓓∞ (∐ 𝓓∞ δ₄) (∐ 𝓓∞ δ₅) l₁ l₂
    where
     r : (n : ℕ) → f n n ≡ ε∞-family σ (succ n)
     r n = ap (ε∞ (succ n)) γ
      where
       γ : π-exp (succ n) (ε-exp-family σ n) ≡ ⦅ σ ⦆ (succ n)
       γ = to-continuous-function-≡ (𝓓 n) (𝓓 n) ψ
        where
         σ' : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 n ⟩
         σ' = [ 𝓓 n , 𝓓 n ]⟨ ⦅ σ ⦆ (succ n) ⟩
         ψ : π∞ n ∘ ε∞ n ∘ σ' ∘ π∞ n ∘ ε∞ n ∼ σ'
         ψ x = (π∞ n ∘ ε∞ n ∘ σ' ∘ π∞ n ∘ ε∞ n) x ≡⟨ p₁ ⟩
               (σ' ∘ π∞ n ∘ ε∞ n) x               ≡⟨ p₂ ⟩
               σ' x                               ∎
          where
           p₁ = ε∞-section-of-π∞ (σ' (π∞ n (ε∞ n x)))
           p₂ = ap σ' (ε∞-section-of-π∞ x)
     l₁ : ∐ 𝓓∞ δ₄ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₅
     l₁ = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₄ (∐ 𝓓∞ δ₅) γ
      where
       γ : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₅) (λ n → ∐ 𝓓∞ (δ₃ n))
       γ n = ∐-is-lowerbound-of-upperbounds 𝓓∞ (δ₃ n) (∐ 𝓓∞ δ₅) ψ
        where
         ψ : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₅) (f n)
         ψ m = f n m                       ⊑⟨ 𝓓∞ ⟩[ u₁ ]
               f (n +' m) m                ⊑⟨ 𝓓∞ ⟩[ u₂ ]
               f (n +' m) (n +' m)         ⊑⟨ 𝓓∞ ⟩[ u₃ ]
               ε∞-family σ (succ (n +' m)) ⊑⟨ 𝓓∞ ⟩[ u₄ ]
               ∐ 𝓓∞ δ₅ ∎⟨ 𝓓∞ ⟩
          where
           u₁ = π-exp-family-is-monotone'
                 (ε-exp-family σ n) (ε-exp-family σ (n +' m))
                 (ε-exp-family-is-monotone σ (≤-+ n m))
           u₂ = π-exp-family-is-monotone (ε-exp-family σ (n +' m)) (≤-+' n m)
           u₃ = ≡-to-⊑ 𝓓∞ (r (n +' m))
           u₄ = ∐-is-upperbound 𝓓∞ δ₅ (succ (n +' m))
     l₂ : ∐ 𝓓∞ δ₅ ⊑⟨ 𝓓∞ ⟩ ∐ 𝓓∞ δ₄
     l₂ = ∐-is-lowerbound-of-upperbounds 𝓓∞ δ₅ (∐ 𝓓∞ δ₄) γ
      where
       γ : is-upperbound (underlying-order 𝓓∞) (∐ 𝓓∞ δ₄) (ε∞-family σ)
       γ n = ε∞-family σ n        ⊑⟨ 𝓓∞ ⟩[ u ]
             ε∞-family σ (succ n) ⊑⟨ 𝓓∞ ⟩[ ≡-to-⊑ 𝓓∞ ((r n) ⁻¹) ]
             f n n                ⊑⟨ 𝓓∞ ⟩[ ∐-is-upperbound 𝓓∞ (δ₃ n) n ]
             ∐ 𝓓∞ (δ₃ n)          ⊑⟨ 𝓓∞ ⟩[ ∐-is-upperbound 𝓓∞ δ₄ n ]
             ∐ 𝓓∞ δ₄              ∎⟨ 𝓓∞ ⟩
        where
         u = ε∞-family-is-monotone σ n (succ n) (≤-succ n)

\end{code}

\begin{code}

π-exp∞-is-section-of-ε-exp∞ : ε-exp∞ ∘ π-exp∞ ∼ id
π-exp∞-is-section-of-ε-exp∞ φ =
 ε-exp∞ (π-exp∞ φ)                               ≡⟨ e₁ ⟩
 ε-exp∞ (∐ 𝓓∞ δ₁)                                ≡⟨ e₂ ⟩
 ∐ 𝓔 {ℕ} {λ n → (ε-exp∞ ∘ π-exp-family φ) n} δ₂  ≡⟨ e₃ ⟩
 ∐ 𝓔 {ℕ} {λ n → ∐ 𝓔 {ℕ} {λ m → f n m} (δ₃ n)} δ₄ ≡⟨ e₄ ⟩
 ∐ 𝓔 {ℕ} {λ n → f n n} δ₅                        ≡⟨ e₅ ⟩
 ∐ 𝓔 {ℕ} {λ n → {!!}} δ₆          ≡⟨ e₆ ⟩
 φ ∎
  where
   𝓔 : DCPO {𝓤₁} {𝓤₁}
   𝓔 = 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞
   f : ℕ → ℕ → ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩
   f n m = ε-exp-family (π-exp-family φ n) m
   δ₁ = π-exp-family-is-directed φ
   δ₂ = image-is-directed' 𝓓∞ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ε-exp∞' δ₁
   δ₃ : (n : ℕ) → is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family (π-exp-family φ n))
   δ₃ n = ε-exp-family-is-directed (π-exp-family φ n)
   p : ε-exp∞ ∘ π-exp-family φ ≡ (λ n → ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (δ₃ n))
   p = dfunext fe (λ n → ε-exp∞-alt (π-exp-family φ n))
   δ₄ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (λ n → ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (δ₃ n))
   δ₄ = (transport (is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)) p δ₂)
   δ₅ : {!!}
   δ₅ = {!!}
   δ₆ : {!!}
   δ₆ = {!!}
   e₁ = ap ε-exp∞ (π-exp∞-alt φ)
   e₂ = continuous-∐-≡ 𝓓∞ 𝓔 ε-exp∞' δ₁
   e₃ = ∐-family-≡ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) p δ₂
   e₄ = {!!}
   e₅ = {!!}
   e₆ = {!antisymmetry 𝓔 (∐ 𝓔 δ₆) φ l₁ l₂!}
    where
     l₁ : ∐ 𝓔 δ₆ ⊑⟨ 𝓔 ⟩ φ
     l₁ = ∐-is-lowerbound-of-upperbounds 𝓔 δ₆ φ γ
      where
       γ : is-upperbound (underlying-order 𝓔) φ {!!}
       γ n σ = {!!} ⊑⟨ 𝓓∞ ⟩[ {!!} ]
               (ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ n ∘ π∞ n) σ ⊑⟨ 𝓓∞ ⟩[ {!!} ]
               (ϕ ∘ ε∞ n ∘ π∞ n) σ               ⊑⟨ 𝓓∞ ⟩[ ϕ-mon {!!} {!!} {!!} ]
               ϕ σ                               ∎⟨ 𝓓∞ ⟩
        where
         ϕ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
         ϕ = [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩
         ϕ-mon : is-monotone 𝓓∞ 𝓓∞ ϕ
         ϕ-mon = {!!}
     l₂ : φ ⊑⟨ 𝓔 ⟩ ∐ 𝓔 δ₆
     l₂ = {!!}


{-

 π-exp∞ (ε-exp∞ σ)                                 ≡⟨ ap π-exp∞ (ε-exp∞-alt σ) ⟩
 π-exp∞ (∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁)                       ≡⟨ e₁ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → (π-exp∞ ∘ ε-exp-family σ) n} δ₂   ≡⟨ ∐-family-≡ 𝓓∞ p δ₂ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → ∐ 𝓓∞ {ℕ} {λ m → f n m} (δ₃ n)} δ₄ ≡⟨ e₂ ⟩
 ∐ 𝓓∞ {ℕ} {λ n → ε∞ n (⦅ σ ⦆ n)} δ₅                ≡⟨ (∐-of-ε∞s σ) ⁻¹ ⟩
 σ                                                 ∎
  where
   f : (n m : ℕ) → ⟨ 𝓓∞ ⟩
   f n m = π-exp-family (ε-exp-family σ n) m
   δ₁ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-family σ)
   δ₁ = ε-exp-family-is-directed σ
   δ₂ : is-Directed 𝓓∞ (π-exp∞ ∘ ε-exp-family σ)
   δ₂ = image-is-directed' (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ π-exp∞' δ₁
   δ₃ : (n : ℕ) → is-Directed 𝓓∞ (π-exp-family (ε-exp-family σ n))
   δ₃ n = π-exp-family-is-directed (ε-exp-family σ n)
   p : π-exp∞ ∘ ε-exp-family σ ≡ λ m → ∐ 𝓓∞ (δ₃ m)
   p = dfunext fe (λ m → π-exp∞-alt (ε-exp-family σ m))
   δ₄ : is-Directed 𝓓∞ (λ n → ∐ 𝓓∞ (δ₃ n))
   δ₄ = transport (is-Directed 𝓓∞) p δ₂
   δ₅ : is-Directed 𝓓∞ (ε∞-family σ)
   δ₅ = ε∞-family-is-directed σ
   e₁ = continuous-∐-≡ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) 𝓓∞ π-exp∞' δ₁
   e₂ = antisymmetry 𝓓∞ (∐ 𝓓∞ δ₄) (∐ 𝓓∞ δ₅) l₁ l₂

-}

\end{code}
