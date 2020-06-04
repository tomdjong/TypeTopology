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

π-exp∞-alt : (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩) → π-exp∞ φ ≡ ∐ 𝓓∞ {ℕ} {λ n → ε∞ (succ n) (π-exp (succ n) φ)} {!!}
π-exp∞-alt φ = {!!}

{-
ε-expπ-exp-succ-deflation : (n : ℕ) (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩)
                  → ε-exp-from-succ n (π-exp-to-succ n φ) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ φ
ε-expπ-exp-succ-deflation n φ σ =
 [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp-from-succ n (π-exp-to-succ n φ) ⟩ σ ⊑⟨ 𝓓∞ ⟩[ l₁ ]
 (ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ n ∘ π∞ n) σ              ⊑⟨ 𝓓∞ ⟩[ l₂ ]
 (ϕ ∘ ε∞ n ∘ π∞ n) σ                            ⊑⟨ 𝓓∞ ⟩[ l₃ ]
 ϕ σ                                            ∎⟨ 𝓓∞ ⟩
  where
   ϕ : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
   ϕ = [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩
   l₁ = ≡-to-⊑ 𝓓∞ (happly' f g refl σ)
    where
     f : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
     f = [ 𝓓∞ , 𝓓∞ ]⟨ ε-exp-from-succ n (π-exp-to-succ n φ) ⟩
     g : ⟨ 𝓓∞ ⟩ → ⟨ 𝓓∞ ⟩
     g = ε∞ n ∘ π∞ n ∘ ϕ ∘ ε∞ n ∘ π∞ n
   l₂ = ε∞π∞-deflation ((ϕ ∘ ε∞ n ∘ π∞ n) σ)
   l₃ = mon (ε∞ n (π∞ n σ)) σ (ε∞π∞-deflation σ)
    where
     mon : is-monotone 𝓓∞ 𝓓∞ ϕ
     mon = continuous-implies-monotone 𝓓∞ 𝓓∞ φ

ε-expπ-exp-deflation : (n : ℕ) (φ : ⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩) → ε-exp n (π-exp n φ) ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ φ
ε-expπ-exp-deflation zero φ = -- Because of implicit arguments, I use transitivity
                              -- rather than the cleaner ⊑⟨...⟩[...] syntax.
 transitivity (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
  ((ε-exp-from-succ 0 ∘ ε 0 ∘ π 0 ∘ π-exp-to-succ 0) φ)
  ((ε-exp-from-succ 0 ∘ π-exp-to-succ 0) φ) φ
  l₁ l₂
 where
  l₁ : (ε-exp-from-succ 0 ∘ ε 0 ∘ π 0 ∘ π-exp-to-succ 0) φ
     ⊑⟨ 𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞ ⟩ (ε-exp-from-succ 0 ∘ π-exp-to-succ 0) φ
  l₁ = mon ((ε 0 ∘ π 0 ∘ π-exp-to-succ 0) φ) (π-exp-to-succ 0 φ)
        (επ-deflation 0 (π-exp-to-succ 0 φ))
   where
    mon : is-monotone (𝓓 1) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (ε-exp-from-succ 0)
    mon = continuous-implies-monotone (𝓓 1) (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞)
           (ε-exp-from-succ 0 , ε-exp-from-succ-is-continuous 0)
  l₂ : (ε-exp-from-succ 0 ∘ π-exp-to-succ 0) φ ⊑⟨ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) ⟩ φ
  l₂ = ε-expπ-exp-succ-deflation 0 φ
ε-expπ-exp-deflation (succ n) φ = ε-expπ-exp-succ-deflation n φ

π-expε-exp-succ-section : (n : ℕ) → π-exp-to-succ n ∘ ε-exp-from-succ n ∼ id
π-expε-exp-succ-section n (f , c) = to-continuous-function-≡ (𝓓 n) (𝓓 n) γ
 where
  γ : [ 𝓓 n , 𝓓 n ]⟨ π-exp-to-succ n (ε-exp-from-succ n (f , c)) ⟩ ∼ f
  γ x = [ 𝓓 n , 𝓓 n ]⟨ π-exp-to-succ n (ε-exp-from-succ n (f , c)) ⟩ x ≡⟨ refl ⟩
        (π∞ n ∘ ε∞ n ∘ f ∘ π∞ n ∘ ε∞ n) x                      ≡⟨ e₁   ⟩
        (f ∘ π∞ n ∘ ε∞ n) x                                    ≡⟨ e₂   ⟩
        f x ∎
   where
    e₁ = ε∞-section-of-π∞ ((f ∘ π∞ n ∘ ε∞ n) x)
    e₂ = ap f (ε∞-section-of-π∞ x)

ε-exp-section-of-π-exp : (n : ℕ) → π-exp n ∘ ε-exp n ∼ id
ε-exp-section-of-π-exp zero x =
 (π-exp 0 ∘ ε-exp 0) x                               ≡⟨ refl ⟩
 (π 0 ∘ π-exp-to-succ 0 ∘ ε-exp-from-succ 0 ∘ ε 0) x ≡⟨ p ⟩
 (π 0 ∘ ε 0) x                               ≡⟨ ε-section-of-π 0 x ⟩
 x                                           ∎
  where
   p = ap (π 0) (π-expε-exp-succ-section 0 (ε 0 x))
ε-exp-section-of-π-exp (succ n) = π-expε-exp-succ-section n
-}

\end{code}

\begin{code}

{-
key₁ : (n m k : ℕ) (l₁ : n ≤ k) (l₂ : m ≤ k) (σ : ⟨ 𝓓∞ ⟩) → π-exp n (β m (⦅ σ ⦆ m)) ≡ π⁺ l₁ (ε⁺ l₂ (⦅ σ ⦆ m))
key₁ zero zero k l₁ l₂ σ = {!!}
key₁ zero (succ m) k l₁ l₂ σ = {!!}
key₁ (succ n) zero k l₁ l₂ σ = {!!}
key₁ (succ n) (succ m) k l₁ l₂ σ = {!!}

π-exp∞-after-β∞-is-id : π-exp∞ ∘ β∞ ∼ id
π-exp∞-after-β∞-is-id σ = to-𝓓∞-≡ γ
 where
  γ : (n : ℕ) → ⦅ (π-exp∞ ∘ β∞) σ ⦆ n ≡ ⦅ σ ⦆ n
  γ n = ⦅ (π-exp∞ ∘ β∞) σ ⦆ n ≡⟨ refl ⟩
        π-exp n (β∞ σ) ≡⟨ refl ⟩
        π-exp n (∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁) ≡⟨ u₁ ⟩
        ∐ (𝓓 n) {ℕ} {π-exp n ∘ colimit-family σ} δ₂ ≡⟨ refl ⟩
        ∐ (𝓓 n) {ℕ} {λ m → π-exp n (β m (⦅ σ ⦆ m))} δ₂ ≡⟨ p ⟩
        ⦅ σ ⦆ n ∎
{-        ∐ (𝓓 n) {ℕ} {λ m → ⦅ ε∞ m (⦅ σ ⦆ m) ⦆ n} δ₄ ≡⟨ refl ⟩
          ⦅ ∐ 𝓓∞ δ₃ ⦆ n ≡⟨ ap (λ - → ⦅ - ⦆ n) ((∐-of-ε∞s σ) ⁻¹) ⟩
          ⦅ σ ⦆ n ∎ -}
   where
    δ₁ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family σ)
    δ₁ = colimit-family-is-directed σ
    δ₂ : is-Directed (𝓓 n) (π-exp n ∘ colimit-family σ)
    δ₂ = image-is-directed' (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (π-exp n , π-exp-is-continuous n) δ₁
    δ₃ : is-Directed 𝓓∞ (ε∞-family σ)
    δ₃ = ε∞-family-is-directed σ
    δ₄ : is-Directed (𝓓 n) (family-at-ith-component (ε∞-family σ) n)
    δ₄ = family-at-ith-component-is-directed (ε∞-family σ) δ₃ n
    u₁ = continuous-∐-≡ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (𝓓 n) (π-exp n , π-exp-is-continuous n) δ₁
    p = antisymmetry (𝓓 n) (∐ (𝓓 n) δ₂) (⦅ σ ⦆ n) u v
     where
      u : ∐ (𝓓 n) δ₂ ⊑⟨ 𝓓 n ⟩ ⦅ σ ⦆ n
      u = ∐-is-lowerbound-of-upperbounds (𝓓 n) δ₂ (⦅ σ ⦆ n) ub
       where
        ub : is-upperbound (underlying-order (𝓓 n)) (⦅ σ ⦆ n)
              (λ m → π-exp n (β m (⦅ σ ⦆ m)))
        ub m = π-exp n (β m (⦅ σ ⦆ m)) ⊑⟨ 𝓓 n ⟩[ {!!} ]
               ⦅ ε∞ m (⦅ σ ⦆ m) ⦆ n ⊑⟨ 𝓓 n ⟩[ ∐-is-upperbound (𝓓 n) δ₄ m ]
               ∐ (𝓓 n) δ₄ ⊑⟨ 𝓓 n ⟩[ ≡-to-⊑ (𝓓 n) (ap (λ - → ⦅ - ⦆ n) ((∐-of-ε∞s σ) ⁻¹)) ]
               ⦅ σ ⦆ n ∎⟨ 𝓓 n ⟩
      v : ⦅ σ ⦆ n ⊑⟨ 𝓓 n ⟩ ∐ (𝓓 n) δ₂
      v = ⦅ σ ⦆ n ⊑⟨ 𝓓 n ⟩[ ≡-to-⊑ (𝓓 n) ((β-section-of-π-exp n (⦅ σ ⦆ n)) ⁻¹) ]
          π-exp n (β n (⦅ σ ⦆ n)) ⊑⟨ 𝓓 n ⟩[ ∐-is-upperbound (𝓓 n) δ₂ n ]
          ∐ (𝓓 n) δ₂ ∎⟨ 𝓓 n ⟩

blah : (n m : ℕ) (l : n ≤ m) (f : ⟨ 𝓓 (succ m) ⟩)
     → [ 𝓓 n , 𝓓 n ]⟨ π⁺ {succ n} {succ m} l f ⟩
     ≡ π⁺ {n} {m} l ∘  [ 𝓓 m , 𝓓 m ]⟨ f ⟩ ∘ ε⁺ {n} {m} l
blah n m l f = [ 𝓓 n , 𝓓 n ]⟨ π⁺ {succ n} {succ m} l f ⟩ ≡⟨ {!!} ⟩
               [ 𝓓 n , 𝓓 n ]⟨ π⁺-helper-Σ (succ n) (succ m) (subtraction' (succ n) (succ m) l) f ⟩ ≡⟨ ap (λ - → [ 𝓓 n , 𝓓 n ]⟨ - ⟩) (π⁺-helper-on-succ (succ n) m _ _ f) ⟩
               [ 𝓓 n , 𝓓 n ]⟨ (π⁺-helper-Σ (succ n) m _ ∘ π m) f ⟩ ≡⟨ {!!} ⟩
               {!!} ≡⟨ {!!} ⟩
               π⁺ l ∘ underlying-function (𝓓 m) (𝓓 m) f ∘ ε⁺ l ∎

test : (n m : ℕ) → π-exp n ∘ β m ∼ π⁺ {n} {n +' m} (≤-+ n m) ∘ ε⁺ {m} {n +' m} (≤-+' n m)
test zero m = {!!}
test (succ n) zero = {!!}
test (succ n) (succ m) (f , c) = to-continuous-function-≡ (𝓓 n) (𝓓 n) γ
 where
  γ : π∞ n ∘ ε∞ m ∘ f ∘ π∞ m ∘ ε∞ n ∼ [ 𝓓 n , 𝓓 n ]⟨ (π⁺ {succ n} {succ n +' succ m} (≤-+ (succ n) (succ m)) ∘ ε⁺ {succ m} {succ n +' succ m} (≤-+' (succ n) (succ m))) (f , c) ⟩
  γ = {!!}

β∞-after-π-exp∞-is-id : β∞ ∘ π-exp∞ ∼ id
β∞-after-π-exp∞-is-id φ = to-continuous-function-≡ 𝓓∞ 𝓓∞ γ
 where
  γ : [ 𝓓∞ , 𝓓∞ ]⟨ β∞ (π-exp∞ φ) ⟩ ∼ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩
  γ σ = to-𝓓∞-≡ ψ
   where
    ψ : (n : ℕ) → ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ β∞ (π-exp∞ φ) ⟩ σ ⦆ n ≡ ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ σ ⦆ n
    ψ n = ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ β∞ (π-exp∞ φ) ⟩ σ ⦆ n ≡⟨ refl ⟩
          ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ ∐ (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) δ₁ ⟩ σ ⦆ n ≡⟨ refl ⟩
          ⦅ ∐ 𝓓∞ δ₂ ⦆ n ≡⟨ refl ⟩
          ∐ (𝓓 n) {ℕ} {λ m → ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ β m (π-exp m φ) ⟩ σ ⦆ n} δ₃ ≡⟨ {!!} ⟩
          ∐ (𝓓 n) {ℕ} {λ m → ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ (ε∞ m (⦅ σ ⦆ m)) ⦆ n} δ₆ ≡⟨ refl ⟩
          ⦅ ∐ 𝓓∞ δ₅ ⦆ n ≡⟨ ap (λ - → ⦅ - ⦆ n) ((continuous-∐-≡ 𝓓∞ 𝓓∞ φ δ₄) ⁻¹) ⟩
          ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ (∐ 𝓓∞ δ₄) ⦆ n ≡⟨ ap (λ - → ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ - ⦆ n) ((∐-of-ε∞s σ) ⁻¹) ⟩
          ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ σ ⦆ n ∎
     where
      δ₁ : is-Directed (𝓓∞ ⟹ᵈᶜᵖᵒ 𝓓∞) (colimit-family (π-exp∞ φ))
      δ₁ = colimit-family-is-directed (π-exp∞ φ)
      δ₂ : is-Directed 𝓓∞ (pointwise-family 𝓓∞ 𝓓∞ (colimit-family (π-exp∞ φ)) σ)
      δ₂ = pointwise-family-is-directed 𝓓∞ 𝓓∞ (colimit-family (π-exp∞ φ)) δ₁ σ
      δ₃ : is-Directed (𝓓 n) (family-at-ith-component
                               (pointwise-family 𝓓∞ 𝓓∞ (colimit-family (π-exp∞ φ)) σ) n)
      δ₃ = family-at-ith-component-is-directed
            (pointwise-family 𝓓∞ 𝓓∞ (colimit-family (π-exp∞ φ)) σ) δ₂ n
      δ₄ : is-Directed 𝓓∞ (ε∞-family σ)
      δ₄ = ε∞-family-is-directed σ
      δ₅ : is-Directed 𝓓∞ ([ 𝓓∞ ,  𝓓∞ ]⟨ φ ⟩ ∘ ε∞-family σ)
      δ₅ = image-is-directed' 𝓓∞ 𝓓∞ φ δ₄
      δ₆ : is-Directed (𝓓 n)
             (family-at-ith-component
              ([ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ ∘ ε∞-family σ) n)
      δ₆ = family-at-ith-component-is-directed ([ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ ∘ ε∞-family σ) δ₅ n
      {-
      p = antisymmetry (𝓓 n) (∐ (𝓓 n) δ₃) (⦅ [ 𝓓∞ , 𝓓∞ ]⟨ φ ⟩ σ ⦆ n)
          u v
       where
        u : ∐ (𝓓 n) δ₃ ⊑⟨ 𝓓 n ⟩ ⦅ [ 𝓓∞ ,  𝓓∞ ]⟨ φ ⟩ σ ⦆ n
        u = {!\!}
        v : ⦅ [ 𝓓∞ ,  𝓓∞ ]⟨ φ ⟩ σ ⦆ n ⊑⟨ 𝓓 n ⟩ ∐ (𝓓 n) δ₃
        v = ⦅ [ 𝓓∞ ,  𝓓∞ ]⟨ φ ⟩ σ ⦆ n ⊑⟨ 𝓓 n ⟩[ βα-deflation {!n!} φ σ {!n!} ]
            ⦅ [ 𝓓∞ , 𝓓∞ ]⟨ β n (α n φ) ⟩ σ ⦆ n ⊑⟨ 𝓓 n ⟩[ ∐-is-upperbound (𝓓 n) δ₃ n ]
            ∐ (𝓓 n) δ₃ ∎⟨ 𝓓 n ⟩ -}

{-
  colimit-family : ⟨ 𝓓∞ ⟩ → I → ⟨ 𝓔 ⟩
  colimit-family σ i = g i (⦅ σ ⦆ i)

          family-at-ith-component
                               (pointwise-family 𝓓∞ 𝓓∞ (colimit-family (α∞ φ)) σ) n m}
-}
-}

\end{code}
