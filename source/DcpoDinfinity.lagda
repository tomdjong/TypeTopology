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
open import DcpoLimits pt fe 𝓤₀ 𝓤₁ 𝓤₁
open import DcpoLifting pt fe 𝓤₀ pe

open import NaturalsOrder
open import NaturalsAddition renaming (_+_ to _+'_)

𝓓⊥ : ℕ → DCPO⊥ {𝓤₁} {𝓤₁}
𝓓⊥ zero     = 𝓛-DCPO⊥ {𝓤₀} {𝟙{𝓤₀}} (props-are-sets 𝟙-is-prop)
𝓓⊥ (succ n) = 𝓓⊥ n ⟹ᵈᶜᵖᵒ⊥ 𝓓⊥ n

𝓓 : ℕ → DCPO {𝓤₁} {𝓤₁}
𝓓 n = 𝓓⊥ n ⁻

𝓓-diagram-succ : (n : ℕ) → DCPO[ 𝓓 n , 𝓓 (succ n) ]
                         × DCPO[ 𝓓 (succ n) , 𝓓 n ]
𝓓-diagram-succ zero = (e₀ , e₀-continuity) , p₀ , p₀-continuity
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
𝓓-diagram-succ (succ n) = (e , e-continuity) , (p , p-continuity)
 where
  IH : DCPO[ 𝓓 n , 𝓓 (succ n) ] × DCPO[ 𝓓 (succ n) , 𝓓 n ]
  IH = 𝓓-diagram-succ n
  eₙ : DCPO[ 𝓓 n , 𝓓 (succ n) ]
  eₙ = pr₁ IH
  pₙ : DCPO[ 𝓓 (succ n) , 𝓓 n ]
  pₙ = pr₂ IH
  e : ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 (succ (succ n)) ⟩
  e f = DCPO-∘ (𝓓 (succ n)) (𝓓 n) (𝓓 (succ n)) pₙ h
   where
    h : DCPO[ 𝓓 n , 𝓓 (succ n) ]
    h = DCPO-∘ (𝓓 n) (𝓓 n) (𝓓 (succ n)) f eₙ
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
  p f = DCPO-∘ (𝓓 n) (𝓓 (succ n)) (𝓓 n) eₙ h
   where
    h : DCPO[ 𝓓 (succ n) , 𝓓 n ]
    h = DCPO-∘ (𝓓 (succ n)) (𝓓 (succ n)) (𝓓 n) f pₙ
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

π'⁺ : (n : ℕ) → DCPO[ 𝓓 (succ n) , 𝓓 n ]
π'⁺ n = pr₂ (𝓓-diagram-succ n)

π' : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 n ⟩
π' n = underlying-function (𝓓 (succ n)) (𝓓 n) (π'⁺ n)

π'-is-continuous : (n : ℕ) → is-continuous (𝓓 (succ n)) (𝓓 n) (π' n)
π'-is-continuous n = pr₂ (pr₂ (𝓓-diagram-succ n))

ε'⁺ : (n : ℕ) → DCPO[ 𝓓 n , 𝓓 (succ n) ]
ε'⁺ n = pr₁ (𝓓-diagram-succ n)

ε' : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (succ n) ⟩
ε' n = underlying-function (𝓓 n) (𝓓 (succ n)) (ε'⁺ n)

ε'-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (𝓓 (succ n)) (ε' n)
ε'-is-continuous n = pr₂ (pr₁ (𝓓-diagram-succ n))

π-helper : {n m : ℕ} (k : ℕ) → n +' k ≡ m → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
π-helper zero refl = id
π-helper {n} {m} (succ k) refl = IH ∘ π' (n +' k)
 where
  IH : ⟨ 𝓓 (n +' k) ⟩ → ⟨ 𝓓 n ⟩
  IH = π-helper {n} {n +' k} k refl

π : {n m : ℕ} → (n ≤ m) → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
π {n} {m} l = γ (subtraction n m l)
 where
  γ : (Σ k ꞉ ℕ , k +' n ≡ m) → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
  γ (k , p) = π-helper {n} {m} k q
   where
    q : n +' k ≡ m
    q = addition-commutativity n k ∙ p

π-helper-is-continuous : {n m : ℕ} (k : ℕ) (p : n +' k ≡ m)
                       → is-continuous (𝓓 m) (𝓓 n) (π-helper k p)
π-helper-is-continuous {n} {m} zero refl = id-is-continuous (𝓓 n)
π-helper-is-continuous {n} {m} (succ k) refl = γ
 where
  f : ⟨ 𝓓 (n +' k) ⟩ → ⟨ 𝓓 n ⟩
  f = π-helper k refl
  γ : is-continuous (𝓓 m) (𝓓 n) (f ∘ π' (n +' k))
  γ = ∘-is-continuous (𝓓 m) (𝓓 (n +' k)) (𝓓 n)
       (π' (n +' k)) f (π'-is-continuous (n +' k)) IH
   where
    IH : is-continuous (𝓓 (n +' k)) (𝓓 n) f
    IH = π-helper-is-continuous {n} {n +' k} k refl

π-is-continuous : {n m : ℕ} (l : n ≤ m) → is-continuous (𝓓 m) (𝓓 n) (π {n} {m} l)
π-is-continuous {n} {m} l = π-helper-is-continuous k q
 where
  k : ℕ
  k = pr₁ (subtraction n m l)
  q : n +' k ≡ m
  q = addition-commutativity n k ∙ pr₂ (subtraction n m l)

ε-helper : {n m : ℕ} (k : ℕ) → n +' k ≡ m → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
ε-helper zero refl = id
ε-helper {n} {m} (succ k) refl = ε' (n +' k) ∘ IH
 where
  IH : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (n +' k) ⟩
  IH = ε-helper {n} {n +' k} k refl

ε-helper-is-continuous : {n m : ℕ} (k : ℕ) (p : n +' k ≡ m)
                       → is-continuous (𝓓 n) (𝓓 m) (ε-helper k p)
ε-helper-is-continuous {n} {m} zero refl = id-is-continuous (𝓓 n)
ε-helper-is-continuous {n} {m} (succ k) refl = γ
 where
  f : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (n +' k) ⟩
  f =  ε-helper k refl
  γ : is-continuous (𝓓 n) (𝓓 (n +' succ k)) (ε' (n +' k) ∘ f)
  γ = ∘-is-continuous (𝓓 n) (𝓓 (n +' k)) (𝓓 m)
       f (ε' (n +' k)) IH (ε'-is-continuous (n +' k))
   where
    IH : is-continuous (𝓓 n) (𝓓 (n +' k)) f
    IH = ε-helper-is-continuous {n} {n +' k} k refl

ε : {n m : ℕ} → (n ≤ m) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
ε {n} {m} l = γ (subtraction n m l)
 where
  γ : Σ k ꞉ ℕ , k +' n ≡ m → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
  γ (k , p) = ε-helper {n} {m} k q
   where
    q : n +' k ≡ m
    q = addition-commutativity n k ∙ p

ε-is-continuous : {n m : ℕ} (l : n ≤ m) → is-continuous (𝓓 n) (𝓓 m) (ε {n} {m} l)
ε-is-continuous {n} {m} l = ε-helper-is-continuous k q
 where
  k : ℕ
  k = pr₁ (subtraction n m l)
  q : n +' k ≡ m
  q = addition-commutativity n k ∙ pr₂ (subtraction n m l)

ε'-section-of-π' : (n : ℕ) → π' n ∘ ε' n ∼ id
ε'-section-of-π' zero x = refl
ε'-section-of-π' (succ n) (f , c) =
 to-subtype-≡ (λ g → being-continuous-is-a-prop (𝓓 n) (𝓓 n) g) γ
  where
   γ : (λ x → π' n ({!!} (ε' n x))) ≡ f
   -- (λ x → π' n (pr₁ (ε' (succ n) (f , c)) (ε' n x))) ≡ f
   γ = {!!}
{-
 π' (succ n) (ε' (succ n) f) ≡⟨ refl ⟩
 {!!} ≡⟨ {!!} ⟩
 {!!} ≡⟨ {!!} ⟩
 {!!} ≡⟨ {!!} ⟩
 f ∎
  where
   IH : π' n ∘ ε' n ∼ id
   IH = ε'-section-of-π' n
-}

open Diagram
      {𝓤₀} {ℕ} _≤_
      (λ {n} → ≤-refl n)
      (λ {n} {m} {k} → ≤-trans n m k)
      ≤-is-prop-valued
      ∣ 0 ∣
      (λ n m → ∣ n +' m , (≤-+ n m) , (≤-+' n m)  ∣)
      𝓓
      (λ {n} {m} → ε {n} {m})
      (λ {n} {m} → π {n} {m})
      {!!}
      {!!}
      (λ {n} {m} → ε-is-continuous {n} {m})
      (λ {n} {m} → π-is-continuous {n} {m})
      {!!}
      {!!}
      {!!}
      {!!}

{-
module Diagram
        {I : 𝓥 ̇ }
        (_⊑_ : I → I → 𝓦 ̇ )
        (⊑-refl : {i : I} → i ⊑ i)
        (⊑-trans : {i j k : I} → i ⊑ j → j ⊑ k → i ⊑ k)
        (⊑-prop-valued : (i j : I) → is-prop (i ⊑ j))
        (I-inhabited : ∥ I ∥)
        (I-weakly-directed : (i j : I) → ∃ k ꞉ I , i ⊑ k × j ⊑ k)
        (𝓓 : I → DCPO {𝓤} {𝓣})
        (ε : {i j : I} → i ⊑ j → ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩)
        (π : {i j : I} → i ⊑ j → ⟨ 𝓓 j ⟩ → ⟨ 𝓓 i ⟩)
        (επ-deflation : {i j : I} (l : i ⊑ j) → (x : ⟨ 𝓓 j ⟩)
                      → ε l (π l x) ⊑⟨ 𝓓 j ⟩ x )
        (ε-section-of-π : {i j : I} (l : i ⊑ j) → π l ∘ ε l ∼ id )
        (ε-is-continuous : {i j : I} (l : i ⊑ j)
                         → is-continuous (𝓓 i) (𝓓 j) (ε {i} {j} l))
        (π-is-continuous : {i j : I} (l : i ⊑ j)
                         → is-continuous (𝓓 j) (𝓓 i) (π {i} {j} l))
        (ε-id : (i : I ) → ε (⊑-refl {i}) ∼ id)
        (π-id : (i : I ) → π (⊑-refl {i}) ∼ id)
        (ε-comp : {i j k : I} (l : i ⊑ j) (m : j ⊑ k)
                → ε m ∘ ε l ∼ ε (⊑-trans l m))
        (π-comp : {i j k : I} (l : i ⊑ j) (m : j ⊑ k)
                → π l ∘ π m ∼ π (⊑-trans l m))
       where
-}

\end{code}
