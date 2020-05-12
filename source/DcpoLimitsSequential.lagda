Tom de Jong, 12 May 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoLimitsSequential
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓤 𝓣 : Universe)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓤₀
open import DcpoBasics pt fe 𝓤₀
open import DcpoLimits pt fe 𝓤₀ 𝓤 𝓣

open import NaturalsAddition renaming (_+_ to _+'_)
open import NaturalsOrder

open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Miscelanea

module SequentialDiagram
        (𝓓 : ℕ → DCPO {𝓤} {𝓣})
        (ε : (n : ℕ) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (succ n) ⟩)
        (π : (n : ℕ) → ⟨ 𝓓 (succ n) ⟩ → ⟨ 𝓓 n ⟩)
        (επ-deflation : (n : ℕ) (x : ⟨ 𝓓 (succ n) ⟩) → ε n (π n x) ⊑⟨ 𝓓 (succ n) ⟩ x )
        (ε-section-of-π : (n : ℕ) → π n ∘ ε n ∼ id )
        (ε-is-continuous : (n : ℕ) → is-continuous (𝓓 n) (𝓓 (succ n)) (ε n))
        (π-is-continuous : (n : ℕ) → is-continuous (𝓓 (succ n)) (𝓓 n) (π n))
       where

 -- First, some helpers. Maybe move these to NaturalsOrder.lagda?
 left-addition-is-embedding : (n m : ℕ) → is-prop (Σ k ꞉ ℕ , n +' k ≡ m)
 left-addition-is-embedding n m =
  equiv-to-prop γ (right-addition-is-embedding n m)
   where
    γ : (Σ k ꞉ ℕ , n +' k ≡ m) ≃ (Σ k ꞉ ℕ , k +' n ≡ m)
    γ = Σ-cong ϕ
     where
      ϕ : (k : ℕ) → (n +' k ≡ m) ≃ (k +' n ≡ m)
      ϕ k = logically-equivalent-props-are-equivalent ℕ-is-set ℕ-is-set
             (λ p → addition-commutativity k n ∙ p)
             (λ q → addition-commutativity n k ∙ q)

 subtraction' : (n m : ℕ) → n ≤ m → Σ k ꞉ ℕ , n +' k ≡ m
 subtraction' n m l = k , q
  where
   k : ℕ
   k = pr₁ (subtraction n m l)
   q : n +' k ≡ m
   q = addition-commutativity n k ∙ pr₂ (subtraction n m l)

 ε⁺-helper : (n m k : ℕ) → n +' k ≡ m → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
 ε⁺-helper n n zero refl = id
 ε⁺-helper n m (succ k) refl = ε (n +' k) ∘ IH
  where
   IH : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (n +' k) ⟩
   IH = ε⁺-helper n (n +' k) k refl

 ε⁺-helper-Σ : (n m : ℕ) → (Σ k ꞉ ℕ , n +' k ≡ m) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
 ε⁺-helper-Σ n m (k , p) = ε⁺-helper n m k p

 ε⁺ : {n m : ℕ} → n ≤ m → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
 ε⁺ {n} {m} l = ε⁺-helper-Σ n m (subtraction' n m l)

 π⁺-helper : (n m k : ℕ) → n +' k ≡ m → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
 π⁺-helper n n zero refl = id
 π⁺-helper n m (succ k) refl = IH ∘ π (n +' k)
  where
   IH : ⟨ 𝓓 (n +' k) ⟩ → ⟨ 𝓓 n ⟩
   IH = π⁺-helper n (n +' k) k refl

 π⁺-helper-Σ : (n m : ℕ) → (Σ k ꞉ ℕ , n +' k ≡ m) → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
 π⁺-helper-Σ n m (k , p) = π⁺-helper n m k p

 π⁺ : {n m : ℕ} → (n ≤ m) → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
 π⁺ {n} {m} l = π⁺-helper-Σ n m (subtraction' n m l)

 ε⁺π⁺-deflation-helper : (n m k : ℕ) (p : n +' k ≡ m) (x : ⟨ 𝓓 m ⟩)
                       → ε⁺-helper n m k p (π⁺-helper n m k p x) ⊑⟨ 𝓓 m ⟩ x
 ε⁺π⁺-deflation-helper n n zero refl x = reflexivity (𝓓 n) x
 ε⁺π⁺-deflation-helper n m (succ k) refl x =
  ε⁺-helper n m (succ k) refl (π⁺-helper n m (succ k) refl x) ⊑⟨ 𝓓 m ⟩[ u₁ ]
  ε (n +' k) (ε' (π' (π (n +' k) x)))                         ⊑⟨ 𝓓 m ⟩[ u₂ ]
  ε (n +' k) (π (n +' k) x)                                   ⊑⟨ 𝓓 m ⟩[ u₃ ]
  x                                                           ∎⟨ 𝓓 m ⟩
   where
    ε' : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (n +' k) ⟩
    ε' = ε⁺-helper n (n +' k) k refl
    π' : ⟨ 𝓓 (n +' k) ⟩ → ⟨ 𝓓 n ⟩
    π' = π⁺-helper n (n +' k) k refl
    u₁ = reflexivity (𝓓 m) (ε⁺-helper n (n +' succ k) (succ k) refl
                             (π⁺-helper n (n +' succ k) (succ k) refl x))
    u₂ = mon (ε' (π' (π (n +' k) x))) (π (n +' k) x) IH
     where
      mon : is-monotone (𝓓 (n +' k)) (𝓓 (succ (n +' k))) (ε (n +' k))
      mon = continuous-implies-monotone (𝓓 (n +' k)) (𝓓 (succ (n +' k)))
             (ε (n +' k) , ε-is-continuous (n +' k))
      IH : ε' (π' (π (n +' k) x)) ⊑⟨ 𝓓 (n +' k) ⟩ π (n +' k) x
      IH = ε⁺π⁺-deflation-helper n (n +' k) k refl (π (n +' k) x)
    u₃ = επ-deflation (n +' k) x

 ε⁺π⁺-deflation : {n m : ℕ} (l : n ≤ m) (x : ⟨ 𝓓 m ⟩)
                → ε⁺ {n} {m} l (π⁺ {n} {m} l x) ⊑⟨ 𝓓 m ⟩ x
 ε⁺π⁺-deflation {n} {m} l = ε⁺π⁺-deflation-helper n m k q
  where
   k : ℕ
   k = pr₁ (subtraction n m l)
   q : n +' k ≡ m
   q = addition-commutativity n k ∙ pr₂ (subtraction n m l)

 ε⁺-section-of-π⁺-helper : (n m k : ℕ) (p : n +' k ≡ m)
                         → π⁺-helper n m k p ∘ ε⁺-helper n m k p ∼ id
 ε⁺-section-of-π⁺-helper n n zero refl x = refl
 ε⁺-section-of-π⁺-helper n m (succ k) refl x =
  π⁺-helper n m (succ k) refl (ε⁺-helper n m (succ k) refl x) ≡⟨ refl ⟩
  π' (π (n +' k) (ε (n +' k) (ε' x)))                         ≡⟨ q ⟩
  π' (id (ε' x))                                              ≡⟨ IH ⟩
  x                                                           ∎
   where
    ε' : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (n +' k) ⟩
    ε' = ε⁺-helper n (n +' k) k refl
    π' : ⟨ 𝓓 (n +' k) ⟩ → ⟨ 𝓓 n ⟩
    π' = π⁺-helper n (n +' k) k refl
    q = ap π' (ε-section-of-π (n +' k) (ε' x))
    IH = ε⁺-section-of-π⁺-helper n (n +' k) k refl x

 ε⁺-section-of-π⁺ : {n m : ℕ} (l : n ≤ m)
                  → π⁺ l ∘ ε⁺ {n} {m} l ∼ id
 ε⁺-section-of-π⁺ {n} {m} l = ε⁺-section-of-π⁺-helper n m k q
  where
   k : ℕ
   k = pr₁ (subtraction n m l)
   q : n +' k ≡ m
   q = addition-commutativity n k ∙ pr₂ (subtraction n m l)

 ε⁺-is-continuous-helper : (n m k : ℕ) (p : n +' k ≡ m)
                         → is-continuous (𝓓 n) (𝓓 m) (ε⁺-helper n m k p)
 ε⁺-is-continuous-helper n n zero refl = id-is-continuous (𝓓 n)
 ε⁺-is-continuous-helper n m (succ k) refl =
  ∘-is-continuous (𝓓 n) (𝓓 (n +' k)) (𝓓 m)
   (ε⁺-helper n (n +' k) k refl) (ε (n +' k)) IH (ε-is-continuous (n +' k))
    where
     IH : is-continuous (𝓓 n) (𝓓 (n +' k)) (ε⁺-helper n (n +' k) k refl)
     IH = ε⁺-is-continuous-helper n (n +' k) k refl

 ε⁺-is-continuous : {n m : ℕ} (l : n ≤ m)
                  → is-continuous (𝓓 n) (𝓓 m) (ε⁺ {n} {m} l)
 ε⁺-is-continuous {n} {m} l = ε⁺-is-continuous-helper n m k q
  where
   k : ℕ
   k = pr₁ (subtraction n m l)
   q : n +' k ≡ m
   q = addition-commutativity n k ∙ pr₂ (subtraction n m l)

 π⁺-is-continuous-helper : (n m k : ℕ) (p : n +' k ≡ m)
                         → is-continuous (𝓓 m)  (𝓓 n) (π⁺-helper n m k p)
 π⁺-is-continuous-helper n n zero refl = id-is-continuous (𝓓 n)
 π⁺-is-continuous-helper n m (succ k) refl =
  ∘-is-continuous (𝓓 m) (𝓓 (n +' k)) (𝓓 n)
   (π (n +' k)) (π⁺-helper n (n +' k) k refl) (π-is-continuous (n +' k)) IH
    where
     IH : is-continuous (𝓓 (n +' k)) (𝓓 n) (π⁺-helper n (n +' k) k refl)
     IH = π⁺-is-continuous-helper n (n +' k) k refl

 π⁺-is-continuous : {n m : ℕ} (l : n ≤ m)
                  → is-continuous (𝓓 m) (𝓓 n) (π⁺ {n} {m} l)
 π⁺-is-continuous {n} {m} l = π⁺-is-continuous-helper n m k q
  where
   k : ℕ
   k = pr₁ (subtraction n m l)
   q : n +' k ≡ m
   q = addition-commutativity n k ∙ pr₂ (subtraction n m l)

 ε⁺-id : (n : ℕ) → ε⁺ {n} {n} (≤-refl n) ∼ id
 ε⁺-id n x = ε⁺ {n} {n} (≤-refl n) x      ≡⟨ refl ⟩
             ε⁺-helper-Σ n n s x          ≡⟨ q    ⟩
             ε⁺-helper-Σ n n (0 , refl) x ≡⟨ refl ⟩
             x                            ∎
  where
   s : Σ k ꞉ ℕ , n +' k ≡ n
   s = subtraction' n n (≤-refl n)
   q = ap (λ - → ε⁺-helper-Σ n n - x)
        (left-addition-is-embedding n n s (0 , refl))

 π⁺-id : (n : ℕ) → π⁺ {n} {n} (≤-refl n) ∼ id
 π⁺-id n x = π⁺ {n} {n} (≤-refl n) x      ≡⟨ refl ⟩
             π⁺-helper-Σ n n s x          ≡⟨ q    ⟩
             π⁺-helper-Σ n n (0 , refl) x ≡⟨ refl ⟩
             x                            ∎
  where
   s : Σ k ꞉ ℕ , n +' k ≡ n
   s = subtraction' n n (≤-refl n)
   q = ap (λ - → π⁺-helper-Σ n n - x)
        (left-addition-is-embedding n n s (0 , refl))

 ε⁺-comp-helper : {n m k : ℕ} (a b : ℕ) (p : n +' a ≡ m) (q : m +' b ≡ k)
                → ε⁺-helper m k b q ∘ ε⁺-helper n m a p
                ∼ ε⁺-helper n k (a +' b)
                   ((addition-associativity n a b) ⁻¹ ∙ ap (λ - → - +' b) p ∙ q)
 ε⁺-comp-helper zero zero refl refl x = refl
 ε⁺-comp-helper (succ a) zero refl refl x = refl
 ε⁺-comp-helper zero (succ b) refl refl x = {!!}
 ε⁺-comp-helper (succ a) (succ b) refl refl x = {!!}

{- ε⁺-comp-helper : {n m k : ℕ} (l : n ≤ m) (a : ℕ) (p : m +' a ≡ k)
                → ε⁺-helper m k a p ∘ ε⁺ {n} {m} l
                ∼ ε⁺ (≤-trans n m k l
                       (cosubtraction m k (a , (addition-commutativity a m ∙ p))))
 ε⁺-comp-helper l a refl x = {!!} -}

 ε⁺-comp : {n m k : ℕ} (l₁ : n ≤ m) (l₂ : m ≤ k)
         → ε⁺ {m} {k} l₂ ∘ ε⁺ {n} {m} l₁ ∼ ε⁺ (≤-trans n m k l₁ l₂)
 ε⁺-comp {n} {zero} {k} l₁ l₂ = {!!}
 ε⁺-comp {n} {succ m} {k} l₁ l₂ = {!!}

 open Diagram
       {𝓤₀} {ℕ}
       _≤_
       (λ {n} → ≤-refl n)
       (λ {n} {m} {k} → ≤-trans n m k)
       ≤-is-prop-valued
       ∣ 0 ∣
       (λ n m → ∣ n +' m , ≤-+ n m , ≤-+' n m ∣)
       𝓓
       ε⁺
       π⁺
       (λ {n} {m} → ε⁺π⁺-deflation {n} {m})
       (λ {n} {m} → ε⁺-section-of-π⁺ {n} {m})
       ε⁺-is-continuous
       π⁺-is-continuous
       ε⁺-id
       π⁺-id
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
