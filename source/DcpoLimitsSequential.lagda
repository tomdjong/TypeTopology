Tom de Jong, 12 & 13 May 2020.

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
open import NaturalNumbers-Properties
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

\end{code}

We start by introducing some helper functions that will enable us to define
functions by induction on the difference m - n for two natural numbers n and m
with n ≤ m.

We use left-addition and subtraction' below instead of right-addition and
subtraction, because addition is defined by induction on its second argument. So
we get more definitional equalities using this approach.

\begin{code}

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

\end{code}

Define repeated compositions of εs.

\begin{code}

 ε⁺-helper : (n m k : ℕ) → n +' k ≡ m → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
 ε⁺-helper n n zero refl = id
 ε⁺-helper n m (succ k) refl = ε (n +' k) ∘ IH
  where
   IH : ⟨ 𝓓 n ⟩ → ⟨ 𝓓 (n +' k) ⟩
   IH = ε⁺-helper n (n +' k) k refl

 ε⁺-helper-on-succ : (n m k : ℕ) (p : n +' succ k ≡ succ m)
                   → ε⁺-helper n (succ m) (succ k) p
                   ∼ ε m ∘ ε⁺-helper n m k (succ-lc p)
 ε⁺-helper-on-succ n m k refl x = refl

 ε⁺-helper-Σ : (n m : ℕ) → (Σ k ꞉ ℕ , n +' k ≡ m) → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
 ε⁺-helper-Σ n m (k , p) = ε⁺-helper n m k p

 ε⁺ : {n m : ℕ} → n ≤ m → ⟨ 𝓓 n ⟩ → ⟨ 𝓓 m ⟩
 ε⁺ {n} {m} l = ε⁺-helper-Σ n m (subtraction' n m l)

\end{code}

Similarly for π.

\begin{code}

 π⁺-helper : (n m k : ℕ) → n +' k ≡ m → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
 π⁺-helper n n zero refl = id
 π⁺-helper n m (succ k) refl = IH ∘ π (n +' k)
  where
   IH : ⟨ 𝓓 (n +' k) ⟩ → ⟨ 𝓓 n ⟩
   IH = π⁺-helper n (n +' k) k refl

 π⁺-helper-on-succ : (n m k : ℕ) (p : n +' succ k ≡ succ m)
                   → π⁺-helper n (succ m) (succ k) p
                   ∼ π⁺-helper n m k (succ-lc p) ∘ π m
 π⁺-helper-on-succ n m k refl x = refl

 π⁺-helper-Σ : (n m : ℕ) → (Σ k ꞉ ℕ , n +' k ≡ m) → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
 π⁺-helper-Σ n m (k , p) = π⁺-helper n m k p

 π⁺ : {n m : ℕ} → (n ≤ m) → ⟨ 𝓓 m ⟩ → ⟨ 𝓓 n ⟩
 π⁺ {n} {m} l = π⁺-helper-Σ n m (subtraction' n m l)

\end{code}

Since ε n ∘ π n is a deflation, so is ε⁺ l ∘ π⁺ l for l : n ≤ m.

\begin{code}

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

\end{code}

Since ε n is a section of π n, so is ε⁺ l of π⁺ l for l : n ≤ m.

\begin{code}

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

\end{code}

Since ε and π are continuous, so are ε⁺ and π⁺.

\begin{code}

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

\end{code}

(ε⁺ ≤-refl n) and (π⁺ ≤-refl n) are both the identity on 𝓓 n.

\begin{code}

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

\end{code}

The most laborious part: composing two ε⁺s is ε⁺ on ≤-trans. And similarly for π⁺.

\begin{code}

 ε⁺-comp-helper : {n m k : ℕ} (a b : ℕ) (p : n +' a ≡ m) (q : m +' b ≡ k)
                → ε⁺-helper m k b q ∘ ε⁺-helper n m a p
                ∼ ε⁺-helper n k (a +' b)
                   ((addition-associativity n a b) ⁻¹ ∙ ap (λ - → - +' b) p ∙ q)
 ε⁺-comp-helper {n} {m} {k} a zero refl refl x = refl
 ε⁺-comp-helper {n} {m} {k} a (succ b) refl refl x =
  ε _ (ε⁺-helper (n +' a) _ b refl (ε⁺-helper n _ a refl x)) ≡⟨ i    ⟩
  ε _ (ε⁺-helper n (n +' a +' b) (a +' b) p x)               ≡⟨ refl ⟩
  ε _ (ε⁺-helper-Σ n (n +' a +' b) (a +' b , p) x)           ≡⟨ ii   ⟩
  ε _ (ε⁺-helper-Σ n (n +' a +' b) (a +' b , succ-lc p') x)  ≡⟨ refl ⟩
  ε _ (ε⁺-helper n (n +' a +' b) (a +' b) (succ-lc p') x)    ≡⟨ iii  ⟩
  ε⁺-helper n (n +' a +' succ b) (succ (a +' b)) p' x        ≡⟨ refl ⟩
  ε⁺-helper n (n +' a +' succ b) (a +' succ b) p' x          ∎
   where
    p : n +' (a +' b) ≡ n +' a +' b
    p = addition-associativity n a b ⁻¹
    p' : n +' (a +' succ b) ≡ n +' a +' succ b
    p' = addition-associativity n a (succ b) ⁻¹
    i = ap (ε (n +' a +' b)) (IH x)
     where
      IH : ε⁺-helper (n +' a) (n +' a +' b) b refl ∘ ε⁺-helper n (n +' a) a refl
         ∼ ε⁺-helper n (n +' a +' b) (a +' b) (addition-associativity n a b ⁻¹)
      IH = ε⁺-comp-helper {n} {n +' a} {n +' a +' b} a b refl refl
    ii = ap (λ - → ε (n +' a +' b) (ε⁺-helper-Σ n (n +' a +' b) - x)) h
     where
      h : a +' b , p ≡ a +' b , succ-lc p'
      h = left-addition-is-embedding n (n +' a +' b)
           (a +' b , p) (a +' b , succ-lc p')
    iii = (ε⁺-helper-on-succ n (n +' a +' b) (a +' b) p' x) ⁻¹

 ε⁺-comp : {n m k : ℕ} (l₁ : n ≤ m) (l₂ : m ≤ k)
         → ε⁺ {m} {k} l₂ ∘ ε⁺ {n} {m} l₁ ∼ ε⁺ (≤-trans n m k l₁ l₂)
 ε⁺-comp {n} {m} {k} l₁ l₂ x =
  ε⁺ {m} {k} l₂ (ε⁺ {n} {m} l₁ x)         ≡⟨ refl ⟩
  ε⁺-helper m k b q (ε⁺-helper n m a p x) ≡⟨ i    ⟩
  ε⁺-helper n k (a +' b) r x              ≡⟨ refl ⟩
  ε⁺-helper-Σ n k (a +' b , r) x        ≡⟨ ii   ⟩
  ε⁺-helper-Σ n k s x                     ≡⟨ refl ⟩
  ε⁺ (≤-trans n m k l₁ l₂) x              ∎
   where
    a : ℕ
    a = pr₁ (subtraction' n m l₁)
    p : n +' a ≡ m
    p = pr₂ (subtraction' n m l₁)
    b : ℕ
    b = pr₁ (subtraction' m k l₂)
    q : m +' b ≡ k
    q = pr₂ (subtraction' m k l₂)
    r : n +' (a +' b) ≡ k
    r = (addition-associativity n a b) ⁻¹ ∙ ap (λ - → - +' b) p ∙ q
    s : Σ c ꞉ ℕ , n +' c ≡ k
    s = subtraction' n k (≤-trans n m k l₁ l₂)
    i  = ε⁺-comp-helper a b p q x
    ii = ap (λ - → ε⁺-helper-Σ n k - x) h
     where
      h : a +' b , r ≡ s
      h = left-addition-is-embedding n k (a +' b , r) s

 π⁺-comp-helper : {n m k : ℕ} (a b : ℕ) (p : n +' a ≡ m) (q : m +' b ≡ k)
                → π⁺-helper n m a p ∘ π⁺-helper m k b q
                ∼ π⁺-helper n k (a +' b)
                   ((addition-associativity n a b) ⁻¹ ∙ ap (λ - → - +' b) p ∙ q)
 π⁺-comp-helper {n} {m} {k} a zero refl refl x = refl
 π⁺-comp-helper {n} {m} {k} a (succ b) refl refl x =
  π⁺-helper n _ a refl (π⁺-helper (n +' a) _ b refl (π _ x)) ≡⟨ IH   ⟩
  π⁺-helper n (n +' a +' b) (a +' b) p (π _ x)               ≡⟨ refl ⟩
  π⁺-helper-Σ n (n +' a +' b) (a +' b , p) (π _ x)           ≡⟨ i    ⟩
  π⁺-helper-Σ n (n +' a +' b) (a +' b , succ-lc p') (π _ x)  ≡⟨ refl ⟩
  π⁺-helper n (n +' a +' b) (a +' b) (succ-lc p') (π _ x)    ≡⟨ ii ⟩
  π⁺-helper n (n +' a +' succ b) (a +' succ b) p' x          ∎
   where
    p : n +' (a +' b) ≡ n +' a +' b
    p = addition-associativity n a b ⁻¹
    p' : n +' (a +' succ b) ≡ n +' a +' succ b
    p' = addition-associativity n a (succ b) ⁻¹
    IH = π⁺-comp-helper a b refl refl (π (n +' a +' b) x)
    i  = ap (λ - → π⁺-helper-Σ n (n +' a +' b) - (π _ x)) h
     where
      h : a +' b , p ≡ a +' b , succ-lc p'
      h = left-addition-is-embedding n (n +' a +' b)
           (a +' b , p) (a +' b , succ-lc p')
    ii = π⁺-helper-on-succ n (n +' a +' b) (a +' b) p' x ⁻¹

 π⁺-comp : {n m k : ℕ} (l₁ : n ≤ m) (l₂ : m ≤ k)
         → π⁺ {n} {m} l₁ ∘ π⁺ {m} {k} l₂  ∼ π⁺ (≤-trans n m k l₁ l₂)
 π⁺-comp {n} {m} {k} l₁ l₂ x =
  π⁺ {n} {m} l₁ (π⁺ {m} {k} l₂ x)         ≡⟨ refl ⟩
  π⁺-helper n m a p (π⁺-helper m k b q x) ≡⟨ i    ⟩
  π⁺-helper n k (a +' b) r x              ≡⟨ refl ⟩
  π⁺-helper-Σ n k (a +' b , r) x          ≡⟨ ii   ⟩
  π⁺-helper-Σ n k s x                     ≡⟨ refl ⟩
  π⁺ (≤-trans n m k l₁ l₂) x              ∎
   where
    a : ℕ
    a = pr₁ (subtraction' n m l₁)
    p : n +' a ≡ m
    p = pr₂ (subtraction' n m l₁)
    b : ℕ
    b = pr₁ (subtraction' m k l₂)
    q : m +' b ≡ k
    q = pr₂ (subtraction' m k l₂)
    r : n +' (a +' b) ≡ k
    r = (addition-associativity n a b) ⁻¹ ∙ ap (λ - → - +' b) p ∙ q
    s : Σ c ꞉ ℕ , n +' c ≡ k
    s = subtraction' n k (≤-trans n m k l₁ l₂)
    i  = π⁺-comp-helper a b p q x
    ii = ap (λ - → π⁺-helper-Σ n k - x) h
     where
      h : a +' b , r ≡ s
      h = left-addition-is-embedding n k (a +' b , r) s

\end{code}

Finally, we can open the directed preorder module with the above parameters.

\begin{code}

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
       ε⁺-comp
       π⁺-comp

\end{code}