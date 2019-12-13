Tom de Jong, 12 December 2019.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc -- hiding (⊥)

module AlgebraicLattice
        (fe : FunExt)
        (pe : PropExt)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import UF-Subsingletons -- hiding (⊥)
open import UF-Subsingletons-FunExt
-- open import UF-Retracts
open import UF-Miscelanea

open import Two-Properties
-- open import LPO fe
-- open import GenericConvergentSequence hiding (_⊑_)
open import NaturalsOrder


-- open import NaturalsAddition renaming (_+_ to _+'_)
-- open import NaturalNumbers-Properties

-- We study Ω as a lattice

Ω₀ : 𝓤₁ ̇
Ω₀ = Ω 𝓤₀

_⊑_ : Ω₀ → Ω₀ → 𝓤₀ ̇
p ⊑ q = p holds → q holds

∐ : {I : 𝓤₀ ̇ } (q : I → Ω₀) → Ω₀
∐ {I} q = ((∃ \(i : I) → (q i) holds) , ∥∥-is-a-prop)


is-compact : (c : Ω₀) → 𝓤₁ ̇
is-compact c = (I : 𝓤₀ ̇ ) (q : I → Ω₀)
             → ∥ I ∥
             → (c ⊑ ∐ q)
             → ∃ \(i : I) → (c ⊑ q i)

⊤-is-compact : is-compact ⊤
⊤-is-compact I q s l = ∥∥-functor γ u
 where
  u : ∐ q holds
  u = l *
  γ : (Σ \i → (q i) holds) → (Σ \i → ⊤ ⊑ q i)
  γ (i , h) = i , (λ _ → h)

⊥-is-compact : is-compact ⊥
⊥-is-compact I q s l = ∥∥-functor γ s
 where
  γ : I → Σ \i → ⊥ ⊑ q i
  γ i = i , 𝟘-elim

-- Cantor space
ℂ : 𝓤₀ ̇
ℂ = ℕ → 𝟚

⟨_⟩₁ : ℂ → 𝓤₀ ̇
⟨ α ⟩₁ = Σ \(n : ℕ) → α n ≡ ₁

ℕ∞ : 𝓤₀ ̇
ℕ∞ = Σ \(α : ℂ) → is-prop ⟨ α ⟩₁

ι : ℕ∞ → ℂ
ι = pr₁

⟨_⟩ : ℕ∞ → Ω₀
⟨ α ⟩ = ⟨ ι α ⟩₁ , pr₂ α

ℕ∞-at-most-one-₁ : (α : ℕ∞) (n m : ℕ)
                 → ι α n ≡ ₁
                 → ι α m ≡ ₁
                 → n ≡ m
ℕ∞-at-most-one-₁ α n m p q = ap pr₁ γ
 where
  u : Σ \(k : ℕ) → ι α k ≡ ₁
  u = n , p
  v : Σ \(k : ℕ) → ι α k ≡ ₁
  v = m , q
  γ : u ≡ v
  γ = pr₂ ⟨ α ⟩ u v

LPO : 𝓤₀ ̇
LPO = (α : ℕ∞) → decidable ⟨ ι α ⟩₁

⟨_⟩¹ᵤ_ : ℕ∞ → ℕ → 𝓤₀ ̇
⟨ α ⟩¹ᵤ n = (Σ \(m : ℕ) → (m ≤ n) × (ι α m ≡ ₁))

⟨_⟩ᵤ_ : ℕ∞ → ℕ → Ω₀
⟨ α ⟩ᵤ n = (⟨ α ⟩¹ᵤ n , i)
 where
  i : is-prop (⟨ α ⟩¹ᵤ n)
  i (m , p) (k , q) = to-Σ-≡ (a , b)
   where
    a : m ≡ k
    a = ℕ∞-at-most-one-₁ α m k (pr₂ p) (pr₂ q)
    b : transport (λ x → (x ≤ n) × (ι α x ≡ ₁)) a p ≡ q
    b = ×-is-prop (≤-is-prop-valued k n) 𝟚-is-set _ q

⟨_⟩ᵤ_-decidable : (α : ℕ∞) (n : ℕ) → decidable (⟨ α ⟩¹ᵤ n)
⟨ α ⟩ᵤ zero -decidable = 𝟚-equality-cases a b
 where
  a : ι α 0 ≡ ₀ → (⟨ α ⟩¹ᵤ 0) + ¬ (⟨ α ⟩¹ᵤ 0)
  a e = inr γ
   where
    γ : ⟨ α ⟩¹ᵤ 0 → 𝟘
    γ (0 , _ , e') = zero-is-not-one ϕ
     where
      ϕ = ₀     ≡⟨ e ⁻¹ ⟩
          ι α 0 ≡⟨ e' ⟩
          ₁     ∎
  b : ι α 0 ≡ ₁ → (⟨ α ⟩¹ᵤ 0) + ¬ (⟨ α ⟩¹ᵤ 0)
  b e = inl (0 , ≤-refl 0 , e)
⟨ α ⟩ᵤ succ n -decidable = cases u v IH
 where
  IH : decidable (⟨ α ⟩¹ᵤ n)
  IH = ⟨ α ⟩ᵤ n -decidable
  u : ⟨ α ⟩¹ᵤ n → (⟨ α ⟩¹ᵤ succ n) + ¬ (⟨ α ⟩¹ᵤ succ n)
  u (m , l , e) = inl (m , ≤-trans m n (succ n) l (≤-succ n) , e)
  v : ¬ (⟨ α ⟩¹ᵤ n) → (⟨ α ⟩¹ᵤ succ n) + ¬ (⟨ α ⟩¹ᵤ succ n)
  v h = 𝟚-equality-cases a b
   where
    a : ι α (succ n) ≡ ₀ → (⟨ α ⟩¹ᵤ succ n) + ¬ (⟨ α ⟩¹ᵤ succ n)
    a e = inr γ
     where
      γ : ⟨ α ⟩¹ᵤ succ n → 𝟘
      γ (m , l , e') = cases x y (≤-split m n l)
       where
        x : m ≤ n → 𝟘
        x l' = h (m , l' , e')
        y : m ≡ succ n → 𝟘
        y p = zero-is-not-one ϕ
         where
          ϕ = ₀            ≡⟨ e ⁻¹ ⟩
              ι α (succ n) ≡⟨ ap (ι α) (p ⁻¹) ⟩
              ι α m        ≡⟨ e' ⟩
              ₁            ∎
    b : ι α (succ n) ≡ ₁ → (⟨ α ⟩¹ᵤ succ n) + ¬ (⟨ α ⟩¹ᵤ succ n)
    b e = inl (succ n , ≤-refl (succ n) , e)

everything-compact-implies-LPO : ((p : Ω₀) → is-compact p) → LPO
everything-compact-implies-LPO C α = ∥∥-rec i γ h
 where
  q : ℕ → Ω 𝓤₀
  q n = ⟨ α ⟩ᵤ n
  h : ∃ \n → (⟨ α ⟩ holds → (q n) holds)
  h = C ⟨ α ⟩ ℕ q ∣ zero ∣ t
   where
    t : ⟨ α ⟩ holds → (∐ q) holds
    t (n , e) = ∣ (n , n , ≤-refl n , e) ∣
  i : is-prop (decidable ⟨ ι α ⟩₁)
  i = decidability-of-prop-is-prop (fe 𝓤₀ 𝓤₀) (pr₂ ⟨ α ⟩)
  γ : (Σ \n → ⟨ α ⟩ holds → q n holds)
    → (Σ \n → pr₁ α n ≡ ₁) + ¬ (Σ \n → pr₁ α n ≡ ₁)
  γ (n , f) = 𝟚-equality-cases a b
   where
    a : ι α n ≡ ₀ → (Σ \m → ι α m ≡ ₁) + ¬ (Σ \m → ι α m ≡ ₁)
    a e = inr {!!}
    b : ι α n ≡ ₁ → (Σ \m → ι α m ≡ ₁) + ¬ (Σ \m → ι α m ≡ ₁)
    b e = inl (n , e)

\end{code}

This uses GenericConvergentSequence, which is a bit awkward to use in this case.

⟨_⟩ : ℕ∞ → Ω₀
⟨ α ⟩ = ((Σ \(n : ℕ) → α ≡ under n) , γ)
 where
  γ : is-prop (Σ \n → α ≡ under n)
  γ (n , p) (m , q) = to-Σ-≡ (a , b)
   where
    a : n ≡ m
    a = under-lc (p ⁻¹ ∙ q)
    b : transport (λ - → α ≡ under -) a p ≡ q
    b = ℕ∞-is-set (fe 𝓤₀ 𝓤₀) _ _

≡₀-≡-under : (α : ℕ∞) (n : ℕ) → incl α n ≡ ₀ → α ≡ under n
≡₀-≡-under α zero = is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀)
≡₀-≡-under α (succ n) p = Succ-criterion (fe 𝓤₀ 𝓤₀) γ p
 where
  γ : incl α n ≡ ₁
  γ = 𝟚-equality-cases a b
   where
    a : incl α n ≡ ₀ → incl α n ≡ ₁
    a q = {!!}
    b : incl α n ≡ ₁ → incl α n ≡ ₁
    b = id


⟨_⟩'_ : ℕ∞ → ℕ → Ω₀
⟨ α ⟩' n = ((Σ \(m : ℕ) → (m ≤ n × (α ≡ under m))) , γ)
 where
  γ : is-prop (Σ \m → (m ≤ n × (α ≡ under m)))
  γ (m , _ , p) (k , _ , q) =
   to-Σ-≡
    ((under-lc (p ⁻¹ ∙ q)) ,
     (×-is-prop (≤-is-prop-valued k n) (ℕ∞-is-set (fe 𝓤₀ 𝓤₀)) _ _))

⟨⟩'-decidable : (α : ℕ∞) (n : ℕ) → decidable ((⟨ α ⟩' n) holds)
⟨⟩'-decidable α zero = 𝟚-equality-cases' {_} {_} {_} {incl α 0} a b
 where
  a : incl α 0 ≡ ₀ → (⟨ α ⟩' zero) holds
  a z = (0 , (≤-refl 0 , is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀) z))
  b : incl α 0 ≡ ₁ → ¬ ((⟨ α ⟩' zero) holds)
  b o (0 , _ , e) = zero-is-not-one γ
   where
    γ = ₀           ≡⟨ refl ⟩
        incl Zero 0 ≡⟨ ap (λ - → incl - 0) (e ⁻¹) ⟩
        incl α 0    ≡⟨ o ⟩
        ₁           ∎
⟨⟩'-decidable α (succ n) = {!!} -- 𝟚-equality-cases' {_} {_} {_} {incl α (succ n)} a b
 where
  IH : decidable ((⟨ α ⟩' n) holds)
  IH = ⟨⟩'-decidable α n
  u : (⟨ α ⟩' n) holds →
        ((⟨ α ⟩' succ n) holds) + ¬ ((⟨ α ⟩' succ n) holds)
  u (m , l , e) = inl (m , (≤-trans m n (succ n) l (≤-succ n) , e))
  v : ¬ ((⟨ α ⟩' n) holds) →
        ((⟨ α ⟩' succ n) holds) + ¬ ((⟨ α ⟩' succ n) holds)
  v x = 𝟚-equality-cases' {_} {_} {_} {incl α (succ n)} a b
   where
    h : incl α n ≡ ₁
    h = 𝟚-equality-cases c d
     where
      c : incl α n ≡ ₀ → incl α n ≡ ₁
      c z = 𝟘-elim (x (n , ((≤-refl n) , {!!})))
      d : incl α n ≡ ₁ → incl α n ≡ ₁
      d = id
    a : incl α (succ n) ≡ ₀ → (⟨ α ⟩' succ n) holds
    a z = (succ n) , ((≤-refl (succ n)) , (Succ-criterion (fe 𝓤₀ 𝓤₀) {!!} z))
    b : incl α (succ n) ≡ ₁ → ¬ ((⟨ α ⟩' succ n) holds)
    b = {!!}

everything-compact-LPO : ((p : Ω₀) → is-compact p) → LPO
everything-compact-LPO C α = ∥∥-rec i γ h
 where
  q : ℕ → Ω 𝓤₀
  q n = ⟨ α ⟩' n
  h : ∃ \n → (⟨ α ⟩ holds → (q n) holds)
  h = C ⟨ α ⟩ ℕ q ∣ zero ∣ t
   where
    t : ⟨ α ⟩ holds → (∐ q) holds
    t (n , e) = ∣ (n , n , ((≤-refl n) , e)) ∣
  i : is-prop (⟨ α ⟩ holds + ¬ (⟨ α ⟩ holds))
  i = decidability-of-prop-is-prop (fe 𝓤₀ 𝓤₀) (pr₂ ⟨ α ⟩)
  γ : (Σ \n → ⟨ α ⟩ holds → q n holds)
    → (⟨ α ⟩ holds) + ¬ (⟨ α ⟩ holds)
  γ (n , f) = cases a b (⟨⟩'-decidable α n)
   where
    a : q n holds → (⟨ α ⟩ holds) + ¬ (⟨ α ⟩ holds)
    a (m , _ , e) = inl (m , e)
    b : ¬ (q n holds) → (⟨ α ⟩ holds) + ¬ (⟨ α ⟩ holds)
    b g = inr (λ x → g (f x))
