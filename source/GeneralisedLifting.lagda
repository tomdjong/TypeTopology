\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module GeneralisedLifting
        (𝓥 : Universe) -- universe for index types for directed families
--        (𝓣 : Universe) -- universe of propositions
        (pt : propositional-truncations-exist)
        (pe : propext 𝓥)
        (fe : ∀ {𝓦} {𝓦'} → funext 𝓦 𝓦')
       where

open PropositionalTruncation pt
-- open import UF-Miscelanea
open import UF-Subsingletons hiding (⊥)
open import UF-Subsingletons-FunExt

-- open import UF-ImageAndSurjection
-- open ImageAndSurjection pt

open import Lifting 𝓥
open import LiftingMiscelanea 𝓥
open import LiftingMiscelanea-PropExt-FunExt 𝓥 pe fe
open import UF-Equiv

-- open import LiftingMonad 𝓣

open import Dcpo pt fe 𝓥

𝓕 : DCPO {𝓤} {𝓦} → DCPO {𝓥 ⁺ ⊔ 𝓤 } {𝓥 ⊔ 𝓦}
𝓕 {𝓤} {𝓦} 𝓓 = 𝓛 D , _⊑_ , 𝕤 , pv , ρ , τ , σ , c
 where
  D : 𝓤 ̇
  D = ⟨ 𝓓 ⟩
  _⊑_ : 𝓛 D → 𝓛 D → 𝓥 ⊔ 𝓦 ̇
  (P , ϕ , _) ⊑ (Q , ψ , _) = (P → Q) × ((p : P) (q : Q) → ϕ p ⊑⟨ 𝓓 ⟩ ψ q )
  𝕤 : is-set (𝓛 D)
  𝕤 = lifting-of-set-is-a-set (sethood 𝓓)
  pv : is-prop-valued _⊑_
  pv l m = ×-is-prop
            (Π-is-prop fe
             (λ _ → being-defined-is-a-prop m))
            (Π-is-prop fe
             (λ p → Π-is-prop fe
             (λ q → prop-valuedness 𝓓 (value l p) (value m q))))
  ρ : is-reflexive _⊑_
  ρ (P , ϕ , i) = id , γ
   where
    γ : (p q : P) → ϕ p ⊑⟨ 𝓓 ⟩ ϕ q
    γ p q = transport (λ - → ϕ p ⊑⟨ 𝓓 ⟩ -)
      (value-is-constant (P , ϕ , i) p q) (reflexivity 𝓓 _)
  τ : is-transitive _⊑_
  τ (P , ϕ , i) (Q , ψ , j) (R , χ , k) (u₁ , u₂) (v₁ , v₂) = v₁ ∘ u₁ , γ
   where
    γ : (p : P) (r : R) → ϕ p ⊑⟨ 𝓓 ⟩ χ r
    γ p r = transitivity 𝓓 (ϕ p) (ψ (u₁ p)) (χ r) α β
     where
      α : ϕ p ⊑⟨ 𝓓 ⟩ ψ (u₁ p)
      α = u₂ p (u₁ p)
      β : ψ (u₁ p) ⊑⟨ 𝓓 ⟩ χ r
      β = v₂ (u₁ p) r
  σ : is-antisymmetric _⊑_
  σ (P , ϕ , i) (Q , ψ , j) (u₁ , u₂) (v₁ , v₂) = ⋍-to-≡ (γ , dfunext fe h)
   where
    γ : P ≃ Q
    γ = logically-equivalent-props-are-equivalent i j u₁ v₁
    h : (p : P) → ϕ p ≡ ψ (⌜ γ ⌝ p)
    h p = antisymmetry 𝓓 (ϕ p) (ψ (⌜ γ ⌝ p)) (u₂ p (⌜ γ ⌝ p)) (v₂ (⌜ γ ⌝ p) p)
  c : (I : 𝓥 ̇) (α : I → 𝓛 ⟨ 𝓓 ⟩) → is-directed _⊑_ α → has-sup _⊑_ α
  c I α δ = ∐α , u , l
   where
    Q : I → 𝓥 ̇
    Q i = is-defined (α i)
    ψ : (i : I) → Q i → D
    ψ i q = value (α i) q
    IQ : 𝓥 ̇
    IQ = Σ \(i : I) → Q i
    β : IQ → D
    β (i , q) = ψ i q
    ε : ∥ IQ ∥ → (j₁ j₂ : IQ) → ∃ \(j₃ : IQ) → β j₁ ⊑⟨ 𝓓 ⟩ β j₃ × β j₂ ⊑⟨ 𝓓 ⟩ β j₃
    ε s (i₁ , q₁) (i₂ , q₂) = ∥∥-functor γ (is-directed-order _⊑_ α δ i₁ i₂)
     where
      γ : (Σ \k → (α i₁ ⊑ α k) × (α i₂ ⊑ α k))
        → Σ \(j₃ : IQ) → β (i₁ , q₁) ⊑⟨ 𝓓 ⟩ (β j₃) × β (i₂ , q₂) ⊑⟨ 𝓓 ⟩ (β j₃)
      γ (k , (u₁ , u₂) , (v₁ , v₂)) = (k , u₁ q₁) , a , b
       where
        a : β (i₁ , q₁) ⊑⟨ 𝓓 ⟩ β (k , u₁ q₁)
        a = u₂ q₁ (u₁ q₁)
        b : β (i₂ , q₂) ⊑⟨ 𝓓 ⟩ β (k , u₁ q₁)
        b = v₂ q₂ (u₁ q₁)
    ϕ : ∥ IQ ∥ → D
    ϕ s = ∐ 𝓓 (s , ε s)
    ∐α : 𝓛 D
    ∐α = (∃ \(i : I) → Q i) , ϕ , ∥∥-is-a-prop
    u : (i : I) → α i ⊑ ∐α
    u i = f , γ
     where
      f : Q i → ∥ IQ ∥
      f q = ∣ i , q ∣
      γ : (q : Q i) (s : ∥ IQ ∥)
        →  ψ i q ⊑⟨ 𝓓 ⟩ ϕ s
      γ q s = ∐-is-upperbound 𝓓 (s , (ε s)) (i , q)
    l : (x : 𝓛 D) → ((i : I) → α i ⊑ x) → ∐α ⊑ x
    l (R , χ , p) u = g , γ
     where
      u₁ : (i : I) → Q i → R
      u₁ i = pr₁ (u i)
      g : ∥ IQ ∥ → R
      g = ∥∥-rec p h
       where
        h : IQ → R
        h (i , q) = u₁ i q
      γ : (s : ∥ IQ ∥) (r : R) → ϕ s ⊑⟨ 𝓓 ⟩ χ r
      γ s r = ∐-is-lowerbound-of-upperbounds 𝓓 (s , (ε s)) (χ r) ζ
       where
        ζ : (j : IQ) → β j ⊑⟨ 𝓓 ⟩ χ r
        ζ (i , q) = pr₂ (u i) q r

\end{code}
