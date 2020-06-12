\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc hiding (⊥)

module DcpoPointed
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoBasics pt fe 𝓥

strongly-directed-complete : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                           → is-weakly-directed (underlying-order (𝓓 ⁻)) α
                           → has-sup (underlying-order (𝓓 ⁻)) α
strongly-directed-complete {𝓤} {𝓣} 𝓓 {I} {α} ε = s , u , v
 where
  _⊑_ : ⟪ 𝓓 ⟫ → ⟪ 𝓓 ⟫ → 𝓣 ̇
  _⊑_ = underlying-order (𝓓 ⁻)
  J : 𝓥 ̇
  J = 𝟙{𝓥} + I
  β : J → ⟪ 𝓓 ⟫
  β (inl *) = ⊥ 𝓓
  β (inr i) = α i
  δ : is-directed _⊑_ β
  δ = (∣ inl * ∣ , κ)
   where
    κ : (a b : J) → ∃ \c → (β a ⊑ β c) × (β b ⊑ β c)
    κ (inl *) b = ∣ b , ⊥-is-least 𝓓 (β b) , reflexivity (𝓓 ⁻) (β b) ∣
    κ (inr i) (inl *) = ∣ (inr i) , reflexivity (𝓓 ⁻) (α i) , ⊥-is-least 𝓓 (α i) ∣
    κ (inr i) (inr j) = ∥∥-functor γ (ε i j)
     where
      γ : (Σ \(k : I) → (α i) ⊑ (α k) × (α j) ⊑ (α k))
        → Σ \(c : J) → (β (inr i) ⊑ β c) × (β (inr j) ⊑ β c)
      γ (k , l) = (inr k , l)
  s : ⟪ 𝓓 ⟫
  s = ∐ (𝓓 ⁻) δ
  u : is-upperbound _⊑_ s α
  u i = ∐-is-upperbound (𝓓 ⁻) δ (inr i)
  v : ((t : ⟪ 𝓓 ⟫) → is-upperbound _⊑_ t α → s ⊑ t)
  v t l = ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) δ t h
   where
    h : (k : J) → (β k) ⊑ t
    h (inl *) = ⊥-is-least 𝓓 t
    h (inr i) = l i

\end{code}

The above is useful for showing that pointed dcpos have subsingleton joins.

\begin{code}

subsingleton-indexed-families-are-weakly-directed : (𝓓 : DCPO⊥ {𝓤} {𝓣})
                                                    {P : 𝓥 ̇ }
                                                  → is-prop P
                                                  → (α : P → ⟪ 𝓓 ⟫)
                                                  → is-weakly-directed
                                                     (underlying-order (𝓓 ⁻)) α
subsingleton-indexed-families-are-weakly-directed 𝓓 i α p q =
 ∣ p , reflexivity (𝓓 ⁻) (α p) , ≡-to-⊑ (𝓓 ⁻) (ap α (i q p)) ∣

⋁ₛ : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {P : 𝓥 ̇ } → is-prop P → (P → ⟪ 𝓓 ⟫) → ⟪ 𝓓 ⟫
⋁ₛ 𝓓 {P} i α = pr₁ (strongly-directed-complete 𝓓 δ)
 where
  δ : is-weakly-directed (underlying-order (𝓓 ⁻)) α
  δ = subsingleton-indexed-families-are-weakly-directed 𝓓 i α

⋁ₛ-is-upperbound : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {P : 𝓥 ̇ }
                   (i : is-prop P) (α : P → ⟪ 𝓓 ⟫)
                 → is-upperbound (underlying-order (𝓓 ⁻)) (⋁ₛ 𝓓 i α) α
⋁ₛ-is-upperbound 𝓓 i α =
 sup-is-upperbound (underlying-order (𝓓 ⁻))
  (pr₂ (strongly-directed-complete 𝓓 δ))
  where
   δ : is-weakly-directed (underlying-order (𝓓 ⁻)) α
   δ = subsingleton-indexed-families-are-weakly-directed 𝓓 i α

⋁ₛ-is-lowerbound-of-upperbounds : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {P : 𝓥 ̇ }
                                  (i : is-prop P) (α : P → ⟪ 𝓓 ⟫)
                                → is-lowerbound-of-upperbounds
                                   (underlying-order (𝓓 ⁻)) (⋁ₛ 𝓓 i α) α
⋁ₛ-is-lowerbound-of-upperbounds 𝓓 i α =
 sup-is-lowerbound-of-upperbounds (underlying-order (𝓓 ⁻))
  (pr₂ (strongly-directed-complete 𝓓 δ))
  where
   δ : is-weakly-directed (underlying-order (𝓓 ⁻)) α
   δ = subsingleton-indexed-families-are-weakly-directed 𝓓 i α

⋁ₛ-equality-if-inhabited : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {P : 𝓥 ̇ } (i : is-prop P)
                           (α : P → ⟪ 𝓓 ⟫) (p : P) → ⋁ₛ 𝓓 i α ≡ α p
⋁ₛ-equality-if-inhabited 𝓓 i α p = antisymmetry (𝓓 ⁻) (⋁ₛ 𝓓 i α) (α p) u v
 where
  u : ⋁ₛ 𝓓 i α ⊑⟨ 𝓓 ⁻ ⟩ α p
  u = ⋁ₛ-is-lowerbound-of-upperbounds 𝓓 i α (α p) γ
   where
    γ : is-upperbound (underlying-order (𝓓 ⁻)) (α p) α
    γ q = ≡-to-⊑ (𝓓 ⁻) (ap α (i q p))
  v : α p ⊑⟨ 𝓓 ⁻ ⟩ ⋁ₛ 𝓓 i α
  v = ⋁ₛ-is-upperbound 𝓓 i α p

\end{code}
