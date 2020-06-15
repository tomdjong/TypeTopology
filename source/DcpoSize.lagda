Tom de Jong

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥ ; _holds)

module DcpoSize
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
        (pe : propext 𝓥)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoBasics pt fe 𝓥
open import DcpoPointed pt fe 𝓥

open import UF-Equiv
open import UF-Retracts
open import UF-Size

-- TO DO: Find a better home for this.
Ω¬¬ : (𝓦 : Universe) → 𝓦 ⁺ ̇
Ω¬¬ 𝓦 = Σ P ꞉ 𝓦 ̇ , is-prop P × (¬¬ P → P)

_holds : Ω¬¬ 𝓤 → 𝓤 ̇
(P , i , s) holds  = P

negated-types-are-props : {X : 𝓤 ̇ } → is-prop (¬ X)
negated-types-are-props = Π-is-prop fe (λ _ → 𝟘-is-prop)

negated-types-are-¬¬-stable : {X : 𝓤 ̇ } → ¬¬ (¬ X) → ¬ X
negated-types-are-¬¬-stable = three-negations-imply-one

to-Ω¬¬-≡ : propext 𝓤 → (P Q : Ω¬¬ 𝓤)
         → (P holds → ¬¬ (Q holds)) → (Q holds → ¬¬ (P holds))
         → P ≡ Q
to-Ω¬¬-≡ pe (P , i , Ps) (Q , j , Qs) f g =
 to-Σ-≡ (pe i j (Qs ∘ f) (Ps ∘ g) ,
  ×-is-prop (being-a-prop-is-a-prop fe) (Π-is-prop fe (λ _ → j)) _ _)

is-a-small-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ̇
is-a-small-dcpo 𝓓 = ⟨ 𝓓 ⟩ has-size 𝓥

module _
        (𝓓 : DCPO⊥ {𝓤} {𝓣})
        (x₀ : ⟪ 𝓓 ⟫)
       where

 σ : Ω¬¬ 𝓥 → ⟪ 𝓓 ⟫
 σ (P , i , s) = ⋁ₛ 𝓓 i (λ _ → x₀)

 ρ : is-a-small-dcpo (𝓓 ⁻) → ⟪ 𝓓 ⟫ → Ω¬¬ 𝓥
 ρ (E , ϕ) x = (ψ x ≢ ψ (⊥ 𝓓)) , negated-types-are-props , negated-types-are-¬¬-stable
  where
   ψ : ⟪ 𝓓 ⟫ → E
   ψ = ⌜ ≃-sym ϕ ⌝

 σ-section-of-ρ : (s : is-a-small-dcpo (𝓓 ⁻)) → x₀ ≢ ⊥ 𝓓
                → ρ s ∘ σ ∼ id
 σ-section-of-ρ (E , ϕ) x₀-is-not-⊥ (P , i , st) =
  to-Ω¬¬-≡ pe (ρ' (σ (P , i , st))) (P , i , st) f g
   where
    ρ' : ⟪ 𝓓 ⟫ → Ω¬¬ 𝓥
    ρ' = ρ (E , ϕ)
    ψ : ⟪ 𝓓 ⟫ → E
    ψ = ⌜ ≃-sym ϕ ⌝
    α : P → ⟪ 𝓓 ⟫
    α _ = x₀
    f : ψ (⋁ₛ 𝓓 i α) ≢ ψ (⊥ 𝓓) → ¬¬ P
    f e np = e (ap ψ e')
     where
      e' : ⋁ₛ 𝓓 i α ≡ ⊥ 𝓓
      e' = antisymmetry (𝓓 ⁻) (⋁ₛ 𝓓 i α) (⊥ 𝓓)
            γ
            (⊥-is-least 𝓓 (⋁ₛ 𝓓 i α))
       where
        γ : ⋁ₛ 𝓓 i α ⊑⟨ 𝓓 ⁻ ⟩ ⊥ 𝓓
        γ = ⋁ₛ-is-lowerbound-of-upperbounds 𝓓 i α (⊥ 𝓓) h
         where
          h : is-upperbound (underlying-order (𝓓 ⁻)) (⊥ 𝓓) α
          h p = 𝟘-induction (np p)
    g : P → ¬¬ (ψ (⋁ₛ 𝓓 i α) ≢ ψ (⊥ 𝓓))
    g p = double-negation-intro γ
     where
      γ : ψ (⋁ₛ 𝓓 i α) ≢ ψ (⊥ 𝓓)
      γ e = x₀-is-not-⊥ e''
       where
        e' : ⋁ₛ 𝓓 i α ≡ ⊥ 𝓓
        e' = equivs-are-lc ψ (⌜⌝-is-equiv (≃-sym ϕ)) e
        e'' : x₀ ≡ ⊥ 𝓓
        e'' = x₀                ≡⟨ h ⟩
              ⋁ₛ 𝓓 i α ≡⟨ e' ⟩
              ⊥ 𝓓               ∎
         where
          h = (⋁ₛ-equality-if-inhabited 𝓓 i α p) ⁻¹

lemma₁ : (𝓓 : DCPO⊥ {𝓤} {𝓣})
       → is-a-small-dcpo (𝓓 ⁻)
       → is-a-non-trivial-pointed-dcpo 𝓓
       → ∃ s ꞉ (Ω¬¬ 𝓥 → ⟪ 𝓓 ⟫) , is-section s
lemma₁ 𝓓 sm = ∥∥-functor γ
 where
  γ : (Σ x ꞉ ⟪ 𝓓 ⟫ , x ≢ ⊥ 𝓓) → Σ s ꞉ (Ω¬¬ 𝓥 → ⟪ 𝓓 ⟫) , is-section s
  γ (x₀ , ne) = (σ 𝓓 x₀) , (ρ 𝓓 x₀ sm , σ-section-of-ρ 𝓓 x₀ sm ne)

\end{code}

\begin{code}

open import UF-Univalence
open import UF-UniverseEmbedding
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-Embeddings

-- Explicitly tracking which universes should be univalent

universe-embedding-criterion' : (𝓤 𝓦 : Universe)
                              → is-univalent 𝓤
                              → is-univalent (𝓤 ⊔ 𝓦)
                              →  (f : 𝓤 ̇ → 𝓤 ⊔ 𝓦 ̇ )
                              → ((X : 𝓤 ̇ ) → f X ≃ X)
                              → is-embedding f
universe-embedding-criterion' 𝓤 𝓦 ua ua' f i = embedding-criterion' f γ
 where
  γ : (X X' : 𝓤 ̇ ) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' =  (f X ≡ f X')  ≃⟨ is-univalent-≃ ua' (f X) (f X') ⟩
            (f X ≃ f X')  ≃⟨ Eq-Eq-cong (λ _ _ → fe) (i X) (i X') ⟩
            (X ≃ X')      ≃⟨ ≃-sym (is-univalent-≃ ua X X') ⟩
            (X ≡ X')      ■

lift-is-embedding' : is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓦)
                   → is-embedding (lift {𝓤} 𝓦)
lift-is-embedding' {𝓤} {𝓦} ua ua' =
 universe-embedding-criterion' 𝓤 𝓦 ua ua' (lift 𝓦) (lift-≃ 𝓦)

has-size-is-a-prop' : (𝓦 : Universe)
                    → is-univalent 𝓦
                    → is-univalent (𝓤 ⊔ 𝓦)
                    → (X : 𝓤 ̇ )
                    → is-prop (X has-size 𝓦)
has-size-is-a-prop' {𝓤} 𝓦 ua ua' X = c
 where
  a : (Y : 𝓦 ̇) → (Y ≃ X) ≃ (lift 𝓤 Y ≡ lift 𝓦 X)
  a Y = (Y ≃ X)               ≃⟨ e₁ ⟩
        (lift 𝓤 Y ≃ lift 𝓦 X) ≃⟨ e₂ ⟩
        (lift 𝓤 Y ≡ lift 𝓦 X) ■
   where
    e₁ = Eq-Eq-cong (λ _ _ → fe) (≃-sym (lift-≃ 𝓤 Y)) (≃-sym (lift-≃ 𝓦 X))
    e₂ = ≃-sym (is-univalent-≃ ua' (lift 𝓤 Y) (lift 𝓦 X))
  b : (Σ Y ꞉ 𝓦 ̇ , Y ≃ X) ≃ (Σ Y ꞉ 𝓦 ̇ , lift 𝓤 Y ≡ lift 𝓦 X)
  b = Σ-cong a
  c : is-prop (Σ Y ꞉ 𝓦 ̇ , Y ≃ X)
  c = equiv-to-prop b (lift-is-embedding' ua ua' (lift 𝓦 X))

\end{code}

The main result

\begin{code}

open import SizeBasics

Theorem1 : is-univalent 𝓥 → is-univalent (𝓥 ⁺) -- Only to make Ω¬¬ 𝓥 has-size 𝓥
                                               -- a proposition.
         → (∃ 𝓓 ꞉ DCPO⊥ {𝓤} {𝓣} ,
               is-a-non-trivial-pointed-dcpo 𝓓
             × is-a-small-dcpo (𝓓 ⁻))
         → Ω¬¬ 𝓥 has-size 𝓥
Theorem1 ua ua⁺ = ∥∥-rec i γ
 where
  i : is-prop (Ω¬¬ 𝓥 has-size 𝓥)
  i = has-size-is-a-prop' 𝓥 ua ua⁺ (Ω¬¬ 𝓥)
  γ : (Σ 𝓓 ꞉ DCPO⊥ {𝓤} {𝓣} ,
          is-a-non-trivial-pointed-dcpo 𝓓
        × is-a-small-dcpo (𝓓 ⁻))
    → Ω¬¬ 𝓥 has-size 𝓥
  γ (𝓓 , nt , (E , χ)) = ∥∥-rec i ψ nt
   where
    ψ : (Σ x ꞉ ⟪ 𝓓 ⟫ , x ≢ ⊥ 𝓓) → Ω¬¬ 𝓥 has-size 𝓥
    ψ (x₀ , ne) = retract-of-a-set-has-size (equiv-to-set χ (sethood (𝓓 ⁻))) r
     where
      r = Ω¬¬ 𝓥 ◁⟨ ρ 𝓓 x₀ (E , χ) , (σ 𝓓 x₀) , (σ-section-of-ρ 𝓓 x₀ (E , χ) ne) ⟩
          ⟪ 𝓓 ⟫ ◁⟨ ⌜ χ ⌝ , (equivs-have-sections ⌜ χ ⌝ (⌜⌝-is-equiv χ)) ⟩
          E ◀

\end{code}

\begin{code}

open import DiscreteAndSeparated

is-a-locally-small-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-locally-small-dcpo 𝓓 = (x y : ⟨ 𝓓 ⟩) → (x ⊑⟨ 𝓓 ⟩ y) has-size 𝓥

module _
        (𝓓 : DCPO⊥ {𝓤} {𝓣})
        (x₀ : ⟪ 𝓓 ⟫)
       where

 σ' : Ω¬¬ 𝓥 → ⟪ 𝓓 ⟫
 σ' (P , i , s) = ⋁ₛ 𝓓 i (λ _ → x₀)

 ρ' : is-a-locally-small-dcpo (𝓓 ⁻) → ⟪ 𝓓 ⟫ → Ω¬¬ 𝓥
 ρ' ls x = ¬ L , negated-types-are-props , negated-types-are-¬¬-stable
  where
   L : 𝓥 ̇
   L = has-size-type (ls x (⊥ 𝓓))
   ψ : (x ⊑⟨ 𝓓 ⁻ ⟩ ⊥ 𝓓) → L
   ψ = ⌜ ≃-sym (has-size-equiv (ls x (⊥ 𝓓))) ⌝

 σ'-section-of-ρ' : (ls : is-a-locally-small-dcpo (𝓓 ⁻))
                  → x₀ ≢ ⊥ 𝓓
                  → ρ' ls ∘ σ' ∼ id
 σ'-section-of-ρ' ls x₀-is-not-⊥ (P , i , st) =
  to-Ω¬¬-≡ pe (ρ'' (σ' (P , i , st))) (P , i , st) f g
   where
    ρ'' : ⟪ 𝓓 ⟫ → Ω¬¬ 𝓥
    ρ'' = ρ' ls
    L : ⟪ 𝓓 ⟫ → 𝓥 ̇
    L x = has-size-type (ls x (⊥ 𝓓))
    ψ : (x : ⟪ 𝓓 ⟫) → (x ⊑⟨ 𝓓 ⁻ ⟩ ⊥ 𝓓) → L x
    ψ x = ⌜ ≃-sym (has-size-equiv (ls x (⊥ 𝓓))) ⌝
    φ : (x : ⟪ 𝓓 ⟫) → L x → (x ⊑⟨ 𝓓 ⁻ ⟩ ⊥ 𝓓)
    φ x = ⌜ has-size-equiv (ls x (⊥ 𝓓)) ⌝
    α : P → ⟪ 𝓓 ⟫
    α _ = x₀
    f : ¬ (L (⋁ₛ 𝓓 i α)) → ¬¬ P
    f nl np = nl l
     where
      l : L (⋁ₛ 𝓓 i α)
      l = ψ (⋁ₛ 𝓓 i α) l'
       where
        l' : ⋁ₛ 𝓓 i α ⊑⟨ 𝓓 ⁻ ⟩ ⊥ 𝓓
        l' = ⋁ₛ-is-lowerbound-of-upperbounds 𝓓 i α (⊥ 𝓓) γ
         where
          γ : is-upperbound (underlying-order (𝓓 ⁻)) (⊥ 𝓓) α
          γ p = 𝟘-induction (np p)
    g : P → ¬¬ (¬ (L (⋁ₛ 𝓓 i α)))
    g p = double-negation-intro γ
     where
      γ : ¬ L (⋁ₛ 𝓓 i α)
      γ l = x₀-is-not-⊥ e
       where
        e : x₀ ≡ ⊥ 𝓓
        e = antisymmetry (𝓓 ⁻) x₀ (⊥ 𝓓) ϕ (⊥-is-least 𝓓 x₀)
         where
          ϕ = x₀       ⊑⟨ 𝓓 ⁻ ⟩[ ⋁ₛ-is-upperbound 𝓓 i α p ]
              ⋁ₛ 𝓓 i α ⊑⟨ 𝓓 ⁻ ⟩[ φ (⋁ₛ 𝓓 i α) l ]
              ⊥ 𝓓      ∎⟨ 𝓓 ⁻ ⟩

open import UF-Miscelanea

Theorem1' : (𝓓 : DCPO⊥ {𝓤} {𝓣})
          → is-a-non-trivial-pointed-dcpo 𝓓
          → is-a-locally-small-dcpo (𝓓 ⁻)
          → is-discrete ⟪ 𝓓 ⟫
          → is-discrete (Ω¬¬ 𝓥)
Theorem1' 𝓓 nt ls d = ∥∥-rec (being-discrete-is-a-prop (λ _ _ → fe)) γ nt
 where
  γ : (Σ x ꞉ ⟪ 𝓓 ⟫ , x ≢ ⊥ 𝓓) → is-discrete (Ω¬¬ 𝓥)
  γ (x₀ , x₀-is-not-⊥) = retract-discrete-discrete g d
   where
    g : retract Ω¬¬ 𝓥 of ⟪ 𝓓 ⟫
    g = (ρ' 𝓓 x₀ ls) , (σ' 𝓓 x₀) , (σ'-section-of-ρ' 𝓓 x₀ ls x₀-is-not-⊥)

\end{code}
