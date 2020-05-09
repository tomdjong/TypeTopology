Tom de Jong, 5 May 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoLimits
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
        (𝓤 𝓣 : Universe)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoBasics pt fe 𝓥

open import Poset fe

module Diagram
        {I : 𝓥 ̇ }
--        (I-is-set : is-set I)
        (_⊑_ : I → I → 𝓦 ̇ )
        (⊑-refl : {i : I} → i ⊑ i)
        (⊑-trans : {i j k : I} → i ⊑ j → j ⊑ k → i ⊑ k)
--        (⊑-antisym : (i j : I) → i ⊑ j → j ⊑ i → i ≡ j)
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
--      (ε-id : (i : I ) → ε (⊑-refl i) ∼ id)
--      (π-id : (i : I ) → π (⊑-refl i) ∼ id)
        (ε-comp : {i j k : I} (l : i ⊑ j) (m : j ⊑ k)
                → ε m ∘ ε l ∼ ε (⊑-trans l m))
        (π-comp : {i j k : I} (l : i ⊑ j) (m : j ⊑ k)
                → π l ∘ π m ∼ π (⊑-trans l m))
       where

 𝓓∞-carrier : 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
 𝓓∞-carrier =
  Σ σ ꞉ ((i : I) → ⟨ 𝓓 i ⟩) , ((i j : I) (l : i ⊑ j) → π l (σ j) ≡ σ i)

 ⦅_⦆ : 𝓓∞-carrier → (i : I) → ⟨ 𝓓 i ⟩
 ⦅_⦆ = pr₁

 π-equality : (σ : 𝓓∞-carrier) {i j : I} (l : i ⊑ j) → π l (⦅ σ ⦆ j) ≡ ⦅ σ ⦆ i
 π-equality σ {i} {j} l = pr₂ σ i j l

 to-𝓓∞-≡ : (σ τ : 𝓓∞-carrier) → ((i : I) → ⦅ σ ⦆ i ≡ ⦅ τ ⦆ i) → σ ≡ τ
 to-𝓓∞-≡ σ τ h =
  to-subtype-≡
   (λ σ → Π-is-prop fe
    (λ i → Π-is-prop fe
    (λ j → Π-is-prop fe
    (λ l → sethood (𝓓 i)))))
   (dfunext fe h)

 family-at-ith-component : {𝓐 : 𝓥 ̇ } (α : 𝓐 → 𝓓∞-carrier) (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
 family-at-ith-component α i a = ⦅ α a ⦆ i

 _≼_ : 𝓓∞-carrier → 𝓓∞-carrier → 𝓥 ⊔ 𝓣 ̇
 σ ≼ τ = (i : I) → ⦅ σ ⦆ i ⊑⟨ 𝓓 i ⟩ ⦅ τ ⦆ i

 family-at-ith-component-is-directed : {𝓐 : 𝓥 ̇ } (α : 𝓐 → 𝓓∞-carrier)
                                       (δ : is-directed _≼_ α) (i : I)
                                     → is-Directed (𝓓 i)
                                        (family-at-ith-component α i)
 family-at-ith-component-is-directed {𝓐} α δ i =
  (directed-implies-inhabited _≼_ α δ) , γ
   where
    β : (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
    β = family-at-ith-component α
    γ : is-weakly-directed (underlying-order (𝓓 i)) (β i)
    γ a₁ a₂ = ∥∥-functor g (directed-implies-weakly-directed _≼_ α δ a₁ a₂)
     where
      g : (Σ a ꞉ 𝓐 , (α a₁ ≼ α a) × (α a₂ ≼ α a))
        → (Σ a ꞉ 𝓐 , (β i a₁ ⊑⟨ 𝓓 i ⟩ β i a) × (β i a₂ ⊑⟨ 𝓓 i ⟩ β i a))
      g (a , l₁ , l₂) = a , l₁ i , l₂ i

 𝓓∞-∐ : {𝓐 : 𝓥 ̇ } (α : 𝓐 → 𝓓∞-carrier) (δ : is-directed _≼_ α) → 𝓓∞-carrier
 𝓓∞-∐ {𝓐} α δ = (λ i → ∐ (𝓓 i) (δ' i)) , φ
  where
   β : (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
   β = family-at-ith-component α
   δ' : (i : I) → is-Directed (𝓓 i) (β i)
   δ' = family-at-ith-component-is-directed α δ
   φ : (i j : I) (l : i ⊑ j) → π l (∐ (𝓓 j) (δ' j)) ≡ ∐ (𝓓 i) (δ' i)
   φ i j l = π l (∐ (𝓓 j) (δ' j))       ≡⟨ eq₁ ⟩
             ∐ (𝓓 i) {𝓐} {π l ∘ β j} δ₁ ≡⟨ eq₂ ⟩
             ∐ (𝓓 i) {𝓐} {β i} δ₂       ≡⟨ eq₃ ⟩
             ∐ (𝓓 i) {𝓐} {β i} (δ' i)   ∎
    where
     δ₁ : is-Directed (𝓓 i) (π l ∘ β j)
     δ₁ = image-is-directed' (𝓓 j) (𝓓 i) ((π l) , (π-is-continuous l)) (δ' j)
     h : π l ∘ β j ≡ β i
     h = dfunext fe (λ a → π-equality (α a) l)
     δ₂ : is-Directed (𝓓 i) (β i)
     δ₂ = transport (is-Directed (𝓓 i)) h δ₁
     eq₁ = continuous-∐-≡ (𝓓 j) (𝓓 i) ((π l) , (π-is-continuous l)) (δ' j)
     eq₂ = ∐-family-≡ (𝓓 i) (π l ∘ β j) (β i) h δ₁
     eq₃ = ∐-independent-of-directedness-witness (𝓓 i) δ₂ (δ' i)

 𝓓∞ : DCPO {𝓥 ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⊔ 𝓣}
 𝓓∞ = (𝓓∞-carrier , _≼_ , pa , dc)
  where
   pa : PosetAxioms.poset-axioms _≼_
   pa = sl , pv , r , t , a
    where
     open PosetAxioms {𝓥 ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⊔ 𝓣} {𝓓∞-carrier} _≼_
     sl : is-set 𝓓∞-carrier
     sl = subsets-of-sets-are-sets _ _
           (Π-is-set fe (λ i → sethood (𝓓 i)))
           (Π-is-prop fe
             (λ i → Π-is-prop fe
             (λ j → Π-is-prop fe
             (λ l → sethood (𝓓 i)))))
     pv : is-prop-valued
     pv σ τ = Π-is-prop fe (λ i → prop-valuedness (𝓓 i) (⦅ σ ⦆ i) (⦅ τ ⦆ i))
     r : is-reflexive
     r σ i = reflexivity (𝓓 i) (⦅ σ ⦆ i)
     t : is-transitive
     t σ τ ρ l k i = transitivity (𝓓 i) (⦅ σ ⦆ i) (⦅ τ ⦆ i) (⦅ ρ ⦆ i) (l i) (k i)
     a : is-antisymmetric
     a σ τ l k = to-𝓓∞-≡ σ τ
                  (λ i → antisymmetry (𝓓 i) (⦅ σ ⦆ i) (⦅ τ ⦆ i) (l i) (k i))
   dc : is-directed-complete _≼_
   dc 𝓐 α δ = (𝓓∞-∐ α δ) , ub , lb-of-ubs
    where
     δ' : (i : I) → is-Directed (𝓓 i) (family-at-ith-component α i)
     δ' = family-at-ith-component-is-directed α δ
     ub : (a : 𝓐) → α a ≼ (𝓓∞-∐ α δ)
     ub a i = ∐-is-upperbound (𝓓 i) (δ' i) a
     lb-of-ubs : is-lowerbound-of-upperbounds _≼_ (𝓓∞-∐ α δ) α
     lb-of-ubs τ ub i = ∐-is-lowerbound-of-upperbounds (𝓓 i) (δ' i) (⦅ τ ⦆ i)
                        (λ a → ub a i)

 π∞ : (i : I) → ⟨ 𝓓∞ ⟩ → ⟨ 𝓓 i ⟩
 π∞ i (σ , _) = σ i

 π∞-commutes-with-πs : (i j : I) (l : i ⊑ j) → π l ∘ π∞ j ∼ π∞ i
 π∞-commutes-with-πs i j l σ = π-equality σ l

 open import UF-ImageAndSurjection
 open ImageAndSurjection pt

 κ : {i j : I} → ⟨ 𝓓 i ⟩ → (Σ k ꞉ I , i ⊑ k × j ⊑ k) → ⟨ 𝓓 j ⟩
 κ x (k , lᵢ , lⱼ) = π lⱼ (ε lᵢ x)

 κ-wconstant : (i j : I) (x : ⟨ 𝓓 i ⟩) → wconstant (κ x)
 κ-wconstant i j x (k , lᵢ , lⱼ) (k' , lᵢ' , lⱼ') =
  ∥∥-rec (sethood (𝓓 j)) γ (I-weakly-directed k k')
   where
    γ : (Σ m ꞉ I , k ⊑ m × k' ⊑ m)
      → κ x (k , lᵢ , lⱼ) ≡ κ x (k' , lᵢ' , lⱼ')
    γ (m , u , u') = π lⱼ (ε lᵢ x)                           ≡⟨ e₁ ⟩
                     π lⱼ (π u (ε u (ε lᵢ x)))               ≡⟨ e₂ ⟩
                     π (⊑-trans lⱼ u) (ε u (ε lᵢ x))         ≡⟨ e₃ ⟩
                     π (⊑-trans lⱼ u) (ε (⊑-trans lᵢ u) x)   ≡⟨ e₄ ⟩
                     π (⊑-trans lⱼ u) (ε (⊑-trans lᵢ' u') x) ≡⟨ e₅ ⟩
                     π (⊑-trans lⱼ u) (ε u' (ε lᵢ' x))       ≡⟨ e₆ ⟩
                     π (⊑-trans lⱼ' u') (ε u' (ε lᵢ' x))     ≡⟨ e₇ ⟩
                     π lⱼ' (π u' (ε u' (ε lᵢ' x)))           ≡⟨ e₈ ⟩
                     π lⱼ' (ε lᵢ' x)                         ∎
     where
      e₁ = ap (π lⱼ) (ε-section-of-π u (ε lᵢ x) ⁻¹)
      e₂ = π-comp lⱼ u (ε u (ε lᵢ x))
      e₃ = ap (π (⊑-trans lⱼ u)) (ε-comp lᵢ u x)
      e₄ = ap (π (⊑-trans lⱼ u)) (ap (λ - → ε - x)
           (⊑-prop-valued i m (⊑-trans lᵢ u) (⊑-trans lᵢ' u')))
      e₅ = ap (π (⊑-trans lⱼ u)) ((ε-comp lᵢ' u' x) ⁻¹)
      e₆ = ap (λ - → π - _) (⊑-prop-valued j m (⊑-trans lⱼ u) (⊑-trans lⱼ' u'))
      e₇ = (π-comp lⱼ' u' (ε u' (ε lᵢ' x))) ⁻¹
      e₈ = ap (π lⱼ') (ε-section-of-π u' (ε lᵢ' x))

 ρ : (i j : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩
 ρ i j x = wconstant-from-∥∥-to-set (sethood (𝓓 j)) (κ x)
            (κ-wconstant i j x) (I-weakly-directed i j)

 ρ-in-terms-of-κ : {i j k : I} (lᵢ : i ⊑ k) (lⱼ : j ⊑ k) (x : ⟨ 𝓓 i ⟩)
                 → ρ i j x ≡ κ x (k , lᵢ , lⱼ)
 ρ-in-terms-of-κ {i} {j} {k} lᵢ lⱼ x =
  ρ i j x                    ≡⟨ refl ⟩
  ν (I-weakly-directed i j)  ≡⟨ p ⟩
  ν ∣ (k , lᵢ , lⱼ) ∣        ≡⟨ q ⟩
  κ x (k , lᵢ , lⱼ)          ∎
   where
    s : is-set ⟨ 𝓓 j ⟩
    s = sethood (𝓓 j)
    ω : wconstant (κ x)
    ω = κ-wconstant i j x
    ν : (∃ k' ꞉ I , i ⊑ k' × j ⊑ k') → ⟨ 𝓓 j ⟩
    ν = wconstant-from-∥∥-to-set s (κ x) ω
    p = ap ν (∥∥-is-a-prop (I-weakly-directed i j) ∣ k , lᵢ , lⱼ ∣)
    q = wconstant-to-set-factors-through-∥∥ s (κ x) ω (k , lᵢ , lⱼ)

 ε∞ : (i : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓓∞ ⟩
 ε∞ i x = σ , φ
  where
   σ : (j : I) → ⟨ 𝓓 j ⟩
   σ j = ρ i j x
   φ : (j₁ j₂ : I) (l : j₁ ⊑ j₂) → π l (σ j₂) ≡ σ j₁
   φ j₁ j₂ l = ∥∥-rec (sethood (𝓓 j₁)) γ (I-weakly-directed i j₂)
    where
     γ : (Σ k ꞉ I , i ⊑ k × j₂ ⊑ k) → π l (σ j₂) ≡ σ j₁
     γ (k , lᵢ , l₂) = π l (σ j₂)                  ≡⟨ refl ⟩
                       π l (ρ i j₂ x)              ≡⟨ e₁   ⟩
                       π l (κ x (k , lᵢ , l₂))     ≡⟨ refl ⟩
                       π l (π l₂ (ε lᵢ x))         ≡⟨ e₂   ⟩
                       π (⊑-trans l l₂) (ε lᵢ x)   ≡⟨ refl ⟩
                       π (⊑-trans l l₂) (ε lᵢ x)   ≡⟨ refl ⟩
                       κ x (k , lᵢ , ⊑-trans l l₂) ≡⟨ e₃   ⟩
                       ρ i j₁ x                    ≡⟨ refl ⟩
                       σ j₁                        ∎
      where
       e₁ = ap (π l) (ρ-in-terms-of-κ lᵢ l₂ x)
       e₂ = π-comp l l₂ (ε lᵢ x)
       e₃ = (ρ-in-terms-of-κ lᵢ (⊑-trans l l₂) x) ⁻¹

 ε∞-commutes-with-εs : (i j : I) (l : i ⊑ j) → ε∞ j ∘ ε l ∼ ε∞ i
 ε∞-commutes-with-εs i j l x = to-𝓓∞-≡ (ε∞ j (ε l x)) (ε∞ i x) γ
  where
   γ : (k : I) → ⦅ ε∞ j (ε l x) ⦆ k ≡ ⦅ ε∞ i x ⦆ k
   γ k = ∥∥-rec (sethood (𝓓 k)) g (I-weakly-directed j k)
    where
     g : (Σ m ꞉ I , j ⊑ m × k ⊑ m) → ⦅ ε∞ j (ε l x) ⦆ k ≡ ⦅ ε∞ i x ⦆ k
     g (m , lⱼ , lₖ) =
      ⦅ ε∞ j (ε l x) ⦆ k          ≡⟨ refl ⟩
      ρ j k (ε l x)               ≡⟨ ρ-in-terms-of-κ lⱼ lₖ (ε l x) ⟩
      κ (ε l x) (m , lⱼ , lₖ)     ≡⟨ refl ⟩
      π lₖ (ε lⱼ (ε l x))         ≡⟨ ap (π lₖ) (ε-comp l lⱼ x) ⟩
      π lₖ (ε (⊑-trans l lⱼ) x)   ≡⟨ refl ⟩
      κ x (m , ⊑-trans l lⱼ , lₖ) ≡⟨ (ρ-in-terms-of-κ (⊑-trans l lⱼ) lₖ x) ⁻¹ ⟩
      ρ i k x                     ≡⟨ refl ⟩
      ⦅ ε∞ i x ⦆ k                ∎

 π∞ε∞ : {i : I} → π∞ i ∘ ε∞ i ∼ id
 π∞ε∞ {i} x = π∞ i (ε∞ i x)             ≡⟨ refl ⟩
              ⦅ ε∞ i x ⦆ i              ≡⟨ refl ⟩
              ρ i i x                   ≡⟨ ρ-in-terms-of-κ ⊑-refl ⊑-refl x ⟩
              κ x (i , ⊑-refl , ⊑-refl) ≡⟨ refl ⟩
              π ⊑-refl (ε ⊑-refl x)     ≡⟨ ε-section-of-π ⊑-refl x ⟩
              x                         ∎

 ε∞π∞ : {i : I} (σ : ⟨ 𝓓∞ ⟩) → ε∞ i (π∞ i σ) ⊑⟨ 𝓓∞ ⟩ σ
 ε∞π∞ {i} σ j = ∥∥-rec (prop-valuedness (𝓓 j) (⦅ ε∞ i (π∞ i σ) ⦆ j) (⦅ σ ⦆ j)) γ
                 (I-weakly-directed i j)
  where
   γ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
     → ⦅ ε∞ i (π∞ i σ) ⦆ j ⊑⟨ 𝓓 j ⟩ ⦅ σ ⦆ j
   γ (k , lᵢ , lⱼ) = ⦅ ε∞ i (π∞ i σ) ⦆ j          ⊑⟨ 𝓓 j ⟩[ reflexivity (𝓓 j) _ ]
                     ρ i j (⦅ σ ⦆ i)              ⊑⟨ 𝓓 j ⟩[ u₁ ]
                     κ (⦅ σ ⦆ i) (k , lᵢ , lⱼ)    ⊑⟨ 𝓓 j ⟩[ reflexivity (𝓓 j) _ ]
                     π lⱼ (ε lᵢ (⦅ σ ⦆ i))        ⊑⟨ 𝓓 j ⟩[ u₂ ]
                     π lⱼ (ε lᵢ (π lᵢ (⦅ σ ⦆ k))) ⊑⟨ 𝓓 j ⟩[ u₃ ]
                     π lⱼ (⦅ σ ⦆ k)               ⊑⟨ 𝓓 j ⟩[ u₄ ]
                     ⦅ σ ⦆ j                      ∎⟨ 𝓓 j ⟩
    where
     u₁ = ≡-to-⊑ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ (⦅ σ ⦆ i))
     u₂ = ≡-to-⊑ (𝓓 j) (ap (π lⱼ ∘ ε lᵢ) ((π-equality σ lᵢ) ⁻¹))
     u₃ = continuous-implies-monotone (𝓓 k) (𝓓 j) (π lⱼ , π-is-continuous lⱼ)
           (ε lᵢ (π lᵢ (⦅ σ ⦆ k))) (⦅ σ ⦆ k) (επ-deflation lᵢ (⦅ σ ⦆ k))
     u₄ = ≡-to-⊑ (𝓓 j) (π-equality σ lⱼ)

 π∞-is-continuous : (i : I) → is-continuous 𝓓∞ (𝓓 i) (π∞ i)
 π∞-is-continuous i 𝓐 α δ = ub , lb-of-ubs
  where
   δ' : (j : I) → is-Directed (𝓓 j) (family-at-ith-component α j)
   δ' = family-at-ith-component-is-directed α δ
   ub : (a : 𝓐) → π∞ i (α a) ⊑⟨ 𝓓 i ⟩ π∞ i (∐ 𝓓∞ {𝓐} {α} δ)
   ub a = π∞ i (α a)            ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          ⦅ α a ⦆ i             ⊑⟨ 𝓓 i ⟩[ ∐-is-upperbound (𝓓 i) (δ' i) a ]
          ∐ (𝓓 i) (δ' i)        ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          ⦅ ∐ 𝓓∞ {𝓐} {α} δ ⦆ i  ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          π∞ i (∐ 𝓓∞ {𝓐} {α} δ) ∎⟨ 𝓓 i ⟩
   lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 i))
                 (π∞ i (∐ 𝓓∞ {𝓐} {α} δ)) (π∞ i ∘ α)
   lb-of-ubs x ub = π∞ i (∐ 𝓓∞ {𝓐} {α} δ) ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
                    ∐ (𝓓 i) (δ' i)        ⊑⟨ 𝓓 i ⟩[ l ]
                    x                     ∎⟨ 𝓓 i ⟩
    where
     l = ∐-is-lowerbound-of-upperbounds (𝓓 i) (δ' i) x ub

 ε∞-is-monotone : (i : I) → is-monotone (𝓓 i) 𝓓∞ (ε∞ i)
 ε∞-is-monotone i x y l j =
  ∥∥-rec (prop-valuedness (𝓓 j) (⦅ ε∞ i x ⦆ j) (⦅ ε∞ i y ⦆ j))
   γ (I-weakly-directed i j)
    where
     γ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
       → ⦅ ε∞ i x ⦆ j ⊑⟨ 𝓓 j ⟩ ⦅ ε∞ i y ⦆ j
     γ (k , lᵢ , lⱼ) = ⦅ ε∞ i x ⦆ j      ⊑⟨ 𝓓 j ⟩[ u₁ ]
                       ρ i j x           ⊑⟨ 𝓓 j ⟩[ u₂ ]
                       κ x (k , lᵢ , lⱼ) ⊑⟨ 𝓓 j ⟩[ u₃ ]
                       π lⱼ (ε lᵢ x)     ⊑⟨ 𝓓 j ⟩[ u₄ ]
                       π lⱼ (ε lᵢ y)     ⊑⟨ 𝓓 j ⟩[ u₅ ]
                       κ y (k , lᵢ , lⱼ) ⊑⟨ 𝓓 j ⟩[ u₆ ]
                       ρ i j y           ⊑⟨ 𝓓 j ⟩[ u₇ ]
                       ⦅ ε∞ i y ⦆ j      ∎⟨ 𝓓 j ⟩
      where
       u₁ = reflexivity (𝓓 j) (⦅ ε∞ i x ⦆ j)
       u₂ = ≡-to-⊑ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ x)
       u₃ = reflexivity (𝓓 j) (κ x (k , lᵢ , lⱼ))
       u₄ = mπ (ε lᵢ x) (ε lᵢ y) (mε x y l)
        where
         mε : is-monotone (𝓓 i) (𝓓 k) (ε lᵢ)
         mε = continuous-implies-monotone (𝓓 i) (𝓓 k)
               ((ε lᵢ) , (ε-is-continuous lᵢ))
         mπ : is-monotone (𝓓 k) (𝓓 j) (π lⱼ)
         mπ = continuous-implies-monotone (𝓓 k) (𝓓 j)
               ((π lⱼ) , (π-is-continuous lⱼ))
       u₅ = reflexivity (𝓓 j) (π lⱼ (ε lᵢ y))
       u₆ = ≡-to-⊑ (𝓓 j) ((ρ-in-terms-of-κ lᵢ lⱼ y) ⁻¹)
       u₇ = reflexivity (𝓓 j) (ρ i j y)

 ε∞-is-continuous : (i : I) → is-continuous (𝓓 i) 𝓓∞ (ε∞ i)
 ε∞-is-continuous i = continuity-criterion' (𝓓 i) 𝓓∞ (ε∞ i) (ε∞-is-monotone i) γ
  where
   γ : (𝓐 : 𝓥 ̇) (α : 𝓐 → ⟨ 𝓓 i ⟩) (δ : is-Directed (𝓓 i) α)
     → is-lowerbound-of-upperbounds (underlying-order 𝓓∞)
        (ε∞ i (∐ (𝓓 i) δ)) (ε∞ i ∘ α)
   γ 𝓐 α δ σ ub j =
    ∥∥-rec (prop-valuedness (𝓓 j) (⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j) (⦅ σ ⦆ j))
     g (I-weakly-directed i j)
      where
       g : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
         → ⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j ⊑⟨ 𝓓 j ⟩ ⦅ σ ⦆ j
       g (k , lᵢ , lⱼ) =
        ⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j                  ⊑⟨ 𝓓 j ⟩[ u₁ ]
        ρ i j (∐ (𝓓 i) δ)                       ⊑⟨ 𝓓 j ⟩[ u₂ ]
        κ (∐ (𝓓 i) δ) (k , lᵢ , lⱼ)             ⊑⟨ 𝓓 j ⟩[ u₃ ]
        π lⱼ (ε lᵢ (∐ (𝓓 i) δ))                 ⊑⟨ 𝓓 j ⟩[ u₄ ]
        ∐ (𝓓 j) {𝓐} {πε ∘ α} δ₁                 ⊑⟨ 𝓓 j ⟩[ u₅ ]
        ∐ (𝓓 j) {𝓐} {λ a → ⦅ ε∞ i (α a) ⦆ j} δ₂ ⊑⟨ 𝓓 j ⟩[ u₆ ]
        ⦅ σ ⦆ j ∎⟨ 𝓓 j ⟩
         where
          πε : ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩
          πε = π lⱼ ∘ ε lᵢ
          πε-is-continuous : is-continuous (𝓓 i) (𝓓 j) πε
          πε-is-continuous = ∘-is-continuous (𝓓 i) (𝓓 k) (𝓓 j) (ε lᵢ) (π lⱼ)
                              (ε-is-continuous lᵢ) (π-is-continuous lⱼ)
          πε' : DCPO[ 𝓓 i , 𝓓 j ]
          πε' = πε , πε-is-continuous
          δ₁ : is-Directed (𝓓 j) (πε ∘ α)
          δ₁ = image-is-directed' (𝓓 i) (𝓓 j) πε' δ
          p : πε ∘ α ≡ (λ a → ⦅ ε∞ i (α a) ⦆ j)
          p = dfunext fe h
           where
            h : πε ∘ α ∼ (λ a → ⦅ ε∞ i (α a) ⦆ j)
            h a = πε (α a)              ≡⟨ refl ⟩
                  π lⱼ (ε lᵢ (α a))     ≡⟨ refl ⟩
                  κ (α a) (k , lᵢ , lⱼ) ≡⟨ (ρ-in-terms-of-κ lᵢ lⱼ (α a)) ⁻¹ ⟩
                  ρ i j (α a)           ≡⟨ refl ⟩
                  ⦅ ε∞ i (α a) ⦆ j      ∎
          δ₂ : is-Directed (𝓓 j) (λ a → ⦅ ε∞ i (α a) ⦆ j)
          δ₂ = transport (is-Directed (𝓓 j)) p δ₁
          u₁ = reflexivity (𝓓 j) (⦅ ε∞ i (∐ (𝓓 i) δ) ⦆ j)
          u₂ = ≡-to-⊑ (𝓓 j) (ρ-in-terms-of-κ lᵢ lⱼ (∐ (𝓓 i) δ))
          u₃ = reflexivity (𝓓 j) (κ (∐ (𝓓 i) δ) (k , lᵢ , lⱼ))
          u₄ = continuous-∐-⊑ (𝓓 i) (𝓓 j) πε' δ
          u₅ = ≡-to-⊑ (𝓓 j)
                (∐-family-≡ (𝓓 j) (πε ∘ α) (λ a → ⦅ ε∞ i (α a) ⦆ j) p δ₁)
          u₆ = ∐-is-lowerbound-of-upperbounds (𝓓 j) δ₂ (⦅ σ ⦆ j) (λ a → ub a j)

\end{code}

\begin{code}

 module _
         (𝓔 : DCPO {𝓤'} {𝓣'})
         (f : (i : I) → ⟨ 𝓔 ⟩ → ⟨ 𝓓 i ⟩)
         (f-cont : (i : I) → is-continuous 𝓔 (𝓓 i) (f i))
         (comm : (i j : I) (l : i ⊑ j) → π l ∘ f j ∼ f i)
        where

  limit-mediating-arrow : ⟨ 𝓔 ⟩ → ⟨ 𝓓∞ ⟩
  limit-mediating-arrow y = σ , φ
   where
    σ : (i : I) → ⟨ 𝓓 i ⟩
    σ i = f i y
    φ : (i j : I) (l : i ⊑ j) → π l (f j y) ≡ f i y
    φ i j l = comm i j l y

  limit-mediating-arrow-commutes : (i : I) → π∞ i ∘ limit-mediating-arrow ∼ f i
  limit-mediating-arrow-commutes i y = refl

  limit-mediating-arrow-is-unique : (g : ⟨ 𝓔 ⟩ → ⟨ 𝓓∞ ⟩)
                                  → ((i : I) → π∞ i ∘ g ∼ f i)
                                  → g ∼ limit-mediating-arrow
  limit-mediating-arrow-is-unique g g-comm y =
   to-𝓓∞-≡ (g y) (limit-mediating-arrow y) (λ i → g-comm i y)

\end{code}

\begin{code}

 {- ε∞-family : ⟨ 𝓓∞ ⟩ → I → ⟨ 𝓓∞ ⟩
 ε∞-family σ i = ε∞ i (⦅ σ ⦆ i)

 ∐-of-ε∞s : (σ : ⟨ 𝓓∞ ⟩) → σ ≡ {!!}
 ∐-of-ε∞s = {!!} -}

 module _
         (𝓔 : DCPO {𝓤'} {𝓣'})
         (g : (i : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓔 ⟩)
         (g-cont : (i : I) → is-continuous (𝓓 i) 𝓔 (g i))
         (comm : (i j : I) (l : i ⊑ j) → g j ∘ ε l ∼ g i)
        where

  colimit-family : ⟨ 𝓓∞ ⟩ → I → ⟨ 𝓔 ⟩
  colimit-family σ i = g i (⦅ σ ⦆ i)

  colimit-family-is-monotone : (σ : ⟨ 𝓓∞ ⟩) (i j : I) (l : i ⊑ j)
                             → colimit-family σ i ⊑⟨ 𝓔 ⟩ colimit-family σ j
  colimit-family-is-monotone σ i j l =
   g i (⦅ σ ⦆ i)             ⊑⟨ 𝓔 ⟩[ u ]
   g i (π l (⦅ σ ⦆ j))       ⊑⟨ 𝓔 ⟩[ v ]
   g j (ε l (π l (⦅ σ ⦆ j))) ⊑⟨ 𝓔 ⟩[ w ]
   g j (⦅ σ ⦆ j)             ∎⟨ 𝓔 ⟩
    where
     u = ≡-to-⊑ 𝓔 (ap (g i) ((π-equality σ l) ⁻¹))
     v = ≡-to-⊑ 𝓔 ((comm i j l (π l (⦅ σ ⦆ j))) ⁻¹)
     w = gm (ε l (π l (⦅ σ ⦆ j))) (⦅ σ ⦆ j) (επ-deflation l (⦅ σ ⦆ j))
      where
       gm : is-monotone (𝓓 j) 𝓔 (g j)
       gm = continuous-implies-monotone (𝓓 j) 𝓔 (g j , g-cont j)

  colimit-family-is-directed : (σ : ⟨ 𝓓∞ ⟩) → is-Directed 𝓔 (colimit-family σ)
  colimit-family-is-directed σ = I-inhabited , γ
   where
    γ : is-weakly-directed (underlying-order 𝓔) (colimit-family σ)
    γ i j = ∥∥-functor ψ (I-weakly-directed i j)
     where
      ψ : (Σ k ꞉ I , i ⊑ k × j ⊑ k)
        → (Σ k ꞉ I , colimit-family σ i ⊑⟨ 𝓔 ⟩ colimit-family σ k
                   × colimit-family σ j ⊑⟨ 𝓔 ⟩ colimit-family σ k)
      ψ (k , lᵢ , lⱼ) =
       k , colimit-family-is-monotone σ i k lᵢ ,
           colimit-family-is-monotone σ j k lⱼ

  colimit-mediating-arrow : ⟨ 𝓓∞ ⟩ → ⟨ 𝓔 ⟩
  colimit-mediating-arrow σ = ∐ 𝓔 {I} {φ} δ
   where
    φ : I → ⟨ 𝓔 ⟩
    φ i = colimit-family σ i
    δ : is-Directed 𝓔 φ
    δ = colimit-family-is-directed σ

\end{code}
