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
        (⊑-directed : (i j : I) → ∃ k ꞉ I , i ⊑ k × j ⊑ k)
        (𝓓 : I → DCPO {𝓤} {𝓣})
        (ε : {i j : I} → i ⊑ j → ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩)
        (π : {i j : I} → i ⊑ j → ⟨ 𝓓 j ⟩ → ⟨ 𝓓 i ⟩)
        (επ : {i j : I} (l : i ⊑ j) → (x : ⟨ 𝓓 j ⟩) → ε l (π l x) ⊑⟨ 𝓓 j ⟩ x )
        (πε : {i j : I} (l : i ⊑ j) → π l ∘ ε l ∼ id )
        (ε-continuity : {i j : I} (l : i ⊑ j)
                      → is-continuous (𝓓 i) (𝓓 j) (ε {i} {j} l))
        (π-continuity : {i j : I} (l : i ⊑ j)
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

 family-at-ith-component : {𝓐 : 𝓥 ̇ } (α : 𝓐 → 𝓓∞-carrier) (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
 family-at-ith-component α i a = ⦅ α a ⦆ i

 _≼_ : 𝓓∞-carrier → 𝓓∞-carrier → 𝓥 ⊔ 𝓣 ̇
 σ ≼ τ = (i : I) → ⦅ σ ⦆ i ⊑⟨ 𝓓 i ⟩ ⦅ τ ⦆ i

 family-at-ith-component-is-directed : {𝓐 : 𝓥 ̇ } {α : 𝓐 → 𝓓∞-carrier}
                                       (δ : is-directed _≼_ α) (i : I)
                                     → is-Directed (𝓓 i) (family-at-ith-component α i)
 family-at-ith-component-is-directed {𝓐} {α} δ i =
  (directed-implies-inhabited _≼_ α δ) , γ
   where
    γ : {!!}
    γ = {!!}

{-

     β : (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
     β i a = ⦅ α a ⦆ i
     δ' : (i : I) → is-Directed (𝓓 i) (β i)
     δ' i = (directed-implies-inhabited _≼_ α δ) , γ
      where
       γ : is-weakly-directed (underlying-order (𝓓 i)) (β i)
       γ a₁ a₂ = ∥∥-functor g (directed-implies-weakly-directed _≼_ α δ a₁ a₂)
        where
         g : (Σ a ꞉ 𝓐 , (α a₁ ≼ α a) × (α a₂ ≼ α a))
           → (Σ a ꞉ 𝓐 , (β i a₁ ⊑⟨ 𝓓 i ⟩ β i a) × (β i a₂ ⊑⟨ 𝓓 i ⟩ β i a) )
         g (a , l , k) = a , l i , k i
     σ : X
     σ = (λ i → ∐ (𝓓 i) (δ' i)) , φ
      where
       φ : (i j : I) (l : i ⊑ j) → π l (∐ (𝓓 j) (δ' j)) ≡ ∐ (𝓓 i) (δ' i)
       φ i j l = π l (∐ (𝓓 j) (δ' j))       ≡⟨ eq₁ ⟩
                 ∐ (𝓓 i) {𝓐} {π l ∘ β j} δ₁ ≡⟨ eq₂ ⟩
                 ∐ (𝓓 i) {𝓐} {β i} δ₂       ≡⟨ eq₃ ⟩
                 ∐ (𝓓 i) {𝓐} {β i} (δ' i)   ∎
        where
         δ₁ : is-Directed (𝓓 i) (π l ∘ β j)
         δ₁ = image-is-directed' (𝓓 j) (𝓓 i) ((π l) , (π-continuity l)) (δ' j)
         h : π l ∘ β j ≡ β i
         h = dfunext fe (λ a → π-equality (α a) l)
         δ₂ : is-Directed (𝓓 i) (β i)
         δ₂ = transport (is-Directed (𝓓 i)) h δ₁
         eq₁ = continuous-∐-≡ (𝓓 j) (𝓓 i) ((π l) , (π-continuity l)) (δ' j)
         eq₂ = ∐-family-≡ (𝓓 i) (π l ∘ β j) (β i) h δ₁
         eq₃ = ∐-independent-of-directedness-witness (𝓓 i) δ₂ (δ' i)

-}

 𝓓∞ : DCPO {𝓥 ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⊔ 𝓣}
 𝓓∞ = (X , _≼_ , pa , dc)
  where
   X : 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   X = Σ σ ꞉ ((i : I) → ⟨ 𝓓 i ⟩) , ((i j : I) (l : i ⊑ j) → π l (σ j) ≡ σ i)
   pa : PosetAxioms.poset-axioms _≼_
   pa = sl , pv , r , t , a
    where
     open PosetAxioms {𝓥 ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⊔ 𝓣} {X} _≼_
     sl : is-set X
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
     a σ τ l k = to-subtype-≡
                  (λ σ → Π-is-prop fe
                          (λ i → Π-is-prop fe
                          (λ j → Π-is-prop fe
                          (λ _ → sethood (𝓓 i)))))
                  (dfunext fe ((λ i → antisymmetry (𝓓 i) (⦅ σ ⦆ i) (⦅ τ ⦆ i)
                                      (l i) (k i))))
   dc : is-directed-complete _≼_
   dc 𝓐 α δ = σ , ub , lb-of-ubs
    where
     β : (i : I) → 𝓐 → ⟨ 𝓓 i ⟩
     β i a = ⦅ α a ⦆ i
     δ' : (i : I) → is-Directed (𝓓 i) (β i)
     δ' i = (directed-implies-inhabited _≼_ α δ) , γ
      where
       γ : is-weakly-directed (underlying-order (𝓓 i)) (β i)
       γ a₁ a₂ = ∥∥-functor g (directed-implies-weakly-directed _≼_ α δ a₁ a₂)
        where
         g : (Σ a ꞉ 𝓐 , (α a₁ ≼ α a) × (α a₂ ≼ α a))
           → (Σ a ꞉ 𝓐 , (β i a₁ ⊑⟨ 𝓓 i ⟩ β i a) × (β i a₂ ⊑⟨ 𝓓 i ⟩ β i a) )
         g (a , l , k) = a , l i , k i
     σ : X
     σ = (λ i → ∐ (𝓓 i) (δ' i)) , φ
      where
       φ : (i j : I) (l : i ⊑ j) → π l (∐ (𝓓 j) (δ' j)) ≡ ∐ (𝓓 i) (δ' i)
       φ i j l = π l (∐ (𝓓 j) (δ' j))       ≡⟨ eq₁ ⟩
                 ∐ (𝓓 i) {𝓐} {π l ∘ β j} δ₁ ≡⟨ eq₂ ⟩
                 ∐ (𝓓 i) {𝓐} {β i} δ₂       ≡⟨ eq₃ ⟩
                 ∐ (𝓓 i) {𝓐} {β i} (δ' i)   ∎
        where
         δ₁ : is-Directed (𝓓 i) (π l ∘ β j)
         δ₁ = image-is-directed' (𝓓 j) (𝓓 i) ((π l) , (π-continuity l)) (δ' j)
         h : π l ∘ β j ≡ β i
         h = dfunext fe (λ a → π-equality (α a) l)
         δ₂ : is-Directed (𝓓 i) (β i)
         δ₂ = transport (is-Directed (𝓓 i)) h δ₁
         eq₁ = continuous-∐-≡ (𝓓 j) (𝓓 i) ((π l) , (π-continuity l)) (δ' j)
         eq₂ = ∐-family-≡ (𝓓 i) (π l ∘ β j) (β i) h δ₁
         eq₃ = ∐-independent-of-directedness-witness (𝓓 i) δ₂ (δ' i)
     ub : (a : 𝓐) → α a ≼ σ
     ub a i = ∐-is-upperbound (𝓓 i) (δ' i) a
     lb-of-ubs : is-lowerbound-of-upperbounds _≼_ σ α
     lb-of-ubs τ ub i = ∐-is-lowerbound-of-upperbounds (𝓓 i) (δ' i) (⦅ τ ⦆ i)
                        (λ a → ub a i)

 π∞ : (i : I) → ⟨ 𝓓∞ ⟩ → ⟨ 𝓓 i ⟩
 π∞ i (σ , _) = σ i

 open import UF-ImageAndSurjection
 open ImageAndSurjection pt

 κ : {i j : I} → ⟨ 𝓓 i ⟩ → (Σ k ꞉ I , i ⊑ k × j ⊑ k) → ⟨ 𝓓 j ⟩
 κ x (k , lᵢ , lⱼ) = π lⱼ (ε lᵢ x)

 κ-wconstant : (i j : I) (x : ⟨ 𝓓 i ⟩) → wconstant (κ x)
 κ-wconstant i j x (k , lᵢ , lⱼ) (k' , lᵢ' , lⱼ') = ∥∥-rec (sethood (𝓓 j)) γ (⊑-directed k k')
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
     e₁ = ap (π lⱼ) (πε u (ε lᵢ x) ⁻¹)
     e₂ = π-comp lⱼ u (ε u (ε lᵢ x))
     e₃ = ap (π (⊑-trans lⱼ u)) (ε-comp lᵢ u x)
     e₄ = ap (π (⊑-trans lⱼ u)) (ap (λ - → ε - x)
          (⊑-prop-valued i m (⊑-trans lᵢ u) (⊑-trans lᵢ' u')))
     e₅ = ap (π (⊑-trans lⱼ u)) ((ε-comp lᵢ' u' x) ⁻¹)
     e₆ = ap (λ - → π - _) (⊑-prop-valued j m (⊑-trans lⱼ u) (⊑-trans lⱼ' u'))
     e₇ = (π-comp lⱼ' u' (ε u' (ε lᵢ' x))) ⁻¹
     e₈ = ap (π lⱼ') (πε u' (ε lᵢ' x))

 ρ : (i j : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓓 j ⟩
 ρ i j x = wconstant-from-∥∥-to-set (sethood (𝓓 j)) (κ x)
            (κ-wconstant i j x) (⊑-directed i j)

 ρ-in-terms-of-κ : {i j k : I} (lᵢ : i ⊑ k) (lⱼ : j ⊑ k) (x : ⟨ 𝓓 i ⟩)
                 → ρ i j x ≡ κ x (k , lᵢ , lⱼ)
 ρ-in-terms-of-κ {i} {j} {k} lᵢ lⱼ x =
  ρ i j x             ≡⟨ refl ⟩
  ν (⊑-directed i j)  ≡⟨ p ⟩
  ν ∣ (k , lᵢ , lⱼ) ∣ ≡⟨ q ⟩
  κ x (k , lᵢ , lⱼ)   ∎
   where
    s : is-set ⟨ 𝓓 j ⟩
    s = sethood (𝓓 j)
    ω : wconstant (κ x)
    ω = κ-wconstant i j x
    ν : (∃ k' ꞉ I , i ⊑ k' × j ⊑ k') → ⟨ 𝓓 j ⟩
    ν = wconstant-from-∥∥-to-set s (κ x) ω
    p = ap ν (∥∥-is-a-prop (⊑-directed i j) ∣ k , lᵢ , lⱼ ∣)
    q = wconstant-to-set-factors-through-∥∥ s (κ x) ω (k , lᵢ , lⱼ)

 ε∞ : (i : I) → ⟨ 𝓓 i ⟩ → ⟨ 𝓓∞ ⟩
 ε∞ i x = σ , φ
  where
   σ : (j : I) → ⟨ 𝓓 j ⟩
   σ j = ρ i j x
   φ : (j₁ j₂ : I) (l : j₁ ⊑ j₂) → π l (σ j₂) ≡ σ j₁
   φ j₁ j₂ l = ∥∥-rec (sethood (𝓓 j₁)) γ (⊑-directed i j₂)
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

 π∞ε∞ : {i : I} → π∞ i ∘ ε∞ i ∼ id
 π∞ε∞ {i} x = π∞ i (ε∞ i x)             ≡⟨ refl ⟩
              ⦅ ε∞ i x ⦆ i              ≡⟨ refl ⟩
              ρ i i x                   ≡⟨ ρ-in-terms-of-κ ⊑-refl ⊑-refl x ⟩
              κ x (i , ⊑-refl , ⊑-refl) ≡⟨ refl ⟩
              π ⊑-refl (ε ⊑-refl x)     ≡⟨ πε ⊑-refl x ⟩
              x                         ∎

 ε∞π∞ : {i : I} (σ : ⟨ 𝓓∞ ⟩) → ε∞ i (π∞ i σ) ⊑⟨ 𝓓∞ ⟩ σ
 ε∞π∞ {i} σ j = ∥∥-rec (prop-valuedness (𝓓 j) (⦅ ε∞ i (π∞ i σ) ⦆ j) (⦅ σ ⦆ j)) γ
                 (⊑-directed i j)
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
     u₃ = continuous-implies-monotone (𝓓 k) (𝓓 j) (π lⱼ , π-continuity lⱼ)
           (ε lᵢ (π lᵢ (⦅ σ ⦆ k))) (⦅ σ ⦆ k) (επ lᵢ (⦅ σ ⦆ k))
     u₄ = ≡-to-⊑ (𝓓 j) (π-equality σ lⱼ)

 π∞-continuity : (i : I) → is-continuous 𝓓∞ (𝓓 i) (π∞ i)
 π∞-continuity i I α δ = ub , lb-of-ubs
  where
   ub : (j : I) → π∞ i (α j) ⊑⟨ 𝓓 i ⟩ π∞ i (∐ 𝓓∞ {I} {α} δ)
   ub j = π∞ i (α j) ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          ⦅ α j ⦆ i ⊑⟨ 𝓓 i ⟩[ ∐-is-upperbound (𝓓 i) {!δ!} {!!} ]
          {!!} ⊑⟨ 𝓓 i ⟩[ {!!} ]
          {!!} ⊑⟨ 𝓓 i ⟩[ {!!} ]
          ⦅ ∐ 𝓓∞ {I} {α} δ ⦆ i ⊑⟨ 𝓓 i ⟩[ reflexivity (𝓓 i) _ ]
          π∞ i (∐ 𝓓∞ {I} {α} δ) ∎⟨ 𝓓 i ⟩
   lb-of-ubs : {!!}
   lb-of-ubs = {!!}

\end{code}
