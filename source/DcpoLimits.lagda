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
        (⊑-refl : (i : I) → i ⊑ i)
        (⊑-trans : (i j k : I) → i ⊑ j → j ⊑ k → i ⊑ k)
--        (⊑-antisym : (i j : I) → i ⊑ j → j ⊑ i → i ≡ j)
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
       where

 𝓓∞ : DCPO {𝓥 ⊔ 𝓤 ⊔ 𝓦} {𝓥 ⊔ 𝓣}
 𝓓∞ = (X , _≼_ , pa , dc)
  where
   X : 𝓥 ⊔ 𝓤 ⊔ 𝓦 ̇
   X = Σ σ ꞉ ((i : I) → ⟨ 𝓓 i ⟩) , ((i j : I) (l : i ⊑ j) → π l (σ j) ≡ σ i)
   ⦅_⦆ : X → (i : I) → ⟨ 𝓓 i ⟩
   ⦅_⦆ = pr₁
   π-equality : (σ : X) (i j : I) (l : i ⊑ j) → π l (⦅ σ ⦆ j) ≡ ⦅ σ ⦆ i
   π-equality = pr₂
   _≼_ : X → X → 𝓥 ⊔ 𝓣 ̇
   σ ≼ τ = (i : I) → ⦅ σ ⦆ i ⊑⟨ 𝓓 i ⟩ ⦅ τ ⦆ i
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
         h = dfunext fe (λ a → π-equality (α a) i j l)
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

\end{code}
