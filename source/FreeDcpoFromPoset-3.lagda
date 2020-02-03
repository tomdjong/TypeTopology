Tom de Jong
30-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc hiding (_≈_)

module FreeDcpoFromPoset-3
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe) -- universe where the index types for directedness
                        -- completeness live
       where

open import Poset fe
open import Dcpo pt fe 𝓥

-- open import FreeDcpoFromPoset-1 pt fe 𝓥 public
open import FreeDcpoFromPoset-2 pt fe pe 𝓥 public

open import UF-Quotient

open PropositionalTruncation pt

module FreeDcpoFromPoset-Setup-3
        {P : 𝓤 ̇ }
        (_≤_ : P → P → 𝓣 ̇ )
        ((is-set-P , ≤-prop-valued ,
          ≤-refl , ≤-trans , ≤-anti) : PosetAxioms.poset-axioms _≤_)
       where

 open FreeDcpoFromPoset-Setup-1 (_≤_) (is-set-P , ≤-prop-valued ,
          ≤-refl , ≤-trans , ≤-anti)
 open FreeDcpoFromPoset-Setup-2 (_≤_) (is-set-P , ≤-prop-valued ,
          ≤-refl , ≤-trans , ≤-anti)

 open Quotient pt (λ 𝓤 𝓥 → fe) pe 𝓕 _≈_
               ≈-is-prop-valued
               ≈-is-reflexive
               ≈-is-symmetric
               ≈-is-transitive

 ∐-in-𝓕 : {J : 𝓥 ̇ } (β : J → 𝓕) (δ : is-directed _≼_ β) → 𝓕
 ∐-in-𝓕 {J} β δ = K , γ , κ , φ
  where
   I : J → 𝓥 ̇
   I j = pr₁ (β j)
   α : (j : J) → I j → P
   α j = pr₁ (pr₂ (β j))
   ε : (j : J) → is-directed _≤_ (α j)
   ε j = pr₂ (pr₂ (β j))
   K : 𝓥 ̇
   K = Σ \(j : J) → I j
   γ : K → P
   γ (j , i) = α j i
   κ : ∥ K ∥
   κ = do
    j ← directed-implies-inhabited _≼_ β δ
    i ← directed-implies-inhabited _≤_ (α j) (ε j)
    ∣ j , i ∣
   φ : is-weakly-directed _≤_ γ
   φ (j₁ , i₁) (j₂ , i₂) = do
    (j , m , n) ← directed-implies-weakly-directed _≼_ β δ j₁ j₂
    (i₃ , u)    ← m i₁
    (i₄ , v)    ← n i₂
    (i , μ , ν) ← directed-implies-weakly-directed _≤_ (α j) (ε j) i₃ i₄
    a           ← ∣ ≤-trans (γ (j₁ , i₁)) (γ (j , i₃)) (γ (j , i)) u μ ∣
    b           ← ∣ ≤-trans (γ (j₂ , i₂)) (γ (j , i₄)) (γ (j , i)) v ν ∣
    ∣ (j , i) , a , b ∣

   {-
    ∥∥-rec ∥∥-is-a-prop ϕ (directed-implies-weakly-directed _≼_ β δ j₁ j₂)
     where
      ϕ : (Σ \(j : J) → β j₁ ≼ β j × β j₂ ≼ β j)
        → ∃ \(k : K) → γ (j₁ , i₁) ≤ γ k × γ (j₂ , i₂) ≤ γ k
      ϕ (j , m , n) = ∥∥-rec ∥∥-is-a-prop ψ₁ (m i₁)
       where
        ψ₁ : (Σ \(i : I j) → α j₁ i₁ ≤ α j i)
           → ∃ \(k : K) → γ (j₁ , i₁) ≤ γ k × γ (j₂ , i₂) ≤ γ k
        ψ₁ (i₃ , u) = ∥∥-rec ∥∥-is-a-prop ψ₂ (n i₂)
         where
          ψ₂ : (Σ \(i : I j) → α j₂ i₂ ≤ α j i)
             → ∃ \(k : K) → γ (j₁ , i₁) ≤ γ k × γ (j₂ , i₂) ≤ γ k
          ψ₂ (i₄ , v) =
           ∥∥-rec ∥∥-is-a-prop ψ
           (directed-implies-weakly-directed _≤_ (α j) (ε j) i₃ i₄)
            where
             ψ : (Σ \(i : I j) → α j i₃ ≤ α j i × α j i₄ ≤ α j i)
               → ∃ \(k : K) → γ (j₁ , i₁) ≤ γ k × γ (j₂ , i₂) ≤ γ k
             ψ (i , μ , ν) = ∣ (j , i) , a , b ∣
              where
               a : γ (j₁ , i₁) ≤ γ (j , i)
               a = ≤-trans (γ (j₁ , i₁)) (γ (j , i₃)) (γ (j , i)) u μ
               b : γ (j₂ , i₂) ≤ γ (j , i)
               b = ≤-trans (γ (j₂ , i₂)) (γ (j , i₄)) (γ (j , i)) v ν
    -}

 ∐-in-𝓕-is-ub : {J : 𝓥 ̇ } (β : J → 𝓕) (δ : is-directed _≼_ β)
              → is-upperbound _≼_ (∐-in-𝓕 β δ) β
 ∐-in-𝓕-is-ub β δ j = γ
  where
   γ : β j ≼ ∐-in-𝓕 β δ
   γ i = ∣ (j , i) , (≤-refl _) ∣

 ∐-in-𝓕-is-lb-of-ubs : {J : 𝓥 ̇ } (β : J → 𝓕) (δ : is-directed _≼_ β)
                     → is-lowerbound-of-upperbounds _≼_ (∐-in-𝓕 β δ) β
 ∐-in-𝓕-is-lb-of-ubs β δ α l = γ
  where
   γ : ∐-in-𝓕 β δ ≼ α
   γ (j , i) = l j i

 ∐-in-𝓕/≈ : {I : 𝓥 ̇ } (α : I → 𝓕/≈) (δ : is-directed _⊑_ α) → 𝓕/≈
 ∐-in-𝓕/≈ {I} α δ = {!!}

\end{code}
