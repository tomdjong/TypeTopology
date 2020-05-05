Tom de Jong, 22 April 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module ZornsLemma
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoBasics pt fe 𝓥

open import UF-Equiv
open import UF-Size

Ω/_ : Ω 𝓤 → 𝓥 ⁺ ⊔ 𝓤 ̇
Ω/_ P = Σ Q ꞉ Ω 𝓥 , (Q holds → P holds)

open import Poset fe
open PosetAxioms

Ω/-dcpo : Ω 𝓤 → DCPO {𝓥 ⁺ ⊔ 𝓤} {𝓥}
Ω/-dcpo P = (Ω/ P) , _⊑_ , (i , pv , r , t , a) , d
 where
  _⊑_ : Ω/ P → Ω/ P → 𝓥 ̇
  (Q , f) ⊑ (R , g) = Q holds → R holds
  i : is-set (Ω/ P)
  i = subsets-of-sets-are-sets (Ω 𝓥) (λ Q → Q holds → P holds)
      (Ω-is-a-set fe pe)
      (Π-is-prop fe (λ _ → holds-is-prop P))
  pv : is-prop-valued _⊑_
  pv Q R = Π-is-prop fe (λ _ → holds-is-prop (pr₁ R))
  r : (Q : Ω/ P) → Q ⊑ Q
  r Q = id
  t : is-transitive _⊑_
  t Q R S f g = g ∘ f
  a : is-antisymmetric _⊑_
  a ((Q , i) , u) ((R , j) , v) f g =
   to-subtype-≡ (λ S → Π-is-prop fe (λ _ → holds-is-prop P))
    (to-subtype-≡ (λ A → being-a-prop-is-a-prop fe) (pe i j f g))
  d : is-directed-complete _⊑_
  d I α δ = (((∃ i ꞉ I , pr₁ (α i) holds) , ∥∥-is-a-prop) , w) , s
   where
    w : (∃ i ꞉ I , pr₁ (α i) holds) → P holds
    w = ∥∥-rec (holds-is-prop P) ω
     where
      ω : (Σ i ꞉ I , pr₁ (α i) holds) → P holds
      ω (i , x) = pr₂ (α i) x
    s : is-sup _⊑_ (((∃ i ꞉ I , pr₁ (α i) holds) , ∥∥-is-a-prop) , w) α
    s = ub , lb-of-ubs
     where
      ub : (i₀ : I)
         → α i₀ ⊑ (((∃ i ꞉ I , pr₁ (α i) holds) , ∥∥-is-a-prop) , w)
      ub i₀ x = ∣ i₀ , x ∣
      lb-of-ubs : is-lowerbound-of-upperbounds _⊑_
                    (((∃ i ꞉ I , pr₁ (α i) holds) , ∥∥-is-a-prop) , w) α
      lb-of-ubs R ub x = ∥∥-rec (holds-is-prop (pr₁ R)) γ x
       where
        γ : Σ i ꞉ I , pr₁ (α i) holds → pr₁ R holds
        γ (i , y) = ub i y

every-dcpo-has-maximal-element : (𝓤 𝓣 : Universe) → (𝓥 ⊔ 𝓤 ⊔ 𝓣) ⁺ ̇
every-dcpo-has-maximal-element 𝓤 𝓣 = (𝓓 : DCPO {𝓤} {𝓣})
                                   → Σ x ꞉ ⟨ 𝓓 ⟩ , is-maximal (underlying-order 𝓓) x

every-dcpo-has-maximal-element-implies-resizing : {𝓤 : Universe}
                                                → every-dcpo-has-maximal-element (𝓥 ⁺ ⊔ 𝓤) 𝓥
                                                → propositional-resizing 𝓤 𝓥
every-dcpo-has-maximal-element-implies-resizing {𝓤} M P i = Q , γ
 where
  Q' : ⟨ Ω/-dcpo (P , i) ⟩
  Q' = pr₁ (M (Ω/-dcpo (P , i)))
  Q : 𝓥 ̇
  Q = (pr₁ Q') holds
  Q-implies-P : Q → P
  Q-implies-P = pr₂ Q'
  γ : Q ≃ P
  γ = logically-equivalent-props-are-equivalent (holds-is-prop (pr₁ Q')) i Q-implies-P g
   where
    g : P → Q
    g p = transport (λ - → (pr₁ -) holds) (h ⊤/P (λ _ → *) ⁻¹) *
     where
      ⊤/P : Ω/ (P , i)
      ⊤/P = (𝟙 , 𝟙-is-prop) , (λ _ → p)
      h : is-maximal (underlying-order (Ω/-dcpo (P , i))) Q'
      h = pr₂ (M (Ω/-dcpo (P , i)))

\end{code}
