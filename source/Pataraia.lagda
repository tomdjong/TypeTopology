Tom de Jong, 22 April 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module Pataraia
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

is-inflationary : (𝓓 : DCPO {𝓤} {𝓣}) (f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩) → 𝓤 ⊔ 𝓣 ̇
is-inflationary 𝓓 f = (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ f x

Pataraia-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓤 ⊔ 𝓣 ̇
Pataraia-dcpo 𝓓 = Σ g ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩) , is-monotone 𝓓 𝓓 g
                      × is-inflationary 𝓓 g
                      × ((f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩)
                            → is-monotone 𝓓 𝓓 f
                            → is-inflationary 𝓓 f
                            → ((x : ⟨ 𝓓 ⟩) → f x ⊑⟨ 𝓓 ⟩ g x))

Pataraia-key-statement : (𝓤 𝓣 : Universe) → (𝓥 ⊔ 𝓤 ⊔ 𝓣) ⁺ ̇
Pataraia-key-statement 𝓤 𝓣 = (𝓓 : DCPO {𝓤} {𝓣}) → ∥ ⟨ 𝓓 ⟩ ∥ → Pataraia-dcpo 𝓓

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

Pataraia-implies-resizing : Pataraia-key-statement (𝓥 ⁺ ⊔ 𝓤) (𝓥)
                          → propositional-resizing 𝓤 𝓥
Pataraia-implies-resizing Ψ P i = (pr₁ (G ⊥/P) holds) , γ
 where
  ⊥/P : Ω/ (P , i)
  ⊥/P = (𝟘 , 𝟘-is-prop) , 𝟘-elim
  G : Ω/ (P , i) → Ω/ (P , i)
  G = pr₁ (Ψ (Ω/-dcpo (P , i)) ∣ ⊥/P ∣)
  γ : pr₁ (pr₁ (G ⊥/P)) ≃ P
  γ = logically-equivalent-props-are-equivalent
       (holds-is-prop (pr₁ (G ⊥/P))) i
       f g
   where
    f : pr₁ (G ⊥/P) holds → P
    f = pr₂ (G ⊥/P)
    g : P → pr₁ (G ⊥/P) holds
    g p = h *
     where
      ⊤/P : Ω/ (P , i)
      ⊤/P = (𝟙 , 𝟙-is-prop) , (λ _ → p)
      G' : Ω/ (P , i) → Ω/ (P , i)
      G' Q = ⊤/P
      h : 𝟙{𝓥} → pr₁ (G ⊥/P) holds
      h = Φ G' mon inf ⊥/P
       where
        Φ : (G₁ : ⟨ Ω/-dcpo (P , i) ⟩ → ⟨ Ω/-dcpo (P , i) ⟩)
             → is-monotone (Ω/-dcpo (P , i)) (Ω/-dcpo (P , i)) G₁
             → is-inflationary (Ω/-dcpo (P , i)) G₁
             → ((x : ⟨ Ω/-dcpo (P , i) ⟩)
                  → underlying-order (Ω/-dcpo (P , i)) (G₁ x) (G x))
        Φ = pr₂ (pr₂ (pr₂ (Ψ (Ω/-dcpo (P , i)) ∣ ⊥/P ∣)))
        mon : is-monotone (Ω/-dcpo (P , i)) (Ω/-dcpo (P , i)) G'
        mon Q R _ = id
        inf : is-inflationary (Ω/-dcpo (P , i)) G'
        inf Q q = *

\end{code}
