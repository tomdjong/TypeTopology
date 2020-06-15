Tom de Jong

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoSize2
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
        (pe : propext 𝓥)
        (PE : PropExt)
       where

open PropositionalTruncation pt

open import Poset fe
open PosetAxioms

open import Dcpo pt fe 𝓥
open import DcpoBasics pt fe 𝓥
open import DcpoLifting pt fe 𝓥 pe
open import Lifting 𝓥 hiding (⊥)
open import LiftingMiscelanea-PropExt-FunExt 𝓥 pe fe

open import UF-Equiv
open import UF-Size

every-pointed-dcpo-has-maximal-element-statement : (𝓤 𝓣 : Universe)
                                                 → (𝓥 ⊔ 𝓤 ⊔ 𝓣) ⁺ ̇
every-pointed-dcpo-has-maximal-element-statement 𝓤 𝓣 =
 (𝓓 : DCPO⊥ {𝓤} {𝓣}) → ∃ x ꞉ ⟪ 𝓓 ⟫ , is-maximal (underlying-order (𝓓 ⁻)) x

open import UF-UniverseEmbedding
open import UF-EquivalenceExamples
open import UF-Equiv-FunExt
open import UF-Embeddings

-- Theorem 2
every-dcpo-has-maximal-element-implies-resizing : {𝓤 : Universe}
                                                → every-pointed-dcpo-has-maximal-element-statement
                                                   (𝓥 ⁺ ⊔ 𝓤) (𝓥 ⁺ ⊔ 𝓤)
                                                → propositional-resizing 𝓤 𝓥
every-dcpo-has-maximal-element-implies-resizing {𝓤} M P i =
 ∥∥-rec (prop-has-size-is-a-prop PE (λ _ _ → fe) P i 𝓥) γ (M 𝓛P-DCPO⊥)
  where
   𝓛P-DCPO⊥ : DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⁺ ⊔ 𝓤}
   𝓛P-DCPO⊥ = 𝓛-DCPO⊥ (props-are-sets i)
   γ : (Σ x ꞉ 𝓛 P , is-maximal _⊑'_ x) → P has-size 𝓥
   γ (Q' , Q'-is-max) = Q , ψ
    where
     Q : 𝓥 ̇
     Q = is-defined Q'
     ψ : Q ≃ P
     ψ = logically-equivalent-props-are-equivalent
          (being-defined-is-a-prop Q')
          i (value Q') g
      where
       g : P → Q
       g p = transport is-defined e *
        where
         e : η p ≡ Q'
         e = (Q'-is-max (η p) u) ⁻¹
          where
           u : Q' ⊑' η p
           u q = ⋍-to-≡
                  (logically-equivalent-props-are-equivalent
                   (being-defined-is-a-prop Q')
                   (being-defined-is-a-prop (η p))
                   (λ _ → *) (λ _ → q)
                  , dfunext fe (λ _ → i _ _))

\end{code}

\begin{code}

is-inflationary : (𝓓 : DCPO {𝓤} {𝓣}) → (⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩) → 𝓤 ⊔ 𝓣 ̇
is-inflationary 𝓓 f = (x : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ f x

every-dcpo-has-a-greatest-monotone-inflationary-endomap-statement : (𝓤 𝓣 : Universe)
                                                                  → (𝓥 ⊔ 𝓤 ⊔ 𝓣) ⁺ ̇
every-dcpo-has-a-greatest-monotone-inflationary-endomap-statement 𝓤 𝓣 =
 (𝓓 : DCPO {𝓤} {𝓣}) → Σ g ꞉ (⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩) ,
                           is-monotone 𝓓 𝓓 g
                         × is-inflationary 𝓓 g
                         × ((f : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩) → is-monotone 𝓓 𝓓 f
                                                → is-inflationary 𝓓 f
                                                → (x : ⟨ 𝓓 ⟩) → f x ⊑⟨ 𝓓 ⟩ g x)

every-dcpo-has-a-greatest-monotone-inflationary-endomap-implies-resizing :
   {𝓤 : Universe}
 → every-dcpo-has-a-greatest-monotone-inflationary-endomap-statement
    (𝓥 ⁺ ⊔ 𝓤) (𝓥 ⁺ ⊔ 𝓤)
 → propositional-resizing 𝓤 𝓥
every-dcpo-has-a-greatest-monotone-inflationary-endomap-implies-resizing {𝓤} G P i =
 Q , γ
  where
   ⊥P : 𝓛 P
   ⊥P = ⊥ (𝓛-DCPO⊥ (props-are-sets i))
   𝓛P-DCPO : DCPO {𝓥 ⁺ ⊔ 𝓤} {𝓥 ⁺ ⊔ 𝓤}
   𝓛P-DCPO = 𝓛-DCPO (props-are-sets i)
   g : 𝓛 P → 𝓛 P
   g = pr₁ (G 𝓛P-DCPO)
   Q : 𝓥 ̇
   Q = is-defined (g ⊥P)
   γ : Q ≃ P
   γ = logically-equivalent-props-are-equivalent
        (being-defined-is-a-prop (g ⊥P)) i
        u v
    where
     u : Q → P
     u = value (g ⊥P)
     v : P → Q
     v p = transport is-defined e *
      where
       f : 𝓛 P → 𝓛 P
       f _ = η p
       e : η p ≡ g ⊥P
       e = l *
        where
         l : η p ⊑⟨ 𝓛P-DCPO ⟩ g ⊥P
         l = g-is-greatest f f-is-monotone f-is-inflationary ⊥P
          where
           g-is-greatest : (h : ⟨ 𝓛P-DCPO ⟩ → ⟨ 𝓛P-DCPO ⟩)
                         → is-monotone 𝓛P-DCPO 𝓛P-DCPO h
                         → is-inflationary 𝓛P-DCPO h
                         → (x : ⟨ 𝓛P-DCPO ⟩) → h x ⊑⟨ 𝓛P-DCPO ⟩ g x
           g-is-greatest = pr₂ (pr₂ (pr₂ (G 𝓛P-DCPO)))
           f-is-monotone : is-monotone 𝓛P-DCPO 𝓛P-DCPO f
           f-is-monotone x y l = reflexivity 𝓛P-DCPO (η p)
           f-is-inflationary : is-inflationary 𝓛P-DCPO f
           f-is-inflationary (R , ϕ , j) r = ⋍-to-≡ (a , b)
            where
             a : R ≃ 𝟙{𝓥}
             a = logically-equivalent-props-are-equivalent j 𝟙-is-prop
                  (λ _ → *) (λ _ → r)
             b : ϕ ≡ (λ _ → p) ∘ ⌜ a ⌝
             b = dfunext fe (λ r' → i (ϕ r') p)
   g-is-monotone : is-monotone 𝓛P-DCPO 𝓛P-DCPO g
   g-is-monotone = pr₁ (pr₂ (G 𝓛P-DCPO))
   g-is-inflationary : is-inflationary 𝓛P-DCPO g
   g-is-inflationary = pr₁ (pr₂ (pr₂ (G 𝓛P-DCPO)))

\end{code}
