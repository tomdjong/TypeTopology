Tom de Jong, 6 February 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module CompleteSmallLatticePropResizing where

open import SpartanMLTT

open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Size
open import UF-Retracts

open import Poset

module _
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥) -- this is just here for the poset module
        (𝓤 : Universe) -- fix a universe of "small" types
        {L : 𝓤 ̇ }
        (_⊑_ : L → L → 𝓤 ̇ ) -- our small poset
        (pa : PosetAxioms.poset-axioms fe _⊑_)
       where

 open PosetAxioms fe _⊑_

 is-set-L : is-set L
 is-set-L = pr₁ pa

 ⊑-prop-valued : is-prop-valued
 ⊑-prop-valued = pr₁ (pr₂ pa)

 ⊑-refl : is-reflexive
 ⊑-refl = pr₁ (pr₂ (pr₂ pa))

 ⊑-trans : is-transitive
 ⊑-trans = pr₁ (pr₂ (pr₂ (pr₂ pa)))

 ⊑-anti : is-antisymmetric
 ⊑-anti = pr₂ (pr₂ (pr₂ (pr₂ pa)))

 is-upperbound : {I : 𝓤 ̇ } (l : L) (α : I → L) → 𝓤 ̇
 is-upperbound l α = (i : domain α) → α i ⊑ l

 is-lowerbound-of-upperbounds : {I : 𝓤 ̇ } (l : L) (α : I → L) → 𝓤 ̇
 is-lowerbound-of-upperbounds l α = (y : L) → is-upperbound y α → l ⊑ y

 is-sup : {I : 𝓤 ̇ } → L → (I → L) → 𝓤 ̇
 is-sup s α =
  (is-upperbound s α) × (is-lowerbound-of-upperbounds s α)

 is-complete : 𝓤 ⁺ ̇
 is-complete = (I : 𝓤 ̇ ) (α : I → L)
             → Σ s ꞉ L , is-sup s α

 module _
         (c : is-complete)
        where

  ⋁ : {I : 𝓤 ̇ } → (I → L) → L
  ⋁ {I} α = pr₁ (c I α)

  ⋁-is-ub : {I : 𝓤 ̇ } (α : I → L) → is-upperbound (⋁ α) α
  ⋁-is-ub {I} α = pr₁ (pr₂ (c I α))

  ⋁-is-lb-of-ubs : {I : 𝓤 ̇ } (α : I → L)
                 → is-lowerbound-of-upperbounds (⋁ α) α
  ⋁-is-lb-of-ubs {I} α = pr₂ (pr₂ (c I α))

  bottom : L
  bottom = ⋁ {𝟘} unique-from-𝟘

  top : L
  top = ⋁ {L} id

  Ω-to-L : Ω 𝓤 → L
  Ω-to-L (P , i) = ⋁ {P} α
   where
    α : P → L
    α p = top

  _⊑Ω_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ̇
  P ⊑Ω Q = P holds → Q holds

--  Ω-to-L-is-monotone : {P Q : Ω 𝓤} → P ⊑Ω Q → Ω-to-L P ⊑ Ω-to-L Q
--  Ω-to-L-is-monotone {P} {Q} i = {!!}

{-
  Ω-to-L-reflects-order : {P Q : Ω 𝓤} → Ω-to-L P ⊑ Ω-to-L Q → P ⊑Ω Q
  Ω-to-L-reflects-order {P} {Q} u p = {!!}
   where
    e : Ω-to-L P ≡ top
    e = ⊑-anti (Ω-to-L P) top (⋁-is-ub id (Ω-to-L P))
        (⋁-is-ub (λ (x : P holds) → top) p)
    v : top ⊑ Ω-to-L Q
    v = transport (λ - → - ⊑ Ω-to-L Q) e u -}


  L-to-Ω : L → Ω 𝓤
  L-to-Ω l = top ⊑ l , ⊑-prop-valued top l

  is-non-trivial : 𝓤 ̇
  is-non-trivial = bottom ≢ top

  Ω-retract-of-L : propext 𝓤 → is-non-trivial → Ω 𝓤 ◁ L
  Ω-retract-of-L pe nt = r , (s , rs)
   where
    r : L → Ω 𝓤
    r = L-to-Ω
    s : Ω 𝓤 → L
    s = Ω-to-L
    rs : (P : Ω 𝓤) → r (s P) ≡ P
    rs (P , i) = to-subtype-≡ (λ _ → being-a-prop-is-a-prop fe) γ
     where
      α : P → L
      α p = top
      γ : (top ⊑ ⋁ α) ≡ P
      γ = pe (⊑-prop-valued top (⋁ α)) i f g
       where
        f : top ⊑ ⋁ α → P
        f u = {!!}
         {-
             Idea:
              top ≡ ⋁ {𝟙} (λ * → top) ⊑ ⋁ {P} α
                iff
              𝟙 ⊑ P (since ⋁ is an order embedding)
         -}

        g : P → top ⊑ ⋁ α
        g p = ⋁-is-ub α p


\end{code}
