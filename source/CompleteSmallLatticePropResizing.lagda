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

  Ω-to-L-is-monotone : {P Q : Ω 𝓤} → P ⊑Ω Q → Ω-to-L P ⊑ Ω-to-L Q
  Ω-to-L-is-monotone {P} {Q} u = ⋁-is-lb-of-ubs α (Ω-to-L Q) γ
   where
    α : P holds → L
    α p = top
    γ : P holds → top ⊑ Ω-to-L Q
    γ p = ⋁-is-ub β (u p)
     where
      β : Q holds → L
      β q = top

  -- This just says that the Ω-to-L map reflects the order, i.e. it is an order
  -- embedding.
  is-strongly-non-trivial : 𝓤 ⁺ ̇
  is-strongly-non-trivial = (P Q : Ω 𝓤) → Ω-to-L P ⊑ Ω-to-L Q → P ⊑Ω Q

  L-to-Ω : L → Ω 𝓤
  L-to-Ω l = top ⊑ l , ⊑-prop-valued top l

  is-non-trivial : 𝓤 ̇
  is-non-trivial = bottom ≡ top → 𝟘 {𝓤}

  strongly-non-trivial-implies-non-trivial : is-strongly-non-trivial → is-non-trivial
  strongly-non-trivial-implies-non-trivial snt e = u *
   where
    u : ⊤ ⊑Ω ⊥
    u = snt ⊤ ⊥ v
     where
      v : Ω-to-L ⊤ ⊑ Ω-to-L ⊥
      v = ⋁-is-lb-of-ubs (λ _ → top) (Ω-to-L ⊥) γ
       where
        γ : ⊤ holds → top ⊑ Ω-to-L ⊥
        γ * = transport (λ - → - ⊑ Ω-to-L ⊥) e
              (⋁-is-lb-of-ubs unique-from-𝟘 (Ω-to-L ⊥) 𝟘-induction)

  Ω-retract-of-L : propext 𝓤 → is-strongly-non-trivial → Ω 𝓤 ◁ L
  Ω-retract-of-L pe snt = r , (s , rs)
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
        g : P → top ⊑ ⋁ α
        g p = ⋁-is-ub α p
        f : top ⊑ ⋁ α → P
        f u = snt ⊤ (P , i) v *
         where
          ⌜top⌝ : 𝟙{𝓤} → L
          ⌜top⌝ _ = top
          e : top ≡ ⋁ ⌜top⌝
          e = ⊑-anti top (⋁ ⌜top⌝) (⋁-is-ub ⌜top⌝ *) (⋁-is-ub id (⋁ ⌜top⌝))
          v : ⋁ ⌜top⌝ ⊑ ⋁ α
          v = transport (λ - → - ⊑ ⋁ α) e u

  strongly-non-trivial-implies-Ω-resizing : propext 𝓤
                                          → is-strongly-non-trivial → Ω 𝓤 has-size 𝓤
  strongly-non-trivial-implies-Ω-resizing pe snt =
   retract-gives-has-size is-set-L (Ω-retract-of-L pe snt)


\end{code}
