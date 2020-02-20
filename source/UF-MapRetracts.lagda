Tom de Jong, 16 February 2020 -

Retracts of maps.

f is a retract of g if there is a commutative diagram:

X --s--> W --r--> X # composition is id
|        |        |
f        g        f
|        |        |
∨       ∨        ∨
Y --u--> Z --v--> Y # composition is id

This could be developed further, including notation for composing such retracts
of maps. But the following suffices for our (current) purposes.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-MapRetracts where

open import SpartanMLTT
open import UF-Base
open import UF-Retracts

module _
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {W : 𝓦 ̇ } {Z : 𝓣 ̇ }
       where

 map-retract_of_ : (X → Y) → (W → Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 map-retract_of_ f g = Σ s ꞉ (X ◁ W) , Σ t ꞉ (Y ◁ Z) ,
  g ∘ section s ∼ section t ∘ f
  ×
  f ∘ retraction s ∼ retraction t ∘ g

 _◁₁_ : (X → Y) → (W → Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 f ◁₁ g = map-retract f of g

 infix 0 _◁₁_

 domains-retract : {f : X → Y} {g : W → Z} → f ◁₁ g → X ◁ W
 domains-retract (s , t , c , d) = s

 codomains-retract : {f : X → Y} {g : W → Z} → f ◁₁ g → Y ◁ Z
 codomains-retract (s , t , c , d) = t

 lhs-commutes : {f : X → Y} {g : W → Z} (r : f ◁₁ g)
              → g ∘ section (domains-retract r)
              ∼ section (codomains-retract r) ∘ f
 lhs-commutes (s , t , c , d) = c

 rhs-commutes : {f : X → Y} {g : W → Z} (r : f ◁₁ g)
              → f ∘ retraction (domains-retract r)
              ∼ retraction (codomains-retract r) ∘ g
 rhs-commutes (s , t , c , d) = d

\end{code}
