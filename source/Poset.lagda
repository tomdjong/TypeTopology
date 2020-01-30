Tom de Jong, 30 January 2020

Separate file for poset axioms.
This used to be part of Dcpo.lagda

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

open import UF-Subsingletons hiding (⊥)
open import UF-Subsingletons-FunExt

module Poset
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       where

 module PosetAxioms
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
        where

  is-prop-valued : 𝓤 ⊔ 𝓣 ̇
  is-prop-valued = (x y : D) → is-prop(x ⊑ y)

  is-reflexive : 𝓤 ⊔ 𝓣 ̇
  is-reflexive = (x : D) → x ⊑ x

  is-transitive : 𝓤 ⊔ 𝓣 ̇
  is-transitive = (x y z : D) → x ⊑ y → y ⊑ z → x ⊑ z

  is-antisymmetric : 𝓤 ⊔ 𝓣 ̇
  is-antisymmetric = (x y : D) → x ⊑ y → y ⊑ x → x ≡ y

  poset-axioms : 𝓤 ⊔ 𝓣 ̇
  poset-axioms = is-set D
               × is-prop-valued
               × is-reflexive
               × is-transitive
               × is-antisymmetric

  poset-axioms-is-a-prop : is-prop (poset-axioms)
  poset-axioms-is-a-prop = iprops-are-props γ
   where
    γ : poset-axioms → is-prop poset-axioms
    γ (s , p , r , t , a) = ×-is-prop (being-set-is-a-prop fe)
                            (×-is-prop
                              (Π-is-prop fe
                                (λ x → Π-is-prop fe
                                (λ y → being-a-prop-is-a-prop fe)))
                            (×-is-prop
                              (Π-is-prop fe
                                (λ x → p x x))
                            (×-is-prop
                              (Π-is-prop fe
                                (λ x → Π-is-prop fe
                                (λ y → Π-is-prop fe
                                (λ z → Π-is-prop fe
                                (λ u → Π-is-prop fe
                                (λ v → p x z))))))
                            (Π-is-prop fe
                            (λ x → Π-is-prop fe
                            (λ y → Π-is-prop fe
                            (λ u → Π-is-prop fe
                            (λ v → s))))))))

\end{code}
