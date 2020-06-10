Tom de Jong, 10 June 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoExperiment
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓤 𝓣 : Universe)
        (pe : propext 𝓣)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓣
open import DcpoBasics pt fe 𝓣
open import DcpoLifting pt fe 𝓣 pe

open import Lifting 𝓣 hiding (⊥)

module _
        (X : 𝓤 ̇ )
        (X-is-set : is-set X)
        (f : 𝓛 X → 𝓛 X)
        (f-is-monotone : is-monotone (𝓛-DCPO X-is-set) (𝓛-DCPO X-is-set) f)
       where

 𝓛X-DCPO : DCPO {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛X-DCPO = 𝓛-DCPO X-is-set

 𝓛X-DCPO⊥ : DCPO⊥ {𝓣 ⁺ ⊔ 𝓤} {𝓣 ⁺ ⊔ 𝓤}
 𝓛X-DCPO⊥ = 𝓛-DCPO⊥ X-is-set

 y₀ : 𝓛 X
 y₀ = f (⊥ 𝓛X-DCPO⊥)

 P₀ : 𝓣 ̇
 P₀ = is-defined y₀

 α₀ : 𝟙{𝓣} + P₀ → 𝓛 X
 α₀ (inl *) = ⊥ 𝓛X-DCPO⊥
 α₀ (inr p) = y₀

 δ₀ : is-Directed 𝓛X-DCPO α₀
 δ₀ = ∣ inl * ∣ , ε
  where
   ε : is-weakly-directed (underlying-order 𝓛X-DCPO) α₀
   ε (inl *) (inl *) = ∣ inl * , reflexivity (𝓛X-DCPO) (⊥ 𝓛X-DCPO⊥)  ,
                                 reflexivity (𝓛X-DCPO) (⊥ 𝓛X-DCPO⊥) ∣
   ε (inl *) (inr p) = ∣ inr p , ⊥-is-least 𝓛X-DCPO⊥ y₀ ,
                                 reflexivity 𝓛X-DCPO y₀ ∣
   ε (inr p) (inl *) = ∣ inr p , reflexivity 𝓛X-DCPO y₀ ,
                                 ⊥-is-least 𝓛X-DCPO⊥ y₀ ∣
   ε (inr p) (inr q) = ∣ inr p , reflexivity 𝓛X-DCPO y₀ ,
                                 reflexivity 𝓛X-DCPO y₀ ∣

 x₀ : 𝓛 X
 x₀ = ∐ 𝓛X-DCPO δ₀

 x₀-is-below-all-post-fixed-points : (l : 𝓛 X) → f l ⊑⟨ 𝓛X-DCPO ⟩ l
                                   → x₀ ⊑⟨ 𝓛X-DCPO ⟩ l
 x₀-is-below-all-post-fixed-points l u =
  ∐-is-lowerbound-of-upperbounds 𝓛X-DCPO δ₀ l γ
   where
    γ : is-upperbound (underlying-order 𝓛X-DCPO) l α₀
    γ (inl *) = ⊥-is-least 𝓛X-DCPO⊥ l
    γ (inr p) = y₀             ⊑⟨ 𝓛X-DCPO ⟩[ reflexivity 𝓛X-DCPO y₀ ]
                f (⊥ 𝓛X-DCPO⊥) ⊑⟨ 𝓛X-DCPO ⟩[ v ]
                f l            ⊑⟨ 𝓛X-DCPO ⟩[ u ]
                l              ∎⟨ 𝓛X-DCPO ⟩
     where
      v = f-is-monotone (⊥ 𝓛X-DCPO⊥) l (⊥-is-least 𝓛X-DCPO⊥ l)

 x₀-is-a-pre-fixed-point : x₀ ⊑⟨ 𝓛X-DCPO ⟩ f x₀
 x₀-is-a-pre-fixed-point = ∐-is-lowerbound-of-upperbounds 𝓛X-DCPO δ₀ (f x₀) γ
  where
   γ : is-upperbound (underlying-order 𝓛X-DCPO) (f x₀) α₀
   γ (inl *) = ⊥-is-least 𝓛X-DCPO⊥ (f x₀)
   γ (inr p) = y₀             ⊑⟨ 𝓛X-DCPO ⟩[ reflexivity 𝓛X-DCPO y₀ ]
                f (⊥ 𝓛X-DCPO⊥) ⊑⟨ 𝓛X-DCPO ⟩[ v ]
                f x₀            ∎⟨ 𝓛X-DCPO ⟩
    where
     v = f-is-monotone (⊥ 𝓛X-DCPO⊥) x₀ (⊥-is-least 𝓛X-DCPO⊥ x₀)

 open import Negation

 it-is-false-that-x₀-is-not-a-post-fixed-point : ¬¬ (f x₀ ⊑⟨ 𝓛X-DCPO ⟩ x₀)
 it-is-false-that-x₀-is-not-a-post-fixed-point h = h γ
  where
   γ : f x₀ ⊑⟨ 𝓛X-DCPO ⟩ x₀
   γ q = 𝟘-induction (claim (transport is-defined e q))
    where
     claim : ¬ P₀
     claim p = h (≡-to-⊑ 𝓛X-DCPO ψ)
      where
       claim' : is-defined (x₀)
       claim' = ∣ inr p , p ∣
       ψ : f x₀ ≡ x₀
       ψ = (x₀-is-a-pre-fixed-point claim') ⁻¹
     e : f x₀ ≡ y₀
     e = f x₀            ≡⟨ ap f e' ⟩
         f (⊥ 𝓛X-DCPO⊥)  ≡⟨ refl ⟩
         y₀              ∎
      where
       e' : x₀ ≡ ⊥ 𝓛X-DCPO⊥
       e' = antisymmetry 𝓛X-DCPO x₀ (⊥ 𝓛X-DCPO⊥)
             (∐-is-lowerbound-of-upperbounds 𝓛X-DCPO δ₀ (⊥ 𝓛X-DCPO⊥) ϕ)
             (⊥-is-least 𝓛X-DCPO⊥ x₀)
        where
         ϕ : is-upperbound (underlying-order 𝓛X-DCPO) (⊥ 𝓛X-DCPO⊥) α₀
         ϕ (inl *)  = reflexivity 𝓛X-DCPO (⊥ 𝓛X-DCPO⊥)
         ϕ (inr p₀) = 𝟘-induction (claim p₀)

 it-is-false-that-x₀-is-not-a-fixed-point : ¬¬ (f x₀ ≡ x₀)
 it-is-false-that-x₀-is-not-a-fixed-point =
  ¬¬-functor g p
   where
    g : f x₀ ⊑⟨ 𝓛X-DCPO ⟩ x₀ × x₀ ⊑⟨ 𝓛X-DCPO ⟩ f x₀ → f x₀ ≡ x₀
    g (u , v) = antisymmetry 𝓛X-DCPO (f x₀) x₀ u v
    p : ¬¬ ((f x₀ ⊑⟨ 𝓛X-DCPO ⟩ x₀)
            × (x₀ ⊑⟨ 𝓛X-DCPO ⟩ f x₀))
    p = und (it-is-false-that-x₀-is-not-a-post-fixed-point ,
             double-negation-intro x₀-is-a-pre-fixed-point)

\end{code}
