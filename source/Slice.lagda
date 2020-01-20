Martin Escardo, 6th December 2018.

Cf. The lifting monad.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Slice (𝓣 : Universe) where

open import UF-Subsingletons hiding (⊥)

𝓕 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
𝓕 X = Σ \(I : 𝓣 ̇ ) → I → X

source : {X : 𝓤 ̇ } → 𝓕 X → 𝓣 ̇
source (I , φ) = I

family : {X : 𝓤 ̇ } (l : 𝓕 X) → source l → X
family (I , φ) = φ

η : {X : 𝓤 ̇ } → X → 𝓕 X
η x = 𝟙 , (λ _ → x)

Sigma : {X : 𝓤 ̇ } → 𝓕  X → 𝓣 ̇
Sigma (I , φ) = I

Pi : {X : 𝓤 ̇ } → 𝓕  X → 𝓣 ⊔ 𝓤 ̇
Pi {𝓤} {X} (I , φ) = Σ \(s : X → I) → φ ∘ s ≡ id

open import UF-Classifiers
open import UF-Equiv
open import UF-FunExt
open import UF-Univalence

𝓕-equiv-particular : funext 𝓣 (𝓣 ⁺) → is-univalent 𝓣
                   → (X : 𝓣 ̇ ) → 𝓕 X ≃ (X → 𝓣 ̇ )
𝓕-equiv-particular = type-classifier.classification-equivalence

open import UF-Size
open import UF-Base
open import UF-Equiv-FunExt
open import UF-UA-FunExt
open import UF-UniverseEmbedding
open import UF-EquivalenceExamples

𝓕-equiv : Univalence →  (X : 𝓤 ̇ ) → 𝓕 X ≃ Σ \(A : X → 𝓣 ⊔ 𝓤 ̇ ) → (Σ A) has-size 𝓣
𝓕-equiv {𝓤} ua X = qinveq χ (T , Tχ , χT)
 where
  fe : FunExt
  fe = FunExt-from-Univalence ua
  χ : 𝓕 X → Σ \(A : X → 𝓣 ⊔ 𝓤 ̇ ) → (Σ A) has-size 𝓣
  χ (I , φ) = fiber φ , I , ≃-sym (graph-domain-equiv φ)
  T : (Σ \(A : X → 𝓣 ⊔ 𝓤 ̇ ) → (Σ A) has-size 𝓣) → 𝓕 X
  T (A , I , (f , e)) = I , pr₁ ∘ f
  χT : (σ : Σ \(A : X → 𝓣 ⊔ 𝓤 ̇ ) → (Σ A) has-size 𝓣) → χ (T σ) ≡ σ
  χT (A , I , (f , e)) = p
   where
    h : (x : X) → fiber (pr₁ ∘ f) x ≃ A x
    h x = (Σ \(i : I) → pr₁ (f i) ≡ x) ≃⟨ Σ-change-of-variables (λ (σ : Σ A) → pr₁ σ ≡ x) f e ⟩
          (Σ \(σ : Σ A) → pr₁ σ ≡ x)   ≃⟨ fiber-equiv x ⟩
          A x                          ■
    p : fiber (pr₁ ∘ f) , I , ≃-sym (graph-domain-equiv (pr₁ ∘ f)) ≡ A , I , f , e
    p = to-Σ-≡ (dfunext (fe 𝓤 ((𝓣 ⊔ 𝓤) ⁺)) (λ x → eqtoid (ua (𝓣 ⊔ 𝓤)) (fiber (pr₁ ∘ f) x) (A x) (h x)) ,
                has-size-is-a-prop ua (Σ A) 𝓣 _ (I , f , e))
  Tχ : (l : 𝓕 X) → T (χ l) ≡ l
  Tχ (I , φ) = ap (λ - → I , -) (dfunext (fe 𝓣 𝓤) (λ i → refl))

\end{code}
