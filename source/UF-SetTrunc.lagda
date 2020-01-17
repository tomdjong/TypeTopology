Tom de Jong
17-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-SetTrunc where

open import SpartanMLTT

open import Plus-Properties
open import UF-Base public
open import UF-Equiv public
open import UF-Subsingletons public
open import UF-FunExt public

-- open import UF-Subsingletons-FunExt public

\end{code}

We use the existence of set truncations as an assumption. The following type
collects the data that constitutes this assumption.

\begin{code}

record set-truncations-exist : 𝓤ω where
 field
  ∥_∥₀ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥₀-is-a-set : {𝓤 : Universe} {X : 𝓤 ̇ } → is-set ∥ X ∥₀
  ∣_∣₀ : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥₀
  ∥∥₀-universal-property : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → is-set Y
                         → is-equiv (λ (f : ∥ X ∥₀ → Y) → f ∘ ∣_∣₀)
 infix 0 ∥_∥₀
 infix 0 ∣_∣₀

module SetTruncation (st : set-truncations-exist) where

 open set-truncations-exist st public

 ∣∣₀-precomp : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → (∥ X ∥₀ → Y) → (X → Y)
 ∣∣₀-precomp f x = f ∣ x ∣₀

 ∥∥₀-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         → is-set Y
         → (X → Y)
         → ∥ X ∥₀ → Y
 ∥∥₀-rec i = inverse ∣∣₀-precomp (∥∥₀-universal-property i)

 ∥∥₀-comp : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         → (i : is-set Y)
         → (f : X → Y)
         → (x : X) → ∥∥₀-rec i f ∣ x ∣₀ ≡ f x
 ∥∥₀-comp {𝓤} {𝓥} {X} {Y} i f x =
  ι⁻¹ f ∣ x ∣₀ ≡⟨ refl ⟩
  ι (ι⁻¹ f) x  ≡⟨ happly (inverse-is-section ι (∥∥₀-universal-property i) f) x ⟩
  f x          ∎
   where
    ι : (∥ X ∥₀ → Y) → X → Y
    ι = ∣∣₀-precomp
    ι⁻¹ : (X → Y) → ∥ X ∥₀ → Y
    ι⁻¹ = ∥∥₀-rec i

 ∥∥₀-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → ∥ X ∥₀ → ∥ Y ∥₀
 ∥∥₀-functor f = ∥∥₀-rec ∥∥₀-is-a-set (λ x → ∣ f x ∣₀)

 ∥∥₀-functor-id : {X : 𝓤 ̇ } → ∥∥₀-functor id ≡ id─ ∥ X ∥₀
 ∥∥₀-functor-id {𝓤} {X} =
  ∥∥₀-functor id ≡⟨ refl ⟩
  ι⁻¹ ∣_∣₀      ≡⟨ refl ⟩
  ι⁻¹ (ι id)    ≡⟨ inverse-is-retraction ι e id ⟩
  id            ∎
   where
    ι : (∥ X ∥₀ → ∥ X ∥₀) → X → ∥ X ∥₀
    ι = ∣∣₀-precomp
    ι⁻¹ : (X → ∥ X ∥₀) → ∥ X ∥₀ → ∥ X ∥₀
    ι⁻¹ = ∥∥₀-rec ∥∥₀-is-a-set
    e : is-equiv (∣∣₀-precomp {𝓤} {𝓤} {X} {∥ X ∥₀})
    e = ∥∥₀-universal-property ∥∥₀-is-a-set

\end{code}

TO DO:
- ∥∥₀-functor-comp
