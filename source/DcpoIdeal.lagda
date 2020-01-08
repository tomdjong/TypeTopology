\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module DcpoIdeal
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index type for directed completeness lives
       where

open PropositionalTruncation pt

open import UF-Subsingletons
-- open import UF-Subsingletons-FunExt
open import Dcpo pt fe 𝓥
open import Fin

module _ {𝓤 𝓣 : Universe}
         {B : 𝓤 ̇ }
         (_≺_ : B → B → 𝓣 ̇ )
       where

 _≺-vec_ : {n : ℕ} (v : Vec B n) (x : B) → 𝓣 ̇
 _≺-vec_ {n} v x = (m : Fin n) → (v !! m) ≺ x

 INT : 𝓤 ⊔ 𝓣 ̇
 INT = {n : ℕ} (v : Vec B n) (x : B)
     → (v ≺-vec x → ∃ \(y : B) → v ≺-vec y × (y ≺ x))

 is-abstract-basis : 𝓤 ⊔ 𝓣 ̇
 is-abstract-basis = is-transitive _≺_ × INT

 is-lower-closed : {I : 𝓦 ̇ } → (I → B) → 𝓦 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-lower-closed {𝓦} {I} α = (i : I) (y : B)
   → y ≺ α i
   → ∃ \(j : I) → α j ≡ y

 is-directed' : {I : 𝓦 ̇ } → (I → B) → 𝓦 ⊔ 𝓣 ̇
 is-directed' {𝓦} {I} α = ∥ I ∥ ×
  ((i j : I) → ∃ \(k : I) → (α i ≺ α k) × (α j ≺ α k))

 is-ideal : {I : 𝓦 ̇ } → (I → B) → 𝓤 ⊔ 𝓣 ⊔ 𝓦 ̇
 is-ideal α = is-directed' α × is-lower-closed α

 Idl : (𝓦 : Universe) → 𝓦 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 Idl 𝓦 = Σ \(I : 𝓦 ̇ ) → Σ \(α : I → B) → is-ideal α

 {-

 _⊑_ : {𝓦 : Universe} → Idl 𝓦 → Idl 𝓦 → 𝓤 ⊔ 𝓦 ̇
 (I , α , _) ⊑ (J , β , _) = (i : I) → ∃ \(j : J) → α i ≡ β j

 ⊑-sup : {𝓦 : Universe} {K : 𝓥 ̇ } (Γ : K → Idl 𝓦)
       → is-directed _⊑_ Γ
       → Idl (𝓥 ⊔ 𝓦)
 ⊑-sup {W} {K} Γ δ = (Σ \(k : K) → pr₁ (Γ k)) ,
                     (γ , (u , v))
  where
   γ : (Σ \(k : K) → pr₁ (Γ k)) → B
   γ (k , c) = pr₁ (pr₂ (Γ k)) c
   u : is-directed' γ
   u = {!!}
   v : is-lower-closed γ
   v i y  = {!!}

 module _ (τ : is-transitive _≺_)
          (ι : INT)
        where
  ↓_ : B → Idl (𝓤 ⊔ 𝓣)
  ↓ x = ((Σ \(y : B) → y ≺ x) , pr₁ , u , v)
   where
    u : is-directed' pr₁
    u = (a , b)
     where
      a : ∃ \(y : B) → y ≺ x
      a = do
       (y , _ , l) ← h
       ∣ y , l ∣
       where
        h : ∃ (λ y → ([] ≺-vec y) × (y ≺ x))
        h = ι [] x 𝟘-induction
      b : (i j : Σ (λ y → y ≺ x)) →
            ∃ (λ k → (pr₁ i ≺ pr₁ k) × (pr₁ j ≺ pr₁ k))
      b (y , l) (z , m) = do
       (w , κ , k) ← h
       ∣ (w , k) , (κ 𝟎 , κ (suc 𝟎)) ∣
       where
        h : ∃ \w → ((y ∷ (z ∷ [])) ≺-vec w) × (w ≺ x)
        h = ι (y ∷ (z ∷ [])) x g
         where
          g : (m : Fin 2) → ((y ∷ (z ∷ [])) !! m) ≺ x
          g 𝟎 = l
          g (suc 𝟎) = m
    v : is-lower-closed pr₁
    v (y , l) z m = ∣ ((z , τ z y x m l) , refl) ∣
 -}
\end{code}
