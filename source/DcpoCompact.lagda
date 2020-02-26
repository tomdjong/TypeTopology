Tom de Jong, 11 December 2019 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module DcpoCompact
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

-- open import UF-Subsingletons hiding (⊥)
-- open import UF-Subsingletons-FunExt

open import Dcpo pt fe 𝓥

approximates : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
approximates 𝓓 x y = (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                   → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
                   → ∃ \(i : I) → x ⊑⟨ 𝓓 ⟩ α i

syntax approximates 𝓓 x y = x ≪⟨ 𝓓 ⟩ y

≪-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y
≪-to-⊑ 𝓓 {x} {y} a = ∥∥-rec (prop-valuedness 𝓓 x y) γ g
 where
  α : 𝟙{𝓥} → ⟨ 𝓓 ⟩
  α * = y
  γ : (Σ i ꞉ 𝟙 , x ⊑⟨ 𝓓 ⟩ α i) → x ⊑⟨ 𝓓 ⟩ y
  γ (* , l) = l
  g : ∃ \(i : 𝟙) → x ⊑⟨ 𝓓 ⟩ α i
  g = a 𝟙 α δ (∐-is-upperbound 𝓓 δ *)
   where
    δ : is-Directed 𝓓 α
    δ = (∣ * ∣ , ε)
     where
      ε : (i j : 𝟙)
        → ∃ \(k : 𝟙) →  α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k
      ε * * = ∣ * , reflexivity 𝓓 y , reflexivity 𝓓 y ∣

⊑-≪-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x' x y y' : ⟨ 𝓓 ⟩}
      → x' ⊑⟨ 𝓓 ⟩ x
      → x ≪⟨ 𝓓 ⟩ y
      → y ⊑⟨ 𝓓 ⟩ y'
      → x' ≪⟨ 𝓓 ⟩ y'
⊑-≪-⊑ 𝓓 {x'} {x} {y} {y'} u a v I α δ w = γ
 where
  γ : ∃ \(i : I) → x' ⊑⟨ 𝓓 ⟩ α i
  γ = ∥∥-functor g h
   where
    g : (Σ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i)
      → (Σ i ꞉ I , x' ⊑⟨ 𝓓 ⟩ α i)
    g (i , l) = (i , t)
     where
      t = x'  ⊑⟨ 𝓓 ⟩[ u ]
          x   ⊑⟨ 𝓓 ⟩[ l ]
          α i ∎⟨ 𝓓 ⟩
    h : ∃ \(i : I) → x ⊑⟨ 𝓓 ⟩ α i
    h = a I α δ s
     where
      s = y     ⊑⟨ 𝓓 ⟩[ v ]
          y'    ⊑⟨ 𝓓 ⟩[ w ]
          ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

≪-is-prop-valued : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → is-prop (x ≪⟨ 𝓓 ⟩ y)
≪-is-prop-valued 𝓓 = Π-is-prop fe
                     (λ I → Π-is-prop fe
                     (λ α → Π-is-prop fe
                     (λ δ → Π-is-prop fe
                     (λ u → ∥∥-is-a-prop))))

≪-is-antisymmetric : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩}
                   → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ x → x ≡ y
≪-is-antisymmetric 𝓓 {x} {y} u v = antisymmetry 𝓓 x y (≪-to-⊑ 𝓓 u) (≪-to-⊑ 𝓓 v)

≪-is-transitive : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
                → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ z → x ≪⟨ 𝓓 ⟩ z
≪-is-transitive 𝓓 {x} {y} {z} u v I α δ l = do
 (i , m) ← u I α δ (transitivity 𝓓 y z (∐ 𝓓 δ) (≪-to-⊑ 𝓓 v) l)
 ∣ i , m ∣

compact : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
compact 𝓓 x = x ≪⟨ 𝓓 ⟩ x

is-a-continuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-continuous-dcpo {𝓤} {𝓣} 𝓓 = ∃ B ꞉ 𝓥 ̇ , γ B
 where
  γ : (B : 𝓥 ̇ ) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  γ B = (x : ⟨ 𝓓 ⟩)
      → Σ β ꞉ (B → ⟨ 𝓓 ⟩) , (β-≪-x β x) × (∐β≡x β x)
   where
    β-≪-x : (B → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    β-≪-x β x = ((b : B) → β b ≪⟨ 𝓓 ⟩ x)
    ∐β≡x : (B → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
    ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 β , ∐ 𝓓 δ ≡ x

is-an-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-an-algebraic-dcpo {𝓤} {𝓣} 𝓓 = ∃ B ꞉ 𝓥 ̇ , γ B
 where
  γ : (B : 𝓥 ̇ ) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  γ B = (x : ⟨ 𝓓 ⟩)
      → Σ β ꞉ (B → ⟨ 𝓓 ⟩) , (κ β) × (β-≪-x β x) × (∐β≡x β x)
   where
    κ : (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    κ β = (b : B) → compact 𝓓 (β b)
    β-≪-x : (B → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    β-≪-x β x = ((b : B) → β b ≪⟨ 𝓓 ⟩ x)
    ∐β≡x : (B → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
    ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 β , ∐ 𝓓 δ ≡ x

algebraicity-implies-continuity : (𝓓 : DCPO {𝓤} {𝓣})
                                → is-an-algebraic-dcpo 𝓓
                                → is-a-continuous-dcpo 𝓓
algebraicity-implies-continuity 𝓓 = ∥∥-functor γ
 where
  γ : _
  γ (B , a) = B , c
   where
    c : _
    c x = β , wb , s
     where
      β : B → ⟨ 𝓓 ⟩
      β = pr₁ (a x)
      wb : (b : B) → β b ≪⟨ 𝓓 ⟩ x
      wb = pr₁ (pr₂ (pr₂ (a x)))
      s : Σ δ ꞉ is-Directed 𝓓 β , ∐ 𝓓 δ ≡ x
      s = pr₂ (pr₂ (pr₂ (a x)))

is-algebraic' : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-algebraic' {𝓤} {𝓣} 𝓓 = ∃ B ꞉ 𝓥 ̇ , γ B
 where
  γ : (B : 𝓥 ̇ ) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  γ B = (x : ⟨ 𝓓 ⟩)
      → Σ β ꞉ (B → ⟨ 𝓓 ⟩) , (κ β) × (∐β≡x β x)
   where
    κ : (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    κ β = (b : B) → compact 𝓓 (β b)
    ∐β≡x : (B → ⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
    ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 β , ∐ 𝓓 δ ≡ x

algebraic-implies-algebraic' : (𝓓 : DCPO {𝓤} {𝓣})
                             → is-an-algebraic-dcpo 𝓓
                             → is-algebraic' 𝓓
algebraic-implies-algebraic' 𝓓 = ∥∥-functor γ
 where
  γ : _
  γ (B , a) = B , a'
   where
    a' : _
    a' x = β , κ , s
     where
      β : B → ⟨ 𝓓 ⟩
      β = pr₁ (a x)
      κ : (b : B) → compact 𝓓 (β b)
      κ = pr₁ (pr₂ (a x))
      s : Σ δ ꞉ is-Directed 𝓓 β , ∐ 𝓓 δ ≡ x
      s = pr₂ (pr₂ (pr₂ (a x)))

algebraic'-implies-algebraic : (𝓓 : DCPO {𝓤} {𝓣})
                             → is-algebraic' 𝓓
                             → is-an-algebraic-dcpo 𝓓
algebraic'-implies-algebraic 𝓓 = ∥∥-functor γ
 where
  γ : _
  γ (B , a') = B , a
   where
    a : _
    a x = β , κ , wb , s
     where
      β : B → ⟨ 𝓓 ⟩
      β = pr₁ (a' x)
      κ : (b : B) → compact 𝓓 (β b)
      κ = pr₁ (pr₂ (a' x))
      s : Σ δ ꞉ is-Directed 𝓓 β , ∐ 𝓓 δ ≡ x
      s = pr₂ (pr₂ (a' x))
      wb : (b : B) → β b ≪⟨ 𝓓 ⟩ x
      wb b = ⊑-≪-⊑ 𝓓 u v w
       where
        δ : is-Directed 𝓓 β
        δ = pr₁ s
        u : β b ⊑⟨ 𝓓 ⟩ β b
        u = reflexivity 𝓓 (β b)
        v : β b ≪⟨ 𝓓 ⟩ β b
        v = κ b
        w : β b ⊑⟨ 𝓓 ⟩ x
        w = transport (λ - → β b ⊑⟨ 𝓓 ⟩ -) (pr₂ s) w'
         where
          w' : β b ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
          w' = ∐-is-upperbound 𝓓 δ b

\end{code}
