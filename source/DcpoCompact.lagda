Tom de Jong, late February - early March 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc
open import UF-Equiv
open import UF-Size

module DcpoCompact
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥

approximates : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
approximates 𝓓 x y = (I : 𝓥 ̇ ) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                   → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
                   → ∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i

syntax approximates 𝓓 x y = x ≪⟨ 𝓓 ⟩ y

≪-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → x ≪⟨ 𝓓 ⟩ y → x ⊑⟨ 𝓓 ⟩ y
≪-to-⊑ 𝓓 {x} {y} x≪y = ∥∥-rec (prop-valuedness 𝓓 x y) γ g
 where
  α : 𝟙{𝓥} → ⟨ 𝓓 ⟩
  α * = y
  γ : (Σ i ꞉ 𝟙 , x ⊑⟨ 𝓓 ⟩ α i) → x ⊑⟨ 𝓓 ⟩ y
  γ (* , l) = l
  g : ∃ i ꞉ 𝟙 , x ⊑⟨ 𝓓 ⟩ α i
  g = x≪y 𝟙 α δ (∐-is-upperbound 𝓓 δ *)
   where
    δ : is-Directed 𝓓 α
    δ = (∣ * ∣ , ε)
     where
      ε : (i j : 𝟙)
        → ∃ k ꞉ 𝟙 , α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k
      ε * * = ∣ * , reflexivity 𝓓 y , reflexivity 𝓓 y ∣

⊑-≪-⊑-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x' x y y' : ⟨ 𝓓 ⟩}
           → x' ⊑⟨ 𝓓 ⟩ x
           → x ≪⟨ 𝓓 ⟩ y
           → y ⊑⟨ 𝓓 ⟩ y'
           → x' ≪⟨ 𝓓 ⟩ y'
⊑-≪-⊑-to-≪ 𝓓 {x'} {x} {y} {y'} x'⊑x x≪y y⊑y' I α δ y'⊑∐α = γ
 where
  γ : ∃ i ꞉ I , x' ⊑⟨ 𝓓 ⟩ α i
  γ = ∥∥-functor g h
   where
    g : (Σ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i)
      → (Σ i ꞉ I , x' ⊑⟨ 𝓓 ⟩ α i)
    g (i , l) = (i , t)
     where
      t = x'  ⊑⟨ 𝓓 ⟩[ x'⊑x ]
          x   ⊑⟨ 𝓓 ⟩[ l ]
          α i ∎⟨ 𝓓 ⟩
    h : ∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i
    h = x≪y I α δ y⊑∐α
     where
      y⊑∐α = y     ⊑⟨ 𝓓 ⟩[ y⊑y' ]
             y'    ⊑⟨ 𝓓 ⟩[ y'⊑∐α ]
             ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

⊑-≪-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
         → x ⊑⟨ 𝓓 ⟩ y
         → y ≪⟨ 𝓓 ⟩ z
         → x ≪⟨ 𝓓 ⟩ z
⊑-≪-to-≪ 𝓓 {x} {y} {z} x⊑y y≪z = ⊑-≪-⊑-to-≪ 𝓓 x⊑y y≪z (reflexivity 𝓓 z)

≪-⊑-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
         → x ≪⟨ 𝓓 ⟩ y
         → y ⊑⟨ 𝓓 ⟩ z
         → x ≪⟨ 𝓓 ⟩ z
≪-⊑-to-≪ 𝓓 {x} {y} {z} x≪y y⊑z = ⊑-≪-⊑-to-≪ 𝓓 (reflexivity 𝓓 x) x≪y y⊑z

≪-is-prop-valued : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → is-prop (x ≪⟨ 𝓓 ⟩ y)
≪-is-prop-valued 𝓓 = Π-is-prop fe
                     (λ I → Π-is-prop fe
                     (λ α → Π-is-prop fe
                     (λ δ → Π-is-prop fe
                     (λ u → ∥∥-is-a-prop))))

≪-is-antisymmetric : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩}
                   → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ x → x ≡ y
≪-is-antisymmetric 𝓓 {x} {y} x≪y y≪x =
 antisymmetry 𝓓 x y (≪-to-⊑ 𝓓 x≪y) (≪-to-⊑ 𝓓 y≪x)

≪-is-transitive : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
                → x ≪⟨ 𝓓 ⟩ y → y ≪⟨ 𝓓 ⟩ z → x ≪⟨ 𝓓 ⟩ z
≪-is-transitive 𝓓 {x} {y} {z} x≪y y≪z I α δ z⊑∐α = x≪y I α δ y⊑∐α
 where
  y⊑∐α = y      ⊑⟨ 𝓓 ⟩[ ≪-to-⊑ 𝓓 y≪z ]
         z      ⊑⟨ 𝓓 ⟩[ z⊑∐α ]
         ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

is-compact : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-compact 𝓓 x = x ≪⟨ 𝓓 ⟩ x

\end{code}

\begin{code}

≪-small-on-B : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
≪-small-on-B 𝓓 {B} ι = (b b' : B) → (ι b ≪⟨ 𝓓 ⟩ ι b') has-size 𝓥

is-a-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-basis {𝓤} {𝓣} 𝓓 {B} ι = ≪-small-on-B 𝓓 ι × γ ι
 where
  γ : {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  γ {B} ι = (x : ⟨ 𝓓 ⟩) → ∃ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) , (β≪x β x) × (∐β≡x β x)
   where
     β≪x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
     β≪x {I} β x = ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
     ∐β≡x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
     ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x

is-a-continuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-continuous-dcpo {𝓤} {𝓣} 𝓓 = ∃ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) , is-a-basis 𝓓 ι

basis-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
        → is-a-basis 𝓓 ι
        → B → B → 𝓥 ̇
basis-≪ 𝓓 (≺ , _) b b' = has-size-type (≺ b b')

syntax basis-≪ 𝓓 isb b b' = b ≪ᴮ⟨ 𝓓 ⟩[ isb ] b'

≪ᴮ-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b b' : B) → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b' → ι b ≪⟨ 𝓓 ⟩ ι b'
≪ᴮ-to-≪ 𝓓 {B} {ι} c b b' b≪ᴮb' = ⌜ e ⌝ b≪ᴮb'
 where
  e : b ≪ᴮ⟨ 𝓓 ⟩[ c ] b' ≃ ι b ≪⟨ 𝓓 ⟩ ι b'
  e = has-size-equiv (≺ b b')
   where
    ≺ : ≪-small-on-B 𝓓 ι
    ≺ = pr₁ c

≪-to-≪ᴮ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b b' : B) → ι b ≪⟨ 𝓓 ⟩ ι b' → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b'
≪-to-≪ᴮ 𝓓 {B} {ι} c b b' b≪b' = ⌜ ≃-sym e ⌝ b≪b'
 where
  e : b ≪ᴮ⟨ 𝓓 ⟩[ c ] b' ≃ ι b ≪⟨ 𝓓 ⟩ ι b'
  e = has-size-equiv (≺ b b')
   where
    ≺ : ≪-small-on-B 𝓓 ι
    ≺ = pr₁ c

≪ᴮ-is-prop-valued : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                    (c : is-a-basis 𝓓 ι) {b b' : B}
                  → is-prop (b ≪ᴮ⟨ 𝓓 ⟩[ c ] b')
≪ᴮ-is-prop-valued 𝓓 {B} {ι} (≺ , _) {b} {b'} =
 equiv-to-prop (has-size-equiv (≺ b b')) (≪-is-prop-valued 𝓓)

\end{code}

\begin{code}

⊑-in-terms-of-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩}
                → x ⊑⟨ 𝓓 ⟩ y
                → (z : ⟨ 𝓓 ⟩)
                → z ≪⟨ 𝓓 ⟩ x → z ≪⟨ 𝓓 ⟩ y
⊑-in-terms-of-≪ 𝓓 x⊑y z z≪x = ≪-⊑-to-≪ 𝓓 z≪x x⊑y

⊑-in-terms-of-≪' : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                 → is-a-basis 𝓓 ι
                 → {x y : ⟨ 𝓓 ⟩}
                 → ((b : B) → ι b ≪⟨ 𝓓 ⟩ x → ι b ≪⟨ 𝓓 ⟩ y)
                 → x ⊑⟨ 𝓓 ⟩ y
⊑-in-terms-of-≪' 𝓓 {B} {ι} (_ , c) {x} {y} ≪-hyp =
 ∥∥-rec (prop-valuedness 𝓓 x y) γ (c x)
  where
   γ : (Σ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) ,
          ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
        × (Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x))
     → x ⊑⟨ 𝓓 ⟩ y
   γ (I , β , β≪x , δ , ∐β≡x) = x      ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (∐β≡x ⁻¹) ]
                                 ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩[ ∐β⊑y ]
                                 y      ∎⟨ 𝓓 ⟩
    where
     ∐β⊑y = ∐-is-lowerbound-of-upperbounds 𝓓 δ y ub
      where
       ub : (i : I) → ι (β i) ⊑⟨ 𝓓 ⟩ y
       ub i = ≪-to-⊑ 𝓓 (≪-hyp (β i) (β≪x i))

\end{code}

\begin{code}

basis-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
        → is-a-basis 𝓓 ι
        → B → B → 𝓥 ̇
basis-⊑ 𝓓 {B} {ι} c b₁ b₂ = (b : B) → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₁ → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂

syntax basis-⊑ 𝓓 c b b' = b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b'

⊑ᴮ-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
          (c : is-a-basis 𝓓 ι) {b b' : B}
        → b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b' → ι b ⊑⟨ 𝓓 ⟩ ι b'
⊑ᴮ-to-⊑ 𝓓 {B} {ι} c {b₁} {b₂} b₁⊑ᴮb₂ = ⊑-in-terms-of-≪' 𝓓 c γ
 where
  γ : (b : B) → ι b ≪⟨ 𝓓 ⟩ ι b₁ → ι b ≪⟨ 𝓓 ⟩ ι b₂
  γ b b≪b₁ = ≪ᴮ-to-≪ 𝓓 c b b₂ (b₁⊑ᴮb₂ b (≪-to-≪ᴮ 𝓓 c b b₁ b≪b₁))

⊑-to-⊑ᴮ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
          (c : is-a-basis 𝓓 ι) {b b' : B}
        → ι b ⊑⟨ 𝓓 ⟩ ι b'
        → b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b'
⊑-to-⊑ᴮ 𝓓 {B} {ι} c {b₁} {b₂} b₁⊑b₂ b b≪ᴮb₁ = ≪-to-≪ᴮ 𝓓 c b b₂ γ
 where
  γ : ι b ≪⟨ 𝓓 ⟩ ι b₂
  γ = ⊑-in-terms-of-≪ 𝓓 b₁⊑b₂ (ι b) (≪ᴮ-to-≪ 𝓓 c b b₁ b≪ᴮb₁)

⊑ᴮ-is-prop-valued : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                    (c : is-a-basis 𝓓 ι) {b b' : B}
                  → is-prop (b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b')
⊑ᴮ-is-prop-valued 𝓓 {B} {ι} (≺ , _) {b₁} {b₂} =
 Π-is-prop fe
 λ b → Π-is-prop fe
 λ b≪b₁ → equiv-to-prop (has-size-equiv (≺ b b₂)) (≪-is-prop-valued 𝓓)

⊑-is-small-on-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                      (c : is-a-basis 𝓓 ι) {b b' : B}
                    → (ι b ⊑⟨ 𝓓 ⟩ ι b') has-size 𝓥
⊑-is-small-on-basis 𝓓 {B} {ι} c {b₁} {b₂} = (b₁ ⊑ᴮ⟨ 𝓓 ⟩[ c ] b₂) , γ
 where
  γ : (b₁ ⊑ᴮ⟨ 𝓓 ⟩[ c ] b₂) ≃ ι b₁ ⊑⟨ 𝓓 ⟩ ι b₂
  γ = logically-equivalent-props-are-equivalent
       (⊑ᴮ-is-prop-valued 𝓓 c)
       (prop-valuedness 𝓓 (ι b₁) (ι b₂))
       (⊑ᴮ-to-⊑ 𝓓 c)
       (⊑-to-⊑ᴮ 𝓓 c)

\end{code}

\begin{code}

is-an-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-an-algebraic-dcpo {𝓤} {𝓣} 𝓓 =
 ∃ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) ,
 is-a-basis 𝓓 ι × ((b : B) → is-compact 𝓓 (ι b))


algebraicity-implies-continuity : (𝓓 : DCPO {𝓤} {𝓣})
                                → is-an-algebraic-dcpo 𝓓
                                → is-a-continuous-dcpo 𝓓
algebraicity-implies-continuity 𝓓 = ∥∥-functor γ
 where
  γ : (Σ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) ,
         is-a-basis 𝓓 ι
        × ((b : B) → is-compact 𝓓 (ι b)))
    → Σ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) , is-a-basis 𝓓 ι
  γ (B , ι , isb , comp) = B , ι , isb

\end{code}

\begin{code}

≪-INT₀ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
         (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , ι b ≪⟨ 𝓓 ⟩ x
≪-INT₀ 𝓓 (≺ , c) x = do
 (I , β , ≪x , δ , ∐β≡x) ← c x
 i ← Directed-implies-inhabited 𝓓 δ
 ∣ (β i) , ≪x i ∣

≪ᴮ-INT₀ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b : B) → ∃ b' ꞉ B , b' ≪ᴮ⟨ 𝓓 ⟩[ c ] b
≪ᴮ-INT₀ 𝓓 {B} {ι} c b = ∥∥-functor γ (≪-INT₀ 𝓓 c (ι b))
 where
  γ : (Σ b' ꞉ B , ι b' ≪⟨ 𝓓 ⟩ ι b) → Σ b' ꞉ B , b' ≪ᴮ⟨ 𝓓 ⟩[ c ] b
  γ (b' , b'≪b) = b' , ≪-to-≪ᴮ 𝓓 c b' b b'≪b

\end{code}

It seems that the first lemma from
https://www.cs.bham.ac.uk/~mhe/papers/interpolation.pdf cannot work here,
because ≪ may be non-small when comparing non-basis elements.

≪-∐-lemma : (𝓓 : DCPO {𝓤} {𝓣}) → is-a-continuous-dcpo 𝓓
           → (x y : ⟨ 𝓓 ⟩) {D : 𝓥 ̇ } (𝒹 : D → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 𝒹)
           → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
           → x ≪⟨ 𝓓 ⟩ y
           → ∃ d ꞉ D , x ≪⟨ 𝓓 ⟩ 𝒹 d
≪-∐-lemma 𝓓 (B , ι , ≺ , c) x y {D} 𝒹 δ y⊑∐ x≪y = {!!}
 where
  I : 𝓥 ̇ -- This does not type check
  I = Σ b ꞉ B , Σ d ꞉ D , ι b ≪⟨ 𝓓 ⟩ 𝒹 d

Below, we do follow the proof (of the second lemma) from
https://www.cs.bham.ac.uk/~mhe/papers/interpolation.pdf, but adapted so that we
only include basis elements in the newly constructed directed family.

\begin{code}

≪-INT₁ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
         (x y : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ y
       → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
≪-INT₁ 𝓓 {B} {ι} (≺ , c) x y x≪y = ∥∥-rec ∥∥-is-a-prop γ (c y)
 where
  cd : is-a-basis 𝓓 ι
  cd = (≺ , c)
  γ : (Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → B) ,
       ((i : I) → ι (α i) ≪⟨ 𝓓 ⟩ y)
      × (Σ δ ꞉ is-Directed 𝓓 (ι ∘ α) , ∐ 𝓓 δ ≡ y))
    → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
  γ (I , α , α≪y , δ , ∐α≡y) = ∥∥-functor s t
   where
    J : 𝓥 ̇
    J = Σ b ꞉ B , Σ i ꞉ I , b ≪ᴮ⟨ 𝓓 ⟩[ cd ] α i
    s : (Σ j ꞉ J , x ⊑⟨ 𝓓 ⟩ ι (pr₁ j))
      → Σ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
    s ((b , i , b≪ᴮαi) , x⊑b) = α i , ≪₁ , ≪₂
     where
      ≪₁ : x ≪⟨ 𝓓 ⟩ ι (α i)
      ≪₁ = ⊑-≪-to-≪ 𝓓 x⊑b (≪ᴮ-to-≪ 𝓓 cd b (α i) b≪ᴮαi)
      ≪₂ : ι (α i) ≪⟨ 𝓓 ⟩ y
      ≪₂ = α≪y i
    t : ∃ j ꞉ J , x ⊑⟨ 𝓓 ⟩ ι (pr₁ j)
    t = x≪y J β ε y⊑∐β
     where
      β : J → ⟨ 𝓓 ⟩
      β = ι ∘ pr₁
      ε : is-Directed 𝓓 β
      ε = J-inh , β-wdirected
       where
        J-inh : ∥ J ∥
        J-inh = do
         i ← Directed-implies-inhabited 𝓓 δ
         (b , b≪ᴮαi) ← ≪ᴮ-INT₀ 𝓓 cd (α i)
         ∣ b , i , b≪ᴮαi ∣
        β-wdirected : is-weakly-directed (underlying-order 𝓓) β
        β-wdirected (b₁ , i₁ , b₁≪ᴮαi₁) (b₂ , i₂ , b₂≪ᴮαi₂) = do
         (k , αi₁⊑αk , αi₂⊑αk) ← Directed-implies-weakly-directed 𝓓 δ i₁ i₂
         let b₁≪αk = ≪-⊑-to-≪ 𝓓 (≪ᴮ-to-≪ 𝓓 cd b₁ (α i₁) b₁≪ᴮαi₁) αi₁⊑αk
         let b₂≪αk = ≪-⊑-to-≪ 𝓓 (≪ᴮ-to-≪ 𝓓 cd b₂ (α i₂) b₂≪ᴮαi₂) αi₂⊑αk
         (L , ϕ , ϕ≪αk , (ε , ∐ϕ≡αk)) ← c (ι (α k))
         (l₁ , b₁⊑ϕl₁) ← b₁≪αk L (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (∐ϕ≡αk ⁻¹))
         (l₂ , b₂⊑ϕl₂) ← b₂≪αk L (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (∐ϕ≡αk ⁻¹))
         (m , ϕl₁⊑ϕm , ϕl₂⊑ϕm) ← Directed-implies-weakly-directed 𝓓 ε l₁ l₂
         let ϕm≪ᴮαk = ≪-to-≪ᴮ 𝓓 cd (ϕ m) (α k) (ϕ≪αk m)
         let b₁⊑ϕm = ι b₁     ⊑⟨ 𝓓 ⟩[ b₁⊑ϕl₁ ]
                     ι (ϕ l₁) ⊑⟨ 𝓓 ⟩[ ϕl₁⊑ϕm ]
                     ι (ϕ m)  ∎⟨ 𝓓 ⟩
         let b₂⊑ϕm = ι b₂     ⊑⟨ 𝓓 ⟩[ b₂⊑ϕl₂ ]
                     ι (ϕ l₂) ⊑⟨ 𝓓 ⟩[ ϕl₂⊑ϕm ]
                     ι (ϕ m)  ∎⟨ 𝓓 ⟩
         ∣ (ϕ m , k , ϕm≪ᴮαk) , b₁⊑ϕm , b₂⊑ϕm ∣
      y⊑∐β = y      ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (∐α≡y ⁻¹) ]
             ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩[ h ]
             ∐ 𝓓 ε ∎⟨ 𝓓 ⟩
       where
        h = ∐-is-lowerbound-of-upperbounds 𝓓 δ (∐ 𝓓 ε) ub
         where
          ub : (i : I) → (ι ∘ α) i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
          ub i = ∥∥-rec (prop-valuedness 𝓓 (ι (α i)) (∐ 𝓓 ε))
                 g (c (ι (α i)))
           where
            g : (Σ L ꞉ 𝓥 ̇ , Σ ϕ ꞉ (L → B) ,
                 ((l : L) → ι (ϕ l) ≪⟨ 𝓓 ⟩ ι (α i))
                × (Σ φ ꞉ is-Directed 𝓓 (ι ∘ ϕ) , ∐ 𝓓 φ ≡ ι (α i)))
              → ι (α i) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
            g (L , ϕ , ϕ≪αi , φ , ∐ϕ≡αi) = ι (α i)  ⊑⟨ 𝓓 ⟩[ ⊑₁ ]
                                              ∐ 𝓓 φ ⊑⟨ 𝓓 ⟩[ ⊑₂ ]
                                              ∐ 𝓓 ε ∎⟨ 𝓓 ⟩
             where
              ⊑₁ = ≡-to-⊑ 𝓓 (∐ϕ≡αi ⁻¹)
              ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓓 φ (∐ 𝓓 ε) ub'
               where
                ub' : (l : L) → ι (ϕ l) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
                ub' l = ∐-is-upperbound 𝓓 ε j
                 where
                  j : J
                  j = ϕ l , i , ≪-to-≪ᴮ 𝓓 cd (ϕ l) (α i) (ϕ≪αi l)

≪ᴮ-INT₁ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b₁ b₂ : B) → b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂
        → ∃ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂
≪ᴮ-INT₁ 𝓓 {B} {ι} c b₁ b₂ b₁≪ᴮb₂ =
 ∥∥-functor γ (≪-INT₁ 𝓓 c (ι b₁) (ι b₂) (≪ᴮ-to-≪ 𝓓 c b₁ b₂ b₁≪ᴮb₂))
  where
   γ : (Σ b ꞉ B , ι b₁ ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ ι b₂)
     → Σ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂
   γ (b , b₁≪b , b≪b₂) =
    b , ≪-to-≪ᴮ 𝓓 c b₁ b b₁≪b , ≪-to-≪ᴮ 𝓓 c b b₂ b≪b₂

\end{code}

An interpolation property starting from two inequalities.

≪ᴮ-INT₂ shows that a basis of a continuous dcpo satisifies the axioms of an
"abstract basis" as set out in IdealCompletion.

\begin{code}

≪-INT₂ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
         (x y z : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
       → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × y ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ z
≪-INT₂ 𝓓 {B} {ι} (≺ , c) x y z x≪z y≪z = do
 b₁ , x≪b₁ , b₁≪z ← ≪-INT₁ 𝓓 cd x z x≪z
 b₂ , y≪b₂ , b₂≪z ← ≪-INT₁ 𝓓 cd y z y≪z
 I , α , α≪z , δ , ∐α≡z ← c z
 i₁ , b₁⊑αi₁ ← b₁≪z I (ι ∘ α) δ (≡-to-⊑ 𝓓 (∐α≡z ⁻¹))
 i₂ , b₂⊑αi₂ ← b₂≪z I (ι ∘ α) δ (≡-to-⊑ 𝓓 (∐α≡z ⁻¹))
 k , αi₁⊑αk , αi₂⊑αk ← Directed-implies-weakly-directed 𝓓 δ i₁ i₂
 let b₁⊑αk = ι b₁     ⊑⟨ 𝓓 ⟩[ b₁⊑αi₁ ]
             ι (α i₁) ⊑⟨ 𝓓 ⟩[ αi₁⊑αk ]
             ι (α k)  ∎⟨ 𝓓 ⟩
 let b₂⊑αk = ι b₂     ⊑⟨ 𝓓 ⟩[ b₂⊑αi₂ ]
             ι (α i₂) ⊑⟨ 𝓓 ⟩[ αi₂⊑αk ]
             ι (α k)  ∎⟨ 𝓓 ⟩
 let x≪αk = ≪-⊑-to-≪ 𝓓 x≪b₁ b₁⊑αk
 let y≪αk = ≪-⊑-to-≪ 𝓓 y≪b₂ b₂⊑αk
 ∣ α k , x≪αk , y≪αk , α≪z k ∣
 where
  cd : is-a-basis 𝓓 ι
  cd = (≺ , c)

≪ᴮ-INT₂ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b₁ b₂ b₃ : B) → b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃ → b₂ ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃
        → ∃ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b₂ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃
≪ᴮ-INT₂ 𝓓 {B} {ι} c b₁ b₂ b₃ b₁≪ᴮb₃ b₂≪ᴮb₃ =
 ∥∥-functor γ (≪-INT₂ 𝓓 c (ι b₁) (ι b₂) (ι b₃)
               (≪ᴮ-to-≪ 𝓓 c b₁ b₃ b₁≪ᴮb₃)
               (≪ᴮ-to-≪ 𝓓 c b₂ b₃ b₂≪ᴮb₃))
  where
   γ : (Σ b ꞉ B , ι b₁ ≪⟨ 𝓓 ⟩ ι b × ι b₂ ≪⟨ 𝓓 ⟩ ι b × ι b  ≪⟨ 𝓓 ⟩ ι b₃)
     → Σ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b₂ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b  ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃
   γ (b , b₁≪b , b₂≪b , b≪b₃) = b , ≪-to-≪ᴮ 𝓓 c b₁ b b₁≪b ,
                                    ≪-to-≪ᴮ 𝓓 c b₂ b b₂≪b ,
                                    ≪-to-≪ᴮ 𝓓 c b  b₃ b≪b₃

\end{code}
