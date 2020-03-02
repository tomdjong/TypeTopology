Tom de Jong, 11 December 2019 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
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

compact : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
compact 𝓓 x = x ≪⟨ 𝓓 ⟩ x

\end{code}

\begin{code}

open import UF-Equiv
open import UF-Size

is-a-continuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-continuous-dcpo {𝓤} {𝓣} 𝓓 =
 Σ B ꞉ 𝓥 ̇ ,
 Σ ι ꞉ (B → ⟨ 𝓓 ⟩) ,
 ((b₀ b₁ : B) → (ι b₀ ≪⟨ 𝓓 ⟩ ι b₁) has-size 𝓥) × γ ι
  where
   γ : {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
   γ {B} ι = (x : ⟨ 𝓓 ⟩)
           → ∃ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) , (β≪x β x) × (∐β≡x β x)
    where
     β≪x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
     β≪x {I} β x = ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
     ∐β≡x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
     ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x

basis : (𝓓 : DCPO {𝓤} {𝓣}) → is-a-continuous-dcpo 𝓓 → 𝓥 ̇
basis 𝓓 = pr₁

basis-to-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
              → basis 𝓓 c → ⟨ 𝓓 ⟩
basis-to-dcpo 𝓓 (B , ι , _) = ι

basis-≤ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
        → basis 𝓓 c → basis 𝓓 c → 𝓥 ̇
basis-≤ 𝓓 (B , ι , ≤ , _) b b' = has-size-type (≤ b b')

syntax basis-≤ 𝓓 c b b' = b ≤ᴮ⟨ 𝓓 ⟩[ c ] b'

≤ᴮ-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓) (b b' : basis 𝓓 c)
        → b ≤ᴮ⟨ 𝓓 ⟩[ c ] b' → basis-to-dcpo 𝓓 c b ≪⟨ 𝓓 ⟩ basis-to-dcpo 𝓓 c b'
≤ᴮ-to-≪ 𝓓 c b b' b≤ᴮb' = ⌜ e ⌝ b≤ᴮb'
 where
  ι : basis 𝓓 c → ⟨ 𝓓 ⟩
  ι = basis-to-dcpo 𝓓 c
  e : b ≤ᴮ⟨ 𝓓 ⟩[ c ] b' ≃ ι b ≪⟨ 𝓓 ⟩ ι b'
  e = has-size-equiv (≤ b b')
   where
    ≤ : (b b' : basis 𝓓 c)
      → (ι b ≪⟨ 𝓓 ⟩ ι b') has-size 𝓥
    ≤ = pr₁ (pr₂ (pr₂ c))

≪-to-≤ᴮ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓) (b b' : basis 𝓓 c)
        → basis-to-dcpo 𝓓 c b ≪⟨ 𝓓 ⟩ basis-to-dcpo 𝓓 c b' → b ≤ᴮ⟨ 𝓓 ⟩[ c ] b'
≪-to-≤ᴮ 𝓓 c b b' b≪b' = ⌜ ≃-sym e ⌝ b≪b'
 where
  ι : basis 𝓓 c → ⟨ 𝓓 ⟩
  ι = basis-to-dcpo 𝓓 c
  e : b ≤ᴮ⟨ 𝓓 ⟩[ c ] b' ≃ ι b ≪⟨ 𝓓 ⟩ ι b'
  e = has-size-equiv (≤ b b')
   where
    ≤ : (b b' : basis 𝓓 c)
      → (ι b ≪⟨ 𝓓 ⟩ ι b') has-size 𝓥
    ≤ = pr₁ (pr₂ (pr₂ c))

is-an-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-an-algebraic-dcpo {𝓤} {𝓣} 𝓓 =
 Σ B ꞉ 𝓥 ̇ ,
 Σ ι ꞉ (B → ⟨ 𝓓 ⟩) ,
 ((b₀ b₁ : B) → (ι b₀ ≪⟨ 𝓓 ⟩ ι b₁) has-size 𝓥) × γ ι
  where
   γ : {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
   γ {B} ι = (x : ⟨ 𝓓 ⟩)
           → ∃ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) , (κ β) × (β-≪-x β x) × (∐β≡x β x)
    where
     κ : {I : 𝓥 ̇ } → (I → B) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
     κ {I} β = (i : I) → compact 𝓓 (ι (β i))
     β-≪-x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
     β-≪-x {I} β x = ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
     ∐β≡x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
     ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x

algebraicity-implies-continuity : (𝓓 : DCPO {𝓤} {𝓣})
                                → is-an-algebraic-dcpo 𝓓
                                → is-a-continuous-dcpo 𝓓
algebraicity-implies-continuity 𝓓 (B , ι , ≤ , a) = B , ι , ≤ , c
 where
  c : _
  c x = ∥∥-functor γ (a x)
   where
    γ : _
    γ (I , β , κ , wb , s) = I , β , wb , s

is-algebraic' : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-algebraic' {𝓤} {𝓣} 𝓓 =
 Σ B ꞉ 𝓥 ̇ ,
 Σ ι ꞉ (B → ⟨ 𝓓 ⟩) ,
 ((b₀ b₁ : B) → (ι b₀ ≪⟨ 𝓓 ⟩ ι b₁) has-size 𝓥) × γ ι
  where
   γ : {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
   γ {B} ι = (x : ⟨ 𝓓 ⟩)
           → ∃ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) , (κ β) × (∐β≡x β x)
    where
     κ : {I : 𝓥 ̇ } → (I → B) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
     κ {I} β = (i : I) → compact 𝓓 (ι (β i))
     ∐β≡x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
     ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x

algebraic-implies-algebraic' : (𝓓 : DCPO {𝓤} {𝓣})
                             → is-an-algebraic-dcpo 𝓓
                             → is-algebraic' 𝓓
algebraic-implies-algebraic' 𝓓 (B , ι , ≤ , a) = B , ι , ≤ , a'
 where
  a' : _
  a' x = ∥∥-functor γ (a x)
   where
    γ : _
    γ (I , β , κ , wb , s) = I , β , κ , s

algebraic'-implies-algebraic : (𝓓 : DCPO {𝓤} {𝓣})
                             → is-algebraic' 𝓓
                             → is-an-algebraic-dcpo 𝓓
algebraic'-implies-algebraic 𝓓 (B , ι , ≤ , a') = B , ι , ≤ , a
 where
  a : _
  a x = ∥∥-functor γ (a' x)
   where
    γ : _
    γ (I , β , κ , s) = I , β , κ , wb , s
     where
      wb : (i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x
      wb  i = ≪-⊑-to-≪ 𝓓 v w
       where
        v : ι (β i) ≪⟨ 𝓓 ⟩ ι (β i)
        v = κ i
        w : ι (β i) ⊑⟨ 𝓓 ⟩ x
        w = transport (λ - → ι (β i) ⊑⟨ 𝓓 ⟩ -) ∐≡x w'
         where
          δ : is-Directed 𝓓 (ι ∘ β)
          δ = pr₁ s
          ∐≡x : ∐ 𝓓 δ ≡ x
          ∐≡x = pr₂ s
          w' : ι (β i) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
          w' = ∐-is-upperbound 𝓓 δ i

\end{code}

\begin{code}

≪-INT₀ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
       → (x : ⟨ 𝓓 ⟩)
       → ∃ b ꞉ basis 𝓓 c , basis-to-dcpo 𝓓 c b ≪⟨ 𝓓 ⟩ x
≪-INT₀ 𝓓 (B , ι , ≤ , c) x = do
 (I , β , ≪x , δ , ∐β≡x) ← c x
 i ← Directed-implies-inhabited 𝓓 δ
 ∣ (β i) , ≪x i ∣

≤ᴮ-INT₀ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
        → (b : basis 𝓓 c)
        → ∃ b' ꞉ basis 𝓓 c , b' ≤ᴮ⟨ 𝓓 ⟩[ c ] b
≤ᴮ-INT₀ 𝓓 c b = ∥∥-functor γ (≪-INT₀ 𝓓 c (ι b))
 where
  B : 𝓥 ̇
  B = basis 𝓓 c
  ι : B → ⟨ 𝓓 ⟩
  ι = basis-to-dcpo 𝓓 c
  γ : (Σ b' ꞉ B , ι b' ≪⟨ 𝓓 ⟩ ι b) → Σ b' ꞉ B , b' ≤ᴮ⟨ 𝓓 ⟩[ c ] b
  γ (b' , b'≪b) = b' , ≪-to-≤ᴮ 𝓓 c b' b b'≪b

\end{code}

It seems that the first lemma from
https://www.cs.bham.ac.uk/~mhe/papers/interpolation.pdf cannot work here,
because ≪ may be non-small when comparing non-basis elements.

≪-∐-lemma : (𝓓 : DCPO {𝓤} {𝓣}) → is-a-continuous-dcpo 𝓓
           → (x y : ⟨ 𝓓 ⟩) {D : 𝓥 ̇ } (𝒹 : D → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 𝒹)
           → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
           → x ≪⟨ 𝓓 ⟩ y
           → ∃ d ꞉ D , x ≪⟨ 𝓓 ⟩ 𝒹 d
≪-∐-lemma 𝓓 (B , ι , ≤ , c) x y {D} 𝒹 δ y⊑∐ x≪y = {!!}
 where
  I : 𝓥 ̇ -- This does not type check
  I = Σ b ꞉ B , Σ d ꞉ D , ι b ≪⟨ 𝓓 ⟩ 𝒹 d

Below, we do follow the proof from
https://www.cs.bham.ac.uk/~mhe/papers/interpolation.pdf, but adapted so that we
only include basis elements in the newly constructed directed family.

\begin{code}

≪-INT₁ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
       → (x y : ⟨ 𝓓 ⟩)
       → x ≪⟨ 𝓓 ⟩ y
       → ∃ b ꞉ basis 𝓓 c ,
           x ≪⟨ 𝓓 ⟩ basis-to-dcpo 𝓓 c b
         × basis-to-dcpo 𝓓 c b ≪⟨ 𝓓 ⟩ y
≪-INT₁ 𝓓 (B , ι , ≤ , c) x y x≪y = ∥∥-rec ∥∥-is-a-prop γ (c y)
 where
  cd : is-a-continuous-dcpo 𝓓
  cd = (B , ι , ≤ , c)
  γ : (Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → B) ,
       ((i : I) → ι (α i) ≪⟨ 𝓓 ⟩ y)
      × (Σ δ ꞉ is-Directed 𝓓 (ι ∘ α) , ∐ 𝓓 δ ≡ y))
    → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
  γ (I , α , α≪y , δ , ∐α≡y) = ∥∥-functor s t
   where
    J : 𝓥 ̇
    J = Σ b ꞉ B , Σ i ꞉ I , b ≤ᴮ⟨ 𝓓 ⟩[ cd ] α i
    s : (Σ j ꞉ J , x ⊑⟨ 𝓓 ⟩ ι (pr₁ j))
      → Σ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
    s ((b , i , b≤ᴮαi) , x⊑b) = α i , ≪₁ , ≪₂
     where
      ≪₁ : x ≪⟨ 𝓓 ⟩ ι (α i)
      ≪₁ = ⊑-≪-to-≪ 𝓓 x⊑b (≤ᴮ-to-≪ 𝓓 cd b (α i) b≤ᴮαi)
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
         (b , b≤ᴮαi) ← ≤ᴮ-INT₀ 𝓓 cd (α i)
         ∣ b , i , b≤ᴮαi ∣
        β-wdirected : is-weakly-directed (underlying-order 𝓓) β
        β-wdirected (b₁ , i₁ , b₁≤ᴮαi₁) (b₂ , i₂ , b₂≤ᴮαi₂) = do
         (k , αi₁⊑αk , αi₂⊑αk) ← Directed-implies-weakly-directed 𝓓 δ i₁ i₂
         let b₁≪αk = ≪-⊑-to-≪ 𝓓 (≤ᴮ-to-≪ 𝓓 cd b₁ (α i₁) b₁≤ᴮαi₁) αi₁⊑αk
         let b₂≪αk = ≪-⊑-to-≪ 𝓓 (≤ᴮ-to-≪ 𝓓 cd b₂ (α i₂) b₂≤ᴮαi₂) αi₂⊑αk
         (L , ϕ , ϕ≪αk , (ε , ∐ϕ≡αk)) ← c (ι (α k))
         (l₁ , b₁⊑ϕl₁) ← b₁≪αk L (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (∐ϕ≡αk ⁻¹))
         (l₂ , b₂⊑ϕl₂) ← b₂≪αk L (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (∐ϕ≡αk ⁻¹))
         (m , ϕl₁⊑ϕm , ϕl₂⊑ϕm) ← Directed-implies-weakly-directed 𝓓 ε l₁ l₂
         let ϕm≤ᴮαk = ≪-to-≤ᴮ 𝓓 cd (ϕ m) (α k) (ϕ≪αk m)
         let b₁⊑ϕm = ι b₁     ⊑⟨ 𝓓 ⟩[ b₁⊑ϕl₁ ]
                     ι (ϕ l₁) ⊑⟨ 𝓓 ⟩[ ϕl₁⊑ϕm ]
                     ι (ϕ m)  ∎⟨ 𝓓 ⟩
         let b₂⊑ϕm = ι b₂     ⊑⟨ 𝓓 ⟩[ b₂⊑ϕl₂ ]
                     ι (ϕ l₂) ⊑⟨ 𝓓 ⟩[ ϕl₂⊑ϕm ]
                     ι (ϕ m)  ∎⟨ 𝓓 ⟩
         ∣ (ϕ m , k , ϕm≤ᴮαk) , b₁⊑ϕm , b₂⊑ϕm ∣
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
                  j = ϕ l , i , ≪-to-≤ᴮ 𝓓 cd (ϕ l) (α i) (ϕ≪αi l)




{-

{-
≪-int-lemma : (𝓓 : DCPO {𝓤} {𝓣}) → is-a-continuous-dcpo 𝓓
            → (x y : ⟨ 𝓓 ⟩) {𝓐 : 𝓥 ̇ } (α : 𝓐 → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
            → y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 δ
            → x ≪⟨ 𝓓 ⟩ y
            → ∃ a ꞉ 𝓐 , x ≪⟨ 𝓓 ⟩ α a
≪-int-lemma 𝓓 c x y α δ y⊑∐ x≪y = {!!}
 where
--  I

≪-INT₂ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
       → (b₀ b₁ b : basis 𝓓 c)
       → b₀ ≤ᴮ⟨ 𝓓 ⟩[ c ] b
       → b₁ ≤ᴮ⟨ 𝓓 ⟩[ c ] b
       → ∃ b' ꞉ basis 𝓓 c ,
         b' ≤ᴮ⟨ 𝓓 ⟩[ c ] b
       × b₀ ≤ᴮ⟨ 𝓓 ⟩[ c ] b'
       × b₁ ≤ᴮ⟨ 𝓓 ⟩[ c ] b'
≪-INT₂ 𝓓 (B , ι , c) b₀ b₁ b b₀≤b b₁≤b = {!!}
-}
-}


\end{code}
