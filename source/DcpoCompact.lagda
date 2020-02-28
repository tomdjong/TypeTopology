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
≪-to-⊑ 𝓓 {x} {y} a = ∥∥-rec (prop-valuedness 𝓓 x y) γ g
 where
  α : 𝟙{𝓥} → ⟨ 𝓓 ⟩
  α * = y
  γ : (Σ i ꞉ 𝟙 , x ⊑⟨ 𝓓 ⟩ α i) → x ⊑⟨ 𝓓 ⟩ y
  γ (* , l) = l
  g : ∃ i ꞉ 𝟙 , x ⊑⟨ 𝓓 ⟩ α i
  g = a 𝟙 α δ (∐-is-upperbound 𝓓 δ *)
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
⊑-≪-⊑-to-≪ 𝓓 {x'} {x} {y} {y'} u a v I α δ w = γ
 where
  γ : ∃ i ꞉ I , x' ⊑⟨ 𝓓 ⟩ α i
  γ = ∥∥-functor g h
   where
    g : (Σ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i)
      → (Σ i ꞉ I , x' ⊑⟨ 𝓓 ⟩ α i)
    g (i , l) = (i , t)
     where
      t = x'  ⊑⟨ 𝓓 ⟩[ u ]
          x   ⊑⟨ 𝓓 ⟩[ l ]
          α i ∎⟨ 𝓓 ⟩
    h : ∃ i ꞉ I , x ⊑⟨ 𝓓 ⟩ α i
    h = a I α δ s
     where
      s = y     ⊑⟨ 𝓓 ⟩[ v ]
          y'    ⊑⟨ 𝓓 ⟩[ w ]
          ∐ 𝓓 δ ∎⟨ 𝓓 ⟩

⊑-≪-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
         → x ⊑⟨ 𝓓 ⟩ y
         → y ≪⟨ 𝓓 ⟩ z
         → x ≪⟨ 𝓓 ⟩ z
⊑-≪-to-≪ 𝓓 {x} {y} {z} u a = ⊑-≪-⊑-to-≪ 𝓓 u a (reflexivity 𝓓 z)

≪-⊑-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y z : ⟨ 𝓓 ⟩}
         → x ≪⟨ 𝓓 ⟩ y
         → y ⊑⟨ 𝓓 ⟩ z
         → x ≪⟨ 𝓓 ⟩ z
≪-⊑-to-≪ 𝓓 {x} {y} {z} a u = ⊑-≪-⊑-to-≪ 𝓓 (reflexivity 𝓓 x) a u

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
is-a-continuous-dcpo {𝓤} {𝓣} 𝓓 = Σ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) , γ ι
 where
  γ : {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
  γ {B} ι = (x : ⟨ 𝓓 ⟩)
          → ∃ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) , (β-≪-x β x) × (∐β≡x β x)
   where
    β-≪-x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
    β-≪-x {I} β x = ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
    ∐β≡x : {I : 𝓥 ̇ } → (I → B) → ⟨ 𝓓 ⟩ → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
    ∐β≡x β x = Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x

basis : (𝓓 : DCPO {𝓤} {𝓣}) → is-a-continuous-dcpo 𝓓 → 𝓥 ̇
basis 𝓓 = pr₁

basis-of-continuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → is-a-continuous-dcpo 𝓓
                         → Σ B ꞉ 𝓥 ̇ , (B → ⟨ 𝓓 ⟩)
basis-of-continuous-dcpo 𝓓 (B , ι , _) = B , ι

{- basis-property : (𝓓 : DCPO {𝓤} {𝓣}) → (cd : is-a-continuous-dcpo 𝓓)
               → (x : ⟨ 𝓓 ⟩)
               → Σ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → ) ,
                 ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
                 × (Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x)
basis-property 𝓓 (B , ι , c) = c -}

is-an-algebraic-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-an-algebraic-dcpo {𝓤} {𝓣} 𝓓 = Σ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) , γ ι
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
algebraicity-implies-continuity 𝓓 (B , ι , a) = B , ι , c
 where
  c : _
  c x = ∥∥-functor γ (a x)
   where
    γ : _
    γ (I , β , κ , wb , s) = I , β , wb , s

is-algebraic' : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-algebraic' {𝓤} {𝓣} 𝓓 = Σ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) , γ ι
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
algebraic-implies-algebraic' 𝓓 (B , ι , a) = B , ι , a'
 where
  a' : _
  a' x = ∥∥-functor γ (a x)
   where
    γ : _
    γ (I , β , κ , wb , s) = I , β , κ , s

algebraic'-implies-algebraic : (𝓓 : DCPO {𝓤} {𝓣})
                             → is-algebraic' 𝓓
                             → is-an-algebraic-dcpo 𝓓
algebraic'-implies-algebraic 𝓓 (B , ι , a') = B , ι , a
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

basis-≤ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
        → basis 𝓓 c → basis 𝓓 c → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
basis-≤ 𝓓 (B , ι , _) b b' = ι b ≪⟨ 𝓓 ⟩ ι b'

syntax basis-≤ 𝓓 c b b' = b ≤ᴮ⟨ 𝓓 ⟩[ c ] b'

≪-INT₀ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
       → (b : basis 𝓓 c)
       → ∃ b' ꞉ basis 𝓓 c , b' ≤ᴮ⟨ 𝓓 ⟩[ c ] b
≪-INT₀ 𝓓 (B , ι , c) b = do
 (I , β , ≪b , (δ , ∐β≡b)) ← c (ι b)
 i ← Directed-implies-inhabited 𝓓 δ
 ∣ (β i) , (≪b i) ∣

open import UF-Size

≪-INT₁ : (𝓓 : DCPO {𝓤} {𝓣}) (c : is-a-continuous-dcpo 𝓓)
       → ((x y : basis 𝓓 c) → (x ≤ᴮ⟨ 𝓓 ⟩[ c ] y) has-size 𝓥)
       → (x y : basis 𝓓 c)
       → x ≤ᴮ⟨ 𝓓 ⟩[ c ] y
       → ∃ b ꞉ basis 𝓓 c , x ≤ᴮ⟨ 𝓓 ⟩[ c ] b × b ≤ᴮ⟨ 𝓓 ⟩[ c ] y
≪-INT₁ 𝓓 (B , ι , c) ≤-small x y x≤y = ∥∥-rec ∥∥-is-a-prop γ (c (ι y))
 where
  cd : is-a-continuous-dcpo 𝓓
  cd = (B , ι , c)
  γ : Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → B) ,
      ((i : I) → α i ≤ᴮ⟨ 𝓓 ⟩[ cd ] y) ×
      (Σ δ ꞉ is-Directed 𝓓 (ι ∘ α) , ∐ 𝓓 δ ≡ ι y)
    → ∃ b ꞉ B , x ≤ᴮ⟨ 𝓓 ⟩[ cd ] b × b ≤ᴮ⟨ 𝓓 ⟩[ cd ] y
  γ (I , α , α≪y , (δ , ∐α≡y)) = {!!}
   where
    _≤'_ : B → B → 𝓥 ̇
    b ≤' b' = has-size-type (≤-small b b')
    J : 𝓥 ̇
    J = Σ b ꞉ B , ∃ i ꞉ I , b ≤' α i
    β : J → ⟨ 𝓓 ⟩
    β (b , _) = ι b
    ε : is-Directed 𝓓 β
    ε = {!!}
    claim₀ : ι y ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
    claim₀ = {!!}
    claim₁ : ∃ j ꞉ J , ι x ⊑⟨ 𝓓 ⟩ β j
    claim₁ = x≤y J β ε claim₀


{-

do
 (I , α , ≪y , (δ , ∐α≡y)) ← c (ι y)
 v ← {!!}
 {!!}

-}

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

\end{code}
