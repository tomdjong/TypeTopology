Tom de Jong
8 March 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc

module IdealCompletion-Properties
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe) -- universe where the index types for directedness
                        -- completeness live
       where

open import Dcpo pt fe 𝓥
open import DcpoApproximation pt fe 𝓥
open import DcpoBasis pt fe 𝓥
open import IdealCompletion pt fe pe 𝓥

open import UF-Equiv
open import UF-Powersets

open PropositionalTruncation pt

module Idl-Properties
        {X : 𝓤 ̇ }
        (_≺_ : X → X → 𝓥 ⊔ 𝓣 ̇ )
        (≺-prop-valued : {x y : X} → is-prop (x ≺ y))
        (INT₂ : {y₀ y₁ x : X} → y₀ ≺ x → y₁ ≺ x
              → ∃ z ꞉ X , y₀ ≺ z × y₁ ≺ z × z ≺ x)
        (INT₀ : (x : X) → ∃ y ꞉ X , y ≺ x)
        (≺-trans : {x y z : X} → x ≺ y → y ≺ z → x ≺ z)
       where

 open Ideals {𝓤} {𝓥 ⊔ 𝓣} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans

 roundness : (I : Idl) {x : X} → (x ∈ᵢ I) → ∃ y ꞉ X , y ∈ᵢ I × x ≺ y
 roundness I {x} xI = ∥∥-functor γ h
  where
   h : ∃ y ꞉ X , y ∈ᵢ I × x ≺ y × x ≺ y
   h = directed-sets-are-weakly-directed (carrier I)
       (ideals-are-directed-sets (carrier I) (ideality I))
       x x xI xI
   γ : (Σ y ꞉ X , y ∈ᵢ I × x ≺ y × x ≺ y)
     → Σ y ꞉ X , y ∈ᵢ I × x ≺ y
   γ (y , yI , l , _) = y , yI , l

 ↓_ : X → Idl
 ↓ x = (λ (y : X) → (y ≺ x) , ≺-prop-valued) ,
       ls , inh , δ
  where
   ls : is-lower-set (λ y → (y ≺ x) , ≺-prop-valued)
   ls x y = ≺-trans
   inh : ∃ y ꞉ X , y ≺ x
   inh = INT₀ x
   δ : is-weakly-directed-set (λ y → (y ≺ x) , ≺-prop-valued)
   δ y₁ y₂ l₁ l₂ = ∥∥-functor γ (INT₂ l₁ l₂)
    where
     γ : (Σ z ꞉ X , y₁ ≺ z × y₂ ≺ z × z ≺ x)
       → (Σ z ꞉ X , z ≺ x × y₁ ≺ z × y₂ ≺ z)
     γ (z , m₁ , m₂ , n) = z , n , m₁ , m₂

 ↓-is-monotone : {x y : X} → x ≺ y → (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
 ↓-is-monotone {x} {y} l _ m = ≺-trans m l

\end{code}

\begin{code}

module SmallIdeals
        {X : 𝓥 ̇ }
        (_≺_ : X → X → 𝓥 ̇ )
        (≺-prop-valued : {x y : X} → is-prop (x ≺ y))
        (INT₂ : {y₀ y₁ x : X} → y₀ ≺ x → y₁ ≺ x
              → ∃ z ꞉ X , y₀ ≺ z × y₁ ≺ z × z ≺ x)
        (INT₀ : (x : X) → ∃ y ꞉ X , y ≺ x)
        (≺-trans : {x y z : X} → x ≺ y → y ≺ z → x ≺ z)
       where

 open Ideals {𝓥} {𝓥} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans
 open Idl-Properties {𝓥} {𝓥} {X} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans

 ↓-of-ideal : (I : Idl) → 𝕋 (carrier I) → Idl
 ↓-of-ideal I (i , _) = ↓ i

 ↓-of-ideal-is-directed : (I : Idl) → is-Directed Idl-DCPO (↓-of-ideal I)
 ↓-of-ideal-is-directed (I , ι) = inh , ε
  where
   δ : is-weakly-directed-set I
   δ = directed-sets-are-weakly-directed I (ideals-are-directed-sets I ι)
   inh : ∥ 𝕋 I ∥
   inh = directed-sets-are-inhabited I (ideals-are-directed-sets I ι)
   ε : is-weakly-directed _⊑_ (↓-of-ideal (I , ι))
   ε (i , p) (j , q) = ∥∥-functor γ (δ i j p q)
    where
     γ : (Σ x ꞉ X , x ∈ I × i ≺ x × j ≺ x)
       → Σ k ꞉ 𝕋 I , (↓-of-ideal (I , ι) (i , p) ⊑ ↓-of-ideal (I , ι) k)
                   × (↓-of-ideal (I , ι) (j , q) ⊑ ↓-of-ideal (I , ι) k)
     γ (x , xI , lᵢ , lⱼ) = (x , xI) , (u , v)
      where
       u : ↓-of-ideal (I , ι) (i , p) ⊑ ↓-of-ideal (I , ι) (x , xI)
       u y mᵢ = ≺-trans mᵢ lᵢ
       v : ↓-of-ideal (I , ι) (j , q) ⊑ ↓-of-ideal (I , ι) (x , xI)
       v y m = ≺-trans m lⱼ

 Idl-∐-≡ : (I : Idl)
         → I ≡ ∐ Idl-DCPO {_} {↓-of-ideal I} (↓-of-ideal-is-directed I)
 Idl-∐-≡ I = antisymmetry Idl-DCPO I (∐ Idl-DCPO {_} {α} δ) l₁ l₂
  where
   α : 𝕋 (carrier I) → Idl
   α = ↓-of-ideal I
   δ : is-Directed Idl-DCPO α
   δ = ↓-of-ideal-is-directed I
   l₁ : I ⊑⟨ Idl-DCPO ⟩ ∐ Idl-DCPO {_} {α} δ
   l₁ i p = ∥∥-functor γ (roundness I p)
    where
     γ : (Σ j ꞉ X , j ∈ᵢ I × i ≺ j)
       → Σ a ꞉ 𝕋 (carrier I) , i ∈ᵢ α a
     γ (j , q , m) = (j , q) , m
   l₂ : ∐ Idl-DCPO {_} {α} δ ⊑⟨ Idl-DCPO ⟩ I
   l₂ i p = ∥∥-rec (∈-is-a-prop (carrier I) i) γ p
    where
     γ : (Σ j ꞉ 𝕋 (carrier I) , i ≺ pr₁ j) → i ∈ carrier I
     γ ((j , q) , m) = ideals-are-lower-sets (carrier I) (ideality I)
                           i j m q

 Idl-≪-in-terms-of-⊑ : (I J : Idl) → I ≪⟨ Idl-DCPO ⟩ J
                     → ∃ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
 Idl-≪-in-terms-of-⊑ I J u = ∥∥-functor γ g
  where
   γ : (Σ j ꞉ 𝕋 (carrier J) , I ⊑⟨ Idl-DCPO ⟩ (↓-of-ideal J j))
     → Σ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
   γ ((j , p) , l) = j , (p , l)
   g : ∃ j ꞉ 𝕋 (carrier J) , I ⊑⟨ Idl-DCPO ⟩ (↓-of-ideal J j)
   g = u (𝕋 (carrier J)) (↓-of-ideal J) (↓-of-ideal-is-directed J)
       (≡-to-⊑ Idl-DCPO (Idl-∐-≡ J))

 Idl-≪-in-terms-of-⊑₂ : (I J : Idl) → I ≪⟨ Idl-DCPO ⟩ J
                      → ∃ x ꞉ X , Σ y ꞉ X , x ≺ y
                                          × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                                          × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                                          × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑₂ I J u = ∥∥-rec ∥∥-is-a-prop γ (Idl-≪-in-terms-of-⊑ I J u)
  where
   γ : (Σ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x))
     → ∃ x ꞉ X , Σ y ꞉ X , x ≺ y
               × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
               × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
               × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
   γ (x , xJ , s) = ∥∥-functor g (roundness J xJ)
    where
     g : (Σ y ꞉ X , y ∈ᵢ J × x ≺ y)
       → Σ x ꞉ X , Σ y ꞉ X , x ≺ y
                 × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                 × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                 × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
     g (y , yJ , l) = x , y , l , s , t , r
      where
       t : (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
       t = ↓-is-monotone l
       r : (↓ y) ⊑⟨ Idl-DCPO ⟩ J
       r z m = ideals-are-lower-sets (carrier J) (ideality J) z y m yJ

 Idl-≪-in-terms-of-⊑' : (I J : Idl)
                      → ∃ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                      → I ≪⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑' I J = ∥∥-rec (≪-is-prop-valued Idl-DCPO {I} {J}) γ
  where
   γ : (Σ x ꞉ X , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x))
     → I ≪⟨ Idl-DCPO ⟩ J
   γ (x , xJ , s) 𝓐 α δ t = ∥∥-functor g (t x xJ)
    where
     g : (Σ a ꞉ 𝓐 , x ∈ᵢ α a)
       → Σ a ꞉ 𝓐 , I ⊑⟨ Idl-DCPO ⟩ α a
     g (a , xa) = a , r
      where
       r : I ⊑⟨ Idl-DCPO ⟩ α a
       r = transitivity Idl-DCPO I (↓ x) (α a) s q
        where
         q : (↓ x) ⊑⟨ Idl-DCPO ⟩ α a
         q y l = ideals-are-lower-sets (carrier (α a)) (ideality (α a)) y x l xa

 Idl-≪-in-terms-of-⊑₂' : (I J : Idl)
                       → ∃ x ꞉ X , Σ y ꞉ X , x ≺ y
                                 × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                                 × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                                 × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
                       → I ≪⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑₂' I J = ∥∥-rec (≪-is-prop-valued Idl-DCPO {I} {J}) γ
  where
   γ : (Σ x ꞉ X , Σ y ꞉ X , x ≺ y
                × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                × (↓ y) ⊑⟨ Idl-DCPO ⟩ J)
     → I ≪⟨ Idl-DCPO ⟩ J
   γ (x , y , l , s , _ , r) 𝓐 α δ m = ∥∥-functor g (m x (r x l))
    where
     g : (Σ a ꞉ 𝓐 , x ∈ᵢ α a)
       → Σ a ꞉ 𝓐 , I ⊑⟨ Idl-DCPO ⟩ α a
     g (a , xa) = a , h
      where
       h : I ⊑⟨ Idl-DCPO ⟩ α a
       h = transitivity Idl-DCPO I (↓ x) (α a) s s'
        where
         s' : (↓ x) ⊑⟨ Idl-DCPO ⟩ α a
         s' z n = ideals-are-lower-sets (carrier (α a)) (ideality (α a)) z x n xa

\end{code}

\begin{code}

 ∐-from-Idl-to-a-dcpo : (𝓓 : DCPO {𝓤} {𝓣})
                      → (f : X → ⟨ 𝓓 ⟩)
                      → ({x  y : X} → x ≺ y → f x ⊑⟨ 𝓓 ⟩ f y)
                      → Idl → ⟨ 𝓓 ⟩
 ∐-from-Idl-to-a-dcpo 𝓓 f f-monotone I = ∐ 𝓓 {𝕋 (carrier I)} {ι} δ
  where
   ι : 𝕋 (carrier I) → ⟨ 𝓓 ⟩
   ι = f ∘ pr₁
   δ : is-Directed 𝓓 ι
   δ = (directed-sets-are-inhabited (carrier I) Idir) , ε
    where
     Idir : is-directed-set (carrier I)
     Idir = ideals-are-directed-sets (carrier I) (ideality I)
     ε : is-weakly-directed (underlying-order 𝓓) ι
     ε (x , xI) (y , yI) = ∥∥-functor γ g
      where
       γ : (Σ z ꞉ X , z ∈ᵢ I × x ≺ z × y ≺ z)
         → Σ i ꞉ 𝕋 (carrier I) , (ι (x , xI) ⊑⟨ 𝓓 ⟩ ι i)
                               × (ι (y , yI) ⊑⟨ 𝓓 ⟩ ι i)
       γ (z , zI , lx , ly) = (z , zI) , f-monotone lx , f-monotone ly
       g : ∃ z ꞉ X , z ∈ᵢ I × x ≺ z × y ≺ z
       g = directed-sets-are-weakly-directed (carrier I) Idir x y xI yI

\end{code}

\begin{code}

 Idl-is-continuous : is-a-continuous-dcpo (Idl-DCPO)
 Idl-is-continuous = ∣ X , ↓_ , s , γ ∣
  where
   ≺' : X → X → 𝓥 ̇
   ≺' x y = ∃ z ꞉ X , z ≺ y × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ z)
   s : ≪-small-on-B Idl-DCPO ↓_
   s x y = ≺' x y , e
    where
     e : ≺' x y ≃ (↓ x) ≪⟨ Idl-DCPO ⟩ (↓ y)
     e = logically-equivalent-props-are-equivalent
         ∥∥-is-a-prop
         (≪-is-prop-valued Idl-DCPO {↓ x} {↓ y})
         (Idl-≪-in-terms-of-⊑' (↓ x ) (↓ y))
         (Idl-≪-in-terms-of-⊑ (↓ x) (↓ y))
   γ : (I : Idl)
     → ∃ 𝓐 ꞉ 𝓥 ̇ , Σ α ꞉ (𝓐 → X) ,
         ((a : 𝓐) → (↓ (α a)) ≪⟨ Idl-DCPO ⟩ I)
       × (Σ δ ꞉ is-Directed Idl-DCPO (↓_ ∘ α) ,
           ∐ Idl-DCPO {𝓐} {↓_ ∘ α} δ ≡ I)
   γ I = ∣ 𝕋 (carrier I) , pr₁ , g , δ , ((Idl-∐-≡ I) ⁻¹) ∣
    where
     g : (i : 𝕋 (carrier I)) → (↓ pr₁ i) ≪⟨ Idl-DCPO ⟩ I
     g (i , p) = Idl-≪-in-terms-of-⊑' (↓ i) I ∣ i , p , (λ x → id) ∣
     δ : is-Directed Idl-DCPO (↓-of-ideal I)
     δ = ↓-of-ideal-is-directed I

\end{code}
