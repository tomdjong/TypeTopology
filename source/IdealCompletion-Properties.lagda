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
        {P : 𝓤 ̇ }
        (_≺_ : P → P → 𝓥 ⊔ 𝓣 ̇ )
        (≺-prop-valued : {p q : P} → is-prop (p ≺ q))
        (INT₂ : {q₀ q₁ p : P} → q₀ ≺ p → q₁ ≺ p
              → ∃ r ꞉ P , q₀ ≺ r × q₁ ≺ r × r ≺ p)
        (INT₀ : (p : P) → ∃ q ꞉ P , q ≺ p)
        (≺-trans : {p q r : P} → p ≺ q → q ≺ r → p ≺ r)
       where

 open Ideals {𝓤} {𝓥 ⊔ 𝓣} {P} _≺_ ≺-prop-valued INT₂ INT₀ ≺-trans

 roundness : (I : Idl) {x : P} → (x ∈ᵢ I) → ∃ y ꞉ P , y ∈ᵢ I × x ≺ y
 roundness I {x} x∈I = do
  (y , y∈I , x≺y , _) ← directed-sets-are-weakly-directed (carrier I)
                        (ideals-are-directed-sets (carrier I) (ideality I))
                        x x x∈I x∈I
  ∣ y , y∈I , x≺y ∣

 ↓_ : P → Idl
 ↓ p = (λ (q : P) → (q ≺ p) , ≺-prop-valued) ,
       ls , inh , δ
  where
   ls : is-lower-set (λ q → (q ≺ p) , ≺-prop-valued)
   ls p q = ≺-trans
   inh : ∃ q ꞉ P , q ≺ p
   inh = INT₀ p
   δ : is-weakly-directed-set (λ q → (q ≺ p) , ≺-prop-valued)
   δ q₀ q₁ q₀≺p q₁≺p = do
    r , q₀≺r , q₁≺r , r≺p ← INT₂ q₀≺p q₁≺p
    ∣ r , r≺p , q₀≺r , q₁≺r ∣

 ↓-is-monotone : {p q : P} → p ≺ q → (↓ p) ⊑⟨ Idl-DCPO ⟩ (↓ q)
 ↓-is-monotone {p} {q} p≺q x x≺p = ≺-trans x≺p p≺q


\end{code}

This should be phrased of has-size (i.e. "essentially small").

\begin{code}

module SmallIdeals
        {P : 𝓥 ̇ }
        (_≺_ : P → P → 𝓥 ̇ )
        (≺-prop-valued : {p q : P} → is-prop (p ≺ q))
        (INT₂ : {q₀ q₁ p : P} → q₀ ≺ p → q₁ ≺ p
              → ∃ r ꞉ P , q₀ ≺ r × q₁ ≺ r × r ≺ p)
        (INT₀ : (p : P) → ∃ q ꞉ P , q ≺ p)
        (≺-trans : {p q r : P} → p ≺ q → q ≺ r → p ≺ r)
       where

 open Ideals {𝓥} {𝓥} {P}_≺_ ≺-prop-valued INT₂ INT₀ ≺-trans
 open Idl-Properties {𝓥} {𝓥} {P}_≺_ ≺-prop-valued INT₂ INT₀ ≺-trans

 ↓-of-ideal : (I : Idl) → 𝕋 (carrier I) → Idl
 ↓-of-ideal I (i , i∈I) = ↓ i

 ↓-of-ideal-is-directed : (I : Idl) → is-Directed Idl-DCPO (↓-of-ideal I)
 ↓-of-ideal-is-directed (I , ι) = inh , ε
  where
   δ : is-weakly-directed-set I
   δ = directed-sets-are-weakly-directed I (ideals-are-directed-sets I ι)
   inh : ∥ 𝕋 I ∥
   inh = directed-sets-are-inhabited I (ideals-are-directed-sets I ι)
   ε : is-weakly-directed _⊑_ (↓-of-ideal (I , ι))
   ε (i , i∈I) (j , j∈I) = do
    k , k∈I , i≺k , j≺k ← δ i j i∈I j∈I
    ∣ (k , k∈I) , ((λ x x≺i → ≺-trans x≺i i≺k) , λ x x≺j → ≺-trans x≺j j≺k) ∣

 Idl-∐-≡ : (I : Idl)
         → I ≡ ∐ Idl-DCPO {_} {↓-of-ideal I} (↓-of-ideal-is-directed I)
 Idl-∐-≡ I = antisymmetry Idl-DCPO I (∐ Idl-DCPO {_} {α} δ) ⊑₁ ⊑₂
  where
   α : 𝕋 (carrier I) → Idl
   α = ↓-of-ideal I
   δ : is-Directed Idl-DCPO α
   δ = ↓-of-ideal-is-directed I
   ⊑₁ : I ⊑⟨ Idl-DCPO ⟩ ∐ Idl-DCPO {_} {α} δ
   ⊑₁ i i∈I = do
    j , j∈I , i≺j ← roundness I i∈I
    ∣ (j , j∈I) , i≺j ∣
   ⊑₂ : ∐ Idl-DCPO {_} {α} δ ⊑⟨ Idl-DCPO ⟩ I
   ⊑₂ i i∈∐α = ∥∥-rec (∈-is-a-prop (carrier I) i) γ i∈∐α
    where
     γ : (Σ j ꞉ 𝕋 (carrier I) , i ≺ pr₁ j) → i ∈ carrier I
     γ ((j , j∈I) , i≺j) = ideals-are-lower-sets (carrier I) (ideality I)
                           i j i≺j j∈I

 Idl-≪-in-terms-of-⊑ : (I J : Idl) → I ≪⟨ Idl-DCPO ⟩ J
                     → ∃ x ꞉ P , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
 Idl-≪-in-terms-of-⊑ I J I≪J = do
  ((x , x∈J) , I⊑↓x) ← I≪J (𝕋 (carrier J)) (↓-of-ideal J)
                       (↓-of-ideal-is-directed J)
                       (≡-to-⊑ Idl-DCPO (Idl-∐-≡ J))
  ∣ x , x∈J , I⊑↓x ∣

 Idl-≪-in-terms-of-⊑₂ : (I J : Idl) → I ≪⟨ Idl-DCPO ⟩ J
                      → ∃ x ꞉ P , Σ y ꞉ P , x ≺ y
                                          × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                                          × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                                          × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑₂ I J I≪J = do
  (x , x∈J , I⊑↓x) ← Idl-≪-in-terms-of-⊑ I J I≪J
  (y , y∈J , x≺y) ← roundness J x∈J
  let ↓x⊑↓y = ↓-is-monotone x≺y
  let ↓y⊑J = λ z z≺y → ideals-are-lower-sets (carrier J) (ideality J) z y z≺y y∈J
  ∣ x , y , x≺y , I⊑↓x , ↓x⊑↓y , ↓y⊑J ∣

 Idl-≪-in-terms-of-⊑' : (I J : Idl)
                      → ∃ x ꞉ P , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                      → I ≪⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑' I J = ∥∥-rec (≪-is-prop-valued Idl-DCPO {I} {J}) γ
  where
   γ : (Σ x ꞉ P , x ∈ᵢ J × I ⊑⟨ Idl-DCPO ⟩ (↓ x))
     → I ≪⟨ Idl-DCPO ⟩ J
   γ (x , x∈J , I⊑↓x) 𝓐 α δ J⊑∐α = do
    (a , x∈αa) ← J⊑∐α x x∈J
    let ↓x⊑αa = λ y y≺x → ideals-are-lower-sets (carrier (α a)) (ideality (α a))
                y x y≺x x∈αa
    let I⊑αa = transitivity Idl-DCPO I (↓ x) (α a) I⊑↓x ↓x⊑αa
    ∣ a , I⊑αa ∣

 Idl-≪-in-terms-of-⊑₂' : (I J : Idl)
                       → ∃ x ꞉ P , Σ y ꞉ P , x ≺ y
                                           × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                                           × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                                           × (↓ y) ⊑⟨ Idl-DCPO ⟩ J
                       → I ≪⟨ Idl-DCPO ⟩ J
 Idl-≪-in-terms-of-⊑₂' I J = ∥∥-rec (≪-is-prop-valued Idl-DCPO {I} {J}) γ
  where
   γ : (Σ x ꞉ P , Σ y ꞉ P , x ≺ y
                          × I ⊑⟨ Idl-DCPO ⟩ (↓ x)
                          × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ y)
                          × (↓ y) ⊑⟨ Idl-DCPO ⟩ J)
     → I ≪⟨ Idl-DCPO ⟩ J
   γ (x , y , x≺y , I⊑↓x , ↓x⊑↓y , ↓y⊑J) 𝓐 α δ J⊑∐α = do
    let x∈J = ↓y⊑J x x≺y
    (a , x∈αa) ← J⊑∐α x x∈J
    let ↓x⊑αa = λ z z≺x → ideals-are-lower-sets (carrier (α a)) (ideality (α a))
                          z x z≺x x∈αa
    let I⊑α = transitivity Idl-DCPO I (↓ x) (α a) I⊑↓x ↓x⊑αa
    ∣ a , I⊑α ∣

\end{code}

\begin{code}

 ∐-from-Idl-to-a-dcpo : (𝓓 : DCPO {𝓤} {𝓣})
                      → (f : P → ⟨ 𝓓 ⟩)
                      → ({p q : P} → p ≺ q → f p ⊑⟨ 𝓓 ⟩ f q)
                      → Idl → ⟨ 𝓓 ⟩
 ∐-from-Idl-to-a-dcpo 𝓓 f f-monotone I = ∐ 𝓓 {𝕋 (carrier I)} {ι} δ
  where
   ι : 𝕋 (carrier I) → ⟨ 𝓓 ⟩
   ι (p , p∈I) = f p
   δ : is-Directed 𝓓 ι
   δ = (directed-sets-are-inhabited (carrier I) I-dir) , ε
    where
     I-dir : is-directed-set (carrier I)
     I-dir = ideals-are-directed-sets (carrier I) (ideality I)
     ε : is-weakly-directed (underlying-order 𝓓) ι
     ε (p , p∈I) (q , q∈I) = do
      r , r∈I , p≺r , q≺r ← directed-sets-are-weakly-directed (carrier I) I-dir
                            p q p∈I q∈I
      ∣ (r , r∈I) , (f-monotone p≺r , f-monotone q≺r) ∣

\end{code}

\begin{code}

 Idl-is-continuous : is-a-continuous-dcpo (Idl-DCPO)
 Idl-is-continuous = ∣ P , ↓_ , ≺s , γ ∣
  where
   ≺' : P → P → 𝓥 ̇
   ≺' x y = ∃ z ꞉ P , z ≺ y × (↓ x) ⊑⟨ Idl-DCPO ⟩ (↓ z)
   ≺s : ≪-small-on-B Idl-DCPO ↓_
   ≺s x y = ≺' x y , e
    where
     e : ≺' x y ≃ (↓ x) ≪⟨ Idl-DCPO ⟩ (↓ y)
     e = logically-equivalent-props-are-equivalent
         ∥∥-is-a-prop
         (≪-is-prop-valued Idl-DCPO {↓ x} {↓ y})
         (Idl-≪-in-terms-of-⊑' (↓ x ) (↓ y))
         (Idl-≪-in-terms-of-⊑ (↓ x) (↓ y))
   γ : (I : Idl)
     → ∃ 𝓐 ꞉ 𝓥 ̇ , Σ α ꞉ (𝓐 → P) ,
         ((a : 𝓐) → (↓ (α a)) ≪⟨ Idl-DCPO ⟩ I)
       × (Σ δ ꞉ is-Directed Idl-DCPO (↓_ ∘ α) ,
           ∐ Idl-DCPO {𝓐} {↓_ ∘ α} δ ≡ I)
   γ I = ∣ 𝕋 (carrier I) , pr₁ , g , δ , ((Idl-∐-≡ I) ⁻¹) ∣
    where
     g : (i : 𝕋 (carrier I)) → (↓ pr₁ i) ≪⟨ Idl-DCPO ⟩ I
     g (i , i∈I) = Idl-≪-in-terms-of-⊑' (↓ i) I ∣ i , i∈I , (λ x → id) ∣
     δ : is-Directed Idl-DCPO (↓-of-ideal I)
     δ = ↓-of-ideal-is-directed I

\end{code}
