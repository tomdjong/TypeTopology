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
open import IdealCompletion pt fe pe 𝓥
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
