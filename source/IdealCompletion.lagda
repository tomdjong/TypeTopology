Tom de Jong
26-02-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc

module IdealCompletion
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe) -- universe where the index types for directedness
                        -- completeness live
       where

open import UF-Powersets

open import Dcpo pt fe 𝓥
open import Poset fe
open PosetAxioms

open PropositionalTruncation pt

module Ideals
        {P : 𝓤 ̇ }
        (_≤_ : P → P → 𝓥 ⊔ 𝓣 ̇ )
        (≤-prop-valued : {p q : P} → is-prop (p ≤ q))
        (INT₂ : {q₀ q₁ p : P} → q₀ ≤ p → q₁ ≤ p
              → ∃ r ꞉ P , r ≤ p × q₀ ≤ r × q₁ ≤ r)
        (INT₀ : (p : P) → ∃ q ꞉ P , q ≤ p)
        (≤-trans : {p q r : P} → p ≤ q → q ≤ r → p ≤ r)
       where

 is-lower-set : 𝓟 (𝓥 ⊔ 𝓣) P → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-lower-set A = (p q : P) → p ≤ q → q ∈ A → p ∈ A

 being-a-lower-set-is-a-prop : (I :  𝓟 (𝓥 ⊔ 𝓣) P) → is-prop (is-lower-set I)
 being-a-lower-set-is-a-prop I = Π-is-prop fe
                                 λ p → Π-is-prop fe
                                 λ q → Π-is-prop fe
                                 λ l → Π-is-prop fe
                                 λ i → ∈-is-a-prop I p

 is-inhabited-set : 𝓟 (𝓥 ⊔ 𝓣) P → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 is-inhabited-set A = ∃ p ꞉ P , p ∈ A

 being-an-inhabited-set-is-a-prop : (I : 𝓟 (𝓥 ⊔ 𝓣) P)
                                  → is-prop (is-inhabited-set I)
 being-an-inhabited-set-is-a-prop I = ∥∥-is-a-prop

 is-weakly-directed-set : 𝓟 (𝓥 ⊔ 𝓣) P → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-weakly-directed-set A = (p q : P) → p ∈ A → q ∈ A
                          → ∃ r ꞉ P , r ∈ A
                          × p ≤ r × q ≤ r

 being-a-weakly-directed-set-is-a-prop : (I : 𝓟 (𝓥 ⊔ 𝓣) P)
                                       → is-prop (is-weakly-directed-set I)
 being-a-weakly-directed-set-is-a-prop I = Π-is-prop fe
                                           λ p → Π-is-prop fe
                                           λ q → Π-is-prop fe
                                           λ i → Π-is-prop fe
                                           λ j → ∥∥-is-a-prop

 is-directed-set : 𝓟 (𝓥 ⊔ 𝓣) P → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-directed-set A = is-inhabited-set A × is-weakly-directed-set A

 being-a-directed-set-is-a-prop : (I : 𝓟 (𝓥 ⊔ 𝓣) P)
                                → is-prop (is-directed-set I)
 being-a-directed-set-is-a-prop I =
  ×-is-prop
   (being-an-inhabited-set-is-a-prop I)
   (being-a-weakly-directed-set-is-a-prop I)

 directed-sets-are-inhabited : (A : 𝓟 (𝓥 ⊔ 𝓣) P)
                             → is-directed-set A → is-inhabited-set A
 directed-sets-are-inhabited A = pr₁

 directed-sets-are-weakly-directed : (A : 𝓟 (𝓥 ⊔ 𝓣) P)
                                   → is-directed-set A
                                   → is-weakly-directed-set A
 directed-sets-are-weakly-directed A = pr₂

 is-ideal : 𝓟 (𝓥 ⊔ 𝓣) P → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-ideal I = is-lower-set I × is-directed-set I

 being-an-ideal-is-a-prop : (I : 𝓟 (𝓥 ⊔ 𝓣) P) → is-prop (is-ideal I)
 being-an-ideal-is-a-prop I =
  ×-is-prop
   (being-a-lower-set-is-a-prop I)
   (being-a-directed-set-is-a-prop I)

 ideals-are-lower-sets : (I : 𝓟 (𝓥 ⊔ 𝓣) P) → is-ideal I → is-lower-set I
 ideals-are-lower-sets I = pr₁

 ideals-are-directed-sets : (I : 𝓟 (𝓥 ⊔ 𝓣) P)
                          → is-ideal I → is-directed-set I
 ideals-are-directed-sets I = pr₂

 Idl : 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 Idl = Σ I ꞉ 𝓟 (𝓥 ⊔ 𝓣) P , is-ideal I

 carrier : Idl → 𝓟 (𝓥 ⊔ 𝓣) P
 carrier = pr₁

 ideality : (I : Idl) → is-ideal (carrier I)
 ideality = pr₂

 _∈ᵢ_ : P → Idl → 𝓥 ⊔ 𝓣 ̇
 p ∈ᵢ I = p ∈ carrier I

 ↓_ : P → Idl
 ↓ p = (λ (q : P) → (q ≤ p) , ≤-prop-valued) ,
       ls , inh , δ
  where
   ls : is-lower-set (λ q → (q ≤ p) , ≤-prop-valued)
   ls p q = ≤-trans
   inh : ∃ q ꞉ P , q ≤ p
   inh = INT₀ p
   δ : is-weakly-directed-set (λ q → (q ≤ p) , ≤-prop-valued)
   δ q₀ q₁ u v = INT₂ u v

 _⊑_ : Idl → Idl → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 I ⊑ J = carrier I ⊆ carrier J

 Idl-∐ : {𝓐 : 𝓥 ̇ } (α : 𝓐 → Idl) → is-directed _⊑_ α → Idl
 Idl-∐ {𝓐} α δ = ∐α , ls , inh , ε
  where
   ∐α : 𝓟 (𝓥 ⊔ 𝓣) P
   ∐α p = (∃ a ꞉ 𝓐 , (p ∈ᵢ α a)) , ∥∥-is-a-prop
   ls : is-lower-set ∐α
   ls p q l = ∥∥-functor γ
    where
     γ : (Σ a ꞉ 𝓐 , q ∈ᵢ α a) → (Σ a ꞉ 𝓐 , p ∈ᵢ α a)
     γ (a , u) = a , ideals-are-lower-sets (carrier (α a)) (ideality (α a))
                     p q l u
   inh : ∃ p ꞉ P , p ∈ ∐α
   inh = ∥∥-rec ∥∥-is-a-prop γ (directed-implies-inhabited _⊑_ α δ)
    where
     γ : 𝓐 → ∃ p ꞉ P , p ∈ ∐α
     γ a = ∥∥-functor h inh'
      where
       inh' : is-inhabited-set (carrier (α a))
       inh' = directed-sets-are-inhabited (carrier (α a))
              (ideals-are-directed-sets (carrier (α a)) (ideality (α a)))
       h : (Σ p ꞉ P , p ∈ᵢ α a) → (Σ p ꞉ P , p ∈ ∐α)
       h (p , u) = p , ∣ a , u ∣
   ε : is-weakly-directed-set ∐α
   ε p q p∈∐α q∈∐α = do
    (a , p∈αa) ← p∈∐α
    (b , q∈αb) ← q∈∐α
    (c , αa⊆αc , αb⊆αc) ← directed-implies-weakly-directed _⊑_ α δ a b
    let p∈αc = αa⊆αc p p∈αa
    let q∈αc = αb⊆αc q q∈αb
    (r , r∈αc , p≤r , q≤r) ← directed-sets-are-weakly-directed
                             (carrier (α c))
                             (ideals-are-directed-sets (carrier (α c))
                              (ideality (α c)))
                             p q p∈αc q∈αc
    ∣ r , ∣ c , r∈αc ∣ , p≤r , q≤r ∣

 Idl-DCPO : DCPO {𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤} {𝓥 ⊔ 𝓤 ⊔ 𝓣}
 Idl-DCPO = Idl , _⊑_ , γ
  where
   γ : dcpo-axioms _⊑_
   γ = pa , dc
    where
     pa : poset-axioms _⊑_
     pa = s , pv , r , t , a
      where
       s : is-set Idl
       s = subtypes-of-sets-are-sets carrier
            (pr₁-lc λ {I} → being-an-ideal-is-a-prop I)
            (powersets-are-sets fe fe pe)
       pv : is-prop-valued _⊑_
       pv I J = ⊆-is-a-prop fe fe (carrier I) (carrier J)
       r : (I : Idl) → I ⊑ I
       r I = ⊆-reflexivity (carrier I)
       t : is-transitive _⊑_
       t I J K = ⊆-transitivity (carrier I) (carrier J) (carrier K)
       a : is-antisymmetric _⊑_
       a I J u v = to-subtype-≡
                    (λ K → being-an-ideal-is-a-prop K)
                    (⊆-antisymmetry pe fe fe (carrier I) (carrier J) u v)
     dc : is-directed-complete _⊑_
     dc 𝓐 α δ = (Idl-∐ α δ) , ub , lb-of-ubs
      where
       ub : (a : 𝓐) → α a ⊑ Idl-∐ α δ
       ub a p p∈αa = ∣ a , p∈αa ∣
       lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ (Idl-∐ α δ) α
       lb-of-ubs I ub p p∈∐α = ∥∥-rec (∈-is-a-prop (carrier I) p) h p∈∐α
        where
         h : (Σ a ꞉ 𝓐 , p ∈ᵢ α a) → p ∈ᵢ I
         h (a , p∈αa) = ub a p p∈αa

 {-
 open import UF-Size

 ∐-from-Idl-to-a-dcpo : (𝓓 : DCPO {𝓤} {𝓣})
                      → P has-size 𝓥 → ((p q : P) → (p ≤ q) has-size 𝓥)
                      → Idl → ⟨ 𝓓 ⟩
 ∐-from-Idl-to-a-dcpo 𝓓 P-small ≤-small I = {!!}
  where
   J : 𝓥 ̇
   J = has-size-type {!!}
 -}

\end{code}

This can be phrased of has-size (i.e. "essentially small").

\begin{code}

module _
        {P : 𝓥 ̇ }
        (_≤_ : P → P → 𝓥 ̇ )
        (≤-prop-valued : {p q : P} → is-prop (p ≤ q))
        (INT₂ : {q₀ q₁ p : P} → q₀ ≤ p → q₁ ≤ p
              → ∃ r ꞉ P , r ≤ p × q₀ ≤ r × q₁ ≤ r)
        (INT₀ : (p : P) → ∃ q ꞉ P , q ≤ p)
        (≤-trans : {p q r : P} → p ≤ q → q ≤ r → p ≤ r)
       where

 open Ideals {𝓥} {𝓥} {P}_≤_ ≤-prop-valued INT₂ INT₀ ≤-trans

 ∐-from-Idl-to-a-dcpo : (𝓓 : DCPO {𝓤} {𝓣})
                      → (f : P → ⟨ 𝓓 ⟩)
                      → ({p q : P} → p ≤ q → f p ⊑⟨ 𝓓 ⟩ f q)
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
      r , r∈I , p≤r , q≤r ← directed-sets-are-weakly-directed (carrier I) I-dir
                            p q p∈I q∈I
      ∣ (r , r∈I) , (f-monotone p≤r , f-monotone q≤r) ∣

\end{code}
