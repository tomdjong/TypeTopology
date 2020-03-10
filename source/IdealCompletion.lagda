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
        (_≺_ : P → P → 𝓥 ⊔ 𝓣 ̇ )
        (≺-prop-valued : {p q : P} → is-prop (p ≺ q))
        (INT₂ : {q₀ q₁ p : P} → q₀ ≺ p → q₁ ≺ p
              → ∃ r ꞉ P , q₀ ≺ r × q₁ ≺ r × r ≺ p)
        (INT₀ : (p : P) → ∃ q ꞉ P , q ≺ p)
        (≺-trans : {p q r : P} → p ≺ q → q ≺ r → p ≺ r)
       where

 is-lower-set : 𝓟 (𝓥 ⊔ 𝓣) P → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-lower-set A = (p q : P) → p ≺ q → q ∈ A → p ∈ A

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
                          × p ≺ r × q ≺ r

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
   ε p q i j = ∥∥-rec₂ ∥∥-is-a-prop γ i j
    where
     γ : (Σ a ꞉ 𝓐 , p ∈ᵢ α a)
       → (Σ b ꞉ 𝓐 , q ∈ᵢ α b)
       → ∃ r ꞉ P , r ∈ ∐α × p ≺ r × q ≺ r
     γ (a , ia) (b , jb) =
      ∥∥-rec ∥∥-is-a-prop g (directed-implies-weakly-directed _⊑_ α δ a b)
       where
        g : (Σ c ꞉ 𝓐 , α a ⊑ α c × α b ⊑ α c)
          → ∃ r ꞉ P , r ∈ ∐α × p ≺ r × q ≺ r
        g (c , l , m) = do
         (r , k , u , v) ← directed-sets-are-weakly-directed (carrier (α c))
                           (ideals-are-directed-sets (carrier (α c))
                            (ideality (α c)))
                           p q ic jc
         ∣ r , ∣ c , k ∣ , u , v ∣
         where
         ic : p ∈ᵢ α c
         ic = l p ia
         jc : q ∈ᵢ α c
         jc = m q jb

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
     dc 𝓐 α δ = (Idl-∐ α δ) , ub , lb
      where
       ub : (a : 𝓐) → α a ⊑ Idl-∐ α δ
       ub a p p∈αa = ∣ a , p∈αa ∣
       lb : is-lowerbound-of-upperbounds _⊑_ (Idl-∐ α δ) α
       lb I ub p p∈∐α = ∥∥-rec (∈-is-a-prop (carrier I) p) h p∈∐α
        where
         h : (Σ a ꞉ 𝓐 , p ∈ᵢ α a) → p ∈ᵢ I
         h (a , p∈αa) = ub a p p∈αa

\end{code}
