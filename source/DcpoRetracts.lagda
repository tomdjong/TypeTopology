Tom de Jong, 13 March 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module DcpoRetracts
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoApproximation pt fe 𝓥
open import DcpoAlgebraic pt fe 𝓥
open import DcpoBasis pt fe 𝓥
open import DcpoBasics pt fe 𝓥
open import IdealCompletion pt fe pe 𝓥
open import IdealCompletion-Properties pt fe pe 𝓥

open import UF-Powersets

open import UF-Size

open import UF-Retracts

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (𝒷 : is-a-basis 𝓓 β)
       where

 open Ideals {𝓥} {𝓥} {B} (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-prop-valued 𝓓 𝒷)
             (reflexivity-implies-INT₂ (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-reflexive 𝓓 𝒷))
             (reflexivity-implies-INT₀ (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-reflexive 𝓓 𝒷))
             (⊑ᴮ-is-transitive 𝓓 𝒷)
 open SmallIdeals {B} (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-prop-valued 𝓓 𝒷)
                  (reflexivity-implies-INT₂ (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-reflexive 𝓓 𝒷))
                  (reflexivity-implies-INT₀ (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-reflexive 𝓓 𝒷))
                  (⊑ᴮ-is-transitive 𝓓 𝒷)
 open Idl-Properties
      {𝓥} {𝓥} {B} (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-prop-valued 𝓓 𝒷)
      (reflexivity-implies-INT₂ (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-reflexive 𝓓 𝒷))
      (reflexivity-implies-INT₀ (basis-⊑ 𝓓 𝒷) (⊑ᴮ-is-reflexive 𝓓 𝒷))
      (⊑ᴮ-is-transitive 𝓓 𝒷)

\end{code}

For a dcpo 𝓓 with basis β : B → ⟨ 𝓓 ⟩, being locally small is equivalent to
asking that (β b ≪ x) is small for all b : B and x ∶ ⟨ 𝓓 ⟩, which is exactly
what we need to get the desired map ⟨ 𝓓 ⟩ → Idl. See DcpoBasis.lagda.

\begin{code}

 to-Idl : is-locally-small 𝓓 → ⟨ 𝓓 ⟩ → Idl
 to-Idl ls x = I , ι
  where
   s : ↓≪-smallness 𝓓 𝒷
   s = being-locally-small-implies-↓≪-smallness 𝓓 𝒷 ls
   I : 𝓟 𝓥 B
   I b = b ≪ₛ⟨ 𝓓 ⟩[ 𝒷 ][ s ] x , ≪ₛ-is-prop-valued 𝓓 𝒷 s b x
   ι : is-ideal I
   ι = l , δ , ε
    where
     l : is-lower-set I
     l b₁ b₂ u i = ∥∥-functor γ i
      where
       γ : (Σ b₃ ꞉ B , b₂ ≪ᴮ⟨ 𝓓 ⟩[ 𝒷 ] b₃ × β b₃ ⊑ₛ⟨ 𝓓 ⟩[ ls ] x)
         → Σ b₃ ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ 𝒷 ] b₃ × β b₃ ⊑ₛ⟨ 𝓓 ⟩[ ls ] x
       γ (b₃ , v , w) = b₃ , φ , w
        where
         φ : b₁ ≪ᴮ⟨ 𝓓 ⟩[ 𝒷 ] b₃
         φ = ≪-to-≪ᴮ 𝓓 𝒷 b₁ b₃
             (⊑-≪-to-≪ 𝓓 (⊑ᴮ-to-⊑ 𝓓 𝒷 u) (≪ᴮ-to-≪ 𝓓 𝒷 b₂ b₃ v))
     δ : ∃ b ꞉ B , b ≪ₛ⟨ 𝓓 ⟩[ 𝒷 ][ s ] x
     δ = ∥∥-functor γ (≪-INT₀ 𝓓 𝒷 x)
      where
       γ : (Σ b ꞉ B , β b ≪⟨ 𝓓 ⟩ x)
         → Σ b ꞉ B , b ≪ₛ⟨ 𝓓 ⟩[ 𝒷 ][ s ] x
       γ (b , u) = b , ≪-to-≪ₛ 𝓓 𝒷 s b x u
     ε : is-weakly-directed-set I
     ε b₁ b₂ u₁ u₂ = ∥∥-functor γ h
      where
       γ : (Σ b ꞉ B , β b₁ ≪⟨ 𝓓 ⟩ β b
                    × β b₂ ≪⟨ 𝓓 ⟩ β b
                    × β b ≪⟨ 𝓓 ⟩ x)
         → Σ b ꞉ B , b ≪ₛ⟨ 𝓓 ⟩[ 𝒷 ][ s ] x
                   × b₁ ⊑ᴮ⟨ 𝓓 ⟩[ 𝒷 ] b
                   × b₂ ⊑ᴮ⟨ 𝓓 ⟩[ 𝒷 ] b
       γ (b , v₁ , v₂ , v) = b ,
                             ≪-to-≪ₛ 𝓓 𝒷 s b x v ,
                             ⊑-to-⊑ᴮ 𝓓 𝒷 (≪-to-⊑ 𝓓 v₁) ,
                             ⊑-to-⊑ᴮ 𝓓 𝒷 (≪-to-⊑ 𝓓 v₂)
       h : ∃ b ꞉ B , β b₁ ≪⟨ 𝓓 ⟩ β b
                   × β b₂ ≪⟨ 𝓓 ⟩ β b
                   × β b ≪⟨ 𝓓 ⟩ x
       h = ≪-INT₂ 𝓓 𝒷 (β b₁) (β b₂) x
           (≪ₛ-to-≪ 𝓓 𝒷 s b₁ x u₁) (≪ₛ-to-≪ 𝓓 𝒷 s b₂ x u₂)

 -- TO DO: Refactor this?
 ideals-are-directed : (I : Idl)
                     → is-Directed 𝓓 (β ∘ (λ (i : 𝕋 (carrier I)) → pr₁ i))
 ideals-are-directed (I , ι) = h , ε
  where
   δ : is-directed-set I
   δ = ideals-are-directed-sets I ι
   α : 𝕋 I → ⟨ 𝓓 ⟩
   α = β ∘ pr₁
   h : ∥ 𝕋 I ∥
   h = directed-sets-are-inhabited I δ
   ε : is-weakly-directed (underlying-order 𝓓) α
   ε (b₁ , i₁) (b₂ , i₂) =
    ∥∥-functor γ (directed-sets-are-weakly-directed I δ b₁ b₂ i₁ i₂)
     where
      γ : (Σ b ꞉ B , b ∈ I
                   × b₁ ⊑ᴮ⟨ 𝓓 ⟩[ 𝒷 ] b
                   × b₂ ⊑ᴮ⟨ 𝓓 ⟩[ 𝒷 ] b)
        → Σ r ꞉ 𝕋 I , α (b₁ , i₁) ⊑⟨ 𝓓 ⟩ α r
                    × α (b₂ , i₂) ⊑⟨ 𝓓 ⟩ α r
      γ (b , i , u₁ , u₂) = (b , i) , ⊑ᴮ-to-⊑ 𝓓 𝒷 u₁ , ⊑ᴮ-to-⊑ 𝓓 𝒷 u₂

 from-Idl : Idl → ⟨ 𝓓 ⟩
 from-Idl I = ∐ 𝓓 (ideals-are-directed I)

 Idl-retract : is-locally-small 𝓓 → ⟨ 𝓓 ⟩ ◁ Idl
 Idl-retract ls = r , s , γ
  where
   r : Idl → ⟨ 𝓓 ⟩
   r = from-Idl
   s : ⟨ 𝓓 ⟩ → Idl
   s = to-Idl ls
   γ : r ∘ s ∼ id
   γ x = antisymmetry 𝓓 (r (s x)) x u v
    where
     sm : ↓≪-smallness 𝓓 𝒷
     sm = being-locally-small-implies-↓≪-smallness 𝓓 𝒷 ls
     u : r (s x) ⊑⟨ 𝓓 ⟩ x
     u = ∐-is-lowerbound-of-upperbounds 𝓓 (ideals-are-directed (s x)) x g
      where
       g : (i : 𝕋 (carrier (s x))) → β (pr₁ i) ⊑⟨ 𝓓 ⟩ x
       g (b , w) = ≪-to-⊑ 𝓓 (≪ₛ-to-≪ 𝓓 𝒷 sm b x w)
     v : x ⊑⟨ 𝓓 ⟩ r (s x)
     v = ∥∥-rec (prop-valuedness 𝓓 x (r (s x))) g h
      where
       g : approximate-from-basis-Σ 𝓓 β x → x ⊑⟨ 𝓓 ⟩ r (s x)
       g (I , α , wb , δ , e) = x       ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (e ⁻¹) ]
                                ∐ 𝓓 δ   ⊑⟨ 𝓓 ⟩[ w ]
                                r (s x) ∎⟨ 𝓓 ⟩
        where
         w : ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ r (s x)
         w = ∐-is-lowerbound-of-upperbounds 𝓓 δ (r (s x)) ϕ
          where
           ϕ : (i : I) → β (α i) ⊑⟨ 𝓓 ⟩ r (s x)
           ϕ i = ∐-is-upperbound 𝓓 (ideals-are-directed (s x)) (α i , ψ)
            where
             ψ : α i ≪ₛ⟨ 𝓓 ⟩[ 𝒷 ][ sm ] x
             ψ = ≪-to-≪ₛ 𝓓 𝒷 sm (α i) x (wb i)
       h : approximate-from-basis 𝓓 β x
       h = pr₂ 𝒷 x

\end{code}

Observation from 13/03/2020.

The exponential E^D of two locally-small dcpos D and E is not locally
small. This is because the order of the exponential mentions all elements of the
D (so E^D is locally small if D is additionally assumed to be small).

However, we do have the following result.

If D is continuous and E is locally small, then E^D is locally small.  Proof: We
claim that Π x : D , f x ⊑ g x is equivalent to Π b : B , f b ⊑ g b (where B is
a basis of D). Since B is small, the latter is small, making E^D locally
small. For the proof of the equivalence, note that the left-to-right implication
is trivial. For the converse, let x : D and (by continuity) write x = ∐ α with
every element αᵢ : B. Then:
f x      =
f (∐ α)  = (by continuity of f)
∐ᵢ (f αᵢ) ⊑ (by assumption and the fact that αᵢ : B)
∐ᵢ (g αᵢ) ⊑ (by continuity of g)
g (∐ α)  =
g x.

TO DO: Formalise this.
