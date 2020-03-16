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
open import IdealCompletion pt fe pe 𝓥
open import IdealCompletion-Properties pt fe pe 𝓥

open import UF-Powersets

module _
        (𝓓 : DCPO {𝓤} {𝓣})
        {B : 𝓥 ̇ }
        (β : B → ⟨ 𝓓 ⟩)
        (c : is-a-basis 𝓓 β)
       where

 open Ideals {𝓥} {𝓥} {B} (basis-⊑ 𝓓 c) (⊑ᴮ-is-prop-valued 𝓓 c)
             (reflexivity-implies-INT₂ (basis-⊑ 𝓓 c) (⊑ᴮ-is-reflexive 𝓓 c))
             (reflexivity-implies-INT₀ (basis-⊑ 𝓓 c) (⊑ᴮ-is-reflexive 𝓓 c))
             (⊑ᴮ-is-transitive 𝓓 c)
 open SmallIdeals {B} (basis-⊑ 𝓓 c) (⊑ᴮ-is-prop-valued 𝓓 c)
                  (reflexivity-implies-INT₂ (basis-⊑ 𝓓 c) (⊑ᴮ-is-reflexive 𝓓 c))
                  (reflexivity-implies-INT₀ (basis-⊑ 𝓓 c) (⊑ᴮ-is-reflexive 𝓓 c))
                  (⊑ᴮ-is-transitive 𝓓 c)
 open Idl-Properties
      {𝓥} {𝓥} {B} (basis-⊑ 𝓓 c) (⊑ᴮ-is-prop-valued 𝓓 c)
      (reflexivity-implies-INT₂ (basis-⊑ 𝓓 c) (⊑ᴮ-is-reflexive 𝓓 c))
      (reflexivity-implies-INT₀ (basis-⊑ 𝓓 c) (⊑ᴮ-is-reflexive 𝓓 c))
      (⊑ᴮ-is-transitive 𝓓 c)

 to-Idl : locally-small-dcpo 𝓓 → ⟨ 𝓓 ⟩ → Idl
 to-Idl ls x = I , ι
  where
   _⊑'_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓥 ̇
   _⊑'_ = locally-small-order 𝓓 ls
   I : 𝓟 𝓥 B
   I b = (∃ b' ꞉ B , b ≪ᴮ⟨ 𝓓 ⟩[ c ] b' × (β b' ⊑' x)) , ∥∥-is-a-prop
   ι : {!!}
   ι = {!!}

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
