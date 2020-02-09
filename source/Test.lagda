Tom de Jong, 9 February 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Test where

open import UF-Base
open import SpartanMLTT
open import UF-Equiv
open import UF-Retracts
open import UF-Size

retract-gives-has-size' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                        → retract X of Y
                        → X has-size 𝓥
retract-gives-has-size' {𝓤} {𝓥} {X} {Y} (r , s , ρ) = Z , γ
 where
  Z : 𝓥 ̇
  Z = Σ y ꞉ Y , s (r y) ≡ y
  γ : Z ≃ X
  γ = qinveq f (g , (gf , fg))
   where
    f : Z → X
    f (y , e) = r y
    g : X → Z
    g x = (s x) , ap s (ρ x)
    gf : (z : Z) → g (f z) ≡ z
    gf (y , e) = to-Σ-≡ (e , ϕ)
     where
      h : (y' : Y) (e' : s (r y) ≡ y')
        → transport (λ - → s (r -) ≡ -) e' (ap s (ρ (r y)))
          ≡
          ap s (ap r (e' ⁻¹) ∙ ρ (r y)) ∙ e'
          -- ((ap (s ∘ r) (e' ⁻¹)) ∙ (ap s (ρ (r y)))) ∙ e'
      h .(s (r y)) refl =
       transport (λ - → s (r -) ≡ -) refl (ap s (ρ (r y))) ≡⟨ refl ⟩
       ap s (ρ (r y)) ≡⟨ ap (λ - → ap s -) ((refl-left-neutral {_} {_} {_} {_} {ρ (r y)} ⁻¹)) ⟩
       ap s (refl ∙ ρ (r y)) ≡⟨ refl ⟩
       ap s (ap r (refl ⁻¹) ∙ ρ (r y)) ∙ refl ∎
      h' : (y' : Y) (e' : s (r y) ≡ y')
         → ap s (ap r (e' ⁻¹) ∙ ρ (r y)) ∙ e' ≡ {!!}
      h' = {!!}
      ϕ : transport (λ - → s (r -) ≡ -) e (ap s (ρ (r y))) ≡ e
      ϕ = transport (λ - → s (r -) ≡ -) e (ap s (ρ (r y))) ≡⟨ h y e ⟩
            {-
              ap (s ∘ r) (e ⁻¹) ∙ ap s (ρ (r y)) ∙ e ≡⟨ ap (λ - → - ∙ ap s (ρ (r y)) ∙ e) ((ap-ap r s (e ⁻¹)) ⁻¹) ⟩
              ap s (ap r (e ⁻¹)) ∙ ap s (ρ (r y)) ∙ e ≡⟨ ap (λ - → - ∙ e) ((ap-comp s (ap r (e ⁻¹)) (ρ (r y))) ⁻¹) ⟩
            -}
          ap s (ap r (e ⁻¹) ∙ ρ (r y)) ∙ e ≡⟨ {!!} ⟩
          {!!} ≡⟨ {!!} ⟩
          e ∎
    fg : (x : X) → f (g x) ≡ x
    fg x = ρ x

\end{code}
