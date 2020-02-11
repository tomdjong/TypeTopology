
Tom de Jong, 10 February 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SizeBasics where

open import SpartanMLTT

open import UF-Base
open import UF-Equiv
open import UF-Retracts
open import UF-Embeddings
open import UF-EquivalenceExamples
open import UF-UA-FunExt
open import UF-PropTrunc
open import UF-Size
open import UF-Univalence

\end{code}

\begin{code}

_has-size₁_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓦 : Universe) → 𝓦 ⁺ ⊔ 𝓤 ⊔ 𝓥 ̇
f has-size₁ 𝓦 = (y : codomain f) → fiber f y has-size 𝓦

has-size₁-is-a-prop : Univalence
                    → {𝓦 : Universe}
                    → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                    → is-prop (f has-size₁ 𝓦)
has-size₁-is-a-prop {𝓤} {𝓥} ua {𝓦} {X} {Y} {f} =
 Π-is-prop (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺)))
 (λ (y : Y) → has-size-is-a-prop ua (fiber f y) 𝓦)
  where
   fe : FunExt
   fe = FunExt-from-Univalence ua

has-size-to-has-size₁ : (𝓥 : Universe) {X : 𝓤 ̇ }
                      → X has-size 𝓥
                      → unique-to-𝟙 {_} {𝓥} {X} has-size₁ 𝓥
has-size-to-has-size₁ 𝓥 {X} (Y , e) u = Y , γ
 where
  γ = Y                   ≃⟨ e ⟩
      X                   ≃⟨ ≃-sym (fibers-of-unique-to-𝟙 u) ⟩
      fiber unique-to-𝟙 u ■

has-size₁-to-has-size : (𝓥 : Universe) {X : 𝓤 ̇ }
                      → unique-to-𝟙 {_} {𝓥} {X} has-size₁ 𝓥
                      → X has-size 𝓥
has-size₁-to-has-size 𝓥 {X} h = Y , γ
 where
  Y : 𝓥 ̇
  Y = pr₁ (h *)
  γ : Y ≃ X
  γ = Y                   ≃⟨ pr₂ (h *) ⟩
      fiber unique-to-𝟙 * ≃⟨ fibers-of-unique-to-𝟙 * ⟩
      X                   ■

singleton-has-size : (𝓥 : Universe) {X : 𝓤 ̇ }
                   → is-singleton X
                   → X has-size 𝓥
singleton-has-size {𝓤} 𝓥 {X} i = (𝟙{𝓥}) , singleton-≃-𝟙' i

equivalence-has-size₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (𝓦 : Universe)
                      → (f : X → Y)
                      → is-equiv f
                      → f has-size₁ 𝓦
equivalence-has-size₁ 𝓦 f i y = singleton-has-size 𝓦 γ
 where
  γ : is-singleton (fiber f y)
  γ = equivs-are-vv-equivs f i y

-- TO DO: Embedding-Resizing <-> Prop. Resizing

section-embedding-into-set-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                    → (s : X → Y)
                                    → is-section s
                                    → is-embedding s
                                    → is-set Y
                                    → s has-size₁ 𝓥
section-embedding-into-set-has-size s (r , ρ) ε σ y = (s (r y) ≡ y) , γ
 where
  γ : (s (r y) ≡ y) ≃ fiber s y
  γ = qinveq f (g , (gf , fg))
   where
    f : s (r y) ≡ y → fiber s y
    f q = (r y) , q
    g : fiber s y → s (r y) ≡ y
    g (x , p) = s (r y)     ≡⟨ ap (s ∘ r) (p ⁻¹) ⟩
                s (r (s x)) ≡⟨ ap s (ρ x) ⟩
                s x         ≡⟨ p ⟩
                y           ∎
    gf : (q : s (r y) ≡ y) → g (f q) ≡ q
    gf q = σ (g (f q)) q
    fg : (w : fiber s y) → f (g w) ≡ w
    fg (x , refl) = to-subtype-≡ (λ _ → σ) (ρ x)

retract-of-a-set-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → is-set Y
                          → retract X of Y
                          → X has-size 𝓥
retract-of-a-set-has-size {𝓤} {𝓥} {X} {Y} i (r , s , ρ) = ?

{-

Tom de Jong, 6 February 2020

Can we prove this for all types Y (i.e. not just sets)?

Added 9 February 2020: Yes, we can, provided we assume that the section is an
embedding (proved below). Note that the section is always left-cancellable, and
so if Y is a set, then it is automatically an embedding.

We keep the special case and construction below, because it was discovered first
and doesn't require the existence of propositional truncations.

\begin{code}

retract-of-a-set-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → is-set Y
                          → retract X of Y
                          → X has-size 𝓥
retract-of-a-set-has-size {𝓤} {𝓥} {X} {Y} i (r , s , ρ) = Z , γ
 where
  Z : 𝓥 ̇
  Z = Σ y ꞉ Y , s (r y) ≡ y
  γ : Z ≃ X
  γ = qinveq f (g , gf , fg)
   where
    f : Z → X
    f (y , p) = r y
    g : X → Z
    g x = (s x) , ap s (ρ x)
    gf : (z : Z) → g (f z) ≡ z
    gf (y , p) = to-Σ-≡ (p , (i _ p))
    fg : (x : X) → f (g x) ≡ x
    fg x = ρ x

module _ (pt : propositional-truncations-exist) where
 open PropositionalTruncation pt

 retract-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → (ρ : retract X of Y)
                  → is-embedding (section ρ)
                  → X has-size 𝓥
 retract-has-size {𝓤} {𝓥} {X} {Y} (r , s , ρ) semb =
  (Σ y ꞉ Y , ∥ s (r y) ≡ y ∥) , γ
   where
    γ = (Σ y ꞉ Y , ∥ s (r y) ≡ y ∥) ≃⟨ Σ-cong ψ ⟩
        (Σ y ꞉ Y , fiber s y)       ≃⟨ ≃-sym (sum-of-fibers X Y s) ⟩
        X                           ■
     where
      ψ : (y : Y) → ∥ s (r y) ≡ y ∥ ≃ fiber s y
      ψ y = logically-equivalent-props-are-equivalent
             ∥∥-is-a-prop (semb y)
             f g
       where
        f : ∥ s (r y) ≡ y ∥ → fiber s y
        f = ∥∥-rec (semb y) ϕ
         where
          ϕ : s (r y) ≡ y → fiber s y
          ϕ q = (r y) , q
        g : fiber s y → ∥ s (r y) ≡ y ∥
        g (x , p) = ∣ q ∣
         where
          q = s (r y)     ≡⟨ ap (s ∘ r) (p ⁻¹) ⟩
              s (r (s x)) ≡⟨ ap s (ρ x) ⟩
              s x         ≡⟨ p ⟩
              y           ∎

 retract-of-a-set-has-size' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → is-set Y
                            → retract X of Y
                            → X has-size 𝓥
 retract-of-a-set-has-size' {𝓤} {𝓥} {X} {Y} i (r , s , ρ) =
  retract-has-size (r , s , ρ) γ
   where
    γ : is-embedding s
    γ = lc-maps-into-sets-are-embeddings s (sections-are-lc s (r , ρ)) i

-}

\end{code}
