
Tom de Jong, 10 February 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SizeBasics where

open import SpartanMLTT

open import UF-Base
open import UF-Embeddings
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-PropTrunc
open import UF-Retracts
open import UF-UA-FunExt
open import UF-Univalence

open import UF-Size

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
      X                   ≃⟨ ≃-sym (fiber-of-unique-to-𝟙 u) ⟩
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
      fiber unique-to-𝟙 * ≃⟨ fiber-of-unique-to-𝟙 * ⟩
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

embedding-resizing : (𝓤 𝓥 𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ (𝓦 ⁺) ̇
embedding-resizing 𝓤 𝓥 𝓦 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y)
                         → is-embedding f
                         → f has-size₁ 𝓦

Embedding-resizing : 𝓤ω
Embedding-resizing = {𝓤 𝓥 𝓦 : Universe} → embedding-resizing 𝓤 𝓥 𝓦

Embedding-resizing-gives-Propositional-resizing : Embedding-resizing
                                                → Propositional-resizing
Embedding-resizing-gives-Propositional-resizing Er {𝓤} {𝓥} P i = (Q , γ)
 where
  er : fiber (unique-to-𝟙 {_} {𝓥} {P}) * has-size 𝓥
  er = Er P (𝟙{𝓥}) unique-to-𝟙 ε *
   where
    ε : is-embedding (unique-to-𝟙 {_} {𝓥} {P})
    ε * = Σ-is-prop i (λ _ → props-are-sets 𝟙-is-prop)
  Q : 𝓥 ̇
  Q = pr₁ er
  γ = Q                   ≃⟨ pr₂ er ⟩
      fiber unique-to-𝟙 * ≃⟨ fiber-of-unique-to-𝟙 * ⟩
      P                   ■

Propositional-resizing-gives-Embedding-resizing : Propositional-resizing
                                                → Embedding-resizing
Propositional-resizing-gives-Embedding-resizing Pr X Y f e y =
 Pr (fiber f y) (e y)

fiber-of-section-to-a-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → is-set Y
                          → (s : X → Y)
                          → (ρ : is-section s)
                          → (y : Y) → (fiber s y) ≃ (s (pr₁ ρ y) ≡ y)
fiber-of-section-to-a-set σ s (r , ρ) y = qinveq f (g , (gf , fg))
 where
  f : fiber s y → s (r y) ≡ y
  f (x , p) = s (r y)     ≡⟨ ap (s ∘ r) (p ⁻¹) ⟩
              s (r (s x)) ≡⟨ ap s (ρ x) ⟩
              s x         ≡⟨ p ⟩
              y           ∎
  g : s (r y) ≡ y → fiber s y
  g q = (r y) , q
  gf : (w : fiber s y) → g (f w) ≡ w
  gf (x , refl) = to-subtype-≡ (λ _ → σ) (ρ x)
  fg : (q : s (r y) ≡ y) → f (g q) ≡ q
  fg q = σ (f (g q)) q

fixed-points-of-section-retraction-to-set : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                          → is-set Y
                                          → (ρ : X ◁ Y)
                                          → (Σ y ꞉ Y ,
                                             section ρ (retraction ρ y) ≡ y)
                                          ≃ X
fixed-points-of-section-retraction-to-set {𝓤} {𝓥} {X} {Y} i (r , s , ρ) =
 (Σ y ꞉ Y , s (r y) ≡ y) ≃⟨ γ ⟩
 (Σ y ꞉ Y , (fiber s y)) ≃⟨ ≃-sym (sum-of-fibers X Y s) ⟩
 X                       ■
  where
   γ = Σ-cong (λ (y : Y) → ≃-sym (fiber-of-section-to-a-set i s (r , ρ) y))

retract-of-a-set-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → is-set Y
                          → X ◁ Y
                          → X has-size 𝓥
retract-of-a-set-has-size {𝓤} {𝓥} {X} {Y} i (r , s , ρ) =
 (Σ y ꞉ Y , s (r y) ≡ y) ,
 fixed-points-of-section-retraction-to-set i (r , s , ρ)

module _ (pt : propositional-truncations-exist) where
 open PropositionalTruncation pt

 fiber-of-section-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → (s : X → Y)
                            → (ρ : is-section s)
                            → is-embedding s
                            → (y : Y) → fiber s y ≃ ∥ s (pr₁ ρ y) ≡ y ∥
 fiber-of-section-embedding s (r , ρ) ε y =
  logically-equivalent-props-are-equivalent (ε y) ∥∥-is-a-prop f g
   where
    f : fiber s y → ∥ s (r y) ≡ y ∥
    f (x , refl) = ∣ ap s (ρ x) ∣
    g : ∥ s (r y) ≡ y ∥ → fiber s y
    g = ∥∥-rec (ε y) h
     where
      h : s (r y) ≡ y → fiber s y
      h q = (r y) , q

 fixed-points-of-embedding-retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                      → (ρ : X ◁ Y)
                                      → is-embedding (section ρ)
                                      → (Σ y ꞉ Y ,
                                         ∥ section ρ (retraction ρ y) ≡ y ∥)
                                      ≃ X
 fixed-points-of-embedding-retraction {𝓤} {𝓥} {X} {Y} (r , s , ρ) ε =
  (Σ y ꞉ Y , ∥ s (r y) ≡ y ∥) ≃⟨ h ⟩
  (Σ y ꞉ Y , fiber s y)       ≃⟨ ≃-sym (sum-of-fibers X Y s) ⟩
  X                           ■
   where
    h = Σ-cong (λ (y : Y) → ≃-sym (fiber-of-section-embedding s (r , ρ) ε y))

 fiber-of-section-to-a-set' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → is-set Y
                            → (s : X → Y)
                            → (ρ : is-section s)
                            → (y : Y) → (fiber s y) ≃ (s (pr₁ ρ y) ≡ y)
 fiber-of-section-to-a-set' σ s (r , ρ) y =
  fiber s y       ≃⟨ fiber-of-section-embedding s (r , ρ) ε y ⟩
  ∥ s (r y) ≡ y ∥ ≃⟨ h ⟩
  (s (r y) ≡ y)   ■
   where
    ε = lc-maps-into-sets-are-embeddings s (sections-are-lc s ((r , ρ))) σ
    h = logically-equivalent-props-are-equivalent ∥∥-is-a-prop σ
        (∥∥-rec σ id) ∣_∣

 embedding-retract-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → (ρ : X ◁ Y)
                            → is-embedding (section ρ)
                            → X has-size 𝓥
 embedding-retract-has-size {𝓤} {𝓥} {X} {Y} (r , s , ρ) ε =
  (Σ y ꞉ Y , ∥ s (r y) ≡ y ∥) ,
  fixed-points-of-embedding-retraction (r , s , ρ) ε

\end{code}

\begin{code}

subtype-resizing : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇
subtype-resizing 𝓤 𝓥 = (X : 𝓤 ̇ ) (P : X → 𝓥 ̇ )
                     → ((x : X) → is-prop (P x))
                     → (Σ x ꞉ X , P x) has-size 𝓤

Subtype-resizing : 𝓤ω
Subtype-resizing = {𝓤 𝓥 : Universe} → subtype-resizing 𝓤 𝓥

Subtype-resizing-gives-Propositional-resizing : Subtype-resizing
                                              → Propositional-resizing
Subtype-resizing-gives-Propositional-resizing Sr {𝓤} {𝓥} P i = Q , γ
 where
  sr : (𝟙{𝓥} × P) has-size 𝓥
  sr = Sr (𝟙{𝓥}) (λ _ → P) (λ _ → i)
  Q : 𝓥 ̇
  Q = pr₁ sr
  γ = Q     ≃⟨ pr₂ sr ⟩
      𝟙 × P ≃⟨ 𝟙-lneutral ⟩
      P     ■

Propositional-resizing-gives-Subtype-resizing : Propositional-resizing
                                              → Subtype-resizing
Propositional-resizing-gives-Subtype-resizing Pr {𝓤} {𝓥} X P i =
 (Σ x ꞉ X , Q x) , γ
  where
   pr : (x : X) → (P x) has-size 𝓤
   pr x = Pr (P x) (i x)
   Q : X → 𝓤 ̇
   Q x = pr₁ (pr x)
   γ : (Σ x ꞉ X , Q x) ≃ (Σ x ꞉ X , P x)
   γ = Σ-cong (λ (x : X) → pr₂ (pr x))

\end{code}
