Tom de Jong, 10 February 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SizeBasics where

open import SpartanMLTT

open import UF-Base hiding (_≈_)
open import UF-Embeddings
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-PropTrunc hiding (_≈_)
open import UF-Retracts
open import UF-UA-FunExt
open import UF-Univalence

open import UF-Size

\end{code}

\begin{code}

singleton-has-size : {𝓥 : Universe} {X : 𝓤 ̇ }
                   → is-singleton X
                   → X has-size 𝓥
singleton-has-size i = (𝟙 , singleton-≃-𝟙' i)

\end{code}

We consider some resizing principles and prove that they are all equivalent
propositional resizing.

\begin{code}

subtype-resizing : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇
subtype-resizing 𝓤 𝓥 = (X : 𝓤 ̇ ) (P : X → 𝓥 ̇ )
                     → ((x : X) → is-prop (P x))
                     → (Σ x ꞉ X , P x) has-size 𝓤

Subtype-resizing : 𝓤ω
Subtype-resizing = {𝓤 𝓥 : Universe} → subtype-resizing 𝓤 𝓥

Subtype-resizing-implies-Propositional-resizing : Subtype-resizing
                                                → Propositional-resizing
Subtype-resizing-implies-Propositional-resizing Sr {𝓤} {𝓥} P i = Q , γ
 where
  sr : (𝟙{𝓥} × P) has-size 𝓥
  sr = Sr (𝟙{𝓥}) (λ _ → P) (λ _ → i)
  Q : 𝓥 ̇
  Q = has-size-type sr
  γ = Q     ≃⟨ has-size-equiv sr ⟩
      𝟙 × P ≃⟨ 𝟙-lneutral ⟩
      P     ■

Propositional-resizing-implies-Subtype-resizing : Propositional-resizing
                                                → Subtype-resizing
Propositional-resizing-implies-Subtype-resizing Pr {𝓤} {𝓥} X P i =
 (Σ x ꞉ X , Q x) , γ
  where
   pr : (x : X) → (P x) has-size 𝓤
   pr x = Pr (P x) (i x)
   Q : X → 𝓤 ̇
   Q x = resize Pr (P x) (i x)
   γ : (Σ x ꞉ X , Q x) ≃ (Σ x ꞉ X , P x)
   γ = Σ-cong (λ (x : X) → has-size-equiv (pr x))

module _
        (pt : propositional-truncations-exist)
       where
 open import UF-ImageAndSurjection
 open ImageAndSurjection pt
 open PropositionalTruncation pt

 image-resizing-codomain : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇
 image-resizing-codomain 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                           → (f : X → Y)
                           → image f has-size 𝓥

 Image-resizing-codomain : 𝓤ω
 Image-resizing-codomain = {𝓤 𝓥 : Universe} → image-resizing-codomain 𝓤 𝓥

 Image-resizing-codomain-implies-Propositional-resizing : Image-resizing-codomain
                                                        → Propositional-resizing
 Image-resizing-codomain-implies-Propositional-resizing Ir {𝓤} {𝓥} P s = Q , γ
  where
   ir : image unique-to-𝟙 has-size 𝓥
   ir = Ir P (𝟙{𝓥}) unique-to-𝟙
   Q : 𝓥 ̇
   Q = has-size-type ir
   γ = Q                           ≃⟨ has-size-equiv ir ⟩
       image unique-to-𝟙           ≃⟨ ≃-refl (image unique-to-𝟙) ⟩
       (Σ u ꞉ 𝟙 , ∃ p ꞉ P , * ≡ u) ≃⟨ i ⟩
       (Σ u ꞉ 𝟙 , Σ p ꞉ P , * ≡ u) ≃⟨ ≃-refl _ ⟩
       (Σ u ꞉ 𝟙 , P × (* ≡ u))     ≃⟨ Σ-flip ⟩
       P × (Σ u ꞉ 𝟙 , * ≡ u)       ≃⟨ ii ⟩
       P × 𝟙{𝓥}                    ≃⟨ 𝟙-rneutral ⟩
       P                           ■
    where
     i  = Σ-cong (λ u → a-prop-is-equivalent-to-its-truncation (σ u))
      where
       σ : (u : 𝟙) → is-prop (Σ p ꞉ P , * ≡ u)
       σ _ = Σ-is-prop s (λ _ → props-are-sets 𝟙-is-prop)
     ii = ×cong (≃-refl P) (singleton-≃-𝟙 (singleton-types-are-singletons *))

 Propositional-resizing-implies-Image-resizing-codomain : Propositional-resizing
                                                        → Image-resizing-codomain
 Propositional-resizing-implies-Image-resizing-codomain Pr {𝓤} {𝓥} X Y f =
  Propositional-resizing-implies-Subtype-resizing Pr Y S (λ y → ∥∥-is-a-prop)
   where
    S : Y → 𝓤 ⊔ 𝓥 ̇
    S y = ∃ x ꞉ X , f x ≡ y

\end{code}

Here are some additional resizing principles, for which I have not been able
that they are equivalent to propositional resizing (or Ω-Resizing), but they
are/seem related.

\begin{code}

module _
        (pt : propositional-truncations-exist)
        (fe : FunExt)
        (pe : PropExt)
       where

 open import UF-Quotient
 open Quotient pt fe

 open import UF-ImageAndSurjection hiding (_≈_)
 open ImageAndSurjection pt
 open PropositionalTruncation pt

 quotient-resizing : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇
 quotient-resizing 𝓤 𝓥 = (X : 𝓤 ̇ ) (_≈_ : X → X → 𝓥 ̇ )
                         (≈p : is-prop-valued _≈_)
                         (≈r : reflexive _≈_)
                         (≈s : symmetric _≈_)
                         (≈t : transitive _≈_)
                       → (X/≈ (pe 𝓥) X _≈_ ≈p ≈r ≈s ≈t) has-size 𝓤

 Quotient-resizing : 𝓤ω
 Quotient-resizing = {𝓤 𝓥 : Universe} → quotient-resizing 𝓤 𝓥

 image-resizing-domain : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇
 image-resizing-domain 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y)
                           → image f has-size 𝓤

 Image-resizing-domain : 𝓤ω
 Image-resizing-domain = {𝓤 𝓥 : Universe} → image-resizing-domain 𝓤 𝓥

 surjective-resizing : (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ (𝓥 ⁺) ̇
 surjective-resizing 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y)
                         → is-surjection f
                         → Y has-size 𝓤

 Surjective-resizing : 𝓤ω
 Surjective-resizing = {𝓤 𝓥 : Universe} → surjective-resizing 𝓤 𝓥

 Image-resizing-domain-implies-Quotient-resizing : Image-resizing-domain
                                                 → Quotient-resizing
 Image-resizing-domain-implies-Quotient-resizing Ir {𝓤} {𝓥} X _≈_ ≈p ≈r ≈s ≈t =
  Ir X (X → Ω 𝓥) (equiv-rel (pe 𝓥) X _≈_ ≈p ≈r ≈s ≈t)

 Image-resizing-domain-implies-Surjective-resizing : Image-resizing-domain
                                                   → Surjective-resizing
 Image-resizing-domain-implies-Surjective-resizing Ir {𝓤} {𝓥} X Y f s = Z , γ
  where
   ir : image f has-size 𝓤
   ir = Ir X Y f
   Z : 𝓤 ̇
   Z = has-size-type ir
   γ = Z       ≃⟨ has-size-equiv ir ⟩
       image f ≃⟨ surjection-≃-image f s ⟩
       Y       ■

 Surjective-resizing-implies-Image-resizing-domain : Surjective-resizing
                                                   → Image-resizing-domain
 Surjective-resizing-implies-Image-resizing-domain Sr {𝓤} {𝓥} X Y f =
  Sr X (image f) (corestriction f) (corestriction-surjection f)

 Ω-Resizing-implies-quotient-resizing : {𝓤 𝓥 : Universe}
                                      → Ω-Resizing 𝓥 𝓤 → quotient-resizing 𝓤 𝓥
 Ω-Resizing-implies-quotient-resizing {𝓤} {𝓥} ΩR X _≈_ ≈p ≈r ≈s ≈t =
  (image _≋'_) , γ
   where
    _≋_ : X → X → Ω 𝓥
    x ≋ y = x ≈ y , ≈p x y
    Ω' : 𝓤 ̇
    Ω' = has-size-type ΩR
    e : Ω' ≃ Ω 𝓥
    e = has-size-equiv ΩR
    _≋'_ : X → X → Ω'
    x ≋' y = back-eqtofun e (x ≋ y)
    fe' : {𝓤 𝓥 : Universe} → funext 𝓤 𝓥
    fe' {𝓤} {𝓥} = fe 𝓤 𝓥
    γ : image _≋'_ ≃ image _≋_
    γ = image _≋'_                                   ≃⟨ ≃-refl _ ⟩
        (Σ α ꞉ (X → Ω') , ∃ x ꞉ X , _≋'_ x ≡ α)      ≃⟨ I ⟩
        (Σ α ꞉ (X → Ω') , ∃ x ꞉ X , _≋_ x ≡ ⌜ ϕ ⌝ α) ≃⟨ II ⟩
        image _≋_                                    ■
     where
      ϕ : (X → Ω') ≃ (X → Ω 𝓥)
      ϕ = →cong (fe') (fe') (≃-refl X) e
      II = Σ-change-of-variables (λ (α : X → Ω 𝓥) → ∃ x ꞉ X , _≋_ x ≡ α)
           ⌜ ϕ ⌝ (⌜⌝-is-equiv ϕ)
      I = Σ-cong h
       where
        h : (α : X → Ω')
          → (∃ x ꞉ X , _≋'_ x ≡ α) ≃ (∃ x ꞉ X , _≋_ x ≡ ⌜ ϕ ⌝ α)
        h α = logically-equivalent-props-are-equivalent
              ∥∥-is-a-prop ∥∥-is-a-prop f g
         where
          f : (∃ x ꞉ X , _≋'_ x ≡ α) → (∃ x ꞉ X , _≋_ x ≡ ⌜ ϕ ⌝ α)
          f = ∥∥-functor ψ
           where
            ψ : (Σ x ꞉ X , _≋'_ x ≡ α) → (Σ x ꞉ X , _≋_ x ≡ ⌜ ϕ ⌝ α)
            ψ (x , u) = x , v
             where
              v = _≋_ x                          ≡⟨ i ⟩
                  ⌜ e ⌝ ∘ back-eqtofun e ∘ _≋_ x ≡⟨ refl ⟩
                  ⌜ e ⌝ ∘ (_≋'_ x)               ≡⟨ ap (λ - → ⌜ e ⌝ ∘ -) u ⟩
                  ⌜ e ⌝ ∘ α                      ≡⟨ refl ⟩
                  ⌜ ϕ ⌝ α                        ∎
               where
                i = ap (λ - → - ∘ _≋_ x)
                    (dfunext fe' (inverse-is-section ⌜ e ⌝ (⌜⌝-is-equiv e))) ⁻¹
          g : (∃ x ꞉ X , _≋_ x ≡ ⌜ ϕ ⌝ α) → (∃ x ꞉ X , _≋'_ x ≡ α)
          g = ∥∥-functor ψ
           where
            ψ : (Σ x ꞉ X , _≋_ x ≡ ⌜ ϕ ⌝ α) → (Σ x ꞉ X , _≋'_ x ≡ α)
            ψ (x , u) = x , v
             where
              v = _≋'_ x                     ≡⟨ refl ⟩
                  back-eqtofun e ∘ _≋_ x     ≡⟨ ap (λ - → back-eqtofun e ∘ -) u ⟩
                  back-eqtofun e ∘ ⌜ ϕ ⌝ α   ≡⟨ refl ⟩
                  back-eqtofun e ∘ ⌜ e ⌝ ∘ α ≡⟨ i ⟩
                  α                          ∎
               where
                i = ap (λ - → - ∘ α)
                    (dfunext fe' (inverse-is-retraction ⌜ e ⌝ (⌜⌝-is-equiv e)))

\end{code}

We prove for sets that having a certain size is closed under retracts.

We can prove the same thing for (higher) types if the section is additionally
assumed to be an embedding.

Note that for sets this extra condition is automatically true. However, we keep
the specific construction for sets, because, unlike the general construction, it
does not require propositional truncation.

\begin{code}

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
  ∥ s (r y) ≡ y ∥ ≃⟨ a-prop-is-equivalent-to-its-truncation σ ⟩
  (s (r y) ≡ y)   ■
   where
    ε = lc-maps-into-sets-are-embeddings s (sections-are-lc s ((r , ρ))) σ

 embedding-retract-has-size : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                            → (ρ : X ◁ Y)
                            → is-embedding (section ρ)
                            → X has-size 𝓥
 embedding-retract-has-size {𝓤} {𝓥} {X} {Y} (r , s , ρ) ε =
  (Σ y ꞉ Y , ∥ s (r y) ≡ y ∥) ,
  fixed-points-of-embedding-retraction (r , s , ρ) ε

\end{code}
