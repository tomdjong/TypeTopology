Tom de Jong, 10 February 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module SizeBasics-Maps where

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
open import SizeBasics

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

has-size-to-has-size₁ : {𝓥 : Universe} {X : 𝓤 ̇ }
                      → X has-size 𝓥
                      → unique-to-𝟙 {_} {𝓥} {X} has-size₁ 𝓥
has-size-to-has-size₁ {𝓤} {𝓥} {X} (Y , e) u = Y , γ
 where
  γ = Y                   ≃⟨ e ⟩
      X                   ≃⟨ ≃-sym (fiber-of-unique-to-𝟙 u) ⟩
      fiber unique-to-𝟙 u ■

has-size₁-to-has-size : {𝓥 : Universe} {X : 𝓤 ̇ }
                      → unique-to-𝟙 {_} {𝓥} {X} has-size₁ 𝓥
                      → X has-size 𝓥
has-size₁-to-has-size {𝓤} {𝓥} {X} h = Y , γ
 where
  Y : 𝓥 ̇
  Y = pr₁ (h *)
  γ : Y ≃ X
  γ = Y                   ≃⟨ pr₂ (h *) ⟩
      fiber unique-to-𝟙 * ≃⟨ fiber-of-unique-to-𝟙 * ⟩
      X                   ■

equivalence-has-size₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {𝓦 : Universe}
                      → (f : X → Y)
                      → is-equiv f
                      → f has-size₁ 𝓦
equivalence-has-size₁ f i y = singleton-has-size γ
 where
  γ : is-singleton (fiber f y)
  γ = equivs-are-vv-equivs f i y

composite-has-size₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
                    → f has-size₁ 𝓣 → g has-size₁ 𝓣 → (g ∘ f) has-size₁ 𝓣
composite-has-size₁ {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {Z} {f} {g} s t z =
 (Σ a ꞉ A , B (fiber-point g z (⌜ u ⌝ a))) , γ
 where
  A : 𝓣 ̇
  A = has-size-type (t z)
  u : A ≃ fiber g z
  u = has-size-equiv (t z)
  B : Y → 𝓣 ̇
  B y = has-size-type (s y)
  v : (y : Y) → B y ≃ fiber f y
  v y = has-size-equiv (s y)
  γ = (Σ a ꞉ A , B (fiber-point g z (⌜ u ⌝ a)))         ≃⟨ i ⟩
      (Σ a ꞉ A , fiber f (fiber-point g z (⌜ u ⌝ a)))   ≃⟨ ii ⟩
      (Σ w ꞉ (fiber g z) , fiber f (fiber-point g z w)) ≃⟨ iii ⟩
      fiber (g ∘ f) z                                   ■
   where
    i   = Σ-cong (λ w → v (fiber-point g z (⌜ u ⌝ w)))
    ii  = Σ-change-of-variables (λ v → fiber f (pr₁ v)) ⌜ u ⌝ (⌜⌝-is-equiv u)
    iii = ≃-sym (fiber-of-composite f g z)

~-has-size₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : X → Y }
            → f has-size₁ 𝓦
            → f ∼ g
            → g has-size₁ 𝓦
~-has-size₁ {𝓤} {𝓥} {𝓦} {X} {Y} {f} {g} s H y = Z , (e ● (∼-fiber-≃ H y))
 where
  Z : 𝓦 ̇
  Z = has-size-type (s y)
  e : Z ≃ fiber f y
  e = has-size-equiv (s y)

\end{code}

We use the classifiers module to further study "small" maps in relation to
"small" types.

\begin{code}

module _
        {𝓤 𝓥 : Universe}
        (fe : funext 𝓤 (𝓥 ⁺ ⊔ 𝓤))
        (fe' : funext 𝓤 (𝓤 ⁺ ⊔ (𝓥 ⁺)))
        (ua : is-univalent 𝓤)
        (Y : 𝓤 ̇ )
       where

 open import UF-UniverseEmbedding
 open import UF-Classifiers
 open general-classifier {𝓤} {𝓥 ⁺ ⊔ 𝓤} fe fe' ua Y (λ X → X has-size 𝓥)

 has-size-classifier : (Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , f has-size₁ 𝓥)
                     ≃ (Y → Σ X ꞉ 𝓤 ̇ , X has-size 𝓥)
 has-size-classifier = classification-equivalence

module _
        {𝓤 𝓥 : Universe}
        (fe : FunExt)
        (ua : is-univalent (𝓤 ⊔ 𝓥))
       where

 open import UF-Equiv-FunExt
 open import UF-UniverseEmbedding

 Σ-small-types-≃-small-universe : (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , X has-size 𝓥) ≃ 𝓥 ̇
 Σ-small-types-≃-small-universe =
  (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , X has-size 𝓥)            ≃⟨ Σ-flip ⟩
  (Σ Y ꞉ 𝓥 ̇ , Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , Y ≃ X)        ≃⟨ i ⟩
  (Σ Y ꞉ 𝓥 ̇ , Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , lift 𝓤 Y ≃ X) ≃⟨ ii ⟩
  (Σ Y ꞉ 𝓥 ̇ , Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , lift 𝓤 Y ≡ X) ≃⟨ iii ⟩
  (Σ Y ꞉ 𝓥 ̇ , 𝟙{𝓥})                        ≃⟨ 𝟙-rneutral ⟩
  𝓥 ̇                                       ■
   where
    ii  = Σ-cong (λ Y → Σ-cong (λ X → ≃-sym (is-univalent-≃ ua (lift 𝓤 Y) X)))
    iii = Σ-cong h
     where
      h : (Y : 𝓥 ̇) → (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , lift 𝓤 Y ≡ X) ≃ 𝟙
      h Y = singleton-≃-𝟙 (singleton-types-are-singletons (lift 𝓤 Y))
    i   = Σ-cong f
     where
      f : (Y : 𝓥 ̇)
        → (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , Y ≃ X) ≃ (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , lift 𝓤 Y ≃ X)
      f Y = Σ-cong g
       where
        g : (X : 𝓤 ⊔ 𝓥 ̇) → (Y ≃ X) ≃ (lift 𝓤 Y ≃ X)
        g X = qinveq ϕ (ψ , (ψϕ , ϕψ))
         where
          ϕ : Y ≃ X → lift 𝓤 Y ≃ X
          ϕ e = (lift-≃ 𝓤 Y) ● e
          ψ : lift 𝓤 Y ≃ X → Y ≃ X
          ψ e = (≃-sym (lift-≃ 𝓤 Y)) ● e
          ψϕ : (e : Y ≃ X) → ψ (ϕ e) ≡ e
          ψϕ e = ψ (ϕ e)                                   ≡⟨ refl ⟩
                 (≃-sym (lift-≃ 𝓤 Y)) ● ((lift-≃ 𝓤 Y) ● e) ≡⟨ i' ⟩
                 ≃-sym (lift-≃ 𝓤 Y) ● lift-≃ 𝓤 Y ● e       ≡⟨ ii' ⟩
                 ≃-refl Y ● e                              ≡⟨ ≃-refl-left fe e ⟩
                 e                                         ∎
           where
            i'  = ≃-assoc fe (≃-sym (lift-≃ 𝓤 Y)) (lift-≃ 𝓤 Y) e
            ii' = ap (λ - → - ● e) (≃-sym-left-inverse fe (lift-≃ 𝓤 Y))
          ϕψ : (e : lift 𝓤 Y ≃ X) → ϕ (ψ e) ≡ e
          ϕψ e = ϕ (ψ e)                                 ≡⟨ refl ⟩
                 lift-≃ 𝓤 Y ● ((≃-sym (lift-≃ 𝓤 Y)) ● e) ≡⟨ i' ⟩
                 (lift-≃ 𝓤 Y ● ≃-sym (lift-≃ 𝓤 Y)) ● e   ≡⟨ ii' ⟩
                 ≃-refl (lift 𝓤 Y) ● e                   ≡⟨ ≃-refl-left fe e ⟩
                 e                                       ∎
           where
            i'  = ≃-assoc fe (lift-≃ 𝓤 Y) (≃-sym (lift-≃ 𝓤 Y)) e
            ii' = ap (λ - → - ● e) (≃-sym-right-inverse fe (lift-≃ 𝓤 Y))

 module _ (Y : 𝓤 ⊔ 𝓥 ̇ ) where

  open import UF-Classifiers
  open general-classifier {𝓤 ⊔ 𝓥} {𝓤 ⊔ 𝓥 ⁺} (fe _ _) (fe _ _)
                          ua Y (λ X → X has-size 𝓥)

  has-size-classifier-simplified : (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , Σ f ꞉ (X → Y) , f has-size₁ 𝓥)
                                 ≃ (Y → 𝓥 ̇)
  has-size-classifier-simplified =
   (Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , Σ f ꞉ (X → Y) , f has-size₁ 𝓥) ≃⟨ classification-equivalence ⟩
   (Y → Σ X ꞉ 𝓤 ⊔ 𝓥 ̇ , X has-size 𝓥)              ≃⟨ h ⟩
   (Y → 𝓥 ̇)                                       ■
    where
     h = →cong (fe _ _) (fe _ _) (≃-refl Y) Σ-small-types-≃-small-universe

\end{code}

We should also consider the other case, i.e. the case where Y : 𝓤 ̇ and we
consider types of size 𝓤 ⊔ 𝓥. Then we should get:

(Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , f has-size₁ (𝓤 ⊔ 𝓥)) ≃ (Y → 𝓤 ̇ )

We leave this as a TODO for now.

\begin{code}

module _
        {𝓤 𝓥 : Universe}
        (fe : FunExt)
        (ua : is-univalent (𝓤 ⊔ 𝓥))
       where

 open import UF-Equiv-FunExt
 open import UF-UniverseEmbedding

 -- This should have a better name?

 transport-equiv : {X : 𝓤 ̇ } {X' Y : 𝓤 ⊔ 𝓥 ̇ } (e' : X' ≃ Y) (e : X' ≃ X)
                 → transport (λ - → - ≃ X) (eqtoid ua X' Y e') e
                 ≡ ≃-sym e' ● e
 transport-equiv {X} {X'} {Y} e' e = {!τ!}
  where
   τ : (p : X' ≡ Y)
     → p ≡ eqtoid ua X' Y e'
     → transport (λ - → - ≃ X) p e ≡ ≃-sym e' ● e
   τ refl q = {!!}

 resizing-up-does-nothing : (Σ X ꞉ 𝓤 ̇ , X has-size (𝓤 ⊔ 𝓥)) ≃ 𝓤 ̇
 resizing-up-does-nothing = qinveq f (g , gf , fg)
  where
   f : (Σ X ꞉ 𝓤 ̇ , X has-size (𝓤 ⊔ 𝓥)) → 𝓤 ̇
   f = pr₁
   g : 𝓤 ̇ → (Σ X ꞉ 𝓤 ̇ , X has-size (𝓤 ⊔ 𝓥))
   g X = X , (resize-up {𝓤} {𝓥} X)
   fg : (X : 𝓤 ̇ ) → f (g X) ≡ X
   fg X = refl
   gf : (p : Σ X ꞉ 𝓤 ̇ , X has-size (𝓤 ⊔ 𝓥)) → g (f p) ≡ p
   gf (X , Y , e) = to-Σ-≡ (refl , γ)
    where
     γ : lift 𝓥 X , lift-≃ 𝓥 X ≡ Y , e
     γ = to-Σ-≡ (eqtoid ua (lift 𝓥 X) Y χ ,
          to-subtype-≡ (λ _ → being-equiv-is-a-prop fe _)
          (dfunext (fe _ _) h))
      where
       χ = lift 𝓥 X ≃⟨ lift-≃ 𝓥 X ⟩
           X         ≃⟨ ≃-sym e ⟩
           Y         ■
       e' : lift 𝓥 X ≡ Y
       e' = eqtoid ua (lift 𝓥 X) Y χ
       h : (y : Y)
         → ⌜ transport (λ - → - ≃ X) e' (lift-≃ 𝓥 X) ⌝ y
         ≡ pr₁ e y
       h y = ⌜ transport (λ - → - ≃ X) e' (lift-≃ 𝓥 X) ⌝ y ≡⟨ ℏ ⟩
             ⌜ (≃-sym χ ● lift-≃ 𝓥 X) ⌝ y                  ≡⟨ refl ⟩
             ⌜ e ⌝ y                                       ∎
        where
         ℏ = happly (ap ⌜_⌝ (transport-equiv χ (lift-≃ 𝓥 X))) y

 module _ (Y : 𝓤 ̇ ) (ua' : is-univalent 𝓤) where

  open import UF-Classifiers
  open general-classifier {𝓤} {(𝓤 ⁺) ⊔ (𝓥 ⁺)} (fe _ _) (fe _ _)
                          ua' Y (λ X → X has-size (𝓤 ⊔ 𝓥))

  has-size-classifier-simplified' : (Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) ,
                                     f has-size₁ (𝓤 ⊔ 𝓥))
                                  ≃ (Y → 𝓤 ̇)
  has-size-classifier-simplified' =
   (Σ X ꞉ 𝓤 ̇ , Σ f ꞉ (X → Y) , f has-size₁ (𝓤 ⊔ 𝓥)) ≃⟨ i ⟩
   (Y → Σ X ꞉ 𝓤 ̇ , X has-size (𝓤 ⊔ 𝓥))              ≃⟨ ii ⟩
   (Y → 𝓤 ̇)                                         ■
    where
     i = classification-equivalence
     ii = →cong (fe _ _) (fe _ _) (≃-refl Y) resizing-up-does-nothing

\end{code}

Next, we consider the resizing of embeddings and prove that this is equivalent
to propositional resizing.

\begin{code}

embedding-resizing : (𝓤 𝓥 𝓦 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ⁺ ⊔ (𝓦 ⁺) ̇
embedding-resizing 𝓤 𝓥 𝓦 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (f : X → Y)
                         → is-embedding f
                         → f has-size₁ 𝓦

Embedding-resizing : 𝓤ω
Embedding-resizing = {𝓤 𝓥 𝓦 : Universe} → embedding-resizing 𝓤 𝓥 𝓦

Embedding-resizing-implies-Propositional-resizing : Embedding-resizing
                                                  → Propositional-resizing
Embedding-resizing-implies-Propositional-resizing Er {𝓤} {𝓥} P i =
 has-size₁-to-has-size γ
  where
   γ : (u : 𝟙) → fiber (unique-to-𝟙 {_} {𝓥} {P}) u has-size 𝓥
   γ u = Er P 𝟙 unique-to-𝟙 ε u
    where
     ε : is-embedding (unique-to-𝟙 {_} {𝓥} {P})
     ε * = Σ-is-prop i (λ _ → props-are-sets 𝟙-is-prop)

Propositional-resizing-implies-Embedding-resizing : Propositional-resizing
                                                  → Embedding-resizing
Propositional-resizing-implies-Embedding-resizing Pr X Y f e y =
 Pr (fiber f y) (e y)

\end{code}

There should be some theorems about has-size₁ being closed under (appropriately
coherent) retracts of maps for which the sections are embeddings.

See UF-MapRetracts.

This should be compared to the (simpler) case of has-size for types.
