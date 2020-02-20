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

singleton-has-size : {𝓥 : Universe} {X : 𝓤 ̇ }
                   → is-singleton X
                   → X has-size 𝓥
singleton-has-size i = (𝟙 , singleton-≃-𝟙' i)

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

\begin{code}

{-

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

\end{code}

\begin{code}

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
  (Σ Y ꞉ 𝓥 ̇ , 𝟙{𝓥})                          ≃⟨ 𝟙-rneutral ⟩
  𝓥 ̇                                         ■
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

\begin{code}

-}

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

\begin{code}

module _
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {W : 𝓤' ̇ } {Z : 𝓥' ̇ }
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 map-retract-into-a-set-has-size₁ : {f : X → Y} {g : W → Z}
                                  → (r : f ◁₁ g)
                                  → is-embedding (section (domains-retract r))
                                  → is-embedding (section (codomains-retract r))
                                  → g has-size₁ 𝓦
                                  → f has-size₁ 𝓦
 map-retract-into-a-set-has-size₁ {𝓦} {f} {g} (r₁ , r₂ , c , d) δ ε ghs y =
  {!!}
   where
    s : X → W
    s = section r₁
    r : W → X
    r = retraction r₁
    u : Y → Z
    u = section r₂
    v : Z → Y
    v = retraction r₂
    a : (x : X) → r (s x) ≡ x
    a = retract-condition r₁
    b : (y : Y) → v (u y) ≡ y
    b = retract-condition r₂
    i : fiber f y ≃ (Σ x ꞉ X , u (f x) ≡ u y)
    i = Σ-cong (λ (x : X) → (ap u) , (embedding-embedding' u ε (f x) y))
    ii : (Σ x ꞉ X , u (f x) ≡ u y) ≃ (Σ x ꞉ X , g (s x) ≡ u y)
    ii = ∼-fiber-≃ c (u y)
    iii : (Σ x ꞉ X , g (s x) ≡ u y) ≃ (Σ ϕ ꞉ (fiber g (u y)) , fiber s (fiber-point g (u y) ϕ))
    iii = fiber-of-composite s g (u y)

    σ' : (Σ x ꞉ X , g (s x) ≡ u y) → fiber g (u y)
    σ' (x , p) = s x , p

    ρ' : fiber g (u y) → (Σ x ꞉ X , g (s x) ≡ u y)
    ρ' (w , q) = r w , p
     where
      p = g (s (r w)) ≡⟨ (c (r w)) ⁻¹ ⟩
          u (f (r w)) ≡⟨ ap u (((d w) ⁻¹) ∙ ((ap v q) ∙ (b y))) ⟩
          u y         ∎
      {-
          u (f (r w)) ≡⟨ ap u ((d w) ⁻¹) ⟩
          u (v (g w)) ≡⟨ ap (u ∘ v) q ⟩
          u (v (u y)) ≡⟨ ap u (b y) ⟩
          u y         ∎
       -}

    𝓇 : (Σ x ꞉ X , g (s x) ≡ u y) ◁ fiber g (u y)
    𝓇 = ρ' , (σ' , 𝒽)
     where
      𝒽 : (k : (Σ x ꞉ X , g (s x) ≡ u y)) → ρ' (σ' k) ≡ k
      𝒽 (x , p) = to-Σ-≡ ((a x) , h)
       where
        h : transport (λ x' → g (s x') ≡ u y) (a x)
              ((c (r (s x))) ⁻¹ ∙ ap u (((d (s x)) ⁻¹) ∙ ((ap v p) ∙ (b y))))
              -- (((c (r (s x))) ⁻¹) ∙ ((ap u ((d (s x)) ⁻¹)) ∙ ((ap (u ∘ v) p) ∙ (ap u (b y)))))
          ≡ p
        h = transport (λ x' → g (s x') ≡ u y) (a x)
              ((c (r (s x))) ⁻¹ ∙ ap u (((d (s x)) ⁻¹) ∙ ((ap v p) ∙ (b y)))) ≡⟨ {!!} ⟩
            ap (g ∘ s) ((a x) ⁻¹) ∙ ((c (r (s x))) ⁻¹ ∙ ap u (((d (s x)) ⁻¹) ∙ ((ap v p) ∙ (b y)))) ≡⟨ ap (λ - → - ∙ _) ((ap-sym (g ∘ s) (a x)) ⁻¹) ⟩
            (ap (g ∘ s) ((a x))) ⁻¹ ∙ ((c (r (s x))) ⁻¹ ∙ ap u (((d (s x)) ⁻¹) ∙ ((ap v p) ∙ (b y)))) ≡⟨ ∙assoc {!!} {!!} {!!} ⟩
            (ap (g ∘ s) ((a x))) ⁻¹ ∙ (c (r (s x))) ⁻¹ ∙ (ap u (((d (s x)) ⁻¹) ∙ ((ap v p) ∙ (b y)))) ≡⟨ ap (λ - → - ∙ _) (⁻¹-contravariant (c (r (s x))) _) ⟩
            ((c (r (s x)) ∙ ap (g ∘ s) (a x)) ⁻¹) ∙ _ ≡⟨ ap (λ - → - ⁻¹ ∙ _) (homotopies-are-natural (u ∘ f) (g ∘ s) c) ⟩
            (ap (u ∘ f) (a x) ∙ c x) ⁻¹ ∙ {!!}    ≡⟨ {!!} ⟩
            p ∎

    {-
    σ' : (Σ ϕ ꞉ (fiber g (u y)) , fiber s (fiber-point g (u y) ϕ)) → fiber g (u y)
    σ' = pr₁
    ρ' : fiber g (u y) → (Σ ϕ ꞉ (fiber g (u y)) , fiber s (fiber-point g (u y) ϕ))
    ρ' (w , q) = ⌜ iii ⌝ ((r w) , p)
     where-
      p = g (s (r w)) ≡⟨ (c (r w)) ⁻¹ ⟩
          u (f (r w)) ≡⟨ ap u (d w) ⁻¹ ⟩
          u (v (g w)) ≡⟨ ap (u ∘ v) q ⟩
          u (v (u y)) ≡⟨ ap u (b y) ⟩
          u y         ∎
    𝓇 : (Σ ϕ ꞉ (fiber g (u y)) , fiber s (fiber-point g (u y) ϕ)) ◁ fiber g (u y)
    𝓇 = ρ' , (σ' , ρ'σ')
     where
      ρ'σ' : (k : (Σ ϕ ꞉ (fiber g (u y)) , fiber s (fiber-point g (u y) ϕ)))
           → ρ' (σ' k) ≡ k
      ρ'σ' ((w , q) , (x , p)) = to-subtype-≡ {!!} (to-Σ-≡ ({!!} , {!!}))
    -}

\end{code}

\begin{code}

{-

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

Question: are images with small domain small?

Answer: equivalent to PR? (Quotient) construction

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

-}


{-
 Quotient-resizing-gives-Set-truncation : Quotient-resizing → (X : 𝓤 ̇ )
                                        → Σ Y ꞉ 𝓤 ̇ , {!!}
 Quotient-resizing-gives-Set-truncation = {!!}

 Quotient-resizing-implies-Image-resizing-domain : Quotient-resizing
                                                 → Image-resizing-domain
 Quotient-resizing-implies-Image-resizing-domain Qr {𝓤} {𝓥} X Y f =
  {!!}
   where
    _≈_ : X → X → 𝓥 ̇
    x ≈ x' = ∥ f x ≡ f x' ∥
    ≈p : is-prop-valued _≈_
    ≈p x x' = ∥∥-is-a-prop
    ≈r : reflexive _≈_
    ≈r x = ∣ refl ∣
    ≈s : symmetric _≈_
    ≈s x x' = ∥∥-functor _⁻¹
    ≈t : transitive _≈_
    ≈t x x' x'' r s = do
     u ← r
     v ← s
     ∣ u ∙ v ∣
    Q : 𝓤 ⊔ (𝓥 ⁺) ̇
    Q = X/≈ (pe 𝓥) X _≈_ ≈p ≈r ≈s ≈t
    ηQ : X → Q
    ηQ = η (pe 𝓥) X _≈_ ≈p ≈r ≈s ≈t
    _≋_ : X → X → 𝓤 ̇
    x ≋ x' = ∥ x ≡ x' ∥
    ≋p : is-prop-valued _≋_
    ≋p x x' = ∥∥-is-a-prop
    ≋r : reflexive _≋_
    ≋r x = ∣ refl ∣
    ≋s : symmetric _≋_
    ≋s x x' = ∥∥-functor _⁻¹
    ≋t : transitive _≋_
    ≋t x x' x'' r s = do
     u ← r
     v ← s
     ∣ u ∙ v ∣
    X/≋ : {!!} ̇
    X/≋ = {!!}
    γ : Q ≃ image f
    γ = qinveq ϕ (ψ , (ψϕ , ϕψ))
     where
      up : ∃! f' ꞉ (Q → image f), f' ∘ ηQ ≡ corestriction f
      up = universal-property (pe 𝓥) X _≈_ ≈p ≈r ≈s ≈t (image f)
           {!!} (corestriction f) {!!}
      ϕ : Q → image f
      ϕ = {!!}
      ψ : image f → Q
      ψ = {!!}
      ψϕ : (q : Q) → ψ (ϕ q) ≡ q
      ψϕ = {!!}
      ϕψ : (w : image f) → ϕ (ψ w) ≡ w
      ϕψ = {!!}
-}

 {- Quotient-resizing-implies-Propositional-resizing : Quotient-resizing
                                                  → Propositional-resizing
 Quotient-resizing-implies-Propositional-resizing Qr {𝓤} {𝓥} P i = {!!} -}

 {-
 quotient-resizing⁺ : (𝓤 𝓥 : Universe) → (𝓤 ⁺) ⁺ ⊔ (𝓥 ⁺) ̇
 quotient-resizing⁺ 𝓤 𝓥 = (X : 𝓤 ⁺ ̇ ) (_≈_ : X → X → 𝓥 ̇ )
                          (≈p : is-prop-valued _≈_)
                          (≈r : reflexive _≈_)
                          (≈s : symmetric _≈_)
                          (≈t : transitive _≈_)
                        → (X/≈ (pe 𝓥) X _≈_ ≈p ≈r ≈s ≈t) has-size (𝓤 ⁺)

 Quotient-resizing⁺ : 𝓤ω
 Quotient-resizing⁺ = {𝓤 𝓥 : Universe} → quotient-resizing⁺ 𝓤 𝓥


 image-resizing-domain⁺ : (𝓤 𝓥 : Universe) → (𝓤 ⁺) ⁺ ⊔ (𝓥 ⁺) ̇
 image-resizing-domain⁺ 𝓤 𝓥 = (X : 𝓤 ⁺ ̇ ) (Y : 𝓥 ̇ ) (f : X → Y)
                            → image f has-size (𝓤 ⁺)

 Image-resizing-domain⁺ : 𝓤ω
 Image-resizing-domain⁺ = {𝓤 𝓥 : Universe} → image-resizing-domain⁺ 𝓤 𝓥
-}


\end{code}