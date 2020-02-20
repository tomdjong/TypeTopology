Tom de Jong, 16 February 2020 -

Retracts of maps.

f is a retract of g if there is a commutative diagram:

X --s--> W --r--> X # composition is id
|        |        |
f        g        f
|        |        |
∨       ∨        ∨
Y --u--> Z --v--> Y # composition is id

This could be developed further, including notation for composing such retracts
of maps. But the following suffices for our (current) purposes.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-MapRetracts where

open import SpartanMLTT
open import UF-Base
open import UF-Retracts
open import UF-Embeddings
open import UF-Equiv
open import UF-EquivalenceExamples

module _
        {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {W : 𝓦 ̇ } {Z : 𝓣 ̇ }
       where

 map-retract_of_ : (X → Y) → (W → Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 map-retract_of_ f g = Σ s ꞉ (X ◁ W) , Σ t ꞉ (Y ◁ Z) ,
  g ∘ section s ∼ section t ∘ f
  ×
  f ∘ retraction s ∼ retraction t ∘ g

 _◁₁_ : (X → Y) → (W → Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 f ◁₁ g = map-retract f of g

 infix 0 _◁₁_

 domains-retract : {f : X → Y} {g : W → Z} → f ◁₁ g → X ◁ W
 domains-retract (s , t , c , d) = s

 codomains-retract : {f : X → Y} {g : W → Z} → f ◁₁ g → Y ◁ Z
 codomains-retract (s , t , c , d) = t

 lhs-commutes : {f : X → Y} {g : W → Z} (r : f ◁₁ g)
              → g ∘ section (domains-retract r)
              ∼ section (codomains-retract r) ∘ f
 lhs-commutes (s , t , c , d) = c

 rhs-commutes : {f : X → Y} {g : W → Z} (r : f ◁₁ g)
              → f ∘ retraction (domains-retract r)
              ∼ retraction (codomains-retract r) ∘ g
 rhs-commutes (s , t , c , d) = d

\end{code}

If f is a retract of g, are the fibers of f retracts (in a suitable sense) of
the fibers of g?

As a first step, we record the following fact.

\begin{code}

 map-retract-gives-fiber-retract : {f : X → Y} {g : W → Z} → (mr : f ◁₁ g)
                                 → (y : Y)
                                 → fiber f y
                                 ◁ fiber (g ∘ section (domains-retract mr) ∘
                                          retraction (domains-retract mr))
                                         (section (codomains-retract mr) y)
 map-retract-gives-fiber-retract {f} {g} ((r , s , rs) , ((u , v , vu) , c , d)) y =
  fiber f y               ◁⟨ Σ-section-retract (u , v , vu) f y ⟩
  fiber (v ∘ f) (v y)     ◁⟨ equiv-retract-r (∼-fiber-≃ c (v y)) ⟩
  fiber (g ∘ s) (v y)     ◁⟨ Σ-reindex-retract r (s , rs) ⟩
  fiber (g ∘ s ∘ r) (v y) ◀

\end{code}

At the price of adding a coherence condition and the assumption that v (in the
diagram above) is an embedding, we can do better.

For notational purposes, we use some module parameters to record and name all of
the data of the map retract.

\begin{code}

 module _
         {f : X → Y}
         {g : W → Z}
         (s : X → W)
         (r : W → X)
         (a : (x : X) → r (s x) ≡ x)
         (v : Y → Z)
         (u : Z → Y)
         (b : (y : Y) → u (v y) ≡ y)
         (c : (x : X) → g (s x) ≡ v (f x))
         (d : (w : W) → f (r w) ≡ u (g w))
        where

  map-retract-gives-fiber-retract' : is-embedding v
                                   → ((x : X) → ap f (a x) ⁻¹ ∙ d (s x)
                                                ≡ (b (f x)) ⁻¹ ∙ ap u ((c x) ⁻¹))
                                   → (y : Y)
                                   → fiber f y
                                   ◁ fiber g (v y)
  map-retract-gives-fiber-retract' ε coh y =
   fiber f y ◁⟨ Σ-section-retract (u , v , b) f y ⟩
   fiber (v ∘ f) (v y) ◁⟨ equiv-retract-r (∼-fiber-≃ c (v y)) ⟩
   fiber (g ∘ s) (v y) ◁⟨ ρ , (σ , ρσ) ⟩
   fiber g (v y) ◀
    where
     ρ : fiber g (v y) → fiber (g ∘ s) (v y)
     ρ (w , q) = (r w) , p
      where
       p = g (s (r w)) ≡⟨ c (r w) ⟩
           v (f (r w)) ≡⟨ ap v p' ⟩
           v y         ∎
        where
         p' : f (r w) ≡ y
         p' = f (r w) ≡⟨ d w ⟩
              u (g w) ≡⟨ ap u q ⟩
              u (v y) ≡⟨ b y ⟩
              y       ∎
     σ : fiber (g ∘ s) (v y) → fiber g (v y)
     σ (x , p) = s x , p
     ρσ : (xp : fiber (g ∘ s) (v y)) → ρ (σ xp) ≡ xp
     ρσ (x , p) = to-Σ-≡ ((a x) , γ)
      where
       p' : g (s (r (s x))) ≡ v y
       p' = pr₂ (ρ (s x , p))
       γ = transport (λ - → g (s -)≡ v y) (a x) p'  ≡⟨ I ⟩
           ap (g ∘ s) (a x ⁻¹) ∙ p'                 ≡⟨ by-definition ⟩
           ap (g ∘ s) (a x ⁻¹) ∙ (c (r (s x)) ∙ p₁) ≡⟨ II ⟩
           ap (g ∘ s) (a x ⁻¹) ∙ c (r (s x)) ∙ p₁   ≡⟨ III ⟩
           c x ∙ ap (v ∘ f) (a x ⁻¹) ∙ p₁           ≡⟨ IV ⟩
           c x ∙ (ap (v ∘ f) (a x ⁻¹) ∙ p₁)         ≡⟨ ap (λ - → c x ∙ -) ℏ ⟩
           c x ∙ (c x ⁻¹ ∙ p)                       ≡⟨ V ⟩
           c x ∙ c x ⁻¹ ∙ p                         ≡⟨ VI ⟩
           refl ∙ p                                 ≡⟨ refl-left-neutral ⟩
           p                                        ∎
        where
         p₂ : f (r (s x)) ≡ y
         p₂ = d (s x) ∙ (ap u p ∙ b y)
         p₁ : v (f (r (s x))) ≡ v y
         p₁ = ap v p₂
         I   = transport-fiber (g ∘ s) (a x) p'
         II  = (∙assoc (ap (g ∘ s) (a x ⁻¹)) (c (r (s x))) p₁) ⁻¹
         III = ap (λ - → - ∙ p₁) (homotopies-are-natural (g ∘ s) (v ∘ f) c {x} {r (s x)} {a x ⁻¹}) ⁻¹
         IV  = ∙assoc (c x) (ap (v ∘ f) (a x ⁻¹)) p₁
         V   = (∙assoc (c x) (c x ⁻¹) p) ⁻¹
         VI  = ap (λ - → - ∙ p) ((right-inverse (c x)) ⁻¹)
         ℏ = ap (v ∘ f) (a x ⁻¹) ∙ p₁       ≡⟨ ap (λ - → - ∙ p₁) ((ap-ap f v (a x ⁻¹)) ⁻¹) ⟩
             ap v (ap f (a x ⁻¹)) ∙ p₁      ≡⟨ by-definition ⟩
             ap v (ap f (a x ⁻¹)) ∙ ap v p₂ ≡⟨ (ap-∙ v (ap f (a x ⁻¹)) p₂) ⁻¹ ⟩
             ap v (ap f (a x ⁻¹) ∙ p₂)      ≡⟨ ap (ap v) h ⟩
             ap v q                         ≡⟨ inverse-is-section (ap v) ε' (c x ⁻¹ ∙ p) ⟩
             c x ⁻¹ ∙ p                     ∎
          where
           ε' : is-equiv (ap v {f x} {y})
           ε' = embedding-embedding' v ε (f x) y
           q : f x ≡ y
           q = back-eqtofun ((ap v) , ε')
               ((c x ⁻¹) ∙ p)
           h : ap f (a x ⁻¹) ∙ p₂ ≡ q
           h = {!!}

\end{code}
