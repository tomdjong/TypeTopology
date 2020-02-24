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
open import UF-Subsingletons

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
 map-retract-gives-fiber-retract {f} {g}
  ((r , s , rs) , ((u , v , vu) , c , d)) y =
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
                                   → ((x : X) → ap f (a x ⁻¹) ∙ d (s x)
                                                ≡ b (f x) ⁻¹ ∙ ap u (c x ⁻¹))
                                   → (y : Y)
                                   → fiber f y
                                   ◁ fiber g (v y)
  map-retract-gives-fiber-retract' ε coh y =
   fiber f y           ◁⟨ Σ-section-retract (u , v , b) f y ⟩
   fiber (v ∘ f) (v y) ◁⟨ equiv-retract-r (∼-fiber-≃ c (v y)) ⟩
   fiber (g ∘ s) (v y) ◁⟨ ρ , (σ , ρσ) ⟩
   fiber g (v y)       ◀
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
         III = ap (λ - → - ∙ p₁) (homotopies-are-natural (g ∘ s) (v ∘ f) c
                {x} {r (s x)} {a x ⁻¹}) ⁻¹
         IV  = ∙assoc (c x) (ap (v ∘ f) (a x ⁻¹)) p₁
         V   = (∙assoc (c x) (c x ⁻¹) p) ⁻¹
         VI  = ap (λ - → - ∙ p) ((right-inverse (c x)) ⁻¹)
         ℏ = ap (v ∘ f) (a x ⁻¹) ∙ p₁       ≡⟨ I' ⟩
             ap v (ap f (a x ⁻¹)) ∙ p₁      ≡⟨ by-definition ⟩
             ap v (ap f (a x ⁻¹)) ∙ ap v p₂ ≡⟨ (ap-∙ v (ap f (a x ⁻¹)) p₂) ⁻¹ ⟩
             ap v (ap f (a x ⁻¹) ∙ p₂)      ≡⟨ ap (ap v) h ⟩
             ap v q                         ≡⟨ II' ⟩
             c x ⁻¹ ∙ p                     ∎
          where
           ε' : is-equiv (ap v {f x} {y})
           ε' = embedding-embedding' v ε (f x) y
           q : f x ≡ y
           q = back-eqtofun ((ap v) , ε')
               ((c x ⁻¹) ∙ p)
           I'  = ap (λ - → - ∙ p₁) ((ap-ap f v (a x ⁻¹)) ⁻¹)
           II' = inverse-is-section (ap v) ε' (c x ⁻¹ ∙ p)
           h = ap f (a x ⁻¹) ∙ p₂                            ≡⟨ by-definition ⟩
               ap f (a x ⁻¹) ∙ (d (s x) ∙ (ap u p ∙ b y))    ≡⟨ I₂ ⟩
               ap f (a x ⁻¹) ∙ d (s x) ∙ (ap u p ∙ b y)      ≡⟨ II₂ ⟩
               b (f x) ⁻¹ ∙ ap u (c x ⁻¹) ∙ (ap u p ∙ b y)   ≡⟨ III₂ ⟩
               b (f x) ⁻¹ ∙ (ap u (c x ⁻¹) ∙ (ap u p ∙ b y)) ≡⟨ IV₂ ⟩
               b (f x) ⁻¹ ∙ (ap u (c x ⁻¹) ∙ ap u p ∙ b y)   ≡⟨ V₂ ⟩
               b (f x) ⁻¹ ∙ (ap u (c x ⁻¹ ∙ p) ∙ b y)        ≡⟨ VI₂ ⟩
               b (f x) ⁻¹ ∙ ap u (c x ⁻¹ ∙ p) ∙ b y          ≡⟨ VII₂ ⟩
               b (f x) ⁻¹ ∙ ap u (ap v q) ∙ b y              ≡⟨ VIII₂ ⟩
               b (f x) ⁻¹ ∙ ap (u ∘ v) q ∙ b y               ≡⟨ IX₂ ⟩
               ap id q                                       ≡⟨ X₂ ⟩
               q                                             ∎
            where
             I₂    = (∙assoc (ap f (a x ⁻¹)) (d (s x)) (ap u p ∙ b y)) ⁻¹
             II₂   = ap (λ - → - ∙ (ap u p ∙ b y)) (coh x)
             III₂  = ∙assoc (b (f x) ⁻¹) (ap u (c x ⁻¹)) (ap u p ∙ b y)
             IV₂   = ap (λ - → b (f x) ⁻¹ ∙ -)
                     ((∙assoc (ap u (c x ⁻¹)) (ap u p) (b y)) ⁻¹)
             V₂    = ap (λ - → b (f x) ⁻¹ ∙ (- ∙ b y)) ((ap-∙ u (c x ⁻¹) p) ⁻¹)
             VI₂   = (∙assoc (b (f x) ⁻¹) (ap u (c x ⁻¹ ∙ p)) (b y)) ⁻¹
             VII₂  = ap (λ - → b (f x) ⁻¹ ∙ ap u - ∙ b y) (II' ⁻¹)
             VIII₂ = ap (λ - → b (f x) ⁻¹ ∙ - ∙ b y) (ap-ap v u q)
             IX₂   = homotopies-are-natural'' (u ∘ v) id b {f x} {y} {q}
             X₂    = (ap-id-is-id q) ⁻¹

\end{code}

We can get the desired retract without the embedding assumption, see Lemma 4.7.3
of the HoTT book.

It is noteworthy to mention that the coherence law above (which I
"rediscovered") is part of the definition of a retract in Definition 4.7.2 of
the HoTT book.

We use the same naming as there.

A --s--> X --r--> A # composition is id
|        |        |
g        f        g
|        |        |
∨        ∨        ∨
B --s'-> Y --r'-> B # composition is id

\begin{code}

module _
        {A : 𝓤 ̇ } {B : 𝓥 ̇ } {X : 𝓤' ̇ } {Y : 𝓥' ̇ }
        {f : X → Y}
        {g : A → B}
        (s : A → X)
        (r : X → A)
        (s' : B → Y)
        (r' : Y → B)
        (R : (a : A) → r (s a) ≡ a)
        (R' : (b : B) → r' (s' b) ≡ b)
        (L : (a : A) → f (s a) ≡ s' (g a))
        (K : (x : X) → g (r x) ≡ r' (f x))
        (H : (a : A) → K (s a) ∙ ap r' (L a) ≡ ap g (R a) ∙ R' (g a) ⁻¹)
       where

 map-retract-gives-fiber-retract'' : (b : B) → fiber g b ◁ fiber f (s' b)
 map-retract-gives-fiber-retract'' b = ρ , σ , ρσ
  where
   σ : fiber g b → fiber f (s' b)
   σ (a , p)  = (s a) , (f (s a)  ≡⟨ L a ⟩
                        s' (g a) ≡⟨ ap s' p ⟩
                        s' b     ∎)
   ρ : fiber f (s' b) → fiber g b
   ρ (x , q) = (r x) , (g (r x)   ≡⟨ K x ⟩
                        r' (f x)  ≡⟨ ap r' q ⟩
                        r' (s' b) ≡⟨ R' b ⟩
                        b         ∎)
   ρσ : (w : fiber g b) → ρ (σ w) ≡ w
   ρσ (a , refl) = to-Σ-≡ (R a , γ)
    where
     γ = transport (λ - → g - ≡ g a) (R a) p                     ≡⟨ i ⟩
         ap g (R a ⁻¹) ∙ p                                       ≡⟨ ii ⟩
         ap g (R a ⁻¹) ∙ (K (s a) ∙ (ap r' (L a) ∙ R' b))        ≡⟨ iii ⟩
         ap g (R a ⁻¹) ∙ (K (s a) ∙ ap r' (L a) ∙ R' b)          ≡⟨ iv ⟩
         ap g (R a ⁻¹) ∙ (ap g (R a) ∙ R' (g a) ⁻¹ ∙ R' (g a))   ≡⟨ v ⟩
         ap g (R a ⁻¹) ∙ (ap g (R a) ∙ (R' (g a) ⁻¹ ∙ R' (g a))) ≡⟨ vi ⟩
         ap g (R a ⁻¹) ∙ ap g (R a)                              ≡⟨ vii ⟩
         ap g (R a) ⁻¹ ∙ ap g (R a)                              ≡⟨ viii ⟩
         refl                                                    ∎
      where
       p : g (r (s a)) ≡ g a
       p = K (s a) ∙ (ap r' (L a ∙ ap s' refl) ∙ R' b)
       i    = transport-fiber g (R a) p
       ii   = by-definition
       iii  = ap (λ - → ap g (R a ⁻¹) ∙ -)
             ((∙assoc (K (s a)) (ap r' (L a)) (R' b)) ⁻¹)
       iv   = ap (λ - → ap g (R a ⁻¹) ∙ (- ∙ R' b)) (H a)
       v    = ap (λ - → ap g (R a ⁻¹) ∙ -)
             (∙assoc (ap g (R a)) (R' (g a) ⁻¹) (R' (g a)))
       vi   = ap (λ - → ap g (R a ⁻¹) ∙ (ap g (R a) ∙ -))
              (left-inverse (R' (g a)))
       vii  = ap (λ - → - ∙ ap g (R a)) ((ap-sym g (R a)) ⁻¹)
       viii = left-inverse (ap g (R a))

\end{code}

Moreover, if s and s' are embeddings, then so is σ.

\begin{code}

 fiber-retract-section-is-embedding : is-embedding s
                                    → is-embedding s'
                                    → (b : B)
                                    → is-embedding (section
                                       (map-retract-gives-fiber-retract'' b))
 fiber-retract-section-is-embedding ε ε' b = embedding-criterion' σ γ
  where
   σ : fiber g b → fiber f (s' b)
   σ = section (map-retract-gives-fiber-retract'' b)
   σ₂ : (a : A) (p : g a ≡ b) → f (s a) ≡ s' b
   σ₂ a p = L a ∙ ap s' p
   γ : (u v : fiber g b) → (σ u ≡ σ v) ≃ (u ≡ v)
   γ (a , p) (a' , p') =
    (σ (a , p) ≡ σ (a' , p'))                                ≃⟨ Σ-≡-≃ ⟩
    (Σ q ꞉ s a ≡ s a' , transport T q (σ₂ a p) ≡ (σ₂ a' p')) ≃⟨ i ⟩
    (Σ q ꞉ s a ≡ s a' , ap f (q ⁻¹) ∙ σ₂ a p ≡ σ₂ a' p')     ≃⟨ ii ⟩
    (Σ q ꞉ a ≡ a' , ap f (ap s q ⁻¹) ∙ σ₂ a p ≡ σ₂ a' p')    ≃⟨ iii ⟩
    (Σ q ꞉ a ≡ a' , ap s' (ap g (q ⁻¹) ∙ p) ≡ ap s' p')      ≃⟨ iv ⟩
    (Σ q ꞉ a ≡ a' , ap g (q ⁻¹) ∙ p ≡ p')                    ≃⟨ v ⟩
    (Σ q ꞉ a ≡ a' , transport (λ - → g - ≡ b) q p ≡ p')      ≃⟨ ≃-sym Σ-≡-≃ ⟩
    (a , p ≡ a' , p')                                        ■
     where
      T : X → 𝓥' ̇
      T x = f x ≡ s' b
      i   = Σ-cong (λ q → idtoeq _ _
            (ap (λ - → - ≡ σ₂ a' p') (transport-fiber f q (σ₂ a p))))
      ii  = ≃-sym (Σ-change-of-variables (λ q → ap f (q ⁻¹) ∙ σ₂ a p ≡ σ₂ a' p')
            (ap s) (embedding-embedding' s ε a a'))
      iv  = Σ-cong (λ q → ≃-sym ((ap (ap s')) , embedding-embedding' (ap s')
            (equivs-are-embeddings (ap s') (embedding-embedding' s' ε' (g a') b))
            (ap g (q ⁻¹) ∙ p) p'))
      v   = Σ-cong (λ q → idtoeq _ _ (ap (λ - → - ≡ p')
            (transport-fiber g q p) ⁻¹))
      iii = Σ-cong (λ q → idtoeq _ _ (h q))
       where
        h : (q : a ≡ a')
          → (ap f (ap s q ⁻¹) ∙ σ₂ a p ≡ σ₂ a' p')
          ≡ (ap s' (ap g (q ⁻¹) ∙ p) ≡ ap s' p')
        h refl = (ap f (ap s refl ⁻¹) ∙ σ₂ a p ≡ σ₂ a' p') ≡⟨ refl ⟩
                 (refl ∙ σ₂ a p ≡ σ₂ a' p')                ≡⟨ i' ⟩
                 (σ₂ a p ≡ σ₂ a p')                        ≡⟨ by-definition ⟩
                 (L a ∙ ap s' p ≡ L a ∙ ap s' p')          ≡⟨ cancel-left-≡ ⟩
                 (ap s' p ≡ ap s' p')                      ≡⟨ ii' ⟩
                 (ap s' (refl ∙ p) ≡ ap s' p')             ≡⟨ refl ⟩
                 (ap s' (ap g (refl ⁻¹) ∙ p) ≡ ap s' p')   ∎
         where
          i'  = ap (λ - → - ≡ σ₂ a' p') refl-left-neutral
          ii' = ap (λ - → ap s' - ≡ ap s' p')
                (refl-left-neutral {𝓥} {B} {g a} {b} {p}) ⁻¹

\end{code}
