\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module PropUniv where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Equiv

-- open import UF-EquivalenceExamples
-- open import UF-Equiv-FunExt
-- open import UF-Yoneda
-- open import UF-Retracts

vvfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
vvfunext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
             → ((x : X) → is-singleton (A x))
             → is-singleton (Π A)

propositional-univalence : (𝓤 : Universe) → 𝓤 ⁺ ̇
propositional-univalence 𝓤 = (P : 𝓤 ̇ ) → is-prop P
                           → (X : 𝓤 ̇ ) → is-equiv (idtoeq P X)

prop-eqtoid : propositional-univalence 𝓤 → (P : 𝓤 ̇ ) → is-prop P → (Y : 𝓤 ̇ )
            → P ≃ Y → P ≡ Y
prop-eqtoid pu P i Y = pr₁ (pr₁ (pu P i Y))

prop-idtoeq-eqtoid : (pu : propositional-univalence 𝓤)
                   → (P : 𝓤 ̇ ) (i : is-prop P) (Y : 𝓤 ̇ )
                   → (e : P ≃ Y) → idtoeq P Y (prop-eqtoid pu P i Y e) ≡ e
prop-idtoeq-eqtoid pu P i Y = pr₂ (pr₁ (pu P i Y))

propositional-≃-induction : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-≃-induction 𝓤 𝓥 = (P : 𝓤 ̇ ) → is-prop P
                              → (A : (Y : 𝓤 ̇ ) → P ≃ Y → 𝓥 ̇ )
                              → A P (≃-refl P) → (Y : 𝓤 ̇ ) (e : P ≃ Y) → A Y e

propositional-JEq : propositional-univalence 𝓤
                  → (𝓥 : Universe)
                  → propositional-≃-induction 𝓤 𝓥
propositional-JEq {𝓤} pu 𝓥 P i A b Y e = transport (A Y) (prop-idtoeq-eqtoid pu P i Y e) g
 where
  A' : (Y : 𝓤 ̇ ) → P ≡ Y → 𝓥 ̇
  A' Y q = A Y (idtoeq P Y q)
  b' : A' P refl
  b' = b
  f' : (Y : 𝓤 ̇ ) (q : P ≡ Y) → A' Y q
  f' = Jbased P A' b'
  g : A Y (idtoeq P Y (prop-eqtoid pu P i Y e))
  g = f' Y (prop-eqtoid pu P i Y e)

prop-precomp-is-equiv : propositional-univalence 𝓤
                      → (X Y Z : 𝓤 ̇ )
                      → is-prop X
                      → (f : X → Y)
                      → is-equiv f
                      → is-equiv (λ (g : Y → Z) → g ∘ f)
prop-precomp-is-equiv {𝓤} pu X Y Z i f ise =
 propositional-JEq pu 𝓤 X i (λ W e → is-equiv (λ g → g ∘ ⌜ e ⌝))
   (id-is-an-equiv (X → Z)) Y (f , ise)

prop-precomp-is-equiv' : propositional-univalence 𝓤
                       → (X Y Z : 𝓤 ̇ )
                       → is-prop Y
                       → (f : X → Y)
                       → is-equiv f
                       → is-equiv (λ (g : Y → Z) → g ∘ f)
prop-precomp-is-equiv' {𝓤} pu X Y Z i f ise =
 prop-precomp-is-equiv pu X Y Z j f ise
  where
   j : is-prop X
   j = equiv-to-prop (f , ise) i

lemma₁ : propositional-univalence 𝓤
       → (X : 𝓥 ̇ ) (Y : 𝓤 ̇ )
       → is-prop Y
       → is-prop (X → Y)
lemma₁ {𝓤} {𝓥} pu X Y i f₀ f₁ = γ
 where
  Δ : 𝓤 ̇
  Δ = Σ y₀ ꞉ Y , Σ y₁ ꞉ Y , y₀ ≡ y₁
  δ : Y → Δ
  δ y = (y , y , refl)
  π₀ π₁ : Δ → Y
  π₀ (y₀ , y₁ , p) = y₀
  π₁ (y₀ , y₁ , p) = y₁
  δ-is-equiv : is-equiv δ
  δ-is-equiv = (π₀ , η) , (π₀ , ε)
   where
    η : (d : Δ) → δ (π₀ d) ≡ d
    η (y₀ , y₁ , refl) = refl
    ε : (y : Y) → π₀ (δ y) ≡ y
    ε y = refl
  πδ : π₀ ∘ δ ≡ π₁ ∘ δ
  πδ = refl
  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ
  φ-is-equiv : is-equiv φ
  φ-is-equiv = prop-precomp-is-equiv pu Y Δ Y i δ δ-is-equiv
  π₀-equals-π₁ : π₀ ≡ π₁
  π₀-equals-π₁ = equivs-are-lc φ φ-is-equiv πδ
  γ : f₀ ≡ f₁
  γ = f₀                              ≡⟨ refl ⟩
      (λ x → f₀ x)                    ≡⟨ refl ⟩
      (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁ ⟩
      (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl ⟩
      (λ x → f₁ x)                    ≡⟨ refl ⟩
      f₁                              ∎
   where
    h : (x : X) → f₀ x ≡ f₁ x
    h x = i (f₀ x) (f₁ x)

prop-funext : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
prop-funext 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → is-prop Y → (f g : X → Y)
                → ((x : X) → f x ≡ g x) → f ≡ g

pua-to-prop-funext : {𝓤 𝓥 : Universe}
                   → propositional-univalence 𝓤
                   → prop-funext 𝓥 𝓤
pua-to-prop-funext {𝓤} {𝓥} pu X Y i f g _ = lemma₁ pu X Y i f g

prop-postcomp-invertible : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                         → prop-funext 𝓦 𝓤
                         → prop-funext 𝓦 𝓥
                         → is-prop X
                         → is-prop Y
                         → (f : X → Y)
                         → qinv f
                         → qinv (λ (h : A → X) → f ∘ h)
prop-postcomp-invertible {𝓤} {𝓥} {𝓦} {X} {Y} {A} pfe pfe' i j f (g , η , ε) = γ
 where
  f' : (A → X) → (A → Y)
  f' h = f ∘ h
  g' : (A → Y) → (A → X)
  g' k = g ∘ k
  η' : (h : A → X) → g' (f' h) ≡ h
  η' h = pfe A X i (g' (f' h)) h t -- nfe (η ∘ h)
   where
    t : (x : A) → g (f (h x)) ≡ h x
    t = η ∘ h
  ε' : (k : A → Y) → f' (g' k) ≡ k
  ε' k = pfe' A Y j (f' (g' k)) k (ε ∘ k) -- nfe' (ε ∘ k)
  γ : qinv f'
  γ = (g' , η' , ε')

prop-postcomp-equiv : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                    → prop-funext 𝓦 𝓤 → prop-funext 𝓦 𝓥
                    → (f : X → Y)
                    → is-prop X → is-prop Y
                    → is-equiv f
                    → is-equiv (λ (h : A → X) → f ∘ h)
prop-postcomp-equiv pfe pfe' f i j e =
 qinvs-are-equivs (λ h → f ∘ h)
  (prop-postcomp-invertible pfe pfe' i j f (equivs-are-qinvs f e))

vvfunext' : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
vvfunext' 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
              → ((x : X) → is-prop (A x))
              → is-prop (Π A)


open import UF-PropTrunc
open import UF-Retracts

module _
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 ∥∥-comp : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
 ∥∥-comp 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) (i : is-prop Y) (f : X → Y)
             → (x : X) → ∥∥-rec i f ∣ x ∣ ≡ f x

 ∥∥-comp-gives-vvfunext : ∥∥-comp {!!} {!!}
                         → vvfunext' 𝓤 𝓥
 ∥∥-comp-gives-vvfunext {𝓤} {𝓥} c {X} {A} ν = retract-of-prop (r , s , η) i
  where
   s : Π A → ∥ Π A ∥
   s = ∣_∣
   r : ∥ Π A ∥ → Π A
   r f' x = ∥∥-rec (ν x) (λ g → g x) f'
   η : (φ : Π A) → r (s φ) ≡ φ
   η φ = {!c!}
   i : is-prop ∥ Π A ∥
   i = ∥∥-is-a-prop

{-
lemma₂ : propositional-univalence 𝓤
       → (X : 𝓤 ̇ )
       → (A : X → 𝓥 ̇ )
       → ((x : X) → is-prop (A x))
       → is-prop (Π A)
lemma₂ {𝓤} {𝓥} pu X A i f₀ f₁ = γ
 where
  Δ : X → 𝓥 ̇
  Δ x = Σ a₀ ꞉ A x , Σ a₁ ꞉ A x , a₀ ≡ a₁
  δ : (Π A) → Π Δ
  δ g x = (g x , g x , refl)
  π₀ π₁ : (Π Δ) → Π A
  π₀ g x = pr₁ (g x)
  π₁ g x = pr₁ (pr₂ (g x))
  δ-is-equiv : is-equiv δ
  δ-is-equiv = (π₀ , η) , (π₀ , ε)
   where
    η : (d : Π Δ) → δ (π₀ d) ≡ d
    η g = {!!}
    ε : (g : Π A) → π₀ (δ g) ≡ g
    ε g = {!!}

{-
  πδ : π₀ ∘ δ ≡ π₁ ∘ δ
  πδ = refl
  φ : (Δ → Y) → (Y → Y)
  φ π = π ∘ δ
  φ-is-equiv : is-equiv φ
  φ-is-equiv = prop-precomp-is-equiv pu Y Δ Y i δ δ-is-equiv
  π₀-equals-π₁ : π₀ ≡ π₁
  π₀-equals-π₁ = equivs-are-lc φ φ-is-equiv πδ
-}
  γ : f₀ ≡ f₁
  γ = f₀                              ≡⟨ refl ⟩
      (λ x → f₀ x)                    ≡⟨ refl ⟩
      {!!} ≡⟨ {!!} ⟩
      {!!} ≡⟨ {!!} ⟩
--      (λ x → π₀ (f₀ x , f₁ x , h x))  ≡⟨ ap (λ π x → π (f₀ x , f₁ x , h x)) π₀-equals-π₁ ⟩
--      (λ x → π₁ (f₀ x , f₁ x , h x))  ≡⟨ refl ⟩
      (λ x → f₁ x)                    ≡⟨ refl ⟩
      f₁                              ∎
   where
    h : (x : X) → f₀ x ≡ f₁ x
    h x = i x (f₀ x) (f₁ x)
-}


\end{code}
