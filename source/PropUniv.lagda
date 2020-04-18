\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module PropUniv where

open import SpartanMLTT
open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Equiv
open import UF-Retracts

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

vvfunext-unprime : vvfunext' 𝓤 𝓥 → vvfunext 𝓤 𝓥
vvfunext-unprime vfe' ν =
 pointed-props-are-singletons
   (λ x → singleton-types-are-pointed (ν x))
   (vfe' (λ x → singletons-are-props (ν x)))

-- We use Voevodsky's construction as a way to "have" a prop. trunc. with a
-- judgemental computation rule

∥_∥ᵥ : {𝓤 𝓥 : Universe} → 𝓤 ̇ → 𝓥 ⁺ ⊔ 𝓤 ̇
∥_∥ᵥ {𝓤} {𝓥} X = (P : 𝓥 ̇ ) → is-prop P → (X → P) → P

∥∥ᵥ-rec : {X : 𝓤 ̇ } {P : 𝓥 ̇ } → is-prop P → (X → P) → ∥ X ∥ᵥ → P
∥∥ᵥ-rec {𝓤} {𝓥} {X} {P} i f t = t P i f

∣_∣ᵥ : {𝓥 : Universe} {X : 𝓤 ̇ } → X → ∥_∥ᵥ {𝓤} {𝓥} X
∣_∣ᵥ x P _ f = f x

∥∥ᵥ-comp : {X : 𝓤 ̇ } {P : 𝓥 ̇ } (i : is-prop P) (f : X → P) (x : X)
         → ∥∥ᵥ-rec i f ∣ x ∣ᵥ ≡ f x
∥∥ᵥ-comp i f x = refl

prop-trunc-implies-funext : (𝓤 𝓥 : Universe)
                          → ((Y : (𝓤 ⊔ 𝓥) ̇ ) → is-prop (∥_∥ᵥ {𝓤 ⊔ 𝓥} {𝓥} Y))
                          → vvfunext' 𝓤 𝓥
prop-trunc-implies-funext 𝓤 𝓥 pt {X} {A} ν =
 retract-of-prop (r , s , ρ) (pt (Π A))
  where
   r : ∥ Π A ∥ᵥ → Π A
   r g x = ∥∥ᵥ-rec (ν x) (λ f → f x) g
   s : Π A → ∥ Π A ∥ᵥ
   s = ∣_∣ᵥ
   ρ : (f : Π A) → r (s f) ≡ f
   ρ f = refl

\end{code}

\begin{code}

lemma₂ : propositional-univalence (𝓤 ⊔ 𝓥)
       → propositional-univalence 𝓥
       → (X : 𝓥 ̇ ) (A : X → 𝓤 ̇ )
       → is-prop X                        -- We would like to get rid of this
       → ((x : X) → is-prop (A x))
       → is-prop (Π A)
lemma₂ pu pu' X A i ν = retract-of-prop (r , s , ρ) j
 where
  r : (Σ h ꞉ (X → Σ A) , pr₁ ∘ h ≡ id) → Π A
  r (h , p) x = transport A (happly p x) (pr₂ (h x))
  s : Π A → (Σ h ꞉ (X → Σ A) , pr₁ ∘ h ≡ id)
  s φ = (λ x → x , φ x) , refl
  ρ : (φ : Π A) → r (s φ) ≡ φ
  ρ φ = refl
  j : is-prop (Σ h ꞉ (X → Σ A) , pr₁ ∘ h ≡ id)
  j = Σ-is-prop (lemma₁ pu X (Σ A) (Σ-is-prop i ν))
      (λ h → props-are-sets (lemma₁ pu' X X i))

prop-dfunext : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
prop-dfunext 𝓤 𝓥 = (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ )
                 → is-prop X
                 → ((x : X) → is-prop (Y x))
                 → (f g : Π Y)
                 → ((x : X) → f x ≡ g x) → f ≡ g

pua-to-prop-dfunext : propositional-univalence (𝓤 ⊔ 𝓥)
                    → propositional-univalence 𝓤
                    → prop-dfunext 𝓤 𝓥
pua-to-prop-dfunext pu pu' X Y i j f g _ = lemma₂ pu pu' X Y i j f g

open import UF-Equiv

being-a-prop-is-a-prop' : {X : 𝓤 ̇ } → prop-dfunext 𝓤 𝓤 → is-prop (is-prop X)
being-a-prop-is-a-prop' {𝓤} {X} fe f g = c₁
 where
  l : is-set X
  l = props-are-sets f
  c : (x y : X) → f x y ≡ g x y
  c x y = l (f x y) (g x y)
  c₀ : (x : X) → f x ≡ g x
  c₀ x = {!!} -- dfunext fe (c x)
  c₁ : f ≡ g
  c₁  = {!!} -- dfunext fe c₀


identifications-of-props-are-props' : propext 𝓤 → prop-dfunext 𝓤 𝓤
                                    → (P : 𝓤 ̇ ) → is-prop P
                                    → (X : 𝓤 ̇ ) → is-prop (X ≡ P)
identifications-of-props-are-props' {𝓤} pe fe P i = local-hedberg' P (λ X → g X ∘ f X , k X)
 where
  f : (X : 𝓤 ̇ ) → X ≡ P → is-prop X × (X ⇔ P)
  f X refl = i , (id , id)
  g : (X : 𝓤 ̇ ) → is-prop X × (X ⇔ P) → X ≡ P
  g X (l , φ , γ) = pe l i φ γ
  j : (X : 𝓤 ̇ ) → is-prop (is-prop X × (X ⇔ P))
  j X = ×-prop-criterion ((λ _ → being-a-prop-is-a-prop' fe) ,
                          (λ l → ×-is-prop (fe P {!!} {!!} {!!} {!!}))
                                            {!!})
  k : (X : 𝓤 ̇ ) → wconstant (g X ∘ f X)
  k X p q = ap (g X) (j X (f X p) (f X q))

prop-dfunext-to-pua : prop-dfunext 𝓤 𝓤 → propext 𝓤 → propositional-univalence 𝓤
prop-dfunext-to-pua pdfe pe P i X =
 qinvs-are-equivs (idtoeq P X) (ι , a , b)
  where
   ι : P ≃ X → P ≡ X
   ι e = pe i (equiv-to-prop (≃-sym e) i) ⌜ e ⌝ ⌜ ≃-sym e ⌝
   a : (u : P ≡ X) → ι (idtoeq P X u) ≡ u
   a u = {!!}
   b : (e : P ≃ X) → idtoeq P X (ι e) ≡ e
   b e = Σ-is-prop ϕ ψ (idtoeq P X (ι e)) e
    where
     j : is-prop X
     j = equiv-to-prop (≃-sym e) i
     ϕ : is-prop (P → X)
     ϕ f g = pdfe P (λ _ → X) i (λ p → j) f g (λ p → j (f p) (g p))
     ψ : (f : P → X) → is-prop (is-equiv f)
     ψ f = ×-is-prop {!!} {!!}
--          (λ f g → pdfe P (λ _ → X) i (λ _ → j) f g (λ p → equiv-to-prop (≃-sym e) i (f p) (g p)))
--         {!λ!} (idtoeq P X (ι e)) e


\end{code}
