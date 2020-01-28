Tom de Jong
27-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module FreeSemiLattice where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Subsingletons-FunExt

𝓟 : (𝓣 : Universe) → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
𝓟 𝓣 X = X → Ω 𝓣

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 𝓣 X → 𝓣 ̇
x ∈ A = A x holds

∈-is-a-prop : {X : 𝓤 ̇ } (A : 𝓟 𝓣 X) (x : X)
            → is-prop (x ∈ A)
∈-is-a-prop A x = holds-is-prop (A x)

𝕋 : {X : 𝓤 ̇ } → 𝓟 𝓣 X → 𝓣 ⊔ 𝓤 ̇
𝕋 {𝓤} {𝓣} {X} A = Σ \(x : X) → x ∈ A

_⊆_ : {X : 𝓤 ̇ } → 𝓟 𝓣 X → 𝓟 𝓣 X → 𝓤 ⊔ 𝓣 ̇
_⊆_ {𝓤} {𝓣} {X} A B = (x : X) → x ∈ A → x ∈ B

⊆-is-a-prop : {X : 𝓤 ̇ }
            → funext 𝓤 𝓣 → funext 𝓣 𝓣
            → (A B : 𝓟 𝓣 X)
            → is-prop (A ⊆ B)
⊆-is-a-prop fe fe' A B = Π-is-prop fe
                         (λ x → Π-is-prop fe'
                         (λ _ → ∈-is-a-prop B x))

⊆-reflexivity : {X : 𝓤 ̇ } {A : 𝓟 𝓣 X} → A ⊆ A
⊆-reflexivity x = id

⊆-transitivity : {X : 𝓤 ̇ } {A B C : 𝓟 𝓣 X}
               → A ⊆ B → B ⊆ C → A ⊆ C
⊆-transitivity i j x a = j x (i x a)

⊆-antisymmetry : propext 𝓣 → funext 𝓤 (𝓣 ⁺) → funext 𝓣 𝓣
               → {X : 𝓤 ̇ } {A B : 𝓟 𝓣 X}
               → A ⊆ B → B ⊆ A → A ≡ B
⊆-antisymmetry {𝓤} {𝓣} pe fe fe' {X} {A} {B} i j = dfunext fe γ
 where
  γ : (x : X) → A x ≡ B x
  γ x = to-subtype-≡ (λ _ → being-a-prop-is-a-prop fe') ϕ
   where
    ϕ : x ∈ A ≡ x ∈ B
    ϕ = pe (∈-is-a-prop A x) (∈-is-a-prop B x) (i x) (j x)

𝕤 : {X : 𝓤 ̇ } → is-set X → X → 𝓟 𝓤 X
𝕤 i x = λ y → ((x ≡ y) , i)

open import UF-PropTrunc

module KuratowskiFinite
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt
 open import UF-ImageAndSurjection
 open ImageAndSurjection pt

 open import UF-Equiv

 open import Fin
 open import ArithmeticViaEquivalence

 is-Kuratowski-finite : 𝓤 ̇ → 𝓤 ̇
 is-Kuratowski-finite X = ∃ \(n : ℕ) → Σ \(e : Fin n → X) → is-surjection e

 being-Kuratowski-finite-is-a-prop : {X : 𝓤 ̇ }
                                   → is-prop (is-Kuratowski-finite X)
 being-Kuratowski-finite-is-a-prop = ∥∥-is-a-prop

 𝓚 : (𝓣 : Universe) → 𝓤 ̇ → 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓚 𝓣 X = Σ \(A : 𝓟 𝓣 X) → is-Kuratowski-finite (𝕋 A)

 ⟨_⟩ : {X : 𝓤 ̇ } → 𝓚 𝓣 X → 𝓟 𝓣 X
 ⟨_⟩ = pr₁

 κ : {X : 𝓤 ̇ } → (A : 𝓚 𝓣 X) → is-Kuratowski-finite (𝕋 ⟨ A ⟩)
 κ = pr₂

 _∈ₖ_ : {X : 𝓤 ̇ } → X → 𝓚 𝓣 X → 𝓣 ̇
 x ∈ₖ A = x ∈ ⟨ A ⟩

 ∈ₖ-is-a-prop : {X : 𝓤 ̇ } (A : 𝓚 𝓣 X) (x : X)
            → is-prop (x ∈ₖ A)
 ∈ₖ-is-a-prop A x = ∈-is-a-prop ⟨ A ⟩ x

 _⊆ₖ_ : {X : 𝓤 ̇ } → 𝓚 𝓣 X → 𝓚 𝓣 X → 𝓤 ⊔ 𝓣 ̇
 A ⊆ₖ B = ⟨ A ⟩ ⊆ ⟨ B ⟩

 ⊆ₖ-is-a-prop : {X : 𝓤 ̇ }
              → funext 𝓤 𝓣 → funext 𝓣 𝓣
              → (A B : 𝓚 𝓣 X)
              → is-prop (A ⊆ₖ B)
 ⊆ₖ-is-a-prop fe fe' A B = ⊆-is-a-prop fe fe' ⟨ A ⟩ ⟨ B ⟩

 ⊆ₖ-reflexivity : {X : 𝓤 ̇ } {A : 𝓚 𝓣 X} → A ⊆ₖ A
 ⊆ₖ-reflexivity {𝓤} {𝓣} {X} {A} = ⊆-reflexivity {𝓤} {𝓣} {X} {⟨ A ⟩}

 ⊆ₖ-transitivity : {X : 𝓤 ̇ } {A B C : 𝓚 𝓣 X}
                 → A ⊆ₖ B → B ⊆ₖ C → A ⊆ₖ C
 ⊆ₖ-transitivity {𝓤} {𝓣} {X} {A} {B} {C} =
  ⊆-transitivity {𝓤 } {𝓣} {X} {⟨ A ⟩} {⟨ B ⟩} {⟨ C ⟩}

 ⊆ₖ-antisymmetry : propext 𝓣 → funext 𝓤 (𝓣 ⁺) → funext 𝓣 𝓣
                 → {X : 𝓤 ̇ } {A B : 𝓚 𝓣 X}
                 → A ⊆ₖ B → B ⊆ₖ A → A ≡ B
 ⊆ₖ-antisymmetry {𝓤} {𝓣} pe fe fe' {X} {A} {B} i j = to-subtype-≡ ϕ ψ
  where
   ϕ : (A : 𝓟 𝓤 X) → is-prop (is-Kuratowski-finite (𝕋 A))
   ϕ _ = being-Kuratowski-finite-is-a-prop
   ψ : ⟨ A ⟩ ≡ ⟨ B ⟩
   ψ = ⊆-antisymmetry pe fe fe' i j

 𝕤ₖ : {X : 𝓤 ̇ } → is-set X → X → 𝓚 𝓤 X
 𝕤ₖ i x = 𝕤 i x , ∣ 1 , e , s ∣
  where
   e : Fin 1 → 𝕋 (𝕤 i x)
   e 𝟎 = x , refl
   s : is-surjection e
   s (x , refl) = ∣ inr * , refl ∣

 _∪_ : {X : 𝓤 ̇ } → 𝓟 𝓣 X → 𝓟 𝓣 X → 𝓟 𝓣 X
 A ∪ B = λ x → (x ∈ A ∨ x ∈ B) , ∥∥-is-a-prop

 _∪ₖ_ : {X : 𝓤 ̇ } → 𝓚 𝓣 X → 𝓚 𝓣 X → 𝓚 𝓣 X
 A ∪ₖ B = (⟨ A ⟩ ∪ ⟨ B ⟩) , γ
  where
   γ : is-Kuratowski-finite (𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩))
   γ = ∥∥-rec being-Kuratowski-finite-is-a-prop ϕ (κ A)
    where
     ϕ : (Σ \(n : ℕ) → Σ \(e : Fin n → 𝕋 ⟨ A ⟩) → is-surjection e)
       → is-Kuratowski-finite (𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩))
     ϕ (n , f , s) = ∥∥-rec being-Kuratowski-finite-is-a-prop ψ (κ B)
      where
       ψ : (Σ \(n : ℕ) → Σ \(e : Fin n → 𝕋 ⟨ B ⟩) → is-surjection e)
         → is-Kuratowski-finite (𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩))
       ψ (m , g , t) = ∣ n +' m , [f,g] , u ∣
        where
         h : Fin n + Fin m → 𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩)
         h (inl k) = pr₁ (f k) , ∣ inl (pr₂ (f k)) ∣
         h (inr k) = pr₁ (g k) , ∣ inr (pr₂ (g k)) ∣
         e : Fin (n +' m) ≃ Fin n + Fin m
         e = pr₂ (+construction n m)
         μ : Fin (n +' m) → Fin n + Fin m
         μ = eqtofun e
         ν : Fin n + Fin m → Fin (n +' m)
         ν = eqtofun (≃-sym e)
         [f,g] : Fin (n +' m) → 𝕋 (⟨ A ⟩ ∪ ⟨ B ⟩)
         [f,g] = h ∘ μ
         u : is-surjection [f,g]
         u (x , p) = ∥∥-rec ∥∥-is-a-prop δ p
          where
           δ : x ∈ₖ A + x ∈ₖ B → ∃ \(k : Fin (n +' m)) → [f,g] k ≡ (x , p)
           δ (inl a) = ∥∥-functor α (s (x , a))
            where
             α : (Σ \l → f l ≡ (x , a))
               → Σ \k → [f,g] k ≡ (x , p)
             α (l , q) = (ν (inl l)) , to-Σ-≡ (σ , ∥∥-is-a-prop _ p)
              where
               σ : pr₁ ([f,g] (ν (inl l))) ≡ x
               σ = pr₁ ([f,g] (ν (inl l))) ≡⟨ refl ⟩
                   pr₁ (h (μ (ν (inl l)))) ≡⟨ i ⟩
                   pr₁ (h (inl l))         ≡⟨ refl ⟩
                   pr₁ (f l)               ≡⟨ ap pr₁ q ⟩
                   x                       ∎
                where
                 i = ap (λ - → pr₁ (h -)) (inverse-is-section μ (pr₂ e) (inl l))
           δ (inr b) = ∥∥-functor β (t (x , b))
            where
             β : (Σ \l → g l ≡ (x , b))
               → Σ \k → [f,g] k ≡ (x , p)
             β (l , r) = (ν (inr l)) , to-Σ-≡ (τ , ∥∥-is-a-prop _ p)
              where
               τ : pr₁ ([f,g] (ν (inr l))) ≡ x
               τ = pr₁ ([f,g] (ν (inr l))) ≡⟨ refl ⟩
                   pr₁ (h (μ (ν (inr l)))) ≡⟨ i ⟩
                   pr₁ (h (inr l))         ≡⟨ refl ⟩
                   pr₁ (g l)               ≡⟨ ap pr₁ r ⟩
                   x                       ∎
                where
                 i = ap (λ - → pr₁ (h -)) (inverse-is-section μ (pr₂ e) (inr l))

-- Assume funext from now on

module _
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       where

 module _
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
        where

  is-prop-valued : 𝓤 ⊔ 𝓣 ̇
  is-prop-valued = (x y : D) → is-prop(x ⊑ y)

  is-reflexive : 𝓤 ⊔ 𝓣 ̇
  is-reflexive = (x : D) → x ⊑ x

  is-transitive : 𝓤 ⊔ 𝓣 ̇
  is-transitive = (x y z : D) → x ⊑ y → y ⊑ z → x ⊑ z

  is-antisymmetric : 𝓤 ⊔ 𝓣 ̇
  is-antisymmetric = (x y : D) → x ⊑ y → y ⊑ x → x ≡ y

  poset-axioms : 𝓤 ⊔ 𝓣 ̇
  poset-axioms = is-set D
               × is-prop-valued
               × is-reflexive
               × is-transitive
               × is-antisymmetric

  poset-axioms-is-a-prop : is-prop (poset-axioms)
  poset-axioms-is-a-prop = iprops-are-props γ
   where
    γ : poset-axioms → is-prop poset-axioms
    γ (s , p , r , t , a) = ×-is-prop (being-set-is-a-prop fe)
                            (×-is-prop
                              (Π-is-prop fe
                                (λ x → Π-is-prop fe
                                (λ y → being-a-prop-is-a-prop fe)))
                            (×-is-prop
                              (Π-is-prop fe
                                (λ x → p x x))
                            (×-is-prop
                              (Π-is-prop fe
                                (λ x → Π-is-prop fe
                                (λ y → Π-is-prop fe
                                (λ z → Π-is-prop fe
                                (λ u → Π-is-prop fe
                                (λ v → p x z))))))
                            (Π-is-prop fe
                              (λ x → Π-is-prop fe
                              (λ y → Π-is-prop fe
                              (λ u → Π-is-prop fe
                              (λ v → s))))))))

  _is-binary-sup-of-[_,_] : D → D → D → 𝓤 ⊔ 𝓣 ̇
  z is-binary-sup-of-[ x , y ] =
   (x ⊑ z × y ⊑ z) × ((u : D) → x ⊑ u → y ⊑ y → z ⊑ u)

  has-binary-sups : 𝓤 ⊔ 𝓣 ̇
  has-binary-sups = (x y : D) → Σ \(z : D) → z is-binary-sup-of-[ x , y ]

  is-binary-sup-is-a-prop : poset-axioms
                          → (z x y : D)
                          → is-prop (z is-binary-sup-of-[ x , y ])
  is-binary-sup-is-a-prop (s , p , r , t , a) z x y = γ
   where
    γ : is-prop (z is-binary-sup-of-[ x , y ])
    γ = ×-is-prop
        (×-is-prop (p x z) (p y z))
        (Π-is-prop fe
         (λ x → Π-is-prop fe
         (λ l → Π-is-prop fe
         (λ m → p z x))))

  having-binary-sups-is-a-prop : poset-axioms → is-prop (has-binary-sups)
  having-binary-sups-is-a-prop (s , p , r , t , a) = Π-is-prop fe ϕ
   where
    ϕ : (x : D)
      → is-prop ((y : D) → Σ \z → z is-binary-sup-of-[ x , y ])
    ϕ x = Π-is-prop fe ψ
     where
      ψ : (y : D) → is-prop (Σ \z → z is-binary-sup-of-[ x , y ])
      ψ y (z , u , l) (z' , u' , l') =
       to-Σ-≡ (e , is-binary-sup-is-a-prop ((s , p , r , t , a)) z' x y _ (u' , l'))
        where
         e : z ≡ z'
         e = a z z' (l z' (pr₁ u') (r y)) (l' z (pr₁ u) (r y))

  join-semilattice-axioms : 𝓤 ⊔ 𝓣 ̇
  join-semilattice-axioms = poset-axioms × has-binary-sups

  join-semilattice-axioms-is-a-prop : is-prop (join-semilattice-axioms)
  join-semilattice-axioms-is-a-prop = iprops-are-props γ
   where
    γ : join-semilattice-axioms → is-prop join-semilattice-axioms
    γ (pa , _) = ×-is-prop poset-axioms-is-a-prop (having-binary-sups-is-a-prop pa)

 module _
         {𝓤 𝓣 : Universe}
        where

  join-semilattice-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓣 ⁺) ̇
  join-semilattice-structure P =
    Σ \(_≤_ : P → P → 𝓣 ̇ ) → join-semilattice-axioms {𝓤} {𝓣} _≤_

  join-semilattice : 𝓤 ⁺ ⊔ (𝓣 ⁺) ̇
  join-semilattice = Σ \(P : 𝓤 ̇ ) → join-semilattice-structure P



 module KuratowskiSemiLattice
         (pt : propositional-truncations-exist)
        where

  open KuratowskiFinite pt

  𝓚-join-semilattice : {𝓤 : Universe} → 𝓤 ̇ → join-semilattice {𝓤 ⁺} {𝓤}
  𝓚-join-semilattice {𝓤} X = 𝓚 𝓤 X , _⊆ₖ_ , (({!!} , {!!}) , {!!})


\end{code}
