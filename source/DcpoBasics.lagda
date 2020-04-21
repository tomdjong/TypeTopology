\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc hiding (⊥)

module DcpoBasics
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open PropositionalTruncation pt

\end{code}

TO DO

\begin{code}

open import Dcpo pt fe 𝓥

≡-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩} → x ≡ y → x ⊑⟨ 𝓓 ⟩ y
≡-to-⊑ 𝓓 {x} {x} refl = reflexivity 𝓓 x

∐-independent-of-directedness-witness : (𝓓 : DCPO {𝓤} {𝓣})
                                        {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                                        (δ ε : is-Directed 𝓓 α)
                                      → ∐ 𝓓 δ ≡ ∐ 𝓓 ε
∐-independent-of-directedness-witness 𝓓 δ ε = ap (∐ 𝓓) p
 where
  p : δ ≡ ε
  p = being-directed-is-a-prop (underlying-order 𝓓) δ ε

is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
            → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
is-monotone 𝓓 𝓔 f = (x y : ⟨ 𝓓 ⟩) → x ⊑⟨ 𝓓 ⟩ y → f x ⊑⟨ 𝓔 ⟩ f y

image-is-directed : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                    {f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩}
                  → is-monotone 𝓓 𝓔 f
                  → {I : 𝓥 ̇ }
                  → {α : I → ⟨ 𝓓 ⟩}
                  → is-Directed 𝓓 α
                  → is-Directed 𝓔 (f ∘ α)
image-is-directed 𝓓 𝓔 {f} m {I} {α} δ =
 Directed-implies-inhabited 𝓓 δ , γ
  where
   γ : is-weakly-directed (underlying-order 𝓔) (f ∘ α)
   γ i j = do
    k , u , v ← Directed-implies-weakly-directed 𝓓 δ i j
    ∣ k , m (α i) (α k) u , m (α j) (α k) v ∣

continuity-criterion : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                       (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                     → (m : is-monotone 𝓓 𝓔 f)
                     → ((I : 𝓥 ̇ )
                        (α : I → ⟨ 𝓓 ⟩)
                        (δ : is-Directed 𝓓 α)
                     → f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (image-is-directed 𝓓 𝓔 m δ))
                     → is-continuous 𝓓 𝓔 f
continuity-criterion 𝓓 𝓔 f m e I α δ = ub , lb-of-ubs
 where
  ub : (i : I) → f (α i) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
  ub i = m (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)
  ε : is-Directed 𝓔 (f ∘ α)
  ε = image-is-directed 𝓓 𝓔 m δ
  lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓔)
              (f (∐ 𝓓 δ)) (f ∘ α)
  lb-of-ubs y u = f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩[ e I α δ  ]
                  ∐ 𝓔 ε     ⊑⟨ 𝓔 ⟩[ ∐-is-lowerbound-of-upperbounds 𝓔 ε y u ]
                  y         ∎⟨ 𝓔 ⟩

continuity-criterion' : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                        (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                      → (m : is-monotone 𝓓 𝓔 f)
                      → ((I : 𝓥 ̇ )
                         (α : I → ⟨ 𝓓 ⟩)
                         (δ : is-Directed 𝓓 α)
                      → is-lowerbound-of-upperbounds (underlying-order 𝓔)
                                                     (f (∐ 𝓓 δ)) (f ∘ α))
                      → is-continuous 𝓓 𝓔 f
continuity-criterion' 𝓓 𝓔 f m lb I α δ = ub , lb I α δ
 where
  ub : (i : I) → f (α i) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
  ub i = m (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)

continuous-implies-monotone : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                              (f : DCPO[ 𝓓 , 𝓔 ])
                            → is-monotone 𝓓 𝓔 (underlying-function 𝓓 𝓔 f)
continuous-implies-monotone 𝓓 𝓔 (f , cts) x y l = γ
  where
   α : 𝟙 {𝓥} + 𝟙 {𝓥} → ⟨ 𝓓 ⟩
   α (inl *) = x
   α (inr *) = y
   δ : is-Directed 𝓓 α
   δ = (∣ inl * ∣ , ε)
    where
     ε : (i j : 𝟙 + 𝟙) → ∃ (\k → α i ⊑⟨ 𝓓 ⟩ α k × α j ⊑⟨ 𝓓 ⟩ α k)
     ε (inl *) (inl *) = ∣ inr * , l , l ∣
     ε (inl *) (inr *) = ∣ inr * , l , reflexivity 𝓓 y ∣
     ε (inr *) (inl *) = ∣ inr * , reflexivity 𝓓 y , l ∣
     ε (inr *) (inr *) = ∣ inr * , reflexivity 𝓓 y , reflexivity 𝓓 y ∣
   a : y ≡ ∐ 𝓓 δ
   a = antisymmetry 𝓓 y (∐ 𝓓 δ)
           (∐-is-upperbound 𝓓 δ (inr *))
           (∐-is-lowerbound-of-upperbounds 𝓓 δ y h)
    where
     h : (i : 𝟙 + 𝟙) → α i ⊑⟨ 𝓓 ⟩ y
     h (inl *) = l
     h (inr *) = reflexivity 𝓓 y
   b : is-sup (underlying-order 𝓔) (f y) (f ∘ α)
   b = transport (λ - → is-sup (underlying-order 𝓔) - (f ∘ α)) (ap f (a ⁻¹))
       (cts (𝟙 + 𝟙) α δ)
   γ : f x ⊑⟨ 𝓔 ⟩ f y
   γ = sup-is-upperbound (underlying-order 𝓔) b (inl *)

image-is-directed' : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                     (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                   → is-Directed 𝓓 α
                   → is-Directed 𝓔 ((underlying-function 𝓓 𝓔 f) ∘ α)
image-is-directed' 𝓓 𝓔 f {I} {α} δ =
 image-is-directed 𝓓 𝓔 m δ
  where
   m : is-monotone 𝓓 𝓔 (underlying-function 𝓓 𝓔 f)
   m = continuous-implies-monotone 𝓓 𝓔 f

continuous-∐-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ)
continuous-∐-⊑ 𝓓 𝓔 (f , c) {I} {α} δ =
 sup-is-lowerbound-of-upperbounds (underlying-order 𝓔) (c I α δ) (∐ 𝓔 ε) u
  where
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed' 𝓓 𝓔 (f , c) δ
   u : is-upperbound (underlying-order 𝓔) (∐ 𝓔 ε) (f ∘ α)
   u = ∐-is-upperbound 𝓔 ε

continuous-∐-⊒ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ) ⊑⟨ 𝓔 ⟩ [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ)
continuous-∐-⊒ 𝓓 𝓔 (f , c) {I} {α} δ =
 ∐-is-lowerbound-of-upperbounds 𝓔 ε (f (∐ 𝓓 δ)) u
  where
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed' 𝓓 𝓔 (f , c) δ
   u : (i : I) → f (α i) ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
   u i = sup-is-upperbound (underlying-order 𝓔) (c I α δ) i

continuous-∐-≡ : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                 (f : DCPO[ 𝓓 , 𝓔 ]) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                 (δ : is-Directed 𝓓 α)
               → [ 𝓓 , 𝓔 ]⟨ f ⟩ (∐ 𝓓 δ) ≡ ∐ 𝓔 (image-is-directed' 𝓓 𝓔 f δ)
continuous-∐-≡ 𝓓 𝓔 (f , c) {I} {α} δ =
 antisymmetry 𝓔 (f (∐ 𝓓 δ)) (∐ 𝓔 ε) a b
  where
   ε : is-Directed 𝓔 (f ∘ α)
   ε = image-is-directed' 𝓓 𝓔 (f , c) δ
   a : f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ ∐ 𝓔 ε
   a = continuous-∐-⊑ 𝓓 𝓔 (f , c) δ
   b : ∐ 𝓔 ε ⊑⟨ 𝓔 ⟩ f (∐ 𝓓 δ)
   b = continuous-∐-⊒ 𝓓 𝓔 (f , c) δ

constant-functions-are-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                                    (e : ⟨ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ d → e)
constant-functions-are-continuous 𝓓 𝓔 e I α δ = u , v
 where
  u : (i : I) → e ⊑⟨ 𝓔 ⟩ e
  u i = reflexivity 𝓔 e
  v : (y : ⟨ 𝓔 ⟩) → ((i : I) → e ⊑⟨ 𝓔 ⟩ y) → e ⊑⟨ 𝓔 ⟩ y
  v y l  = ∥∥-rec (prop-valuedness 𝓔 e y)
                  (λ (i : I) → l i)
                  (Directed-implies-inhabited 𝓓 δ)

\end{code}

TO DO

\begin{code}

strongly-directed-complete : (𝓓 : DCPO⊥ {𝓤} {𝓣}) {I : 𝓥 ̇ } {α : I → ⟪ 𝓓 ⟫}
                           → is-weakly-directed (underlying-order (𝓓 ⁻)) α
                           → has-sup (underlying-order (𝓓 ⁻)) α
strongly-directed-complete {𝓤} {𝓣} 𝓓 {I} {α} ε = s , u , v
 where
  _⊑_ : ⟪ 𝓓 ⟫ → ⟪ 𝓓 ⟫ → 𝓣 ̇
  _⊑_ = underlying-order (𝓓 ⁻)
  J : 𝓥 ̇
  J = 𝟙{𝓥} + I
  β : J → ⟪ 𝓓 ⟫
  β (inl *) = ⊥ 𝓓
  β (inr i) = α i
  δ : is-directed _⊑_ β
  δ = (∣ inl * ∣ , κ)
   where
    κ : (a b : J) → ∃ \c → (β a ⊑ β c) × (β b ⊑ β c)
    κ (inl *) b = ∣ b , ⊥-is-least 𝓓 (β b) , reflexivity (𝓓 ⁻) (β b) ∣
    κ (inr i) (inl *) = ∣ (inr i) , reflexivity (𝓓 ⁻) (α i) , ⊥-is-least 𝓓 (α i) ∣
    κ (inr i) (inr j) = ∥∥-functor γ (ε i j)
     where
      γ : (Σ \(k : I) → (α i) ⊑ (α k) × (α j) ⊑ (α k))
        → Σ \(c : J) → (β (inr i) ⊑ β c) × (β (inr j) ⊑ β c)
      γ (k , l) = (inr k , l)
  s : ⟪ 𝓓 ⟫
  s = ∐ (𝓓 ⁻) δ
  u : is-upperbound _⊑_ s α
  u i = ∐-is-upperbound (𝓓 ⁻) δ (inr i)
  v : ((t : ⟪ 𝓓 ⟫) → is-upperbound _⊑_ t α → s ⊑ t)
  v t l = ∐-is-lowerbound-of-upperbounds (𝓓 ⁻) δ t h
   where
    h : (k : J) → (β k) ⊑ t
    h (inl *) = ⊥-is-least 𝓓 t
    h (inr i) = l i

∐-is-monotone : (𝓓 : DCPO {𝓤} {𝓣}) {I : 𝓥 ̇ } {α β : I → ⟨ 𝓓 ⟩}
                (δ : is-Directed 𝓓 α) (ε : is-Directed 𝓓 β)
              → ((i : I) → α i ⊑⟨ 𝓓 ⟩ β i)
              → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
∐-is-monotone 𝓓 {I} {α} {β} δ ε l =
 ∐-is-lowerbound-of-upperbounds 𝓓 δ (∐ 𝓓 ε) γ
  where
   γ : (i : I) → α i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
   γ i = α i   ⊑⟨ 𝓓 ⟩[ l i ]
         β i   ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 ε i ]
         ∐ 𝓓 ε ∎⟨ 𝓓 ⟩

double-∐-swap : {I J : 𝓥 ̇ } (𝓓 : DCPO {𝓤} {𝓣}) {γ : I × J → ⟨ 𝓓 ⟩}
              → (δᵢ : (i : I) → is-Directed 𝓓 (λ (j : J) → γ (i , j)))
              → (δⱼ : (j : J) → is-Directed 𝓓 (λ (i : I) → γ (i , j)))
              → (ε₁ : is-Directed 𝓓 (λ (j : J) → ∐ 𝓓 (δⱼ j)))
              → (ε₂ : is-Directed 𝓓 (λ (i : I) → ∐ 𝓓 (δᵢ i)))
              → ∐ 𝓓 ε₁ ≡ ∐ 𝓓 ε₂
double-∐-swap {𝓤} {𝓣} {I} {J} 𝓓 {γ} δᵢ δⱼ ε₁ ε₂ =
 antisymmetry 𝓓 (∐ 𝓓 ε₁) (∐ 𝓓 ε₂) u v
  where
   u : ∐ 𝓓 ε₁ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε₂
   u = ∐-is-lowerbound-of-upperbounds 𝓓 ε₁ (∐ 𝓓 ε₂) w
    where
     w : (j : J) → ∐ 𝓓 (δⱼ j) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε₂
     w j = ∐-is-lowerbound-of-upperbounds 𝓓 (δⱼ j) (∐ 𝓓 ε₂) z
      where
       z : (i : I) → γ (i , j) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε₂
       z i = γ (i , j)  ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 (δᵢ i) j ]
             ∐ 𝓓 (δᵢ i) ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 ε₂ i ]
             ∐ 𝓓 ε₂     ∎⟨ 𝓓 ⟩
   v : ∐ 𝓓 ε₂ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε₁
   v = ∐-is-lowerbound-of-upperbounds 𝓓 ε₂ (∐ 𝓓 ε₁) w
    where
     w : (i : I) → ∐ 𝓓 (δᵢ i) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε₁
     w i = ∐-is-lowerbound-of-upperbounds 𝓓 (δᵢ i) (∐ 𝓓 ε₁) z
      where
       z : (j : J) → γ (i , j) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε₁
       z j = γ (i , j)  ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 (δⱼ j) i ]
             ∐ 𝓓 (δⱼ j) ⊑⟨ 𝓓 ⟩[ ∐-is-upperbound 𝓓 ε₁ j ]
             ∐ 𝓓 ε₁     ∎⟨ 𝓓 ⟩

\end{code}
