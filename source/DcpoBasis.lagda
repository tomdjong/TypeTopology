Tom de Jong, late February - early March 2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-PropTrunc
open import UF-Equiv
open import UF-Size

module DcpoBasis
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoApproximation pt fe 𝓥

≪-small-on-B : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
≪-small-on-B 𝓓 {B} ι = (b b' : B) → (ι b ≪⟨ 𝓓 ⟩ ι b') has-size 𝓥

approximate-from-basis-Σ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩)
                         → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
approximate-from-basis-Σ {𝓤} {𝓣} 𝓓 {B} ι x =
 Σ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) , ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
                          × (Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x)

approximate-from-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩)
                       → ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
approximate-from-basis {𝓤} {𝓣} 𝓓 {B} ι x =
 ∃ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) , ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
                          × (Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x)

is-a-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } → (B → ⟨ 𝓓 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-basis {𝓤} {𝓣} 𝓓 {B} ι = ≪-small-on-B 𝓓 ι
                             × ((x : ⟨ 𝓓 ⟩) → approximate-from-basis 𝓓 ι x)

is-a-continuous-dcpo : (𝓓 : DCPO {𝓤} {𝓣}) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
is-a-continuous-dcpo {𝓤} {𝓣} 𝓓 = ∃ B ꞉ 𝓥 ̇ , Σ ι ꞉ (B → ⟨ 𝓓 ⟩) , is-a-basis 𝓓 ι

basis-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
        → is-a-basis 𝓓 ι
        → B → B → 𝓥 ̇
basis-≪ 𝓓 (≺ , _) b b' = has-size-type (≺ b b')

syntax basis-≪ 𝓓 isb b b' = b ≪ᴮ⟨ 𝓓 ⟩[ isb ] b'

≪ᴮ-to-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b b' : B) → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b' → ι b ≪⟨ 𝓓 ⟩ ι b'
≪ᴮ-to-≪ 𝓓 {B} {ι} c b b' = ⌜ e ⌝
 where
  e : b ≪ᴮ⟨ 𝓓 ⟩[ c ] b' ≃ ι b ≪⟨ 𝓓 ⟩ ι b'
  e = has-size-equiv (≺ b b')
   where
    ≺ : ≪-small-on-B 𝓓 ι
    ≺ = pr₁ c

≪-to-≪ᴮ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b b' : B) → ι b ≪⟨ 𝓓 ⟩ ι b' → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b'
≪-to-≪ᴮ 𝓓 {B} {ι} c b b' = ⌜ ≃-sym e ⌝
 where
  e : b ≪ᴮ⟨ 𝓓 ⟩[ c ] b' ≃ ι b ≪⟨ 𝓓 ⟩ ι b'
  e = has-size-equiv (≺ b b')
   where
    ≺ : ≪-small-on-B 𝓓 ι
    ≺ = pr₁ c

≪ᴮ-is-prop-valued : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                    (c : is-a-basis 𝓓 ι) {b b' : B}
                  → is-prop (b ≪ᴮ⟨ 𝓓 ⟩[ c ] b')
≪ᴮ-is-prop-valued 𝓓 {B} {ι} (≺ , _) {b} {b'} =
 equiv-to-prop (has-size-equiv (≺ b b')) (≪-is-prop-valued 𝓓)

\end{code}

\begin{code}

⊑-in-terms-of-≪ : (𝓓 : DCPO {𝓤} {𝓣}) {x y : ⟨ 𝓓 ⟩}
                → x ⊑⟨ 𝓓 ⟩ y
                → (z : ⟨ 𝓓 ⟩)
                → z ≪⟨ 𝓓 ⟩ x → z ≪⟨ 𝓓 ⟩ y
⊑-in-terms-of-≪ 𝓓 l z u = ≪-⊑-to-≪ 𝓓 u l

⊑-in-terms-of-≪' : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                 → is-a-basis 𝓓 ι
                 → {x y : ⟨ 𝓓 ⟩}
                 → ((b : B) → ι b ≪⟨ 𝓓 ⟩ x → ι b ≪⟨ 𝓓 ⟩ y)
                 → x ⊑⟨ 𝓓 ⟩ y
⊑-in-terms-of-≪' 𝓓 {B} {ι} (_ , c) {x} {y} h =
 ∥∥-rec (prop-valuedness 𝓓 x y) γ (c x)
  where
   γ : (Σ I ꞉ 𝓥 ̇ , Σ β ꞉ (I → B) ,
          ((i : I) → ι (β i) ≪⟨ 𝓓 ⟩ x)
        × (Σ δ ꞉ is-Directed 𝓓 (ι ∘ β) , ∐ 𝓓 δ ≡ x))
     → x ⊑⟨ 𝓓 ⟩ y
   γ (I , β , wb , δ , e) = x      ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (e ⁻¹) ]
                            ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩[ l ]
                            y      ∎⟨ 𝓓 ⟩
    where
     l = ∐-is-lowerbound-of-upperbounds 𝓓 δ y ub
      where
       ub : (i : I) → ι (β i) ⊑⟨ 𝓓 ⟩ y
       ub i = ≪-to-⊑ 𝓓 (h (β i) (wb i))

\end{code}

\begin{code}

basis-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
        → is-a-basis 𝓓 ι
        → B → B → 𝓥 ̇
basis-⊑ 𝓓 {B} {ι} c b₁ b₂ = (b : B) → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₁ → b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂

syntax basis-⊑ 𝓓 c b b' = b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b'

⊑ᴮ-to-⊑ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
          (c : is-a-basis 𝓓 ι) {b b' : B}
        → b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b' → ι b ⊑⟨ 𝓓 ⟩ ι b'
⊑ᴮ-to-⊑ 𝓓 {B} {ι} c {b₁} {b₂} l = ⊑-in-terms-of-≪' 𝓓 c γ
 where
  γ : (b : B) → ι b ≪⟨ 𝓓 ⟩ ι b₁ → ι b ≪⟨ 𝓓 ⟩ ι b₂
  γ b wb = ≪ᴮ-to-≪ 𝓓 c b b₂ (l b (≪-to-≪ᴮ 𝓓 c b b₁ wb))

⊑-to-⊑ᴮ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
          (c : is-a-basis 𝓓 ι) {b b' : B}
        → ι b ⊑⟨ 𝓓 ⟩ ι b'
        → b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b'
⊑-to-⊑ᴮ 𝓓 {B} {ι} c {b₁} {b₂} l b u = ≪-to-≪ᴮ 𝓓 c b b₂ γ
 where
  γ : ι b ≪⟨ 𝓓 ⟩ ι b₂
  γ = ⊑-in-terms-of-≪ 𝓓 l (ι b) (≪ᴮ-to-≪ 𝓓 c b b₁ u)

⊑ᴮ-is-prop-valued : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                    (c : is-a-basis 𝓓 ι) {b b' : B}
                  → is-prop (b ⊑ᴮ⟨ 𝓓 ⟩[ c ] b')
⊑ᴮ-is-prop-valued 𝓓 {B} {ι} (≺ , _) {b₁} {b₂} =
 Π-is-prop fe
 λ b → Π-is-prop fe
 λ b≪b₁ → equiv-to-prop (has-size-equiv (≺ b b₂)) (≪-is-prop-valued 𝓓)

⊑-is-small-on-basis : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                      (c : is-a-basis 𝓓 ι) {b b' : B}
                    → (ι b ⊑⟨ 𝓓 ⟩ ι b') has-size 𝓥
⊑-is-small-on-basis 𝓓 {B} {ι} c {b₁} {b₂} = (b₁ ⊑ᴮ⟨ 𝓓 ⟩[ c ] b₂) , γ
 where
  γ : (b₁ ⊑ᴮ⟨ 𝓓 ⟩[ c ] b₂) ≃ ι b₁ ⊑⟨ 𝓓 ⟩ ι b₂
  γ = logically-equivalent-props-are-equivalent
       (⊑ᴮ-is-prop-valued 𝓓 c)
       (prop-valuedness 𝓓 (ι b₁) (ι b₂))
       (⊑ᴮ-to-⊑ 𝓓 c)
       (⊑-to-⊑ᴮ 𝓓 c)

≪-INT₀ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
         (x : ⟨ 𝓓 ⟩) → ∃ b ꞉ B , ι b ≪⟨ 𝓓 ⟩ x
≪-INT₀ 𝓓 {B} {ι} (≺ , c) x = ∥∥-rec ∥∥-is-a-prop γ (c x)
 where
  γ : approximate-from-basis-Σ 𝓓 ι x → ∃ b ꞉ B , ι b ≪⟨ 𝓓 ⟩ x
  γ (I , β , wb , δ , e) = ∥∥-functor g (Directed-implies-inhabited 𝓓 δ)
   where
    g : I → Σ b ꞉ B , ι b ≪⟨ 𝓓 ⟩ x
    g i = β i , wb i

≪ᴮ-INT₀ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b : B) → ∃ b' ꞉ B , b' ≪ᴮ⟨ 𝓓 ⟩[ c ] b
≪ᴮ-INT₀ 𝓓 {B} {ι} c b = ∥∥-functor γ (≪-INT₀ 𝓓 c (ι b))
 where
  γ : (Σ b' ꞉ B , ι b' ≪⟨ 𝓓 ⟩ ι b) → Σ b' ꞉ B , b' ≪ᴮ⟨ 𝓓 ⟩[ c ] b
  γ (b' , u) = b' , ≪-to-≪ᴮ 𝓓 c b' b u

\end{code}

It seems that the first lemma from
https://www.cs.bham.ac.uk/~mhe/papers/interpolation.pdf cannot work here,
because ≪ may be non-small when comparing non-basis elements.

Below, we do follow the proof (of the second lemma) from
https://www.cs.bham.ac.uk/~mhe/papers/interpolation.pdf, but adapted so that we
only include basis elements in the newly constructed directed family.

\begin{code}

-- TO DO: Split and improve this proof

≪-INT₂-aux : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
             {I : 𝓥 ̇ } (α : I → B)
           → 𝓥 ̇
≪-INT₂-aux 𝓓 {B} {ι} c {I} α = Σ b ꞉ B , Σ i ꞉ I , b ≪ᴮ⟨ 𝓓 ⟩[ c ] α i

≪-INT₂-aux-map : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                 (c : is-a-basis 𝓓 ι) {I : 𝓥 ̇ } (α : I → B)
               → ≪-INT₂-aux 𝓓 c α → ⟨ 𝓓 ⟩
≪-INT₂-aux-map 𝓓 {B} {ι} c α = ι ∘ pr₁

≪-INT₂-aux-is-directed : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                         (c : is-a-basis 𝓓 ι) {I : 𝓥 ̇ } (α : I → B)
                       → is-Directed 𝓓 (ι ∘ α)
                       → is-Directed 𝓓 (≪-INT₂-aux-map 𝓓 c α)
≪-INT₂-aux-is-directed 𝓓 {B} {ι} cd {I} α δ = s , ε
 where
  J : 𝓥 ̇
  J = ≪-INT₂-aux 𝓓 cd α
  β : J → ⟨ 𝓓 ⟩
  β = ≪-INT₂-aux-map 𝓓 cd α
  s : ∥ J ∥
  s = ∥∥-rec ∥∥-is-a-prop γ (Directed-implies-inhabited 𝓓 δ)
   where
    γ : I → ∥ J ∥
    γ i = ∥∥-functor g (≪ᴮ-INT₀ 𝓓 cd (α i))
     where
      g : (Σ b ꞉ B , b ≪ᴮ⟨ 𝓓 ⟩[ cd ] α i) → J
      g (b , u) = b , i , u
  ε : is-weakly-directed (underlying-order 𝓓) β
  ε (b₁ , i₁ , u₁) (b₂ , i₂ , u₂) = do
   l₃ , l₁ , l₂ ← t
   𝓐 , ϕ , wb , ε , e ← c (ι (α l₃))
   let v₁ = ≪-⊑-to-≪ 𝓓 (≪ᴮ-to-≪ 𝓓 cd b₁ (α i₁) u₁) l₁
   let v₂ = ≪-⊑-to-≪ 𝓓 (≪ᴮ-to-≪ 𝓓 cd b₂ (α i₂) u₂) l₂
   a₁ , m₁ ← v₁ 𝓐 (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (e ⁻¹))
   a₂ , m₂ ← v₂ 𝓐 (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (e ⁻¹))
   (a₃ , n₁ , n₂) ← Directed-implies-weakly-directed 𝓓 ε a₁ a₂
   let w = ≪-to-≪ᴮ 𝓓 cd (ϕ a₃) (α l₃) (wb a₃)
   let k₁ = ι b₁     ⊑⟨ 𝓓 ⟩[ m₁ ]
            ι (ϕ a₁) ⊑⟨ 𝓓 ⟩[ n₁ ]
            ι (ϕ a₃) ∎⟨ 𝓓 ⟩
   let k₂ = ι b₂     ⊑⟨ 𝓓 ⟩[ m₂ ]
            ι (ϕ a₂) ⊑⟨ 𝓓 ⟩[ n₂ ]
            ι (ϕ a₃) ∎⟨ 𝓓 ⟩
   ∣ (ϕ a₃ , l₃ , w) , k₁ , k₂ ∣
   where
   t : ∃ k ꞉ I , ι (α i₁) ⊑⟨ 𝓓 ⟩ ι (α k) × ι (α i₂) ⊑⟨ 𝓓 ⟩ ι (α k)
   t = Directed-implies-weakly-directed 𝓓 δ i₁ i₂
   c : (x : ⟨ 𝓓 ⟩) → approximate-from-basis 𝓓 ι x
   c = pr₂ cd

≪-INT₂-aux-⊑-∐ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩}
                 (c : is-a-basis 𝓓 ι) {I : 𝓥 ̇ } (α : I → B)
               → (δ : is-Directed 𝓓 (ι ∘ α))
               → ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩ ∐ 𝓓 (≪-INT₂-aux-is-directed 𝓓 c α δ)
≪-INT₂-aux-⊑-∐ 𝓓 {B} {ι} cd {I} α δ =
 ∐-is-lowerbound-of-upperbounds 𝓓 δ (∐ 𝓓 ε) ub
  where
   ε : is-Directed 𝓓 (≪-INT₂-aux-map 𝓓 cd α)
   ε = ≪-INT₂-aux-is-directed 𝓓 cd α δ
   ub : (i : I) → ι (α i) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
   ub i = ∥∥-rec (prop-valuedness 𝓓 (ι (α i)) (∐ 𝓓 ε)) g (c (ι (α i)))
    where
     c : (x : ⟨ 𝓓 ⟩) → approximate-from-basis 𝓓 ι x
     c = pr₂ cd
     g : approximate-from-basis-Σ 𝓓 ι (ι (α i)) → ι (α i) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
     g (J , β , wb , φ , e) = ι (α i) ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (e ⁻¹) ]
                              ∐ 𝓓 φ ⊑⟨ 𝓓 ⟩[ l ]
                              ∐ 𝓓 ε ∎⟨ 𝓓 ⟩
      where
       l = ∐-is-lowerbound-of-upperbounds {!!} {!!} {!!} {!!}

{-
       h = ∐-is-lowerbound-of-upperbounds 𝓓 δ (∐ 𝓓 ε) ub
         where
          ub : (i : I) → (ι ∘ α) i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
          ub i = ∥∥-rec (prop-valuedness 𝓓 (ι (α i)) (∐ 𝓓 ε))
                 g (c (ι (α i)))
           where
            g : (Σ L ꞉ 𝓥 ̇ , Σ ϕ ꞉ (L → B) ,
                 ((l : L) → ι (ϕ l) ≪⟨ 𝓓 ⟩ ι (α i))
                × (Σ φ ꞉ is-Directed 𝓓 (ι ∘ ϕ) , ∐ 𝓓 φ ≡ ι (α i)))
              → ι (α i) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
            g (L , ϕ , ϕ≪αi , φ , ∐ϕ≡αi) = ι (α i)  ⊑⟨ 𝓓 ⟩[ ⊑₁ ]
                                              ∐ 𝓓 φ ⊑⟨ 𝓓 ⟩[ ⊑₂ ]
                                              ∐ 𝓓 ε ∎⟨ 𝓓 ⟩
             where
              ⊑₁ = ≡-to-⊑ 𝓓 (∐ϕ≡αi ⁻¹)
              ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓓 φ (∐ 𝓓 ε) ub'
               where
                ub' : (l : L) → ι (ϕ l) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
                ub' l = ∐-is-upperbound 𝓓 ε j
                 where
                  j : J
                  j = ϕ l , i , ≪-to-≪ᴮ 𝓓 cd (ϕ l) (α i) (ϕ≪αi l)
-}

≪-INT₁ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
         (x y : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ y
       → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
≪-INT₁ 𝓓 {B} {ι} (≺ , c) x y x≪y = ∥∥-rec ∥∥-is-a-prop γ (c y)
 where
  cd : is-a-basis 𝓓 ι
  cd = (≺ , c)
  γ : approximate-from-basis-Σ 𝓓 ι y
    → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
  γ (I , α , α≪y , δ , ∐α≡y) = ∥∥-functor s t
   where
    J : 𝓥 ̇
    J = Σ b ꞉ B , Σ i ꞉ I , b ≪ᴮ⟨ 𝓓 ⟩[ cd ] α i
    s : (Σ j ꞉ J , x ⊑⟨ 𝓓 ⟩ ι (pr₁ j))
      → Σ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ y
    s ((b , i , b≪ᴮαi) , x⊑b) = α i , ≪₁ , ≪₂
     where
      ≪₁ : x ≪⟨ 𝓓 ⟩ ι (α i)
      ≪₁ = ⊑-≪-to-≪ 𝓓 x⊑b (≪ᴮ-to-≪ 𝓓 cd b (α i) b≪ᴮαi)
      ≪₂ : ι (α i) ≪⟨ 𝓓 ⟩ y
      ≪₂ = α≪y i
    t : ∃ j ꞉ J , x ⊑⟨ 𝓓 ⟩ ι (pr₁ j)
    t = x≪y J β ε y⊑∐β
     where
      β : J → ⟨ 𝓓 ⟩
      β = ι ∘ pr₁
      ε : is-Directed 𝓓 β
      ε = J-inh , β-wdirected
       where
        J-inh : ∥ J ∥
        J-inh = do
         i ← Directed-implies-inhabited 𝓓 δ
         (b , b≪ᴮαi) ← ≪ᴮ-INT₀ 𝓓 cd (α i)
         ∣ b , i , b≪ᴮαi ∣
        β-wdirected : is-weakly-directed (underlying-order 𝓓) β
        β-wdirected (b₁ , i₁ , b₁≪ᴮαi₁) (b₂ , i₂ , b₂≪ᴮαi₂) = do
         (k , αi₁⊑αk , αi₂⊑αk) ← Directed-implies-weakly-directed 𝓓 δ i₁ i₂
         let b₁≪αk = ≪-⊑-to-≪ 𝓓 (≪ᴮ-to-≪ 𝓓 cd b₁ (α i₁) b₁≪ᴮαi₁) αi₁⊑αk
         let b₂≪αk = ≪-⊑-to-≪ 𝓓 (≪ᴮ-to-≪ 𝓓 cd b₂ (α i₂) b₂≪ᴮαi₂) αi₂⊑αk
         (L , ϕ , ϕ≪αk , ε , ∐ϕ≡αk) ← c (ι (α k))
         (l₁ , b₁⊑ϕl₁) ← b₁≪αk L (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (∐ϕ≡αk ⁻¹))
         (l₂ , b₂⊑ϕl₂) ← b₂≪αk L (ι ∘ ϕ) ε (≡-to-⊑ 𝓓 (∐ϕ≡αk ⁻¹))
         (m , ϕl₁⊑ϕm , ϕl₂⊑ϕm) ← Directed-implies-weakly-directed 𝓓 ε l₁ l₂
         let ϕm≪ᴮαk = ≪-to-≪ᴮ 𝓓 cd (ϕ m) (α k) (ϕ≪αk m)
         let b₁⊑ϕm = ι b₁     ⊑⟨ 𝓓 ⟩[ b₁⊑ϕl₁ ]
                     ι (ϕ l₁) ⊑⟨ 𝓓 ⟩[ ϕl₁⊑ϕm ]
                     ι (ϕ m)  ∎⟨ 𝓓 ⟩
         let b₂⊑ϕm = ι b₂     ⊑⟨ 𝓓 ⟩[ b₂⊑ϕl₂ ]
                     ι (ϕ l₂) ⊑⟨ 𝓓 ⟩[ ϕl₂⊑ϕm ]
                     ι (ϕ m)  ∎⟨ 𝓓 ⟩
         ∣ (ϕ m , k , ϕm≪ᴮαk) , b₁⊑ϕm , b₂⊑ϕm ∣
      y⊑∐β = y      ⊑⟨ 𝓓 ⟩[ ≡-to-⊑ 𝓓 (∐α≡y ⁻¹) ]
             ∐ 𝓓 δ ⊑⟨ 𝓓 ⟩[ h ]
             ∐ 𝓓 ε ∎⟨ 𝓓 ⟩
       where
        h = ∐-is-lowerbound-of-upperbounds 𝓓 δ (∐ 𝓓 ε) ub
         where
          ub : (i : I) → (ι ∘ α) i ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
          ub i = ∥∥-rec (prop-valuedness 𝓓 (ι (α i)) (∐ 𝓓 ε))
                 g (c (ι (α i)))
           where
            g : (Σ L ꞉ 𝓥 ̇ , Σ ϕ ꞉ (L → B) ,
                 ((l : L) → ι (ϕ l) ≪⟨ 𝓓 ⟩ ι (α i))
                × (Σ φ ꞉ is-Directed 𝓓 (ι ∘ ϕ) , ∐ 𝓓 φ ≡ ι (α i)))
              → ι (α i) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
            g (L , ϕ , ϕ≪αi , φ , ∐ϕ≡αi) = ι (α i)  ⊑⟨ 𝓓 ⟩[ ⊑₁ ]
                                              ∐ 𝓓 φ ⊑⟨ 𝓓 ⟩[ ⊑₂ ]
                                              ∐ 𝓓 ε ∎⟨ 𝓓 ⟩
             where
              ⊑₁ = ≡-to-⊑ 𝓓 (∐ϕ≡αi ⁻¹)
              ⊑₂ = ∐-is-lowerbound-of-upperbounds 𝓓 φ (∐ 𝓓 ε) ub'
               where
                ub' : (l : L) → ι (ϕ l) ⊑⟨ 𝓓 ⟩ ∐ 𝓓 ε
                ub' l = ∐-is-upperbound 𝓓 ε j
                 where
                  j : J
                  j = ϕ l , i , ≪-to-≪ᴮ 𝓓 cd (ϕ l) (α i) (ϕ≪αi l)

≪ᴮ-INT₁ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b₁ b₂ : B) → b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂
        → ∃ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂
≪ᴮ-INT₁ 𝓓 {B} {ι} c b₁ b₂ u =
 ∥∥-functor γ (≪-INT₁ 𝓓 c (ι b₁) (ι b₂) (≪ᴮ-to-≪ 𝓓 c b₁ b₂ u))
  where
   γ : (Σ b ꞉ B , ι b₁ ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ ι b₂)
     → Σ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₂
   γ (b , v , w) = b , ≪-to-≪ᴮ 𝓓 c b₁ b v , ≪-to-≪ᴮ 𝓓 c b b₂ w

\end{code}

An interpolation property starting from two inequalities.

≪ᴮ-INT₂ shows that a basis of a continuous dcpo satisifies the axioms of an
"abstract basis" as set out in IdealCompletion.

\begin{code}

≪-INT₂ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
         (x y z : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
       → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × y ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ z
≪-INT₂ 𝓓 {B} {ι} cd x y z u v = do
 b₁ , u₁ , v₁ ← t₁
 b₂ , u₂ , v₂ ← t₂
 I , α , wb , δ , e ← c z
 i₁ , l₁ ← v₁ I (ι ∘ α) δ (≡-to-⊑ 𝓓 (e ⁻¹))
 i₂ , l₂ ← v₂ I (ι ∘ α) δ (≡-to-⊑ 𝓓 (e ⁻¹))
 k , m₁ , m₂ ← Directed-implies-weakly-directed 𝓓 δ i₁ i₂
 let n₁ = ι b₁     ⊑⟨ 𝓓 ⟩[ l₁ ]
          ι (α i₁) ⊑⟨ 𝓓 ⟩[ m₁ ]
          ι (α k)  ∎⟨ 𝓓 ⟩
 let n₂ = ι b₂     ⊑⟨ 𝓓 ⟩[ l₂ ]
          ι (α i₂) ⊑⟨ 𝓓 ⟩[ m₂ ]
          ι (α k)  ∎⟨ 𝓓 ⟩
 let wx = ≪-⊑-to-≪ 𝓓 u₁ n₁
 let wy = ≪-⊑-to-≪ 𝓓 u₂ n₂
 ∣ α k , wx , wy , wb k ∣
 where
  c : (d : ⟨ 𝓓 ⟩) → approximate-from-basis 𝓓 ι d
  c = pr₂ cd
  t₁ : ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ z
  t₁ = ≪-INT₁ 𝓓 cd x z u
  t₂ : ∃ b ꞉ B , y ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ z
  t₂ = ≪-INT₁ 𝓓 cd y z v

\end{code}

Back-up copy of the original:

≪-INT₂ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
         (x y z : ⟨ 𝓓 ⟩) → x ≪⟨ 𝓓 ⟩ z → y ≪⟨ 𝓓 ⟩ z
       → ∃ b ꞉ B , x ≪⟨ 𝓓 ⟩ ι b × y ≪⟨ 𝓓 ⟩ ι b × ι b ≪⟨ 𝓓 ⟩ z
≪-INT₂ 𝓓 {B} {ι} (≺ , c) x y z x≪z y≪z = do
 b₁ , x≪b₁ , b₁≪z ← ≪-INT₁ 𝓓 cd x z x≪z
 b₂ , y≪b₂ , b₂≪z ← ≪-INT₁ 𝓓 cd y z y≪z
 I , α , α≪z , δ , ∐α≡z ← c z
 i₁ , b₁⊑αi₁ ← b₁≪z I (ι ∘ α) δ (≡-to-⊑ 𝓓 (∐α≡z ⁻¹))
 i₂ , b₂⊑αi₂ ← b₂≪z I (ι ∘ α) δ (≡-to-⊑ 𝓓 (∐α≡z ⁻¹))
 k , αi₁⊑αk , αi₂⊑αk ← Directed-implies-weakly-directed 𝓓 δ i₁ i₂
 let b₁⊑αk = ι b₁     ⊑⟨ 𝓓 ⟩[ b₁⊑αi₁ ]
             ι (α i₁) ⊑⟨ 𝓓 ⟩[ αi₁⊑αk ]
             ι (α k)  ∎⟨ 𝓓 ⟩
 let b₂⊑αk = ι b₂     ⊑⟨ 𝓓 ⟩[ b₂⊑αi₂ ]
             ι (α i₂) ⊑⟨ 𝓓 ⟩[ αi₂⊑αk ]
             ι (α k)  ∎⟨ 𝓓 ⟩
 let x≪αk = ≪-⊑-to-≪ 𝓓 x≪b₁ b₁⊑αk
 let y≪αk = ≪-⊑-to-≪ 𝓓 y≪b₂ b₂⊑αk
 ∣ α k , x≪αk , y≪αk , α≪z k ∣
 where
  cd : is-a-basis 𝓓 ι
  cd = (≺ , c)

\begin{code}

≪ᴮ-INT₂ : (𝓓 : DCPO {𝓤} {𝓣}) {B : 𝓥 ̇ } {ι : B → ⟨ 𝓓 ⟩} (c : is-a-basis 𝓓 ι)
          (b₁ b₂ b₃ : B) → b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃ → b₂ ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃
        → ∃ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b₂ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃
≪ᴮ-INT₂ 𝓓 {B} {ι} c b₁ b₂ b₃ u v =
 ∥∥-functor γ (≪-INT₂ 𝓓 c (ι b₁) (ι b₂) (ι b₃)
               (≪ᴮ-to-≪ 𝓓 c b₁ b₃ u)
               (≪ᴮ-to-≪ 𝓓 c b₂ b₃ v))
  where
   γ : (Σ b ꞉ B , ι b₁ ≪⟨ 𝓓 ⟩ ι b × ι b₂ ≪⟨ 𝓓 ⟩ ι b × ι b  ≪⟨ 𝓓 ⟩ ι b₃)
     → Σ b ꞉ B , b₁ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b₂ ≪ᴮ⟨ 𝓓 ⟩[ c ] b × b  ≪ᴮ⟨ 𝓓 ⟩[ c ] b₃
   γ (b , x , y , z) = b , ≪-to-≪ᴮ 𝓓 c b₁ b x ,
                           ≪-to-≪ᴮ 𝓓 c b₂ b y ,
                           ≪-to-≪ᴮ 𝓓 c b  b₃ z

\end{code}
