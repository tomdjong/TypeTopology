Tom de Jong
30-01-2020

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (_≈_)

module FreeDcpoFromPoset-2
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤} {𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe) -- universe where the index types for directedness
                        -- completeness live
       where

open import Poset fe
open import FreeDcpoFromPoset-1 pt fe 𝓥 public

open import UF-Quotient

open PropositionalTruncation pt

module FreeDcpoFromPoset-Setup-2
        {P : 𝓤 ̇ }
        (_≤_ : P → P → 𝓣 ̇ )
        ((is-set-P , ≤-prop-valued ,
          ≤-refl , ≤-trans , ≤-anti) : PosetAxioms.poset-axioms _≤_)
       where

 open FreeDcpoFromPoset-Setup-1 (_≤_) (is-set-P , ≤-prop-valued ,
          ≤-refl , ≤-trans , ≤-anti)

 open Quotient pt (λ 𝓤 𝓥 → fe)
               pe 𝓕 _≈_
               ≈-is-prop-valued
               ≈-is-reflexive
               ≈-is-symmetric
               ≈-is-transitive

 𝓕/≈ : 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
 𝓕/≈ = X/≈

 𝓕/≈-is-a-set : is-set 𝓕/≈
 𝓕/≈-is-a-set = X/≈-is-set

 _≼-to-Ω_ : 𝓕 → 𝓕 → Ω (𝓥 ⊔ 𝓣)
 f ≼-to-Ω g = (f ≼ g , ≼-is-prop-valued f g)

 ⊑-preparation : (f : 𝓕)
               → ∃! \(f' : (F : X/≈) → Ω (𝓥 ⊔ 𝓣)) → f' ∘ η ≡ _≼-to-Ω_ f
 ⊑-preparation f = universal-property (Ω (𝓥 ⊔ 𝓣))
                   (Ω-is-a-set fe pe) (_≼-to-Ω_ f) γ
  where
   γ : (g h : 𝓕) (e : g ≈ h) → _≼-to-Ω_ f g ≡ _≼-to-Ω_ f h
   γ g h e = to-subtype-≡ (λ _ → being-a-prop-is-a-prop fe)
                 (pe (≼-is-prop-valued f g) (≼-is-prop-valued f h)
                 (λ (u : f ≼ g) → ≼-is-transitive f g h u (≈-to-≼ g h e))
                 (λ (v : f ≼ h) → ≼-is-transitive f h g v (≈-to-≼' g h e)))

 _⊑-prep_ : 𝓕 → 𝓕/≈ → Ω (𝓥 ⊔ 𝓣)
 _⊑-prep_ f = ∃!-witness (⊑-preparation f)

 ⊑-preparation' : ∃! \(f' : 𝓕/≈ → 𝓕/≈ → Ω (𝓥 ⊔ 𝓣)) → f' ∘ η ≡ _⊑-prep_
 ⊑-preparation' = universal-property (𝓕/≈ → Ω (𝓥 ⊔ 𝓣))
                    (Π-is-set fe (λ _ → Ω-is-a-set fe pe))
                    _⊑-prep_ γ
  where
   γ : (f g : 𝓕) → f ≈ g → _⊑-prep_ f ≡ _⊑-prep_ g
   γ f g e = dfunext fe ψ
    where
     ψ : (F : 𝓕/≈) → f ⊑-prep F ≡ g ⊑-prep F
     ψ = η-induction (λ F → f ⊑-prep F ≡ g ⊑-prep F)
                     (λ _ → Ω-is-a-set fe pe)
                     ϕ
      where
       ϕ : (h : 𝓕) → f ⊑-prep η h ≡ g ⊑-prep η h
       ϕ h = f ⊑-prep η h ≡⟨ i ⟩
             f ≼-to-Ω h   ≡⟨ ii ⟩
             g ≼-to-Ω h   ≡⟨ iii ⟩
             g ⊑-prep η h ∎
        where
         i   = happly (∃!-is-witness (⊑-preparation f)) h
         ii  = to-subtype-≡ (λ _ → being-a-prop-is-a-prop fe) ρ
          where
           ρ : f ≼ h ≡ g ≼ h
           ρ = pe (≼-is-prop-valued f h) (≼-is-prop-valued g h)
               (≼-is-transitive g f h (≈-to-≼' f g e))
               (≼-is-transitive f g h (≈-to-≼ f g e))
         iii = (happly (∃!-is-witness (⊑-preparation g)) h) ⁻¹

 _⊑-to-Ω_ : 𝓕/≈ → 𝓕/≈ → Ω (𝓥 ⊔ 𝓣)
 _⊑-to-Ω_ = ∃!-witness ⊑-preparation'

 _⊑_ : 𝓕/≈ → 𝓕/≈ → 𝓥 ⊔ 𝓣 ̇
 F ⊑ G = pr₁ (F ⊑-to-Ω G)

 ⊑-is-prop-valued : (F G : 𝓕/≈) → is-prop (F ⊑ G)
 ⊑-is-prop-valued F G = pr₂ (F ⊑-to-Ω G)

 ⊑-≡-≼-Ω : {f g : 𝓕} → η f ⊑-to-Ω η g ≡ f ≼-to-Ω g
 ⊑-≡-≼-Ω {f} {g} = η f ⊑-to-Ω η g ≡⟨ i ⟩
                f ⊑-prep η g   ≡⟨ ii ⟩
                f ≼-to-Ω g ∎
  where
   i  = happly (happly (∃!-is-witness ⊑-preparation') f) (η g)
   ii = happly (∃!-is-witness (⊑-preparation f)) g

 ⊑-≡-≼ : {f g : 𝓕} → η f ⊑ η g ≡ f ≼ g
 ⊑-≡-≼ = ap pr₁ ⊑-≡-≼-Ω

 ⊑-to-≼ : {f g : 𝓕} → η f ⊑ η g → f ≼ g
 ⊑-to-≼ = transport id ⊑-≡-≼

 ≼-to-⊑ : {f g : 𝓕} → f ≼ g → η f ⊑ η g
 ≼-to-⊑ = transport id (⊑-≡-≼ ⁻¹)

 ⊑-is-reflexive : (F : 𝓕/≈) → F ⊑ F
 ⊑-is-reflexive = η-induction α β γ
  where
   α : 𝓕/≈ → 𝓥 ⊔ 𝓣 ̇
   α F = F ⊑ F
   β : (F : 𝓕/≈) → is-prop (F ⊑ F)
   β F = ⊑-is-prop-valued F F
   γ : (f : 𝓕) → η f ⊑ η f
   γ f = ≼-to-⊑ (≼-is-reflexive f)

 ⊑-is-transitive : (F G H : 𝓕/≈) → F ⊑ G → G ⊑ H → F ⊑ H
 ⊑-is-transitive = η-induction α β γ
  where
   c : (F G H : 𝓕/≈) → is-prop (F ⊑ G → G ⊑ H → F ⊑ H)
   c F G H = Π-is-prop fe
             (λ u → Π-is-prop fe
             (λ v → ⊑-is-prop-valued F H))
   α : 𝓕/≈ → 𝓥 ⁺ ⊔ 𝓣 ⁺ ⊔ 𝓤 ̇
   α F = (G H : 𝓕/≈) → F ⊑ G → G ⊑ H → F ⊑ H
   β : (F : 𝓕/≈) → is-prop (α F)
   β F = Π-is-prop fe
         (λ G → Π-is-prop fe
         (λ H → c F G H))
   γ : (f : 𝓕) → α (η f)
   γ f = η-induction σ τ ρ
    where
     σ : 𝓕/≈ → (𝓥 ⁺) ⊔ (𝓣 ⁺) ⊔ 𝓤 ̇
     σ G = (H : 𝓕/≈) → η f ⊑ G → G ⊑ H → η f ⊑ H
     τ : (G : 𝓕/≈) → is-prop (σ G)
     τ G = Π-is-prop fe
           λ H → c (η f) G H
     ρ : (g : 𝓕) → σ (η g)
     ρ g = η-induction ϕ ψ χ
      where
       ϕ : 𝓕/≈ → 𝓥 ⊔ 𝓣 ̇
       ϕ H = η f ⊑ η g → η g ⊑ H → η f ⊑ H
       ψ : (H : 𝓕/≈) → is-prop (ϕ H)
       ψ H = c (η f) (η g) H
       χ : (h : 𝓕) → ϕ (η h)
       χ h u v = ≼-to-⊑ (≼-is-transitive f g h (⊑-to-≼ u) (⊑-to-≼ v))

 ⊑-is-antisymmetric : (F G : 𝓕/≈) → F ⊑ G → G ⊑ F → F ≡ G
 ⊑-is-antisymmetric = η-induction α β γ
  where
   c : (F G : 𝓕/≈) → is-prop (F ⊑ G → G ⊑ F → F ≡ G)
   c F G = Π-is-prop fe
           (λ u → Π-is-prop fe
           (λ v → 𝓕/≈-is-a-set))
   α : 𝓕/≈ → (𝓥 ⁺) ⊔ (𝓣 ⁺) ⊔ 𝓤 ̇
   α F = (G : 𝓕/≈) → F ⊑ G → G ⊑ F → F ≡ G
   β : (F : 𝓕/≈) → is-prop (α F)
   β F = Π-is-prop fe
         (λ G → c F G)
   γ : (f : 𝓕) → α (η f)
   γ f = η-induction σ ρ τ
    where
     σ : 𝓕/≈ → (𝓥 ⁺) ⊔ (𝓣 ⁺) ⊔ 𝓤 ̇
     σ G = η f ⊑ G → G ⊑ η f → η f ≡ G
     ρ : (G : X/≈) → is-prop (σ G)
     ρ G = c (η f) G
     τ : (g : 𝓕) → σ (η g)
     τ g u v = η-equiv-equal (⊑-to-≼ u , ⊑-to-≼ v)

\end{code}
