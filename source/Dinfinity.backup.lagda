Tom de Jong, 29 April 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module Dinfinity
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓤 : Universe)
        (pe : propext 𝓤)
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓤
open import DcpoBasics pt fe 𝓤
open import DcpoLifting pt fe 𝓤 pe
open import DcpoExponential pt fe 𝓤

open import Poset fe

𝓓 : ℕ → DCPO⊥ {𝓤 ⁺} {𝓤 ⁺}
𝓓 zero     = 𝓛-DCPO⊥ {𝓤} {𝟙{𝓤}} (props-are-sets 𝟙-is-prop)
𝓓 (succ n) = 𝓓 n ⟹ᵈᶜᵖᵒ⊥ 𝓓 n

𝓓-diagram : (n : ℕ) → DCPO[ 𝓓 n ⁻  , 𝓓 (succ n) ⁻ ]
                    × DCPO[ 𝓓 (succ n) ⁻ , 𝓓 n ⁻   ]
𝓓-diagram zero = (e₀ , e₀-continuity) , p₀ , p₀-continuity
 where
  e₀ : ⟨ 𝓓 0 ⁻ ⟩ → ⟨ 𝓓 1 ⁻ ⟩
  e₀ x = (λ y → x) , (constant-functions-are-continuous (𝓓 0 ⁻) (𝓓 0 ⁻) x)
  e₀-continuity : is-continuous (𝓓 0 ⁻) (𝓓 1 ⁻) e₀
  e₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → e₀ (α i) ⊑⟨ (𝓓 1 ⁻) ⟩ e₀ (∐ (𝓓 0 ⁻) δ)
    ub i y =  α i          ⊑⟨ 𝓓 0 ⁻ ⟩[ ∐-is-upperbound (𝓓 0 ⁻) δ i ]
              ∐ (𝓓 0 ⁻) δ  ∎⟨ 𝓓 0 ⁻ ⟩
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 1 ⁻))
                  (e₀ (∐ (𝓓 0 ⁻) δ)) (λ x → e₀ (α x))
    lb-of-ubs (g , c) ub y =
     ∐-is-lowerbound-of-upperbounds (𝓓 0 ⁻) δ (g y) (λ i → ub i y)
  p₀ : ⟨ 𝓓 1 ⁻ ⟩ → ⟨ 𝓓 0 ⁻ ⟩
  p₀ (f , c) = f (⊥ (𝓓 0))
  p₀-continuity : is-continuous (𝓓 1 ⁻) (𝓓 0 ⁻) p₀
  p₀-continuity I α δ = ub , lb-of-ubs
   where
    ub : (i : I) → p₀ (α i) ⊑⟨ 𝓓 0 ⁻ ⟩ p₀ (∐ (𝓓 1 ⁻) {I} {α} δ)
    ub i = ∐-is-upperbound (𝓓 1 ⁻) {I} {α} δ i (⊥ (𝓓 0))
    lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order (𝓓 0 ⁻))
                  (p₀ (∐ (𝓓 1 ⁻) {I} {α} δ)) (λ x → p₀ (α x))
    lb-of-ubs y ub =
     ∐-is-lowerbound-of-upperbounds (𝓓 0 ⁻) ε y ub
      where
       ε : is-Directed (𝓓 0 ⁻) (pointwise-family (𝓓 0 ⁻) (𝓓 0 ⁻) α (⊥ (𝓓 0)))
       ε = pointwise-family-is-directed (𝓓 0 ⁻) (𝓓 0 ⁻) α δ (⊥ (𝓓 0))
𝓓-diagram (succ n) = (e , e-continuity) , (p , p-continuity)
 where
  IH : DCPO[ 𝓓 n ⁻ , 𝓓 (succ n) ⁻ ] × DCPO[ 𝓓 (succ n) ⁻ , 𝓓 n ⁻ ]
  IH = 𝓓-diagram n
  eₙ : DCPO[ 𝓓 n ⁻ , 𝓓 (succ n) ⁻ ]
  eₙ = pr₁ IH
  pₙ : DCPO[ 𝓓 (succ n) ⁻ , 𝓓 n ⁻ ]
  pₙ = pr₂ IH
  e : ⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 (succ (succ n)) ⟫
  e f = DCPO-∘ (𝓓 (succ n) ⁻) (𝓓 n ⁻) (𝓓 (succ n) ⁻) pₙ h
   where
    h : DCPO[ 𝓓 n ⁻ , 𝓓 (succ n) ⁻ ]
    h = DCPO-∘ (𝓓 n ⁻) (𝓓 n ⁻) (𝓓 (succ n) ⁻) f eₙ
  e-continuity : is-continuous (𝓓 (succ n) ⁻) (𝓓 (succ (succ n)) ⁻) e
  e-continuity = ∘-is-continuous
                  (𝓓 (succ n) ⁻)
                  ((𝓓 n ⁻) ⟹ᵈᶜᵖᵒ (𝓓 (succ n) ⁻))
                  (𝓓 (succ (succ n)) ⁻)
                  (λ f → DCPO-∘ (𝓓 n ⁻) (𝓓 n ⁻) (𝓓 (succ n) ⁻) f eₙ)
                  (DCPO-∘ (𝓓 (succ n) ⁻) (𝓓 n ⁻) (𝓓 (succ n) ⁻) pₙ)
                  (DCPO-∘-is-continuous₂ (𝓓 n ⁻) (𝓓 n ⁻) (𝓓 (succ n) ⁻) eₙ)
                  (DCPO-∘-is-continuous₁ (𝓓 (succ n) ⁻) (𝓓 n ⁻)
                   (𝓓 (succ n) ⁻) pₙ)
  p : ⟪ 𝓓 (succ (succ n)) ⟫ → ⟪ 𝓓 (succ n) ⟫
  p f = DCPO-∘ (𝓓 n ⁻) (𝓓 (succ n) ⁻) (𝓓 n ⁻) eₙ h
   where
    h : DCPO[ 𝓓 (succ n) ⁻ , 𝓓 n ⁻ ]
    h = DCPO-∘ (𝓓 (succ n) ⁻) (𝓓 (succ n) ⁻) (𝓓 n ⁻) f pₙ
  p-continuity : is-continuous (𝓓 (succ (succ n)) ⁻) (𝓓 (succ n) ⁻) p
  p-continuity = ∘-is-continuous
                  (𝓓 (succ (succ n)) ⁻)
                  ((𝓓 n ⁻) ⟹ᵈᶜᵖᵒ (𝓓 (succ n) ⁻))
                  (𝓓 (succ n) ⁻)
                  (DCPO-∘ (𝓓 n ⁻) (𝓓 (succ n) ⁻) (𝓓 (succ n) ⁻) eₙ)
                  (λ f → DCPO-∘ (𝓓 n ⁻) (𝓓 (succ n) ⁻) (𝓓 n ⁻) f pₙ)
                  (DCPO-∘-is-continuous₁ (𝓓 n ⁻) (𝓓 (succ n) ⁻)
                   (𝓓 (succ n) ⁻) eₙ)
                  (DCPO-∘-is-continuous₂ (𝓓 n ⁻) (𝓓 (succ n) ⁻) (𝓓 n ⁻) pₙ)

p : (n : ℕ) → DCPO[ 𝓓 (succ n) ⁻ , 𝓓 n ⁻ ]
p n = pr₂ (𝓓-diagram n)

e : (n : ℕ) → DCPO[ 𝓓 n ⁻ , 𝓓 (succ n) ⁻ ]
e n = pr₁ (𝓓-diagram n)

⟨p⟩ : (n : ℕ) → ⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 n ⟫
⟨p⟩ n = underlying-function (𝓓 (succ n) ⁻) (𝓓 n ⁻) (p n)

⟨e⟩ : (n : ℕ) → ⟪ 𝓓 n ⟫ → ⟪ 𝓓 (succ n) ⟫
⟨e⟩ n = underlying-function (𝓓 n ⁻) (𝓓 (succ n) ⁻) (e n)

p-is-strict : (n : ℕ) → ⟨p⟩ n (⊥ (𝓓 (succ n))) ≡ ⊥ (𝓓 n)
p-is-strict zero = refl
p-is-strict (succ n) =
 to-subtype-≡ (λ f → being-continuous-is-a-prop (𝓓 n ⁻) (𝓓 n ⁻) f) (dfunext fe γ)
  where
   IH : ⟨p⟩ n (⊥ (𝓓 (succ n))) ≡ ⊥ (𝓓 n)
   IH = p-is-strict n
   con : ⟪ 𝓓 (succ n) ⟫ → ⟪ 𝓓 (succ n) ⟫
   con y = ⊥ (𝓓 (succ n))
   γ : (x : ⟪ 𝓓 n ⟫) → ⟨p⟩ n (con (⟨e⟩ n x)) ≡ ⊥ (𝓓 n)
   γ x = IH

𝓓∞ : DCPO⊥ {𝓤 ⁺} {𝓤 ⁺}
𝓓∞ = (X , _⊑_ , pa , dc) , ⊥-seq , ⊥-seq-is-least
 where
  X : 𝓤 ⁺ ̇
  X = Σ σ ꞉ ((n : ℕ) → ⟪ 𝓓 n ⟫) , ((n : ℕ) → ⟨p⟩ n (σ (succ n)) ≡ σ n)
  ⦅_⦆ : X → ((n : ℕ) → ⟪ 𝓓 n ⟫)
  ⦅_⦆ = pr₁
  p-equality : (σ : X) (n : ℕ) → ⟨p⟩ n (⦅ σ ⦆ (succ n)) ≡ ⦅ σ ⦆ n
  p-equality = pr₂
  _⊑_ : X → X → 𝓤 ⁺ ̇
  σ ⊑ τ = (n : ℕ) → ⦅ σ ⦆ n ⊑⟨ 𝓓 n ⁻ ⟩ ⦅ τ ⦆ n
  ⊥-seq : X
  ⊥-seq = (λ n → ⊥ (𝓓 n)) , p-is-strict
  ⊥-seq-is-least : is-least _⊑_ ⊥-seq
  ⊥-seq-is-least σ n = ⊥-is-least (𝓓 n) (⦅ σ ⦆ n)
  pa : PosetAxioms.poset-axioms _⊑_
  pa = sl , pv , r , t , a
   where
    open PosetAxioms {_} {_} {X} _⊑_
    sl : is-set X
    sl = subsets-of-sets-are-sets _ _
          (Π-is-set fe (λ n → sethood (𝓓 n ⁻)))
          (Π-is-prop fe (λ n → sethood (𝓓 n ⁻)))
    pv : is-prop-valued
    pv σ τ = Π-is-prop fe (λ n → prop-valuedness (𝓓 n ⁻) (⦅ σ ⦆ n) (⦅ τ ⦆ n))
    r : is-reflexive
    r σ n = reflexivity (𝓓 n ⁻) (⦅ σ ⦆ n)
    a : is-antisymmetric
    a σ τ l k = to-subtype-≡ (λ _ → Π-is-prop fe (λ n → sethood (𝓓 n ⁻)))
                 (dfunext fe (λ n → antisymmetry (𝓓 n ⁻) (⦅ σ ⦆ n) (⦅ τ ⦆ n)
                                     (l n) (k n)))
    t : is-transitive
    t σ τ ρ l k n = transitivity (𝓓 n ⁻) (⦅ σ ⦆ n) (⦅ τ ⦆ n) (⦅ ρ ⦆ n)
                     (l n) (k n)
  dc : is-directed-complete _⊑_
  dc I α δ = σ , ub , lb-of-ubs
   where
    β : (n : ℕ) → I → ⟪ 𝓓 n ⟫
    β n i = ⦅ α i ⦆ n
    ε : (n : ℕ) → is-Directed (𝓓 n ⁻) (β n)
    ε n = (directed-implies-inhabited _⊑_ α δ) , γ
     where
      γ : is-weakly-directed (underlying-order (𝓓 n ⁻)) (β n)
      γ i j = ∥∥-functor g (directed-implies-weakly-directed _⊑_ α δ i j)
       where
        g : (Σ k ꞉ I , (α i ⊑ α k) × (α j ⊑ α k))
          → (Σ k ꞉ I , (β n i ⊑⟨ 𝓓 n ⁻ ⟩ β n k) × (β n j ⊑⟨ 𝓓 n ⁻ ⟩ β n k) )
        g (k , l , m) = k , l n , m n
    σ : X
    σ = (λ n → ∐ (𝓓 n ⁻) (ε n)) , φ
     where
      φ : (n : ℕ) → ⟨p⟩ n (∐ (𝓓 (succ n) ⁻) (ε (succ n))) ≡ ∐ (𝓓 n ⁻) (ε n)
      φ n = ⟨p⟩ n (∐ (𝓓 (succ n) ⁻) (ε (succ n))) ≡⟨ eq₁ ⟩
            ∐ (𝓓 n ⁻) {I} {⟨p⟩ n ∘ β (succ n)} ε' ≡⟨ eq₂ ⟩
            ∐ (𝓓 n ⁻) {I} {β n} ε''               ≡⟨ eq₃ ⟩
            ∐ (𝓓 n ⁻) {I} {β n} (ε n)             ∎
       where
        ε' : is-Directed (𝓓 n ⁻) (⟨p⟩ n ∘ β (succ n))
        ε' = image-is-directed' (𝓓 (succ n) ⁻) (𝓓 n ⁻) (p n) (ε (succ n))
        h : ⟨p⟩ n ∘ β (succ n) ≡ β n
        h = dfunext fe (λ i → p-equality (α i) n)
        ε'' : is-Directed (𝓓 n ⁻) (β n)
        ε'' = transport (is-Directed (𝓓 n ⁻)) h ε'
        eq₁ = continuous-∐-≡ (𝓓 (succ n) ⁻) (𝓓 n ⁻) (p n)
               {I} {β (succ n)} (ε (succ n))
        eq₂ = ∐-family-≡ (𝓓 n ⁻) (⟨p⟩ n ∘ β (succ n)) (β n) h ε'
        eq₃ = ∐-independent-of-directedness-witness (𝓓 n ⁻) ε'' (ε n)
    ub : (i : I) → α i ⊑ σ
    ub i n = ∐-is-upperbound (𝓓 n ⁻) (ε n) i
    lb-of-ubs : is-lowerbound-of-upperbounds _⊑_ σ α
    lb-of-ubs τ ub n = ∐-is-lowerbound-of-upperbounds (𝓓 n ⁻) (ε n) (⦅ τ ⦆ n)
                        (λ i → ub i n)

⦅_⦆ : ⟪ 𝓓∞ ⟫ → (n : ℕ) → ⟪ 𝓓 n ⟫
⦅_⦆ = pr₁

⟨p∞⟩ : (n : ℕ) → ⟪ 𝓓∞ ⟫ → ⟪ 𝓓 n ⟫
⟨p∞⟩ n σ = ⦅ σ ⦆ n

p∞ : (n : ℕ) → DCPO[ 𝓓∞ ⁻ , 𝓓 n ⁻ ]
p∞ n = (⟨p∞⟩ n) , {!!}

open import NaturalsAddition renaming (_+_ to _+'_)
open import NaturalsOrder
open import NaturalNumbers-Properties

⟨e-up⟩ : (n m k : ℕ) → (m ≡ n +' k) → ⟪ 𝓓 n ⟫ → ⟪ 𝓓 m ⟫
⟨e-up⟩ n n zero refl = id
⟨e-up⟩ n .(succ (n +' k)) (succ k) refl = ⟨e⟩ (n +' k) ∘ IH
 where
  IH : ⟪ 𝓓 n ⟫ → ⟪ 𝓓 (n +' k) ⟫
  IH = ⟨e-up⟩ n (n +' k) k refl

⟨e-up⟩-succ-lemma : (n m k : ℕ) (eq : succ m ≡ n +' succ k)
                  → ⟨e-up⟩ n (succ m) (succ k) eq
                  ≡ ⟨e⟩ m ∘ ⟨e-up⟩ n m k (succ-lc eq)
⟨e-up⟩-succ-lemma = {!!}

⟨p-down⟩ : (n m k : ℕ) → (m ≡ n +' k) → ⟪ 𝓓 m ⟫ → ⟪ 𝓓 n ⟫
⟨p-down⟩ n n zero refl = id
⟨p-down⟩ n .(succ (n +' k)) (succ k) refl = IH ∘ ⟨p⟩ (n +' k)
 where
  IH : ⟪ 𝓓 (n +' k) ⟫ → ⟪ 𝓓 n ⟫
  IH = ⟨p-down⟩ n (n +' k) k refl

⟨e∞⟩ : (n : ℕ) → ⟪ 𝓓 n ⟫ → ⟪ 𝓓∞ ⟫
⟨e∞⟩ n x = σ , φ
 where
  σ : (m : ℕ) → ⟪ 𝓓 m ⟫
  σ m = γ (<-decidable n m)
   where
    γ : decidable (n < m) → ⟪ 𝓓 m ⟫
    γ (inl l) = ⟨e-up⟩ n m k eq x
     where
      s : Σ k ꞉ ℕ , k +' n ≡ m
      s = subtraction n m (<-coarser-than-≤ n m l)
      k : ℕ
      k = pr₁ s
      eq = m      ≡⟨ (pr₂ s) ⁻¹ ⟩
           k +' n ≡⟨ addition-commutativity k n ⟩
           n +' k ∎
    γ (inr l) = ⟨p-down⟩ m n k eq x
     where
      l' : n ≥ m
      l' = not-less-bigger-or-equal m n l
      s : Σ k ꞉ ℕ , k +' m ≡ n
      s = subtraction m n l'
      k : ℕ
      k = pr₁ s
      eq = n      ≡⟨ (pr₂ s) ⁻¹ ⟩
           k +' m ≡⟨ addition-commutativity k m ⟩
           m +' k ∎
  φ : (m : ℕ) → ⟨p⟩ m (σ (succ m)) ≡ σ m
  φ m = γ (<-decidable n (succ m))
   where
    γ : decidable (n < (succ m)) → ⟨p⟩ m (σ (succ m)) ≡ σ m
    γ (inl l) = ⟨p⟩ m (σ (succ m)) ≡⟨ {!!} ⟩
                ⟨p⟩ m (⟨e-up⟩ n (succ m) (succ {!!}) {!!} x) ≡⟨ ap (⟨p⟩ m) (happly (⟨e-up⟩-succ-lemma n m {!!} {!!}) x) ⟩
                ⟨p⟩ m ((⟨e⟩ m ∘ ⟨e-up⟩ n m {!!} (succ-lc {!!})) x) ≡⟨ {!!} ⟩
                σ m ∎
    γ (inr l) = {!!}

\end{code}
