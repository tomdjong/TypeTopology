Tom de Jong, 12 December 2019.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc -- hiding (⊥)

module AlgebraicLattice
        (fe₀ : funext 𝓤₀ 𝓤₀)
        -- (pe : PropExt)
        (pt : propositional-truncations-exist)
       where

-- open PropositionalTruncation pt hiding (_∨_)

open import Fin -- renaming (_∷_ to _,_)
open finiteness pt hiding (_∨_)

open import UF-Subsingletons -- hiding (⊥)
open import UF-Subsingletons-FunExt
-- open import UF-Retracts
open import UF-Miscelanea

open import Two-Properties
-- open import LPO fe
-- open import GenericConvergentSequence hiding (_⊑_)
open import NaturalsOrder

open import NaturalsAddition renaming (_+_ to _+'_)
-- open import NaturalNumbers-Properties

open import Lifting 𝓤₀ hiding (⊥)
open import UF-Equiv

-- We study Ω as a lattice

Ω₀ : 𝓤₁ ̇
Ω₀ = Ω 𝓤₀

Ω-≃-𝓛𝟙 : Ω₀ ≃ 𝓛 (𝟙{𝓤₀})
Ω-≃-𝓛𝟙 = qinveq f (g , gf , fg)
 where
  f : Ω₀ → 𝓛 𝟙
  f p = (p holds , unique-to-𝟙 , holds-is-prop p)
  g : 𝓛 𝟙 → Ω₀
  g (p , _ , i) = p , i
  fg : (l : 𝓛 𝟙) → f (g l) ≡ l
  fg (p , ϕ , i) = to-Σ-≡ (refl , γ)
   where
    γ : (unique-to-𝟙 , i) ≡ (ϕ , i)
    γ = to-Σ-≡ (dfunext fe₀ (λ x → 𝟙-is-prop (unique-to-𝟙 x) (ϕ x)) ,
                being-a-prop-is-a-prop fe₀ _ i)
  gf : (p : Ω₀) → g (f p) ≡ p
  gf p = refl

_⊑_ : Ω₀ → Ω₀ → 𝓤₀ ̇
p ⊑ q = p holds → q holds

∐ : {I : 𝓤₀ ̇ } (q : I → Ω₀) → Ω₀
∐ {I} q = ((∃ \(i : I) → (q i) holds) , ∥∥-is-a-prop)

is-directed : {I : 𝓤₀ ̇ } (q : I → Ω₀) → 𝓤₀ ̇
is-directed {I} q = ∥ I ∥ × ((i j : I) → ∃ \(k : I) → q i ⊑ q k × q j ⊑ q k)

is-directed-inhabited : {I : 𝓤₀ ̇ } (q : I → Ω₀)
                      → is-directed q
                      → ∥ I ∥
is-directed-inhabited q = pr₁

is-directed-order : {I : 𝓤₀ ̇ } (q : I → Ω₀)
                  → is-directed q
                  → ((i j : I) → ∃ \(k : I) → q i ⊑ q k × q j ⊑ q k)
is-directed-order q = pr₂

is-compact : (c : Ω₀) → 𝓤₁ ̇
is-compact c = (I : 𝓤₀ ̇ ) (q : I → Ω₀)
             → is-directed q
             → (c ⊑ ∐ q)
             → ∃ \(i : I) → (c ⊑ q i)

decidable-implies-compact : (p : Ω₀)
                          → decidable (p holds)
                          → is-compact p
decidable-implies-compact p (inl x) I q δ l = ∥∥-functor γ (l x)
 where
  γ : (Σ \i → (q i) holds) → Σ \i → p ⊑ q i
  γ (i , qi) = (i , λ _ → qi)
decidable-implies-compact p (inr y) I q δ l = ∥∥-functor γ (is-directed-inhabited q δ)
 where
  γ : I → Σ \i → p ⊑ q i
  γ i = (i , λ (x : p holds) → 𝟘-elim (y x))

compact-implies-decidable : (P : Ω₀)
                          → is-compact P
                          → decidable (P holds)
compact-implies-decidable P c = ∥∥-rec (decidability-of-prop-is-prop fe₀ (holds-is-prop P)) γ h
 where
  χ : 𝟙 + (P holds) → Ω₀
  χ (inl *) = ⊥
  χ (inr p) = ⊤
  γ : (Σ \i → P ⊑ χ i) → decidable (P holds)
  γ (inl * , l) = inr l
  γ (inr p , l) = inl p
  h : ∃ \i → P ⊑ (χ i)
  h = c (𝟙 + (P holds)) χ δ g
   where
    g : P ⊑ (∐ χ)
    g p = ∣ (inr p) , * ∣
    δ : is-directed χ
    δ = (∣ inl * ∣ , ε)
     where
      ε : (i j : 𝟙 + (P holds)) →
            (∃ \k → (pr₁ (χ i) → pr₁ (χ k)) × (pr₁ (χ j) → pr₁ (χ k)))
      ε (inl *) (inl *) = ∣ (inl *) , (id , id) ∣
      ε (inl *) (inr p) = ∣ (inr p) , ((λ _ → *) , id) ∣
      ε (inr p) j = ∣ inr p , (id , λ _ → *) ∣

⊤-is-compact : is-compact ⊤
⊤-is-compact = decidable-implies-compact ⊤ (inl *)

⊥-is-compact : is-compact ⊥
⊥-is-compact = decidable-implies-compact ⊥ (inr 𝟘-elim)

_∨_ : Ω₀ → Ω₀ → Ω₀
P ∨ Q = (∥ P holds + Q holds ∥ , ∥∥-is-a-prop)

∨-left : (P Q : Ω₀) → P ⊑ (P ∨ Q)
∨-left P Q p = ∣ inl p ∣

∨-right : (P Q : Ω₀) → Q ⊑ (P ∨ Q)
∨-right P Q q = ∣ inr q ∣

∨-is-join : (P Q R : Ω₀)
          → P ⊑ R
          → Q ⊑ R
          → (P ∨ Q) ⊑ R
∨-is-join P Q R l m = ∥∥-rec (holds-is-prop R) γ
 where
  γ : P holds + Q holds → R holds
  γ (inl p) = l p
  γ (inr q) = m q

⊑-trans : (P Q R : Ω₀) → P ⊑ Q → Q ⊑ R → P ⊑ R
⊑-trans P Q R l m = m ∘ l

∨-is-compact : (P Q : Ω₀)
             → is-compact P
             → is-compact Q
             → is-compact (P ∨ Q)
∨-is-compact P Q cP cQ I S δ l = do
  (i , a) ← cP I S δ lP
  (j , b) ← cQ I S δ lQ
  (k , u , v) ← is-directed-order S δ i j
  return (k , ∨-is-join P Q (S k)
              (⊑-trans P (S i) (S k) a u)
              (⊑-trans Q (S j) (S k) b v))
 where
  lP : P ⊑ ∐ S
  lP = ⊑-trans P (P ∨ Q) (∐ S) (∨-left P Q) l
  lQ : Q ⊑ ∐ S
  lQ = ⊑-trans Q (P ∨ Q) (∐ S) (∨-right P Q) l

{-
∥∥-rec ∥∥-is-a-prop γ (cP I S δ lP)
 where
  lP : P ⊑ ∐ S
  lP = ⊑-trans P (P ∨ Q) (∐ S) (∨-left P Q) l
  γ : (Σ \i → P ⊑ S i) → (∃ \i → (P ∨ Q) ⊑ S i)
  γ (i , a) = ∥∥-rec ∥∥-is-a-prop ϕ (cQ I S δ lQ)
   where
    lQ : Q ⊑ ∐ S
    lQ = ⊑-trans Q (P ∨ Q) (∐ S) (∨-right P Q) l
    ϕ : (Σ \j → Q ⊑ S j) → (∃ \j → (P ∨ Q) ⊑ S j)
    ϕ (j , b) = ∥∥-functor ψ (is-directed-order S δ i j)
     where
      ψ : (Σ \k → (S i ⊑ S k) × (S j ⊑ S k)) → (Σ \k → (P ∨ Q) ⊑ S k)
      ψ (k , u , v) = k , ∨-is-join P Q (S k) σ τ
       where
        σ : P ⊑ S k
        σ = ⊑-trans P (S i) (S k) a u
        τ : Q ⊑ S k
        τ = ⊑-trans Q (S j) (S k) b v
-}

{-
⊤-is-compact : is-compact ⊤
⊤-is-compact I q s l = ∥∥-functor γ u
 where
  u : ∐ q holds
  u = l *
  γ : (Σ \i → (q i) holds) → (Σ \i → ⊤ ⊑ q i)
  γ (i , h) = i , (λ _ → h)

⊥-is-compact : is-compact ⊥
⊥-is-compact I q s l = ∥∥-functor γ s
 where
  γ : I → Σ \i → ⊥ ⊑ q i
  γ i = i , 𝟘-elim
-}

⟨_⟩₁ : (ℕ → 𝟚) → 𝓤₀ ̇
⟨ α ⟩₁ = Σ \(n : ℕ) → α n ≡ ₁

ℕ∞ : 𝓤₀ ̇
ℕ∞ = Σ \(α : ℕ → 𝟚) → is-prop ⟨ α ⟩₁

ι : ℕ∞ → (ℕ → 𝟚)
ι = pr₁

⟨_⟩ : ℕ∞ → Ω₀
⟨ α ⟩ = ⟨ ι α ⟩₁ , pr₂ α

ℕ∞-at-most-one-₁ : (α : ℕ∞) (n m : ℕ)
                 → ι α n ≡ ₁
                 → ι α m ≡ ₁
                 → n ≡ m
ℕ∞-at-most-one-₁ α n m p q = ap pr₁ γ
 where
  u : Σ \(k : ℕ) → ι α k ≡ ₁
  u = n , p
  v : Σ \(k : ℕ) → ι α k ≡ ₁
  v = m , q
  γ : u ≡ v
  γ = pr₂ ⟨ α ⟩ u v

LPO-instance : ℕ∞ → 𝓤₀ ̇
LPO-instance α = decidable ⟨ ι α ⟩₁

LPO : 𝓤₀ ̇
LPO = (α : ℕ∞) → LPO-instance α

instance-of-LPO-is-subsingleton : (α : ℕ∞) → is-prop (LPO-instance α)
instance-of-LPO-is-subsingleton α =
 decidability-of-prop-is-prop fe₀ (holds-is-prop ⟨ α ⟩)

LPO-is-subsingleton : is-prop LPO
LPO-is-subsingleton = Π-is-prop fe₀ instance-of-LPO-is-subsingleton

⟨_⟩'₁ⁿ_ : ℕ∞ → ℕ → 𝓤₀ ̇
⟨ α ⟩'₁ⁿ n = Σ \(x : Fin' n) → ι α (pr₁ x) ≡ ₁

⟨_⟩'ⁿ_ : ℕ∞ → ℕ → Ω₀
⟨ α ⟩'ⁿ n = ((⟨ α ⟩'₁ⁿ n) , i)
 where
  i : is-prop (⟨ α ⟩'₁ⁿ n)
  i ((m , l) , p) ((m' , l') , p') = to-Σ-≡ (a , b)
   where
    a : (m , l) ≡ (m' , l')
    a = to-Σ-≡ (u , v)
     where
      u : m ≡ m'
      u = ℕ∞-at-most-one-₁ α m m' p p'
      v : transport (λ v → v < n) u l ≡ l'
      v = <-is-prop-valued _ n _ l'
    b : transport (λ x → ι α (pr₁ x) ≡ ₁) a p ≡ p'
    b = 𝟚-is-set _ p'

open import CompactTypes
open import DiscreteAndSeparated

⟨⟩'ⁿ-decidable : (α : ℕ∞) (n : ℕ) → decidable (⟨ α ⟩'₁ⁿ n)
⟨⟩'ⁿ-decidable α n =
 Fin'-Compact n (λ x → ι α (pr₁ x) ≡ ₁) (λ x → 𝟚-is-discrete (ι α (pr₁ x)) ₁)

⟨_⟩₁ⁿ_ : ℕ∞ → ℕ → 𝓤₀ ̇
⟨ α ⟩₁ⁿ n = (Σ \(m : ℕ) → (m ≤ n) × (ι α m ≡ ₁))

⟨_⟩ⁿ_ : ℕ∞ → ℕ → Ω₀
⟨ α ⟩ⁿ n = (⟨ α ⟩₁ⁿ n , i)
 where
  i : is-prop (⟨ α ⟩₁ⁿ n)
  i (m , p) (k , q) = to-Σ-≡ (a , b)
   where
    a : m ≡ k
    a = ℕ∞-at-most-one-₁ α m k (pr₂ p) (pr₂ q)
    b : transport (λ x → (x ≤ n) × (ι α x ≡ ₁)) a p ≡ q
    b = ×-is-prop (≤-is-prop-valued k n) 𝟚-is-set _ q

⟨⟩ⁿ-decidable : (α : ℕ∞) (n : ℕ) → decidable (⟨ α ⟩₁ⁿ n)
⟨⟩ⁿ-decidable α zero = 𝟚-equality-cases a b
 where
  a : ι α 0 ≡ ₀ → (⟨ α ⟩₁ⁿ 0) + ¬ (⟨ α ⟩₁ⁿ 0)
  a e = inr γ
   where
    γ : ⟨ α ⟩₁ⁿ 0 → 𝟘
    γ (0 , _ , e') = zero-is-not-one ϕ
     where
      ϕ = ₀     ≡⟨ e ⁻¹ ⟩
          ι α 0 ≡⟨ e' ⟩
          ₁     ∎
  b : ι α 0 ≡ ₁ → (⟨ α ⟩₁ⁿ 0) + ¬ (⟨ α ⟩₁ⁿ 0)
  b e = inl (0 , ≤-refl 0 , e)
⟨⟩ⁿ-decidable α (succ n) = cases u v IH
 where
  IH : decidable (⟨ α ⟩₁ⁿ n)
  IH = ⟨⟩ⁿ-decidable α n
  u : ⟨ α ⟩₁ⁿ n → (⟨ α ⟩₁ⁿ succ n) + ¬ (⟨ α ⟩₁ⁿ succ n)
  u (m , l , e) = inl (m , ≤-trans m n (succ n) l (≤-succ n) , e)
  v : ¬ (⟨ α ⟩₁ⁿ n) → (⟨ α ⟩₁ⁿ succ n) + ¬ (⟨ α ⟩₁ⁿ succ n)
  v h = 𝟚-equality-cases a b
   where
    a : ι α (succ n) ≡ ₀ → (⟨ α ⟩₁ⁿ succ n) + ¬ (⟨ α ⟩₁ⁿ succ n)
    a e = inr γ
     where
      γ : ⟨ α ⟩₁ⁿ succ n → 𝟘
      γ (m , l , e') = cases x y (≤-split m n l)
       where
        x : m ≤ n → 𝟘
        x l' = h (m , l' , e')
        y : m ≡ succ n → 𝟘
        y p = zero-is-not-one ϕ
         where
          ϕ = ₀            ≡⟨ e ⁻¹ ⟩
              ι α (succ n) ≡⟨ ap (ι α) (p ⁻¹) ⟩
              ι α m        ≡⟨ e' ⟩
              ₁            ∎
    b : ι α (succ n) ≡ ₁ → (⟨ α ⟩₁ⁿ succ n) + ¬ (⟨ α ⟩₁ⁿ succ n)
    b e = inl (succ n , ≤-refl (succ n) , e)

⟨⟩ᵤ-monotone : (α : ℕ∞) (m n : ℕ)
             → m ≤ n
             → (⟨ α ⟩ⁿ m) ⊑ (⟨ α ⟩ⁿ n)
⟨⟩ᵤ-monotone α m n h (k , l , e) = (k , ≤-trans k m n l h , e)

⟨⟩ᵤ-directed-order : (α : ℕ∞) (m n : ℕ)
                   → ∃ \(k : ℕ) → (⟨ α ⟩ⁿ m) ⊑ (⟨ α ⟩ⁿ k) × (⟨ α ⟩ⁿ n) ⊑ (⟨ α ⟩ⁿ k)
⟨⟩ᵤ-directed-order α m n = ∣ (m +' n , u , v) ∣
 where
  u : (⟨ α ⟩ⁿ m) ⊑ (⟨ α ⟩ⁿ (m +' n))
  u = ⟨⟩ᵤ-monotone α m (m +' n) (≤-+ m n)
  v : (⟨ α ⟩ⁿ n) ⊑ (⟨ α ⟩ⁿ (m +' n))
  v = ⟨⟩ᵤ-monotone α n (m +' n) (≤-+' m n)

⟨α⟩-compact-implies-LPO-instance : (α : ℕ∞) → is-compact ⟨ α ⟩ → LPO-instance α
⟨α⟩-compact-implies-LPO-instance α c = ∥∥-rec (instance-of-LPO-is-subsingleton α) γ h
 where
  q : ℕ → Ω₀
  q n = ⟨ α ⟩ⁿ n
  h : ∃ \n → ⟨ α ⟩ ⊑ q n
  h = c ℕ q (∣ zero ∣ , ⟨⟩ᵤ-directed-order α) t
   where
    t : ⟨ α ⟩ ⊑ ∐ q
    t (n , e) = ∣ (n , n , ≤-refl n , e) ∣
  γ : (Σ \n → ⟨ α ⟩ ⊑ q n) → LPO-instance α
  γ (n , l) = cases a b (⟨⟩ⁿ-decidable α n)
   where
    a : ⟨ α ⟩₁ⁿ n → LPO-instance α
    a (m , _ , e) = inl (m , e)
    b : ¬ (⟨ α ⟩₁ⁿ n) → LPO-instance α
    b h = inr (h ∘ l)

everything-compact-implies-LPO : ((p : Ω₀) → is-compact p) → LPO
everything-compact-implies-LPO C α =
 ⟨α⟩-compact-implies-LPO-instance α (C ⟨ α ⟩)

is-algebraic : 𝓤₁ ̇
is-algebraic = ((p : Ω₀) → ∃ \(I : 𝓤₀ ̇ ) → ∃ \(q : I → Ω₀)
             → ((i : I) → is-compact (q i)) × ((i : I) → q i ⊑ p) × (p holds ≡ ∐ q holds))

{-
algebraic-implies-LPO : is-algebraic → LPO
algebraic-implies-LPO A α = ∥∥-rec (instance-of-LPO-is-subsingleton α) γ h
 where
  h : ∃ \I → ∃ \q
    → ((i : I) → is-compact (q i))
    × ((i : I) → (q i) ⊑ ⟨ α ⟩)
    × (⟨ α ⟩ holds ≡ ∐ q holds)
  h = A ⟨ α ⟩
  γ : (Σ \I → (∃ \q
    → ((i : I) → is-compact (q i))
    × ((i : I) → q i ⊑ ⟨ α ⟩)
    × (⟨ α ⟩ holds ≡ ∐ q holds)))
    → LPO-instance α
  γ (I , g) = ∥∥-rec (instance-of-LPO-is-subsingleton α) ϕ g
   where
    ϕ : (Σ \q
      → ((i : I) → is-compact (q i))
      × ((i : I) → q i ⊑ ⟨ α ⟩)
      × (⟨ α ⟩ holds ≡ ∐ q holds))
      → LPO-instance α
    ϕ (q , c , l , e) = {!!}
     -- (i : I) → ∃ \n → q i ⊑ ∃ (m < n) → α m ≡ ₁
-}

{-
𝟚-equality-cases a b
   where
    a : ι α n ≡ ₀ → (Σ \m → ι α m ≡ ₁) + ¬ (Σ \m → ι α m ≡ ₁)
    a e = {!!}
    b : ι α n ≡ ₁ → (Σ \m → ι α m ≡ ₁) + ¬ (Σ \m → ι α m ≡ ₁)
    b e = inl (n , e)
-}

\end{code}

This uses GenericConvergentSequence, which is a bit awkward to use in this case.

⟨_⟩ : ℕ∞ → Ω₀
⟨ α ⟩ = ((Σ \(n : ℕ) → α ≡ under n) , γ)
 where
  γ : is-prop (Σ \n → α ≡ under n)
  γ (n , p) (m , q) = to-Σ-≡ (a , b)
   where
    a : n ≡ m
    a = under-lc (p ⁻¹ ∙ q)
    b : transport (λ - → α ≡ under -) a p ≡ q
    b = ℕ∞-is-set (fe 𝓤₀ 𝓤₀) _ _

≡₀-≡-under : (α : ℕ∞) (n : ℕ) → incl α n ≡ ₀ → α ≡ under n
≡₀-≡-under α zero = is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀)
≡₀-≡-under α (succ n) p = Succ-criterion (fe 𝓤₀ 𝓤₀) γ p
 where
  γ : incl α n ≡ ₁
  γ = 𝟚-equality-cases a b
   where
    a : incl α n ≡ ₀ → incl α n ≡ ₁
    a q = {!!}
    b : incl α n ≡ ₁ → incl α n ≡ ₁
    b = id


⟨_⟩'_ : ℕ∞ → ℕ → Ω₀
⟨ α ⟩' n = ((Σ \(m : ℕ) → (m ≤ n × (α ≡ under m))) , γ)
 where
  γ : is-prop (Σ \m → (m ≤ n × (α ≡ under m)))
  γ (m , _ , p) (k , _ , q) =
   to-Σ-≡
    ((under-lc (p ⁻¹ ∙ q)) ,
     (×-is-prop (≤-is-prop-valued k n) (ℕ∞-is-set (fe 𝓤₀ 𝓤₀)) _ _))

⟨⟩'-decidable : (α : ℕ∞) (n : ℕ) → decidable ((⟨ α ⟩' n) holds)
⟨⟩'-decidable α zero = 𝟚-equality-cases' {_} {_} {_} {incl α 0} a b
 where
  a : incl α 0 ≡ ₀ → (⟨ α ⟩' zero) holds
  a z = (0 , (≤-refl 0 , is-Zero-equal-Zero (fe 𝓤₀ 𝓤₀) z))
  b : incl α 0 ≡ ₁ → ¬ ((⟨ α ⟩' zero) holds)
  b o (0 , _ , e) = zero-is-not-one γ
   where
    γ = ₀           ≡⟨ refl ⟩
        incl Zero 0 ≡⟨ ap (λ - → incl - 0) (e ⁻¹) ⟩
        incl α 0    ≡⟨ o ⟩
        ₁           ∎
⟨⟩'-decidable α (succ n) = {!!} -- 𝟚-equality-cases' {_} {_} {_} {incl α (succ n)} a b
 where
  IH : decidable ((⟨ α ⟩' n) holds)
  IH = ⟨⟩'-decidable α n
  u : (⟨ α ⟩' n) holds →
        ((⟨ α ⟩' succ n) holds) + ¬ ((⟨ α ⟩' succ n) holds)
  u (m , l , e) = inl (m , (≤-trans m n (succ n) l (≤-succ n) , e))
  v : ¬ ((⟨ α ⟩' n) holds) →
        ((⟨ α ⟩' succ n) holds) + ¬ ((⟨ α ⟩' succ n) holds)
  v x = 𝟚-equality-cases' {_} {_} {_} {incl α (succ n)} a b
   where
    h : incl α n ≡ ₁
    h = 𝟚-equality-cases c d
     where
      c : incl α n ≡ ₀ → incl α n ≡ ₁
      c z = 𝟘-elim (x (n , ((≤-refl n) , {!!})))
      d : incl α n ≡ ₁ → incl α n ≡ ₁
      d = id
    a : incl α (succ n) ≡ ₀ → (⟨ α ⟩' succ n) holds
    a z = (succ n) , ((≤-refl (succ n)) , (Succ-criterion (fe 𝓤₀ 𝓤₀) {!!} z))
    b : incl α (succ n) ≡ ₁ → ¬ ((⟨ α ⟩' succ n) holds)
    b = {!!}

everything-compact-LPO : ((p : Ω₀) → is-compact p) → LPO
everything-compact-LPO C α = ∥∥-rec i γ h
 where
  q : ℕ → Ω 𝓤₀
  q n = ⟨ α ⟩' n
  h : ∃ \n → (⟨ α ⟩ holds → (q n) holds)
  h = C ⟨ α ⟩ ℕ q ∣ zero ∣ t
   where
    t : ⟨ α ⟩ holds → (∐ q) holds
    t (n , e) = ∣ (n , n , ((≤-refl n) , e)) ∣
  i : is-prop (⟨ α ⟩ holds + ¬ (⟨ α ⟩ holds))
  i = decidability-of-prop-is-prop (fe 𝓤₀ 𝓤₀) (pr₂ ⟨ α ⟩)
  γ : (Σ \n → ⟨ α ⟩ holds → q n holds)
    → (⟨ α ⟩ holds) + ¬ (⟨ α ⟩ holds)
  γ (n , f) = cases a b (⟨⟩'-decidable α n)
   where
    a : q n holds → (⟨ α ⟩ holds) + ¬ (⟨ α ⟩ holds)
    a (m , _ , e) = inl (m , e)
    b : ¬ (q n holds) → (⟨ α ⟩ holds) + ¬ (⟨ α ⟩ holds)
    b g = inr (λ x → g (f x))
