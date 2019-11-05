Martin Escardo, 24th January 2019.

Voedvodsky (Types'2011) considered resizing rules for a type theory
for univalent foundations. These rules govern the syntax of the formal
system, and hence are of a meta-mathematical nature.

Here we instead formulate, in our type theory without such rules, a
mathematical resizing principle. This principle is provable in the
system with Voevodsky's rules. But we don't postulate this principle
as an axiom. Instead, we use it an assumption, when needed, or as a
conclusion, when it follows from stronger principles, such as excluded
middle.

The consistency of the resizing rules is an open problem at the time
of writing (30th January 2018), but the resizing principle is
consistent relative to ZFC with Grothendieck universes, because it
follows from excluded middle, which is known to be validated by the
simplicial-set model (assuming classical logic in its development).

We develop some consequences of propositional resizing here, such as
the fact that every universe is a retract of any higher universe,
where the section is an embedding (its fibers are all propositions),
which seems to be a new result.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Resizing where

open import SpartanMLTT

open import UF-Base
open import UF-FunExt
open import UF-Subsingletons
open import UF-Subsingletons-FunExt
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-Retracts
open import UF-Embeddings
open import UF-EquivalenceExamples
open import UF-ExcludedMiddle
open import UF-Univalence
open import UF-UA-FunExt
open import UF-UniverseEmbedding
open import UF-PropIndexedPiSigma
open import UF-PropTrunc

open import LawvereFPT

\end{code}

We say that a type X has size 𝓥 if it is equivalent to a type in the
universe 𝓥:

\begin{code}

_has-size_ : 𝓤 ̇ → (𝓥 : Universe) → 𝓥 ⁺  ⊔ 𝓤 ̇
X has-size 𝓥 = Σ \(Y : 𝓥 ̇ ) → Y ≃ X

propositional-resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥)⁺ ̇
propositional-resizing 𝓤 𝓥 = (P : 𝓤 ̇ ) → is-prop P → P has-size 𝓥

\end{code}

Propositional resizing from a universe to a higher universe just holds, of course:

\begin{code}

resize-up : (X : 𝓤 ̇ ) → X has-size (𝓤 ⊔ 𝓥)
resize-up {𝓤} {𝓥} X = lift 𝓥 X , lift-≃ 𝓥 X

resize-up-proposition : propositional-resizing 𝓤 (𝓤 ⊔ 𝓥)
resize-up-proposition {𝓤} {𝓥} P i = resize-up {𝓤} {𝓥} P

\end{code}

We use the following to work with propositional resizing more abstractly:

\begin{code}

resize           : propositional-resizing 𝓤 𝓥 → (P : 𝓤 ̇ ) (i : is-prop P) → 𝓥 ̇
resize-is-a-prop : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P) → is-prop (resize ρ P i)
to-resize        : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P) → P → resize ρ P i
from-resize      : (ρ : propositional-resizing 𝓤 𝓥) (P : 𝓤 ̇ ) (i : is-prop P) → resize ρ P i → P

resize         ρ P i   = pr₁ (ρ P i)
resize-is-a-prop ρ P i = equiv-to-prop (pr₂ (ρ P i)) i
to-resize      ρ P i   = eqtofun (≃-sym(pr₂ (ρ P i)))
from-resize    ρ P i   = eqtofun (pr₂ (ρ P i))

Propositional-resizing : 𝓤ω
Propositional-resizing = {𝓤 𝓥 : Universe} → propositional-resizing 𝓤 𝓥

\end{code}

Propositional resizing is consistent, because it is implied by
excluded middle, which is consistent (with or without univalence):

\begin{code}

EM-gives-PR : EM 𝓤 → propositional-resizing 𝓤 𝓥
EM-gives-PR {𝓤} {𝓥} em P i = Q (em P i) , e
 where
   Q : decidable P → 𝓥 ̇
   Q (inl p) = 𝟙
   Q (inr n) = 𝟘
   j : (d : decidable P) → is-prop (Q d)
   j (inl p) = 𝟙-is-prop
   j (inr n) = 𝟘-is-prop
   f : (d : decidable P) → P → Q d
   f (inl p) p' = *
   f (inr n) p  = 𝟘-elim (n p)
   g : (d : decidable P) → Q d → P
   g (inl p) q = p
   g (inr n) q = 𝟘-elim q
   e : Q (em P i) ≃ P
   e = logically-equivalent-props-are-equivalent (j (em P i)) i (g (em P i)) (f (em P i))

\end{code}

To show that the axiom of propositional resizing is itself a
proposition, we use univalence here (and there is a proof with weaker
hypotheses below).

\begin{code}

has-size-is-a-prop : Univalence → (X : 𝓤 ̇ ) (𝓥 :  Universe)
                   → is-prop (X has-size 𝓥)
has-size-is-a-prop {𝓤} ua X 𝓥 = c
 where
  fe : FunExt
  fe = FunExt-from-Univalence ua
  a : (Y : 𝓥 ̇ ) → (Y ≃ X) ≃ (lift 𝓤 Y ≡ lift 𝓥 X)
  a Y = (Y ≃ X)                ≃⟨ Eq-Eq-cong fe (≃-sym (lift-≃ 𝓤 Y)) (≃-sym (lift-≃ 𝓥 X)) ⟩
        (lift 𝓤 Y ≃ lift 𝓥 X)  ≃⟨ ≃-sym (is-univalent-≃ (ua (𝓤 ⊔ 𝓥)) _ _) ⟩
        (lift 𝓤 Y ≡ lift 𝓥 X)  ■
  b : (Σ \(Y : 𝓥 ̇ ) → Y ≃ X) ≃ (Σ \(Y : 𝓥 ̇ ) → lift 𝓤 Y ≡ lift 𝓥 X)
  b = Σ-cong a
  c : is-prop (Σ \(Y : 𝓥 ̇ ) → Y ≃ X)
  c = equiv-to-prop b (lift-is-embedding ua (lift 𝓥 X))

propositional-resizing-is-a-prop : Univalence → is-prop (propositional-resizing 𝓤 𝓥)
propositional-resizing-is-a-prop {𝓤} {𝓥} ua =  Π-is-prop (fe (𝓤 ⁺) (𝓥 ⁺ ⊔ 𝓤))
                                                (λ P → Π-is-prop (fe 𝓤 (𝓥 ⁺ ⊔ 𝓤))
                                                (λ i → has-size-is-a-prop ua P 𝓥))
 where
  fe : FunExt
  fe = FunExt-from-Univalence ua

\end{code}

And here is a proof that the axiom of propositional resizing is itself
a proposition using propositional and functional extensionality
instead of univalence:

\begin{code}

prop-has-size-is-a-prop : PropExt
                        → FunExt
                        → (P : 𝓤 ̇ )
                        → is-prop P
                        → (𝓥 :  Universe) → is-prop (P has-size 𝓥)
prop-has-size-is-a-prop {𝓤} pe fe P i 𝓥 = c
 where
  j : is-prop (lift 𝓥 P)
  j = equiv-to-prop (lift-≃ 𝓥 P) i
  a : (Y : 𝓥 ̇ ) → (Y ≃ P) ≃ (lift 𝓤 Y ≡ lift 𝓥 P)
  a Y = (Y ≃ P)                ≃⟨ Eq-Eq-cong fe (≃-sym (lift-≃ 𝓤 Y)) (≃-sym (lift-≃ 𝓥 P)) ⟩
        (lift 𝓤 Y ≃ lift 𝓥 P)  ≃⟨ ≃-sym (prop-univalent-≃ (pe (𝓤 ⊔ 𝓥)) (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) (lift 𝓤 Y) (lift 𝓥 P) j) ⟩
        (lift 𝓤 Y ≡ lift 𝓥 P)  ■
  b : (Σ \(Y : 𝓥 ̇ ) → Y ≃ P) ≃ (Σ \(Y : 𝓥 ̇ ) → lift 𝓤 Y ≡ lift 𝓥 P)
  b = Σ-cong a
  c : is-prop (Σ \(Y : 𝓥 ̇ ) → Y ≃ P)
  c = equiv-to-prop b (prop-fiber-lift pe fe (lift 𝓥 P) j)

propositional-resizing-is-a-prop' : PropExt → FunExt → is-prop (propositional-resizing 𝓤 𝓥)
propositional-resizing-is-a-prop' {𝓤} {𝓥} pe fe =  Π-is-prop (fe (𝓤 ⁺) (𝓥 ⁺ ⊔ 𝓤))
                                                     (λ P → Π-is-prop (fe 𝓤 (𝓥 ⁺ ⊔ 𝓤))
                                                     (λ i → prop-has-size-is-a-prop pe fe P i 𝓥))
\end{code}

Impredicativity. We begin with this strong notion, which says that the
type Ω 𝓤 of truth values in the universe 𝓤 has a copy in any successor
universe (i.e. in all universes except the first).

\begin{code}

Ω⁺-resizing : (𝓤 : Universe) → 𝓤ω
Ω⁺-resizing 𝓤 = (𝓥 : Universe) → (Ω 𝓤) has-size (𝓥 ⁺)

Ω⁺-resizing-from-pr-pe-fe : Propositional-resizing → PropExt → FunExt
                          → Ω⁺-resizing 𝓤
Ω⁺-resizing-from-pr-pe-fe {𝓤} ρ pe fe 𝓥 = Ω 𝓥 , qinveq φ (γ , γφ , φγ)
 where
  φ : Ω 𝓥 → Ω 𝓤
  φ (Q , j) = resize ρ Q j , resize-is-a-prop ρ Q j
  γ : Ω 𝓤 → Ω 𝓥
  γ (P , i) = resize ρ P i , resize-is-a-prop ρ P i
  φγ : (p : Ω 𝓤) → φ (γ p) ≡ p
  φγ (P , i) = Ω-ext (fe 𝓤 𝓤) (pe 𝓤)
               (from-resize ρ P i ∘ from-resize ρ (resize ρ P i) (resize-is-a-prop ρ P i))
               (to-resize ρ (resize ρ P i) (resize-is-a-prop ρ P i) ∘ to-resize ρ P i)
  γφ : (q : Ω 𝓥) → γ (φ q) ≡ q
  γφ (Q , j) = Ω-ext (fe 𝓥 𝓥) (pe 𝓥)
               (from-resize ρ Q j ∘ from-resize ρ (resize ρ Q j) (resize-is-a-prop ρ Q j))
               (to-resize ρ (resize ρ Q j) (resize-is-a-prop ρ Q j) ∘ to-resize ρ Q j)

\end{code}

A more standard notion of impredicativity is that the type Ω 𝓤 of
truth-values in the universe 𝓤 itself lives in 𝓤.

\begin{code}

Ω-resizing : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω-resizing 𝓤 = (Ω 𝓤) has-size 𝓤

\end{code}

Propositional resizing doesn't imply that the first universe 𝓤₀ is
impredicative, but it does imply that all other, successor, universes
𝓤 ⁺ are.

\begin{code}

Ω-resizing⁺-from-pr-pe-fe : Propositional-resizing → PropExt → FunExt
                          → Ω-resizing (𝓤 ⁺)
Ω-resizing⁺-from-pr-pe-fe {𝓤} ρ pe fe = Ω⁺-resizing-from-pr-pe-fe ρ pe fe 𝓤

\end{code}

But excluded middle does give the impredicativity of the first
universe, and of all other universes, of course:

\begin{code}

Ω-Resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥 )⁺ ̇
Ω-Resizing 𝓤 𝓥 = (Ω 𝓤) has-size 𝓥

Ω-global-resizing-from-em-pe-fe : EM 𝓤 → propext 𝓤 → funext 𝓤 𝓤
                                → (𝓥 : Universe) → Ω-Resizing 𝓤 𝓥
Ω-global-resizing-from-em-pe-fe {𝓤} lem pe fe 𝓥 =
 (𝟙 {𝓥} + 𝟙 {𝓥}) ,
 qinveq φ
 ((λ p → γ p (em p)) ,
  (λ z → γφ z (em (φ z))) ,
  (λ p → φγ p (em p)))
 where
  em : LEM 𝓤
  em = EM-gives-LEM lem
  φ : 𝟙 + 𝟙 → Ω 𝓤
  φ (inl x) = ⊥
  φ (inr y) = ⊤
  γ : (p : Ω 𝓤) → decidable (p holds) → 𝟙 + 𝟙
  γ p (inl h) = inr *
  γ p (inr n) = inl *
  γφ : (z : 𝟙 + 𝟙) (d : decidable ((φ z) holds)) → γ (φ z) d ≡ z
  γφ (inl x) (inl h) = 𝟘-elim h
  γφ (inl x) (inr n) = ap inl (𝟙-is-prop * x)
  γφ (inr y) (inl h) = ap inr (𝟙-is-prop * y)
  γφ (inr y) (inr n) = 𝟘-elim (n *)
  φγ : (p : Ω 𝓤) (d : decidable (p holds)) → φ (γ p d) ≡ p
  φγ p (inl h) = (true-is-equal-⊤  pe fe (p holds) (holds-is-prop p) h)⁻¹
  φγ p (inr n) = (false-is-equal-⊥ pe fe (p holds) (holds-is-prop p) n)⁻¹

\end{code}

We also have that moving Ω around universes moves propositions around
universes:

\begin{code}

Ω-resizing-gives-propositional-resizing : Ω-Resizing 𝓤 𝓥 → propext 𝓤 → funext 𝓤 𝓤
                                        → propositional-resizing 𝓤 𝓥
Ω-resizing-gives-propositional-resizing {𝓤} {𝓥} (O , e) pe fe P i = Q , ε
 where
  down : Ω 𝓤 → O
  down = eqtofun (≃-sym e)
  O-is-set : is-set O
  O-is-set = equiv-to-set e (Ω-is-a-set fe pe)
  Q : 𝓥 ̇
  Q = down ⊤ ≡ down (P , i)
  j : is-prop Q
  j = O-is-set
  φ : Q → P
  φ q = idtofun 𝟙 P (ap pr₁ (equivs-are-lc down (eqtofun-is-an-equiv (≃-sym e)) q)) *
  γ : P → Q
  γ p = ap down (to-Σ-≡ (pe 𝟙-is-prop i (λ _ → p) (λ _ → *) , being-a-prop-is-a-prop fe _ _))
  ε : Q ≃ P
  ε = logically-equivalent-props-are-equivalent j i φ γ

Ω-resizing₀ : (𝓤 : Universe) → 𝓤 ⁺ ̇
Ω-resizing₀ 𝓤 = (Ω 𝓤) has-size 𝓤₀

Ω-resizing₀-from-em-pe-fe₀ : EM 𝓤 → propext 𝓤 → funext 𝓤 𝓤
                          → Ω-resizing₀ 𝓤
Ω-resizing₀-from-em-pe-fe₀ {𝓤} em pe fe = Ω-global-resizing-from-em-pe-fe em pe fe 𝓤₀

\end{code}

What we get with propositional resizing is that all types of
propositions of any universe 𝓤 are equivalent to Ω 𝓤₀, which lives in
the second universe 𝓤₁:

\begin{code}

Ω-resizing₁ : (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓤₂ ̇
Ω-resizing₁ 𝓤 = (Ω 𝓤) has-size 𝓤₁

Ω-resizing₁-from-pr-pe-fe : Propositional-resizing → PropExt → FunExt
                          → Ω-resizing₁ 𝓤
Ω-resizing₁-from-pr-pe-fe {𝓤} ρ pe fe = Ω⁺-resizing-from-pr-pe-fe ρ pe fe 𝓤₀

Ω-resizing₁-≃-from-pr-pe-fe : Propositional-resizing → PropExt → FunExt
                            → Ω 𝓤 ≃ Ω 𝓤₀
Ω-resizing₁-≃-from-pr-pe-fe {𝓤} ρ pe fe = ≃-sym (pr₂ (Ω-resizing₁-from-pr-pe-fe {𝓤} ρ pe fe))

Ω-𝓤₀-lives-in-𝓤₁ : universe-of (Ω 𝓤₀) ≡ 𝓤₁
Ω-𝓤₀-lives-in-𝓤₁ = refl

\end{code}

With propositional resizing, we have that any universe is a retract of
any larger universe (this seems to be a new result).

\begin{code}

lift-is-section : Univalence
                → Propositional-resizing
                → (𝓤 𝓥 : Universe)
                → is-section (lift {𝓤} 𝓥)
lift-is-section ua R 𝓤 𝓥 = (r , rs)
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = lift 𝓥
  e : is-embedding s
  e = lift-is-embedding ua
  F : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  F Y = resize R (fiber s Y) (e Y)
  f : (Y : 𝓤 ⊔ 𝓥 ̇ ) → F Y → fiber s Y
  f Y = from-resize R (fiber s Y) (e Y)
  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r Y = (p : F Y) → pr₁ (f Y p)
  rs : (X : 𝓤 ̇ ) → r (s X) ≡ X
  rs X = γ
   where
    g : (Y : 𝓤 ⊔ 𝓥 ̇ ) → fiber s Y → F Y
    g Y = to-resize R (fiber s Y) (e Y)
    u : F (s X)
    u = g (s X) (X , refl)
    v : fiber s (s X)
    v = f (s X) u
    i : (Y : 𝓤 ⊔ 𝓥 ̇ ) → is-prop (F Y)
    i Y = resize-is-a-prop R (fiber s Y) (e Y)
    X' : 𝓤 ̇
    X' = pr₁ v
    a : r (s X) ≃ X'
    a = prop-indexed-product (FunExt-from-Univalence ua 𝓤 𝓤) (i (s X)) u
    b : s X' ≡ s X
    b = pr₂ v
    c : X' ≡ X
    c = embedding-lc s e b
    d : r (s X) ≃ X
    d = transport (λ - → r (s X) ≃ -) c a
    γ : r (s X) ≡ X
    γ = eqtoid (ua 𝓤) (r (s X)) X d

\end{code}

We remark that for types that are not sets, sections are not
automatically embeddings (Shulman 2015, Logical Methods in Computer
Science, April 27, 2017, Volume 12, Issue 3,
https://lmcs.episciences.org/2027 , Theorem 3.10).

Hence it is worth stating this explicitly:

\begin{code}

universe-retract' : Univalence
                  → Propositional-resizing
                  → (𝓤 𝓥 : Universe)
                  → Σ \(ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇ )) → is-embedding (section ρ)
universe-retract' ua R 𝓤 𝓥 = (pr₁ a , lift 𝓥 , pr₂ a) , lift-is-embedding ua
 where
  a : Σ \(lower : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇ ) → lower ∘ lift 𝓥 ∼ id
  a = lift-is-section ua R 𝓤 𝓥

\end{code}

A more conceptual version of the above construction is in the module
InjectiveTypes (which was discovered first - this is just an unfolding
of that construction).

Question. If we assume that we have such a retraction, does weak
propositional resizing follow?

Added 25 October 2019 by Tom de Jong

An answer to the question above is given by the following construction (which is
in need of a better name).

If we have a retract r of lift such that it "shrinks", i.e. for every Y, we have
an embedding of r Y into Y, then we get propositional resizing from 𝓤 ⊔ 𝓥 to 𝓤.

In fact, it is enough for the retract r of lift to satisfy:
(i) if Y is a subsingleton, then so is r Y;
(ii) we have a map r Y → Y.

But the shrinking condition is more intuitive.

(Note that shrinking implies (i) and (ii).)

\begin{code}

nice-universe-retract-gives-propositional-resizing : (𝓤 𝓥 : Universe)
                                                   → (ua : is-univalent (𝓤 ⊔ 𝓥))
                                                   → (r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇ )
                                                   → ((X : 𝓤 ̇ ) → r (lift 𝓥 X) ≡ X)
                                                   → ((P : 𝓤 ⊔ 𝓥 ̇ ) → is-prop P → is-prop (r P))
                                                   → ((Y : 𝓤 ⊔ 𝓥 ̇ ) → r Y → Y)
                                                   → propositional-resizing (𝓤 ⊔ 𝓥) 𝓤
nice-universe-retract-gives-propositional-resizing 𝓤 𝓥 ua r rs rprop rback P i = r P , γ
 where
  γ : r P ≃ P
  γ = qinveq f (g , (gf , fg))
   where
    f : r P → P
    f = rback P
    g : P → r P
    g p = Idtofun ϕ *
     where
      ϕ = 𝟙{𝓤}             ≡⟨ (rs 𝟙) ⁻¹ ⟩
          r (lift {𝓤} 𝓥 𝟙) ≡⟨ ap r (eqtoid ua (lift 𝓥 𝟙) P ψ) ⟩
          r P  ∎
       where
        ψ = lift {𝓤} 𝓥 𝟙 ≃⟨ lift-≃ 𝓥 𝟙 ⟩
            𝟙{𝓤}         ≃⟨ singleton-≃-𝟙' (pointed-props-are-singletons p i) ⟩
            P            ■
    gf : (q : r P) → g (f q) ≡ q
    gf q = rprop P i (g (f q)) q
    fg : (p : P) → f (g p) ≡ p
    fg p = i (f (g p)) p

\end{code}

We now consider a variant of the retraction in lift-is-section above, where we
use Σ, rather than Π. We show that this retraction shrinks. In particular, it
satisfies (i) and (ii) above. Moreover, this retraction restricts to an
equivalence on the subsingletons.

\begin{code}

lift-is-section-Σ : Univalence
                  → Propositional-resizing
                  → (𝓤 𝓥 : Universe)
                  → is-section (lift {𝓤} 𝓥)
lift-is-section-Σ ua R 𝓤 𝓥 = (r , rs)
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = lift 𝓥
  e : is-embedding s
  e = lift-is-embedding ua
  F : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  F Y = resize R (fiber s Y) (e Y)
  f : (Y : 𝓤 ⊔ 𝓥 ̇ ) → F Y → fiber s Y
  f Y = from-resize R (fiber s Y) (e Y)
  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r Y = Σ \(p : F Y) → pr₁ (f Y p)
  rs : (X : 𝓤 ̇ ) → r (s X) ≡ X
  rs X = γ
   where
    g : (Y : 𝓤 ⊔ 𝓥 ̇ ) → fiber s Y → F Y
    g Y = to-resize R (fiber s Y) (e Y)
    u : F (s X)
    u = g (s X) (X , refl)
    v : fiber s (s X)
    v = f (s X) u
    i : (Y : 𝓤 ⊔ 𝓥 ̇ ) → is-prop (F Y)
    i Y = resize-is-a-prop R (fiber s Y) (e Y)
    X' : 𝓤 ̇
    X' = pr₁ v
    a : r (s X) ≃ X'
    a = prop-indexed-sum (i (s X)) u
    b : s X' ≡ s X
    b = pr₂ v
    c : X' ≡ X
    c = embedding-lc s e b
    d : r (s X) ≃ X
    d = transport (λ - → r (s X) ≃ -) c a
    γ : r (s X) ≡ X
    γ = eqtoid (ua 𝓤) (r (s X)) X d

universe-retract-Σ : Univalence 
                   → Propositional-resizing
                   → (𝓤 𝓥 : Universe)
                   → 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
universe-retract-Σ ua R 𝓤 𝓥 = pr₁ (lift-is-section-Σ ua R 𝓤 𝓥)

universe-retract-Σ-shrinks : (ua : Univalence)
                             (R : Propositional-resizing)
                             {𝓤 𝓥 : Universe}
                             (Y : 𝓤 ⊔ 𝓥 ̇ )
                             → (universe-retract-Σ ua R 𝓤 𝓥 Y) ↪ Y
universe-retract-Σ-shrinks ua R {𝓤} {𝓥} Y = σ ∘ ρ , (comp-embedding ρ-emb σ-emb)
  where
   s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
   s = lift 𝓥
   unwrap : {Z : 𝓤 ̇ } → s Z → Z
   unwrap (inl z) = z
   inl-unwrap : {Z : 𝓤 ̇ } {z : s Z} → inl (unwrap z) ≡ z
   inl-unwrap {Z} {inl z} = refl
   r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇ 
   r Y = universe-retract-Σ ua R 𝓤 𝓥 Y
   r' : 𝓤 ⊔ 𝓥 ̇ → (𝓤 ⁺) ⊔ (𝓥 ⁺) ̇
   r' Y = Σ \(p : fiber s Y) → pr₁ p   
   ν : r Y ≃ r' Y
   ν = Σ-change-of-variables pr₁ (from-resize R (fiber s Y) (e Y))
         (pr₂ (pr₂ (R (fiber s Y) (e Y))))
    where    
     e : is-embedding s
     e = lift-is-embedding ua
   ρ : r Y → r' Y
   ρ = eqtofun ν
   ρ-emb : is-embedding ρ
   ρ-emb = equivs-are-embeddings ρ (eqtofun-is-an-equiv ν)
   σ : r' Y → Y
   σ ((X , e) , x) = Idtofun e (inl x)
   σ-emb : is-embedding σ
   σ-emb = embedding-criterion σ δ
    where
     δ : (w : r' Y) → is-prop (fiber σ (σ w))
     δ ((X , refl) , x) = retract-of-prop t ipT
      where
       ϕ : (w : fiber s Y) → X → pr₁ w
       ϕ (X' , e') = unwrap ∘ (Idtofun (e' ⁻¹) ∘ inl)
       T : 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇ 
       T = Σ \(w : r' Y) → S w
        where
         S : (w : r' Y) → 𝓤 ⊔ 𝓥 ̇ 
         S ((X' , e') , x') = (Idtofun e' (inl x')) ≡
                               Idtofun e' (inl (ϕ (X' , e') x))
       t : fiber σ (σ ((X , refl) , x)) ◁ T
       t = f , (g , fg)
        where
         p : (w : fiber s Y) → Idtofun (pr₂ w) (inl (ϕ w x)) ≡ inl x
         p (X' , e') =
          Idtofun e' (inl (ϕ w x))             ≡⟨ ap (Idtofun e') p' ⟩
          Idtofun e' (Idtofun (e' ⁻¹) (inl x)) ≡⟨ i ⟩
          Idtofun ((e' ⁻¹) ∙ e') (inl x)       ≡⟨ ii ⟩
          inl x                                ∎
           where
            w : fiber s Y
            w = (X' , e')
            p' = inl (ϕ w x)                            ≡⟨ refl ⟩
                 inl (unwrap (Idtofun (e' ⁻¹) (inl x))) ≡⟨ inl-unwrap ⟩
                 Idtofun (e' ⁻¹) (inl x)                ∎       
            i  = (transport-comp id (e' ⁻¹) e') ⁻¹
            ii = ap (λ - → Idtofun - (inl x)) (left-inverse e')
         f : T → fiber σ (σ ((X , refl) , x))
         f (w , q) = (w , (q ∙ (p (pr₁ w))))
         g : fiber σ (σ ((X , refl) , x)) → T
         g (w , r) = (w , (r ∙ ((p (pr₁ w)) ⁻¹)))
         fg : (v : fiber σ (σ ((X , refl) , x))) → f (g v) ≡ v
         fg (w , r) = to-Σ-≡ (refl , c)
          where
           c = r ∙ (v ⁻¹) ∙ v ≡⟨ ∙assoc r (v ⁻¹) v ⟩
               r ∙ (v ⁻¹ ∙ v) ≡⟨ ap (λ - → r ∙ -) (left-inverse v) ⟩
               r              ∎
            where
             v = p (pr₁ w)
       ipT : is-prop T
       ipT = equiv-to-prop τ (singleton-types'-are-props X)
        where
         τ = T                                                   ≃⟨ i ⟩
             (Σ \w → inl (pr₂ w) ≡ inl (ϕ (pr₁ w) x))            ≃⟨ ii ⟩
             (Σ \w → pr₂ w ≡ ϕ (pr₁ w) x)                        ≃⟨ Σ-assoc ⟩
             (Σ \v → (Σ \x' → x' ≡ ϕ v x))                       ≃⟨ Σ-assoc ⟩
             (Σ \X' → (Σ \e' → (Σ \x' → x' ≡ ϕ (X' , e') x)))    ≃⟨ ≃-refl _ ⟩
             (Σ \X' → (Σ \e' → singleton-type' (ϕ (X' , e') x))) ≃⟨ iii ⟩
             (Σ \X' → (s X' ≡ s X) × 𝟙{𝓤})                      ≃⟨ iv ⟩
             (Σ \X' → s X' ≡ s X)                                ≃⟨ v ⟩
             (Σ \X' → X' ≡ X)                                    ≃⟨ vi ⟩
             singleton-type' X ■
          where
           i   = Σ-cong (λ w → ≃-sym
                   (ap (Idtofun (pr₂ (pr₁ w))) ,
                    embedding-embedding' (Idtofun (pr₂ (pr₁ w)))
                      (equivs-are-embeddings (Idtofun (pr₂ (pr₁ w)))
                        (transports-are-equivs {_} {_} {_} {_}
                                               {s (pr₁ (pr₁ w))} {s X}
                                               (pr₂ (pr₁ w))))
                      (inl (pr₂ w)) (inl (ϕ (pr₁ w) x))))
           ii  = Σ-cong (λ w → ≃-sym
                   (ap inl ,
                    embedding-embedding' inl
                      (inl-embedding (pr₁ (pr₁ w)) 𝟘)
                      (pr₂ w) (ϕ (pr₁ w) x)))
           iii = Σ-cong (λ X' →
                   Σ-cong (λ e' →
                     singleton-≃-𝟙
                       (singleton-types'-are-singletons (ϕ (X' , e') x))))
           iv  = Σ-cong (λ X' → 𝟙-rneutral)
           v   = Σ-cong (λ X' → ≃-sym
                   (ap s ,
                    embedding-embedding' s
                      (lift-is-embedding ua)
                      X' X))
           vi  = ≃-refl (singleton-type' X)

\end{code}

It follows that universe-retract-Σ satisfies (i) and (ii).

\begin{code}

universe-retract-Σ-back-up : (ua : Univalence)
                             (R : Propositional-resizing)
                             {𝓤 𝓥 : Universe}
                             (Y : 𝓤 ⊔ 𝓥 ̇ )
                             → universe-retract-Σ ua R 𝓤 𝓥 Y → Y
universe-retract-Σ-back-up ua R Y = etofun (universe-retract-Σ-shrinks ua R Y)

universe-retract-Σ-of-subsingleton-is-subsingleton : (ua : Univalence)
                                                     (R : Propositional-resizing)
                                                     {𝓤 𝓥 : Universe}
                                                     {Y : 𝓤 ⊔ 𝓥 ̇ }
                                                     → is-prop Y
                                                     → is-prop (universe-retract-Σ ua R 𝓤 𝓥 Y)
universe-retract-Σ-of-subsingleton-is-subsingleton ua R {𝓤} {𝓥} {Y} i =
 embedding-into-prop i (universe-retract-Σ-shrinks ua R Y)

\end{code}

That universe-retract-Σ satifies (ii), i.e. preserves propositions can also be
proved more elementary.

\begin{code}

universe-retract-Σ-of-subsingleton-is-subsingleton' : (ua : Univalence)
                                                     (R : Propositional-resizing)
                                                     {𝓤 𝓥 : Universe}
                                                     {Y : 𝓤 ⊔ 𝓥 ̇ }
                                                     → is-prop Y
                                                     → is-prop (universe-retract-Σ ua R 𝓤 𝓥 Y)
universe-retract-Σ-of-subsingleton-is-subsingleton' ua R {𝓤} {𝓥} {Y} i = Σ-is-prop a b
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = lift 𝓥
  e : is-embedding s
  e = lift-is-embedding ua
  F : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  F Y = resize R (fiber s Y) (e Y)
  f : (Y : 𝓤 ⊔ 𝓥 ̇ ) → F Y → fiber s Y
  f Y = from-resize R (fiber s Y) (e Y)
  a : is-prop (F Y)
  a = resize-is-a-prop R (fiber s Y) (e Y)
  b : (p : F Y) → is-prop (pr₁ (f Y p))
  b p = c
   where
    X : 𝓤 ̇
    X = pr₁ (f Y p)
    ϕ : X ≃ Y
    ϕ = X   ≃⟨ ≃-sym (lift-≃ 𝓥 X) ⟩
        s X ≃⟨ idtoeq (lift 𝓥 X) Y (pr₂ (f Y p)) ⟩
        Y   ■  
    c : is-prop X
    c = equiv-to-prop ϕ i

\end{code}

We now show that the (lift , universe-retract-Σ) pair is an equivalence when
restricted to subsingletons.

\begin{code}

universe-retract-Σ-is-section-on-subsingletons : (ua : Univalence)
                                                 (R : Propositional-resizing)
                                                 {𝓤 𝓥 : Universe}
                                                 {Y : 𝓤 ⊔ 𝓥 ̇ }
                                                 → is-prop Y
                                                 → lift 𝓥 (universe-retract-Σ ua R 𝓤 𝓥 Y) ≡ Y
universe-retract-Σ-is-section-on-subsingletons ua R {𝓤} {𝓥} {Y} i = γ
 where
  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r = universe-retract-Σ ua R 𝓤 𝓥
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = lift {𝓤} 𝓥
  γ : s (r Y) ≡ Y
  γ = propext-from-univalence (ua (𝓤 ⊔ 𝓥)) (equiv-to-prop (lift-≃ 𝓥 (r Y)) p) i g f
   where
    p : is-prop (r Y)
    p = universe-retract-Σ-of-subsingleton-is-subsingleton ua R i
    f : Y → s (r Y)
    f y = inl (Idtofun (χ ∙ ψ) *)
     where
      χ : 𝟙 ≡ r (s 𝟙)
      χ = (pr₂ (lift-is-section-Σ ua R 𝓤 𝓥) 𝟙) ⁻¹
      ψ : r (s 𝟙) ≡ r Y
      ψ = ap r (eqtoid (ua (𝓤 ⊔ 𝓥)) (s 𝟙) Y ϕ)
       where
        ϕ = s 𝟙  ≃⟨ lift-≃ 𝓥 𝟙 ⟩
            𝟙{𝓤} ≃⟨ singleton-≃-𝟙' (pointed-props-are-singletons y i) ⟩
            Y    ■ 
    g : s (r Y) → Y
    g = universe-retract-Σ-back-up ua R Y ∘ eqtofun (lift-≃ 𝓥 (r Y))

propositional-resizing-Ω-≃ : (ua : Univalence)
                             (R : Propositional-resizing)
                             {𝓤 𝓥 : Universe}
                             → Ω 𝓤 ≃ Ω (𝓤 ⊔ 𝓥)
propositional-resizing-Ω-≃ ua R {𝓤} {𝓥} = sΩ , ((rΩ , sΩrΩ) , (rΩ , rΩsΩ))
 where
  s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
  s = lift 𝓥 
  sΩ : Ω 𝓤 → Ω (𝓤 ⊔ 𝓥)
  sΩ (P , i) = s P , (equiv-to-prop (lift-≃ 𝓥 P) i)
  r : 𝓤 ⊔ 𝓥 ̇ → 𝓤 ̇
  r = universe-retract-Σ ua R 𝓤 𝓥
  rΩ : Ω (𝓤 ⊔ 𝓥) → Ω 𝓤
  rΩ (P , i) = (r P , universe-retract-Σ-of-subsingleton-is-subsingleton ua R i)
  sΩrΩ : (P : Ω (𝓤 ⊔ 𝓥)) → sΩ (rΩ P) ≡ P
  sΩrΩ (P , i) = to-Σ-≡
    (universe-retract-Σ-is-section-on-subsingletons ua R i ,
     being-a-prop-is-a-prop (funext-from-univalence (ua (𝓤 ⊔ 𝓥))) _ i)
  rΩsΩ : (P : Ω 𝓤) → rΩ (sΩ P) ≡ P
  rΩsΩ (P , i) = to-Σ-≡
    (pr₂ (lift-is-section-Σ ua R 𝓤 𝓥) P ,
     being-a-prop-is-a-prop (funext-from-univalence (ua 𝓤)) _ i)

\end{code}

These helper functions are only here, because for some reason that I can't quite
figure out, Agda will get stuck typechecking if we don't supply all the implicit
arguments.

\begin{code}

universe-retract-Σ-pr₁ : (ua : Univalence)
                            (R : Propositional-resizing)
                            {𝓤 𝓥 : Universe}
                            (Y : 𝓤 ⊔ 𝓥 ̇ )
                            → universe-retract-Σ ua R 𝓤 𝓥 Y
                            → resize R (fiber (lift {𝓤} 𝓥) Y) (lift-is-embedding ua Y)
universe-retract-Σ-pr₁ ua R {𝓤} {𝓥} Y =
 pr₁ {𝓤} {𝓤} {resize R (fiber s Y) (e Y)}
 {λ w → pr₁ (from-resize R (fiber s Y) (e Y) w)}
  where
   s : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
   s = lift 𝓥
   e : is-embedding s
   e = lift-is-embedding ua

universe-retract-Σ-to-fiber : (ua : Univalence)
                            (R : Propositional-resizing)
                            {𝓤 𝓥 : Universe}
                            (Y : 𝓤 ⊔ 𝓥 ̇ )
                            → universe-retract-Σ ua R 𝓤 𝓥 Y
                            → fiber (lift {𝓤} 𝓥) Y
universe-retract-Σ-to-fiber ua R {𝓤} {𝓥} Y =
 (from-resize R (fiber (lift {𝓤} 𝓥) Y) (lift-is-embedding ua Y))
   ∘
 universe-retract-Σ-pr₁ ua R Y

\end{code}

The retract applied to the universe to the type 𝓤 ̇ in 𝓤 ⁺ ̇ is 𝟘.

\begin{code}

universe-retract-Σ-of-𝓤-is-empty : (ua : Univalence)
                                   (R : Propositional-resizing)
                                   (𝓤 : Universe)
                                   → universe-retract-Σ ua R 𝓤 (𝓤 ⁺) (𝓤 ̇ ) → 𝟘{𝓤₀}
universe-retract-Σ-of-𝓤-is-empty ua R 𝓤  =
 c ∘ (universe-retract-Σ-to-fiber ua R {𝓤} {𝓤 ⁺} (𝓤 ̇))
  where
   c : fiber (lift {𝓤} (𝓤 ⁺)) (𝓤 ̇ ) → 𝟘{𝓤₀}
   c (X , e) = Coquand.Theorem 𝓤 ((X , γ))
    where
     γ = 𝓤 ̇           ≃⟨ idtoeq (𝓤 ̇) (lift (𝓤 ⁺) X) (e ⁻¹) ⟩
         lift (𝓤 ⁺) X ≃⟨ lift-≃ (𝓤 ⁺) X ⟩
         X            ■

\end{code}

It follows that the embedding (universe-retract-Σ 𝓤 ̇) ↪ 𝓤 ̇ cannot be a
surjection.

\begin{code}

module _ (pt : propositional-truncations-exist) where
 open import UF-ImageAndSurjection
 open ImageAndSurjection pt
 open PropositionalTruncation pt

 universe-retract-Σ-not-surjective : (ua : Univalence)
                                     (R : Propositional-resizing)
                                     (𝓤 : Universe)
                                     → ¬ (is-surjection
                                       (universe-retract-Σ-back-up ua R {𝓤} {𝓤 ⁺} (𝓤 ̇)))
 universe-retract-Σ-not-surjective ua R 𝓤 s = ∥∥-rec 𝟘-is-prop γ (s (𝟙{𝓤}))
  where
   γ : (Σ \r → universe-retract-Σ-back-up ua R {𝓤} {𝓤 ⁺} (𝓤 ̇) r ≡ 𝟙) → 𝟘
   γ (r , _) = universe-retract-Σ-of-𝓤-is-empty ua R 𝓤 r

\end{code}

The following construction is due to Voevodsky, but we use the
resizing axiom rather than his rules (and we work with non-cumulative
universes).

\begin{code}

∥_∥⁺ : 𝓤 ̇ → 𝓤 ⁺ ̇
∥ X ∥⁺ = (P : universe-of X ̇ ) → is-prop P → (X → P) → P

∥∥⁺-is-a-prop : FunExt → {X : 𝓤 ̇ } → is-prop (∥ X ∥⁺)
∥∥⁺-is-a-prop fe = Π-is-prop (fe _ _)
                   (λ P → Π-is-prop (fe _ _)
                           (λ i → Π-is-prop (fe _ _)
                                    (λ u → i)))

∣_∣⁺ : {X : 𝓤 ̇ } → X → ∥ X ∥⁺
∣ x ∣⁺ = λ P i u → u x

∥∥⁺-rec : {X P : 𝓤 ̇ } → is-prop P → (X → P) → ∥ X ∥⁺ → P
∥∥⁺-rec {𝓤} {X} {P} i u s = s P i u

resizing-truncation : FunExt → Propositional-resizing → propositional-truncations-exist
resizing-truncation fe R = record {
    ∥_∥          = λ {𝓤} X → resize R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe)
  ; ∥∥-is-a-prop = λ {𝓤} {X} → resize-is-a-prop R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe)
  ; ∣_∣          = λ {𝓤} {X} x → to-resize R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe) ∣ x ∣⁺
  ; ∥∥-rec       = λ {𝓤} {𝓥} {X} {P} i u s → from-resize R P i
                                              (∥∥⁺-rec (resize-is-a-prop R P i)
                                                       (to-resize R P i ∘ u)
                                                       (from-resize R ∥ X ∥⁺ (∥∥⁺-is-a-prop fe) s))
  }

\end{code}

Images:

\begin{code}

module Image
        {𝓤 𝓥 : Universe}
        {X : 𝓤 ̇ }
        {Y : 𝓥 ̇ }
        (fe : FunExt)
        (R : Propositional-resizing)
       where

 open PropositionalTruncation (resizing-truncation fe R)

 image : (X → Y) → 𝓥 ̇
 image f = Σ \y → resize (R {𝓤 ⊔ 𝓥} {𝓥}) (∃ \x → f x ≡ y) ∥∥-is-a-prop

 restriction : (f : X → Y) → image f → Y
 restriction f (y , _) = y

 restriction-embedding : (f : X → Y) → is-embedding(restriction f)
 restriction-embedding f = pr₁-embedding (λ y → resize-is-a-prop R _ _)

 corestriction : (f : X → Y) → X → image f
 corestriction f x = f x , to-resize R _ _ ∣ x , refl ∣

\end{code}

TODO. Prove the properties / perform the constructions in
UF-ImageAndSurjection. Better: reorganize the code so that reproving
is not necessary.

\end{code}
