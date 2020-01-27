Tom de Jong & Martin Escardo, 20 May 2019.

 * Directed complete posets.
 * Continuous maps.
 * Examples and constructions in DcpoConstructions

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module Dcpo
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe) -- where the index type for directed completeness lives
       where

open PropositionalTruncation pt

open import UF-Subsingletons hiding (⊥)
open import UF-Subsingletons-FunExt

module _ {𝓤 𝓣 : Universe}
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

 is-least : D → 𝓤 ⊔ 𝓣 ̇
 is-least x = ∀ (y : D) → x ⊑ y

 has-least : 𝓤 ⊔ 𝓣 ̇
 has-least = Σ (\(x : D) → is-least x)

 is-upperbound : {I : 𝓥 ̇ } (u : D) (α : I → D) → 𝓥 ⊔ 𝓣 ̇
 is-upperbound u α = (i : domain α) → α i ⊑ u

 is-lowerbound-of-upperbounds : {I : 𝓥 ̇ } (u : D) (α : I → D) → 𝓥 ⊔ 𝓤 ⊔ 𝓣 ̇
 is-lowerbound-of-upperbounds u α = (v : D) → is-upperbound v α → u ⊑ v

 is-sup : {I : 𝓥 ̇ } → D → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 is-sup s α = (is-upperbound s α) × (is-lowerbound-of-upperbounds s α)

 sup-is-upperbound : {I : 𝓥 ̇ } {s : D} {α : I → D}
                   → is-sup s α
                   → is-upperbound s α
 sup-is-upperbound i = pr₁ i

 sup-is-lowerbound-of-upperbounds : {I : 𝓥 ̇ } {s : D} {α : I → D}
                                  → is-sup s α
                                  → (u : D)
                                  → is-upperbound u α → s ⊑ u
 sup-is-lowerbound-of-upperbounds i = pr₂ i

 has-sup : {I : 𝓥 ̇ } → (I → D) → 𝓤 ⊔ 𝓥 ⊔ 𝓣 ̇
 has-sup α = Σ \(s : D) → is-sup s α

 the-sup : {I : 𝓥 ̇ } {α : I → D} → has-sup α → D
 the-sup (s , i) = s

 sup-property : {I : 𝓥 ̇ } {α : I → D} (h : has-sup α) → is-sup (the-sup h) α
 sup-property (s , i) = i

 is-inhabited : (I : 𝓥 ̇ ) → 𝓥 ̇
 is-inhabited = ∥_∥

 being-inhabited-is-a-prop : {I : 𝓥 ̇ } → is-prop (is-inhabited I)
 being-inhabited-is-a-prop = ∥∥-is-a-prop

 is-weakly-directed : {I : 𝓥 ̇ } (α : I → D) → 𝓥 ⊔ 𝓣 ̇
 is-weakly-directed {I} α = (i j : I) → ∃ \(k : I) → α i ⊑ α k × α j ⊑ α k

 being-weakly-directed-is-a-prop : {I : 𝓥 ̇ } {α : I → D}
                                 → is-prop (is-weakly-directed α)
 being-weakly-directed-is-a-prop = Π-is-prop fe
                                   (λ i → Π-is-prop fe
                                   (λ j → ∥∥-is-a-prop))

 is-directed : {I : 𝓥 ̇ } (α : I → D) → 𝓥 ⊔ 𝓣 ̇
 is-directed α = is-inhabited (domain α) × is-weakly-directed α

 being-directed-is-a-prop : {I : 𝓥 ̇ } {α : I → D} → is-prop (is-directed α)
 being-directed-is-a-prop =
  ×-is-prop being-inhabited-is-a-prop being-weakly-directed-is-a-prop

 directed-implies-inhabited : {I : 𝓥 ̇ } (α : I → D)
                            → is-directed α
                            → is-inhabited I
 directed-implies-inhabited α = pr₁

 directed-implies-weakly-directed : {I : 𝓥 ̇ } (α : I → D)
                                  → is-directed α
                                  → is-weakly-directed α
 directed-implies-weakly-directed α = pr₂

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

 is-directed-complete : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣  ̇
 is-directed-complete = (I : 𝓥 ̇ ) (α : I → D) → is-directed α → has-sup α

 dcpo-axioms : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇
 dcpo-axioms = poset-axioms × is-directed-complete

 is-sup-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (d : D) (α : I → D)
                  → is-prop (is-sup d α)
 is-sup-is-a-prop ((s , p , r , t , a) , c) d α = γ
  where
   γ : is-prop (is-sup d α)
   γ = ×-is-prop
         (Π-is-prop fe
           (λ i → p (α i) d))
         (Π-is-prop fe
           (λ x → Π-is-prop fe
           (λ l → p d x)))

 having-sup-is-a-prop : dcpo-axioms → {I : 𝓥 ̇ } (α : I → D)
                      → is-prop (has-sup α)
 having-sup-is-a-prop ((s , p , r , t , a) , c) α = γ
  where
   γ : is-prop (has-sup α)
   γ (x , u , l) (y , u' , l') =
    to-Σ-≡ (e , is-sup-is-a-prop ((s , p , r , t , a ) , c) y α _ (u' , l'))
     where
      e : x ≡ y
      e = a x y (l y u') (l' x u)

 being-directed-complete-is-a-prop : dcpo-axioms → is-prop is-directed-complete
 being-directed-complete-is-a-prop a = Π-is-prop fe
                                         (λ I → Π-is-prop fe
                                         (λ α → Π-is-prop fe
                                         (λ δ → having-sup-is-a-prop a α)))

 dcpo-axioms-is-a-prop : is-prop dcpo-axioms
 dcpo-axioms-is-a-prop = iprops-are-props γ
  where
   γ : dcpo-axioms → is-prop dcpo-axioms
   γ a = ×-is-prop
           poset-axioms-is-a-prop
           (being-directed-complete-is-a-prop a)

\end{code}

We proceed by defining the type of dcpos and convenient projection functions.

\begin{code}

module _ {𝓤 𝓣 : Universe} where

 DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO-structure D = Σ \(_⊑_ : D → D → 𝓣 ̇ ) → dcpo-axioms {𝓤} {𝓣} _⊑_

 DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO = Σ \(D : 𝓤 ̇ ) → DCPO-structure D

 ⟨_⟩ : DCPO → 𝓤 ̇
 ⟨ D , _⊑_ , d ⟩ = D

 underlying-order : (𝓓 : DCPO) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣 ̇
 underlying-order (D , _⊑_ , d) = _⊑_

 syntax underlying-order 𝓓 x y = x ⊑⟨ 𝓓 ⟩ y

 axioms-of-dcpo : (𝓓 : DCPO) → dcpo-axioms (underlying-order 𝓓)
 axioms-of-dcpo (D , _⊑_ , d) = d

 sethood : (𝓓 : DCPO) → is-set ⟨ 𝓓 ⟩
 sethood (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = s

 prop-valuedness : (𝓓 : DCPO) → is-prop-valued (underlying-order 𝓓 )
 prop-valuedness (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = p

 reflexivity : (𝓓 : DCPO) → is-reflexive (underlying-order 𝓓)
 reflexivity (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = r

 transitivity : (𝓓 : DCPO) → is-transitive (underlying-order 𝓓)
 transitivity (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = t

 antisymmetry : (𝓓 : DCPO) → is-antisymmetric (underlying-order 𝓓)
 antisymmetry (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = a

\end{code}

We also consider dcpos with a least element.

\begin{code}

 DCPO⊥ : (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓣 ⁺) ̇
 DCPO⊥ = Σ \(𝓓 : DCPO) → has-least (underlying-order 𝓓)

 _⁻ : DCPO⊥ → DCPO
 _⁻ = pr₁

 ⟪_⟫ : DCPO⊥ → 𝓤 ̇
 ⟪ 𝓓 ⟫ = ⟨ 𝓓 ⁻ ⟩

 underlying-order⊥ : (𝓓 : DCPO⊥) → ⟪ 𝓓 ⟫ → ⟪ 𝓓 ⟫ → 𝓣 ̇
 underlying-order⊥ 𝓓 = underlying-order (𝓓 ⁻)

 syntax underlying-order⊥ 𝓓 x y = x ⊑⟪ 𝓓 ⟫ y

 ⊥ : (𝓓 : DCPO⊥) → ⟨ 𝓓 ⁻ ⟩
 ⊥ (𝓓 , x , p) = x

 ⊥-is-least : (𝓓 : DCPO⊥) → is-least (underlying-order (𝓓 ⁻)) (⊥ 𝓓)
 ⊥-is-least (𝓓 , x , p) = p

\end{code}

We introduce pretty syntax for chain reasoning with inequalities.
(Cf. ≡⟨_⟩ and ∎ in Id.lagda, ≃⟨_⟩ and ■ in UF-Equiv.lagda)

For example, given (a b c d : ⟨ 𝓓 ⟩) and
u : a ⊑⟨ 𝓓 ⟩ b
v : b ⊑⟨ 𝓓 ⟩ c
w : c ⊑⟨ 𝓓 ⟩ d

this will allow us to write

z : a ⊑⟨ 𝓓 ⟩ d
z = a ⊑⟨ 𝓓 ⟩[ u ]
    b ⊑⟨ 𝓓 ⟩[ v ]
    c ⊑⟨ 𝓓 ⟩[ w ]
    d ∎⟨ 𝓓 ⟩

rather than the hard(er) to read

z : a ⊑⟨ 𝓓 ⟩ d
z = transitivity 𝓓 a c d z' w
 where
  z' : a ⊑⟨ 𝓓 ⟩ c
  z' = transitivity 𝓓 a b c u v

\begin{code}

 transitivity' : (𝓓 : DCPO) (x : ⟨ 𝓓 ⟩) {y z : ⟨ 𝓓 ⟩}
               → x ⊑⟨ 𝓓 ⟩ y → y ⊑⟨ 𝓓 ⟩ z → x ⊑⟨ 𝓓 ⟩ z
 transitivity' 𝓓 x {y} {z} u v = transitivity 𝓓 x y z u v

 syntax transitivity' 𝓓 x u v = x ⊑⟨ 𝓓 ⟩[ u ] v
 infixr 0 transitivity'

 syntax reflexivity 𝓓 x = x ∎⟨ 𝓓 ⟩
 infix 1 reflexivity

\end{code}

Next, we introduce ∐-notation for the supremum of a directed family in a dcpo.

\begin{code}

 directed-completeness : (𝓓 : DCPO) → is-directed-complete (underlying-order 𝓓)
 directed-completeness (D , _⊑_ , (s  , p  , r  , t  , a)  , c ) = c

 is-Directed : (𝓓 : DCPO) {I : 𝓥 ̇ } (α : I → ⟨ 𝓓 ⟩) → 𝓥 ⊔ 𝓣 ̇
 is-Directed 𝓓 α = is-directed (underlying-order 𝓓) α

 Directed-implies-inhabited : (𝓓 : DCPO) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                            → is-Directed 𝓓 α
                            → ∥ I ∥
 Directed-implies-inhabited 𝓓 = pr₁

 Directed-implies-weakly-directed : (𝓓 : DCPO) {I : 𝓥 ̇} {α : I → ⟨ 𝓓 ⟩}
                                  → is-Directed 𝓓 α
                                  → is-weakly-directed (underlying-order 𝓓) α
 Directed-implies-weakly-directed 𝓓 = pr₂

 ∐ : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} → is-Directed 𝓓 α → ⟨ 𝓓 ⟩
 ∐ 𝓓 {I} {α} δ = pr₁ (directed-completeness 𝓓 I α δ)

 ∐-is-sup : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
          → is-sup (underlying-order 𝓓) (∐ 𝓓 δ) α
 ∐-is-sup 𝓓 {I} {α} δ = pr₂ (directed-completeness 𝓓 I α δ)

 ∐-is-upperbound : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩} (δ : is-Directed 𝓓 α)
                 → is-upperbound (underlying-order 𝓓) (∐ 𝓓 δ) α
 ∐-is-upperbound 𝓓 δ = pr₁ (∐-is-sup 𝓓 δ)

 ∐-is-lowerbound-of-upperbounds : (𝓓 : DCPO) {I : 𝓥 ̇ } {α : I → ⟨ 𝓓 ⟩}
                                  (δ : is-Directed 𝓓 α)
                                → is-lowerbound-of-upperbounds
                                    (underlying-order 𝓓) (∐ 𝓓 δ) α
 ∐-is-lowerbound-of-upperbounds 𝓓 δ = pr₂ (∐-is-sup 𝓓 δ)

\end{code}

We continue by defining continuous maps between dcpos.

\begin{code}

is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
              → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
              → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
is-continuous 𝓓 𝓔 f = (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                      → is-sup (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ α)

being-continuous-is-a-prop : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                             (f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩)
                           → is-prop (is-continuous 𝓓 𝓔 f)
being-continuous-is-a-prop 𝓓 𝓔 f =
 Π-is-prop fe
 (λ I → Π-is-prop fe
 (λ α → Π-is-prop fe
 (λ δ → is-sup-is-a-prop
          (underlying-order 𝓔) (axioms-of-dcpo 𝓔) (f (∐ 𝓓 δ)) (f ∘ α))))

DCPO[_,_] : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
DCPO[ 𝓓 , 𝓔 ] = Σ (\(f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → is-continuous 𝓓 𝓔 f)

-- DCPO⊥[_,_] : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'} → (𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
-- DCPO⊥[ 𝓓 , 𝓔 ] = DCPO[ 𝓓 ⁻ , 𝓔 ⁻ ]

underlying-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'})
                    → DCPO[ 𝓓 , 𝓔 ] → ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩
underlying-function 𝓓 𝓔 (f , _) = f

syntax underlying-function 𝓓 𝓔 f = [ 𝓓 , 𝓔 ]⟨ f ⟩

continuity-of-function : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) (f : DCPO[ 𝓓 , 𝓔 ])
                       → is-continuous 𝓓 𝓔 (underlying-function 𝓓 𝓔 f)
continuity-of-function 𝓓 𝓔 (_ , c) = c

\end{code}
