Tom de Jong, 13 March 2020 -

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module DcpoRetracts
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : ∀ {𝓤} → propext 𝓤)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import Dcpo pt fe 𝓥
open import DcpoApproximation pt fe 𝓥
open import DcpoAlgebraic pt fe 𝓥
open import DcpoBasis pt fe 𝓥
open import IdealCompletion pt fe pe 𝓥
open import IdealCompletion-Properties pt fe pe 𝓥


\end{code}
