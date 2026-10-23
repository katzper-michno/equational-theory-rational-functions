import Lax149335.EquationalTheory

/-!
---
title: Ignoring empty summands
type: claim
---
Let $f = \langle f_E, f_N \rangle : E + N \to B^*$, where $f_E$ is the
empty constant, i.e. $f_E \equiv (E \to 1) \mathbin{;} [\,]$. Then $\mathrm{hom}\, f$ is
provably equivalent to the composition
$$
(E + N)^* \xrightarrow{\ \mathsf{split}\ } E^* \times (N \times E^*)^*
\xrightarrow{\ \mathsf{snd} \,;\, \mathsf{fst}^*\ } N^*
\xrightarrow{\ \mathrm{hom}\, f_N\ } B^* .
$$
-/

namespace Lax149335.EmptySummands

open Lax149335.Types Lax149335.Terms Lax149335.Terms.Term Lax149335.DerivedTerms
  Lax149335.DerivedTerms.Term Lax149335.EquationalTheory

/-- If the case `f_E` of a co-pairing is the empty constant, then `hom f`
factors through `hom f_N`. -/
axiom hom_factors {B E N : Ty} (fE : Term E B⋆) (fN : Term N B⋆)
    (hfE : fE ≡ₜ toUnit E ⨟ nilT B) :
    homT (Term.either fE fN) ≡ₜ
      (split E N ⨟ snd E⋆ ((N ⊗ E⋆)⋆) ⨟ listF (fst N E⋆) ⨟ homT fN)

end Lax149335.EmptySummands
