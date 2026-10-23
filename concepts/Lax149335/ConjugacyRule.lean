import Lax149335.SimpleRationalTerms

/-!
---
title: The conjugacy rule for syntactic conjugates
type: lemma
---
**Lemma 6.2.** For a simple rational term $h : A \to B^*$ and a value $w : 1 \to B^*$,
$$
\mathrm{hom}(w \cdot h) \cdot w \;\equiv\; w \cdot \mathrm{hom}(h \cdot w).
$$
That is, the conjugacy rule holds when its assumption is strengthened from provable to
syntactic conjugacy.

# Formalization notes

The paper states the lemma for a simple rational term over a finite alphabet. Neither
assumption is used in the proof, so the statement is formalised for an arbitrary rational
term $h : A \to B^*$, which makes it stronger.
-/

namespace Lax149335.ConjugacyRule

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.EquationalTheory

/-- **Lemma 6.2.** `hom(w · h) · w ≡ w · hom(h · w)`. -/
axiom conjugacy_of_syntactic {A B : Ty} (h : Term A B⋆) (w : Value B⋆) :
    dotR (homT (dotL w h)) w ≡ₜ dotL w (homT (dotR h w))

end Lax149335.ConjugacyRule
