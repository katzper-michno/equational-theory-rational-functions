import Lax149335.InjectiveSurjectiveTerms
import Lax149335.SimpleRationalWithinSyntax

/-!
---
title: Provable simplification of rational terms
type: theorem
---
**Theorem 7.7 (Provable simplification of rational terms).** Consider rational terms
$f, g : A \to N^*$, where $N$ is a finite alphabet. There is a type $B$ and a surjective
rational term $\pi : B \to A$, such that $\pi \mathbin{;} f$ and $\pi \mathbin{;} g$ are
equivalent to simple rational terms.

This is a strengthening of Theorem 2.9 in which the decomposition is carried out within
the equational system: surjectivity of $\pi$ is the provable notion of Definition 5.4, and
the equivalences are provable.
-/

namespace Lax149335.ProvableSimplification

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory Lax149335.InjectiveSurjectiveTerms
  Lax149335.SimpleRationalWithinSyntax

/-- **Theorem 7.7.** Two terms `A → N*` into the
lists over a finite alphabet become provably equivalent to simple rational terms after
precomposing with a common surjective term `π : B → A`. -/
axiom provable_simplification {A N : Ty} (hN : Ty.IsFinAlph N) (f g : Term A N⋆) :
    ∃ (B : Ty) (π : Term B A), ProvablySurjective π ∧
      (∃ f' : Term B N⋆, IsSimple N f' ∧ (π ⨟ f) ≡ₜ f') ∧
      (∃ g' : Term B N⋆, IsSimple N g' ∧ (π ⨟ g) ≡ₜ g')

end Lax149335.ProvableSimplification
