import Lax149335.SimpleRationalTerms
import Lax149335.Terms

/-!
---
title: Simplification of rational terms
type: theorem
---
**Theorem 2.9 (Simplification of rational terms).** Consider rational terms
$f, g : N^* \to M^*$ where $N$ and $M$ are finite alphabets. There is a type $C$ and a
rational term $\pi : C \to N^*$ with surjective denotation, such that
$[\![ \pi \mathbin{;} f ]\!]$ and $[\![ \pi \mathbin{;} g ]\!]$ are represented by simple
rational terms.

# Formalization notes

"Represented by a simple rational term" refers to the simple rational terms of
Definition 2.5, with output alphabet the set of letters of $M$.
-/

namespace Lax149335.Simplification

open Lax149335.Types Lax149335.Terms Lax149335.SimpleRationalTerms

/-- **Theorem 2.9.** After precomposing with a rational term with surjective denotation, two
rational terms `N* → M*` are represented by simple rational terms. -/
axiom simplification_of_rational_terms {N M : Ty} (hN : Ty.IsFinAlph N)
    (hM : Ty.IsFinAlph M) (f g : Term N⋆ M⋆) :
    ∃ (C : Ty) (π : Term C N⋆), Function.Surjective π.den ∧
      SimpleTerm.IsSimpleFun (Bs := ⟦M⟧) (π ⨟ f).den ∧
      SimpleTerm.IsSimpleFun (Bs := ⟦M⟧) (π ⨟ g).den

end Lax149335.Simplification
