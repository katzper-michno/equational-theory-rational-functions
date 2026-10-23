import Lax149335.RationalFunctions
import Lax149335.Terms

/-!
---
title: Expressive completeness
type: theorem
---
**Theorem (Expressive completeness).** A function between types is rational if and only
if it is the denotation of some rational term.

This theorem is not proved in this submission; it is recorded as an open statement. Nothing
else in the submission depends on it.
-/

namespace Lax149335.ExpressiveCompleteness

open Lax149335.Types Lax149335.RationalFunctions Lax149335.Terms

/-- A function between types is rational if and only if it is the denotation
of some rational term. -/
axiom expressive_completeness {A B : Ty} (f : ⟦A⟧ → ⟦B⟧) :
    IsRationalTypeFun f ↔ ∃ t : Term A B, t.den = f

end Lax149335.ExpressiveCompleteness
