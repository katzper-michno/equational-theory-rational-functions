import Lax149335.EquationalTheory

/-!
---
title: Finite axiomatisation
type: theorem
---
**Theorem (Finite axiomatisation).** Two rational terms $f, g : A \to B$ have the same
denotation if and only if $f \equiv g$ can be proved using the axioms of the equational theory.
-/

namespace Lax149335.FiniteAxiomatisation

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory

/-- Two rational terms have the same denotation if and only if they are
provably equivalent. -/
axiom finite_axiomatisation {A B : Ty} (f g : Term A B) : f.den = g.den ↔ f ≡ₜ g

end Lax149335.FiniteAxiomatisation
