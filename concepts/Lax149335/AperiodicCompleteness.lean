import Lax149335.EquationalTheory

/-!
---
title: Aperiodic completeness
type: corollary
---
**Corollary 7.6 (Aperiodic completeness).** If aperiodic rational terms $f$ and $g$ have
the same denotation, then $f \equiv g$.
-/

namespace Lax149335.AperiodicCompleteness

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory

/-- **Corollary 7.6.** Aperiodic terms with the same denotation are provably equivalent. -/
axiom completeness_aperiodic {A B : Ty} (f g : Term A B)
    (hf : IsAperiodic f) (hg : IsAperiodic g) (h : f.den = g.den) : f ≡ₜ g

end Lax149335.AperiodicCompleteness
