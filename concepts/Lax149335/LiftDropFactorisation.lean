import Lax149335.LiftsAndDrops
import Lax149335.EquationalTheory

/-!
---
title: Lift-drop factorisation
type: lemma
---
**Lemma (Lift-drop factorisation).** Every aperiodic rational term is provably
equivalent to a composition of a lift followed by a drop.
-/

namespace Lax149335.LiftDropFactorisation

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory Lax149335.LiftsAndDrops

/-- Every aperiodic term is provably equivalent to a lift followed by a
drop. -/
axiom lift_drop_factorisation {A B : Ty} (f : Term A B) (hf : IsAperiodic f) :
    ∃ (C : Ty) (l : Term A C) (d : Term C B), IsLift l ∧ IsDrop d ∧ f ≡ₜ (l ⨟ d)

end Lax149335.LiftDropFactorisation
