import Lax149335.LiftsAndDrops
import Lax149335.EquationalTheory

/-!
---
title: Lifts are isomorphisms
type: lemma
---
Every lift is an isomorphism, and its inverse is a drop.
-/

namespace Lax149335.LiftInverses

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory Lax149335.LiftsAndDrops

/-- Every lift `f : A → B` has an inverse `g : B → A` that is a drop. -/
axiom lift_iso {A B : Ty} (f : Term A B) (hf : IsLift f) :
    ∃ g : Term B A, IsDrop g ∧ (f ⨟ g) ≡ₜ Term.id A ∧ (g ⨟ f) ≡ₜ Term.id B

end Lax149335.LiftInverses
