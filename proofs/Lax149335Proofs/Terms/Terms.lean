import Lax149335Proofs.RationalFunctions.Types

/-!
# Rational terms (Section 3)

Rational terms, their denotation and aperiodic terms are defined in the concept
`Lax149335.Terms`. This file adds the notation `⟦f⟧ₜ` for the denotation and the basic
facts about aperiodicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-- Notation `⟦f⟧ₜ` for the denotation of a rational term. -/
scoped notation "⟦" f "⟧ₜ" => Term.den f

end Term

namespace Term

@[simp] theorem isAperiodic_comp {A B C : Ty} (f : Term A B) (g : Term B C) :
    IsAperiodic (f ⨟ g) ↔ IsAperiodic f ∧ IsAperiodic g := by
  simp [IsAperiodic, usesPref]

@[simp] theorem isAperiodic_prodF {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂) :
    IsAperiodic (prodF f g) ↔ IsAperiodic f ∧ IsAperiodic g := by
  simp [IsAperiodic, usesPref]

@[simp] theorem isAperiodic_sumF {A₁ A₂ B₁ B₂ : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂) :
    IsAperiodic (sumF f g) ↔ IsAperiodic f ∧ IsAperiodic g := by
  simp [IsAperiodic, usesPref]

@[simp] theorem isAperiodic_listF {A B : Ty} (f : Term A B) :
    IsAperiodic (listF f) ↔ IsAperiodic f := by
  simp [IsAperiodic, usesPref]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
