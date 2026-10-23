import Lax149335Proofs.Appendix.Groups.Unprefixing
import Mathlib.Tactic.Set
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.TransferInstance

/-!
# Constants into a finite alphabet are aperiodic

The group part of the appendix builds terms out of the constants `Lax149335Proofs.Term.constFin`
into a finite alphabet.  This file records that such a constant does not use the group prefix
multiplication, which is what the aperiodicity arguments about those terms need.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### The terms of this section are aperiodic -/

/-- The values picking out a letter of a finite alphabet do not use the group prefix
multiplication. -/
theorem usesPref_constFin : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) → usesPref (constFin g) = false
  | 0, _ => rfl
  | (_ + 1), .inl _ => rfl
  | (_ + 1), .inr g => by simp [constFin, usesPref, usesPref_constFin g]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
