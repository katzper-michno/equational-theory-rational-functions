import Lax149335Proofs.Bridge

/-!
# Types (Section 2.2 of the paper)

The types, their denotations and string representations, and finite alphabets are defined
in the concept `Lax149335.Types`. This file adds decidable equality of the elements of a
type and the `k`-fold product of a type with itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Ty

/-- Elements of a type can be compared for equality. -/
def decEqDen : (A : Ty) → DecidableEq ⟦A⟧
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .prod A B => letI := decEqDen A; letI := decEqDen B; inferInstanceAs (DecidableEq (_ × _))
  | .sum A B => letI := decEqDen A; letI := decEqDen B; inferInstanceAs (DecidableEq (_ ⊕ _))
  | .list A => letI := decEqDen A; inferInstanceAs (DecidableEq (List _))

instance instDecidableEqDen (A : Ty) : DecidableEq ⟦A⟧ := decEqDen A

/-- The `k`-fold product `Aᵏ` of a type with itself, with `A⁰ = 1`. -/
def pow (A : Ty) : ℕ → Ty
  | 0 => Ty.unit
  | (k + 1) => Ty.prod A (pow A k)

end Ty

end Lax149335Proofs

bridge_export Lax149335Proofs
