import Lax149335Proofs.Terms.Terms

/-!
# Derived terms and notation (Sections 3.1.2, 4.4, 4.6 and 5.1)

This file collects the derived combinators used throughout the paper: co-pairing, the
notation `[]`, `pure`, `prepend`, `append`, `binconcat` from Section 4.6, the inverses
`undistL`, `undistR`, `unblock`, `unpref` of Section 4.4, the concatenation maps of
Section 5.1, and the terms `shift` / `unshift` from Table 1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Values and concatenation with values (Section 5.2) -/

/-! ### Every type is inhabited by a value -/

/-- A canonical value `1 → A` of an arbitrary type, showing that every type is inhabited. -/
def defaultValue : (A : Ty) → Value A
  | .unit => Term.id Ty.unit
  | .prod A B => unitR Ty.unit ⨟ prodF (defaultValue A) (defaultValue B)
  | .sum A B => defaultValue A ⨟ inl A B
  | .list A => nilT A

/-! ### Concatenation maps (Section 5.1) -/

/-- The functorial action of a one-parameter type constructor on a rational term. -/
def TyF.map : (F : TyF) → {A B : Ty} → Term A B → Term (F.app A) (F.app B)
  | .param, _, _, f => f
  | .unit, _, _, _ => id Ty.unit
  | .prod F G, _, _, f => prodF (TyF.map F f) (TyF.map G f)
  | .sum F G, _, _, f => sumF (TyF.map F f) (TyF.map G f)
  | .list F, _, _, f => listF (TyF.map F f)

/-! ### The terms `shift` and `unshift` of Table 1 -/

/-! ### Terms for finite alphabets and the inverse of the group prefix operation -/

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
