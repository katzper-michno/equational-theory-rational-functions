import Lax149335Proofs.GeneralCompleteness.Statements
import Lax149335Proofs.Appendix.Drops.FunctorTools
import Lax149335Proofs.Appendix.Drops.DropNormalisation
import Lax149335Proofs.Appendix.Drops.ListNormalisation
import Lax149335Proofs.Appendix.Groups.Aperiodicity
import Lax149335Proofs.Appendix.Groups.SigmaTypes

/-!
# The canonical term into an arbitrary type is a drop

`Lax149335Proofs.Term.anyTerm A B` is the composition of `A → 1` with the default value of `B`; it
is a drop, which is how the appendix produces drops into the summands of a co-product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Drop injections -/

theorem isDrop_anyTerm (A B : Ty) : IsDrop (Term.anyTerm A B) :=
  IsDrop.bangV A (Term.defaultValue B)

end Lax149335Proofs

bridge_export Lax149335Proofs
