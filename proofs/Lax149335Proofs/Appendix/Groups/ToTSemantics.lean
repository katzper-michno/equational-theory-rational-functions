import Lax149335Proofs.Appendix.Groups.AperiodicEquations
import Lax149335Proofs.Appendix.Groups.SprefInverse

/-!
# The denotation of `toT`

`toT : (Σ A)* → T A` reads a word of `Σ`-annotated letters as an element of
`T A = 1 + (Σ A)* × A`, by splitting off its last letter.  This file computes its denotation
on the empty word and on a word with a last letter, which is what the denotational
computations about `spref` need.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### The denotation of `toT` on a non-empty word -/

theorem den_toT_append (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) (w : List ⟦sigmaTy A n⟧)
    (a : ⟦A⟧) :
    (toT A n).den (w ++ [(injSigma A g).den a]) =
      Sum.inr ((injSigma (((sigmaTy A n)⋆) ⊗ A) g).den (w, a)) := by
  show (sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n)).den
    (unsnocDen (w ++ [(injSigma A g).den a])) = _
  rw [unsnocDen_append_singleton]
  show Sum.inr ((distSigmaR ((sigmaTy A n)⋆) A n).den (w, (injSigma A g).den a)) = _
  rw [den_distSigmaR]

@[simp] theorem den_toT_nil (A : Ty) (n : ℕ) :
    (toT A n).den ([] : List ⟦sigmaTy A n⟧) = Sum.inl () := rfl

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
