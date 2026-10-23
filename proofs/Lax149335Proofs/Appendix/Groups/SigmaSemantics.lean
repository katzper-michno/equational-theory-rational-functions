import Lax149335Proofs.Appendix.Groups.SprefInverse
import Mathlib.Tactic.Set

/-!
# Denotations of the Σ-constructs of the appendix

The appendix proves the consolidation claim (the essential ingredient of the group exchange
lemma) by the *isomorphism trick*: an aperiodic diagram commutes as soon as it commutes
denotationally.  To exploit that one needs to know what the terms of the diagram denote, and
the diagram is built from the constructs `Σ`, `T`, `spref` and `last` of the appendix.

This file computes those denotations.  Every element of `⟦Σ A⟧` is `injSigma A g` applied to
some `a : ⟦A⟧` (`Lax149335Proofs.Term.sigma_cases`), so all the lemmas are stated in that form.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Elements of `Σ A` -/

@[simp] theorem den_sigmaEnc (A : Ty) (n : ℕ) (a : ⟦A⟧) (g : ⟦Ty.finAlph n⟧) :
    (sigmaEnc A n).den (a, g) = (injSigma A g).den a := den_caseR _ a g

@[simp] theorem den_sigmaDec_injSigma (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) (a : ⟦A⟧) :
    (sigmaDec A n).den ((injSigma A g).den a) = (a, g) := by
  have h := congrFun (PEq.sound (injSigma_sigmaDec A g)) a
  simpa using h

/-- Every element of `Σ A` is in one of the summands. -/
theorem sigma_cases (A : Ty) {n : ℕ} (x : ⟦sigmaTy A n⟧) :
    ∃ (a : ⟦A⟧) (g : ⟦Ty.finAlph n⟧), x = (injSigma A g).den a := by
  have h := congrFun (PEq.sound (sigmaDec_sigmaEnc A n)) x
  simp only [den_comp, den_id] at h
  exact ⟨((sigmaDec A n).den x).1, ((sigmaDec A n).den x).2,
    h.symm.trans (den_sigmaEnc A n _ _)⟩

@[simp] theorem den_sigmaCase {A B : Ty} {n : ℕ} (t : ⟦Ty.finAlph n⟧ → Term A B)
    (g : ⟦Ty.finAlph n⟧) (a : ⟦A⟧) :
    (sigmaCase t).den ((injSigma A g).den a) = (t g).den a := by
  have h := congrFun (PEq.sound (injSigma_sigmaCase t g)) a
  simpa using h

@[simp] theorem den_distSigmaR (X A : Ty) : {n : ℕ} → (x : ⟦X⟧) → (g : ⟦Ty.finAlph n⟧) →
    (a : ⟦A⟧) →
    (distSigmaR X A n).den (x, (injSigma A g).den a) = (injSigma (X ⊗ A) g).den (x, a)
  | 0, _, _, _ => rfl
  | (n + 1), x, .inl (), a => rfl
  | (n + 1), x, .inr g, a => by
      show (sumF (Term.id (X ⊗ A)) (distSigmaR X A n)).den
        ((distR X A (sigmaTy A n)).den (x, Sum.inr ((injSigma A g).den a))) = _
      rw [den_distR_inr]
      show Sum.inr ((distSigmaR X A n).den (x, (injSigma A g).den a)) = _
      rw [den_distSigmaR X A x g a]
      rfl

@[simp] theorem den_undistSigmaR (X A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) (x : ⟦X⟧)
    (a : ⟦A⟧) :
    (undistSigmaR X A n).den ((injSigma (X ⊗ A) g).den (x, a)) =
      (x, (injSigma A g).den a) := by
  simp [undistSigmaR]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
