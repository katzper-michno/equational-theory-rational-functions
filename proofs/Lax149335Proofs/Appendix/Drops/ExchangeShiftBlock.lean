import Lax149335Proofs.Appendix.Drops.ExchangeProof

/-!
# The two hard cases of the exchange lemma (appendix, *Proof of Exchange Lemma*)

`Lax149335Proofs.Appendix.Drops.ExchangeProof` reduces the exchange lemma (Lemma 7.5) to the two
prime lifts `shift` and `block`: `Lax149335Proofs.exchange_aux` proves that every lift admits
exchange as soon as those two do.

This file proves the case *Shift*: every drop followed by the prime lift `shift` has a
lift-drop factorisation (`Lax149335Proofs.admitsExchange_shift`).  The drop is put in normal form by
the list normalisation lemma (`Lax149335Proofs.drop_normListable`), and the normal form followed by
`shift` is handled by the shift exchange lemma
(`Lax149335Proofs.exchange_normal_shift`), whose conclusion is a lift followed by a term
provably equal to a drop (`Lax149335Proofs.IsShiftExchangeShape.isEqDrop`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- **The case *Shift* of the exchange lemma** (appendix).  Every drop with codomain
`(S × T)*`, followed by the prime lift `shift`, has a lift-drop factorisation. -/
theorem admitsExchange_shift (S T : Ty) : AdmitsExchange (Term.shift S T) := by
  intro A d hd
  obtain ⟨D, alpha, g, ha, hg, he⟩ := drop_normListable d hd
  obtain ⟨E, beta, k, hb, hk, hek⟩ := exchange_normal_shift hg
  refine IsLiftDrop.congr ((PEq.compL _ he).trans (PEq.comp_assoc _ _ _)) ?_
  exact IsLiftDrop.comp_left ha
    (IsLiftDrop.congr hek (IsLiftDrop.comp_left hb (IsLiftDrop.of_isEqDrop hk.isEqDrop)))

end Lax149335Proofs

bridge_export Lax149335Proofs
