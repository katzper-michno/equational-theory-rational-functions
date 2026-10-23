import Lax149335Proofs.GeneralCompleteness.Statements
import Lax149335Proofs.Appendix.Drops.FunctorTools
import Lax149335Proofs.Appendix.Drops.DropNormalisation
import Lax149335Proofs.Appendix.Drops.ListNormalisation
import Lax149335Proofs.Appendix.Groups.Aperiodicity
import Lax149335Proofs.Appendix.Groups.SigmaTypes
import Lax149335Proofs.Appendix.Groups.AnyTermDrop
import Lax149335Proofs.Appendix.Groups.AperiodicDrops
import Mathlib.Tactic.Choose
import Lax149335Proofs.Appendix.Groups.SigmaCoding
import Lax149335Proofs.GeneralCompleteness.LiftsAndDrops
import Lax149335Proofs.Appendix.Groups.SprefInverse
import Lax149335Proofs.Appendix.Groups.ToTSemantics
import Mathlib.Tactic.Set
import Lax149335Proofs.Appendix.Groups.AperiodicEquations
import Lax149335Proofs.Appendix.Groups.ProductConsolidation

/-!
# The group prefix multiplication as `spref` (appendix, *Grouplifts*)

The appendix works with the variant `spref` of the group prefix multiplication rather than
with the atomic function `pref` itself.  This file relates the two: `pref` is provably equal
to `spref` conjugated by the isomorphisms `A × G ≃ Σ A` and `(Σ A)* ≃ T A`
(`Lax149335Proofs.Term.pref_eq_spref`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The group prefix multiplication has a grouplift-drop factorisation -/

/-- The group prefix multiplication is the appendix variant `spref`, conjugated by the two
isomorphisms `A × G ≃ Σ A` and `(Σ A)* ≃ T A`. -/
theorem Term.pref_eq_spref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term.pref A G ≡ₜ
      (Term.listF (Term.sigmaEnc A n) ⨟ Term.spref A G ⨟ Term.fromT A n ⨟
        Term.listF (Term.sigmaDec A n)) := by
  have hED : (Term.listF (Term.sigmaEnc A n) ⨟ Term.listF (Term.sigmaDec A n)) ≡ₜ
      Term.id ((A ⊗ Ty.finAlph n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (Term.sigmaEnc_sigmaDec A n)).trans (PEq.list_id _))
  have hinner : (Term.listF (Term.sigmaEnc A n) ⨟
      ((Term.listF (Term.sigmaDec A n) ⨟ Term.pref A G) ⨟ Term.listF (Term.sigmaEnc A n))) ≡ₜ
        (Term.pref A G ⨟ Term.listF (Term.sigmaEnc A n)) := by
    calc (Term.listF (Term.sigmaEnc A n) ⨟
          ((Term.listF (Term.sigmaDec A n) ⨟ Term.pref A G) ⨟ Term.listF (Term.sigmaEnc A n)))
        ≡ₜ ((Term.listF (Term.sigmaEnc A n) ⨟
            (Term.listF (Term.sigmaDec A n) ⨟ Term.pref A G)) ⨟
              Term.listF (Term.sigmaEnc A n)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((Term.listF (Term.sigmaEnc A n) ⨟ Term.listF (Term.sigmaDec A n)) ⨟
              Term.pref A G) ⨟ Term.listF (Term.sigmaEnc A n)) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((Term.id ((A ⊗ Ty.finAlph n)⋆) ⨟ Term.pref A G) ⨟
            Term.listF (Term.sigmaEnc A n)) := PEq.compL _ (PEq.compL _ hED)
      _ ≡ₜ (Term.pref A G ⨟ Term.listF (Term.sigmaEnc A n)) :=
          PEq.compL _ (PEq.id_comp _)
  refine PEq.symm ?_
  calc (Term.listF (Term.sigmaEnc A n) ⨟ Term.spref A G ⨟ Term.fromT A n ⨟
        Term.listF (Term.sigmaDec A n))
      ≡ₜ ((((Term.pref A G ⨟ Term.listF (Term.sigmaEnc A n)) ⨟ Term.toT A n) ⨟
            Term.fromT A n) ⨟ Term.listF (Term.sigmaDec A n)) :=
        PEq.compL _ (PEq.compL _
          ((PEq.symm (PEq.comp_assoc _ _ _)).trans (PEq.compL _ hinner)))
    _ ≡ₜ (((Term.pref A G ⨟ Term.listF (Term.sigmaEnc A n)) ⨟
          (Term.toT A n ⨟ Term.fromT A n)) ⨟ Term.listF (Term.sigmaDec A n)) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((Term.pref A G ⨟ Term.listF (Term.sigmaEnc A n)) ⨟
          Term.id ((Term.sigmaTy A n)⋆)) ⨟ Term.listF (Term.sigmaDec A n)) :=
        PEq.compL _ (PEq.compR _ (Term.toT_fromT A n))
    _ ≡ₜ ((Term.pref A G ⨟ Term.listF (Term.sigmaEnc A n)) ⨟
          Term.listF (Term.sigmaDec A n)) := PEq.compL _ (PEq.comp_id _)
    _ ≡ₜ (Term.pref A G ⨟ (Term.listF (Term.sigmaEnc A n) ⨟
          Term.listF (Term.sigmaDec A n))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.pref A G ⨟ Term.id ((A ⊗ Ty.finAlph n)⋆)) := PEq.compR _ hED
    _ ≡ₜ Term.pref A G := PEq.comp_id _

end Lax149335Proofs

bridge_export Lax149335Proofs
