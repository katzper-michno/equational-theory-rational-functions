import Lax149335Proofs.Appendix.Groups.ProductConsolidation
import Lax149335Proofs.Appendix.Groups.AnyTermDrop

/-!
# Reducing an equation about `spref` to a denotational one

Every equation about the group prefix multiplication that the appendix has to prove has
`spref` on one side only.  Since `spref` is invertible, such an equation is equivalent to an
equation between *aperiodic* terms, and by Corollary 7.6 an aperiodic equation only has to be
checked denotationally.

This file records the two resulting tools: `Lax149335Proofs.peq_of_den` for an aperiodic equation,
and `Lax149335Proofs.peq_comp_spref` for an equation of the form `L ; spref ≡ R`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Two tools for the equations

Every equation that the induction has to prove has the group prefix multiplication on one
side only, and `spref` is invertible, so all of them are reduced to *aperiodic* equations,
which by Corollary 7.6 only have to be checked denotationally. -/

/-- An aperiodic equation only has to be checked denotationally (Corollary 7.6). -/
theorem peq_of_den {X Y : Ty} {f g : Term X Y} (hf : IsAperiodic f) (hg : IsAperiodic g)
    (h : ∀ x, f.den x = g.den x) : f ≡ₜ g :=
  completeness_aperiodic f g hf hg (funext h)

/-- An equation `L ; spref ≡ R` between aperiodic terms `L` and `R` only has to be checked
denotationally, after `spref` has been replaced by its inverse `unspref`. -/
theorem peq_comp_spref {X A : Ty} {n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    (L : Term X ((sigmaTy A n)⋆)) (R : Term X (tTy A n))
    (hL : IsAperiodic L) (hR : IsAperiodic R)
    (h : ∀ x, L.den x = (unspref A G).den (R.den x)) : (L ⨟ spref A G) ≡ₜ R := by
  have h1 : L ≡ₜ (R ⨟ unspref A G) := by
    refine peq_of_den hL ?_ h
    simpa [IsAperiodic, usesPref] using hR
  calc (L ⨟ spref A G) ≡ₜ ((R ⨟ unspref A G) ⨟ spref A G) := PEq.compL _ h1
    _ ≡ₜ (R ⨟ (unspref A G ⨟ spref A G)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (R ⨟ Term.id (tTy A n)) := PEq.compR _ (unspref_spref A G)
    _ ≡ₜ R := PEq.comp_id _


end Lax149335Proofs

bridge_export Lax149335Proofs
