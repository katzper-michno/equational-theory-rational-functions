import Lax149335Proofs.Appendix.Groups.SigmaCoding
import Lax149335Proofs.Appendix.Groups.Aperiodicity
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Set

/-!
# The inverse of `spref` (appendix, *Completeness in the presence of groups*)

The appendix works with the variant `spref : (Σ A)* → T A` of the group prefix
multiplication, where `Σ A` is the `|G|`-fold co-product of `A` and `T A = 1 + (Σ A)* × A`.
This file constructs its inverse `unspref` (`Lax149335Proofs.Term.unspref`) and proves the two
inverse laws `Lax149335Proofs.Term.spref_unspref` and `Lax149335Proofs.Term.unspref_spref`, together with
the inverse laws for the two isomorphisms they are built from,
`Lax149335Proofs.Term.undistSigmaR_distSigmaR` and `Lax149335Proofs.Term.fromT_toT`.

Since `spref` is invertible, an equation with `spref` on one side only can be turned into an
*aperiodic* equation; the last section of the file records that the `Σ`-constructs and
`unspref` are indeed aperiodic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### The inverse of `spref` -/

/-- Distributivity of a product over `Σ` is a lift. -/
theorem isLift_distSigmaR (X A : Ty) : (n : ℕ) → IsLift (distSigmaR X A n)
  | 0 => IsLift.id _
  | (n + 1) =>
      IsLift.comp (IsLift.distR _ _ _) (IsLift.sumF (IsLift.id _) (isLift_distSigmaR X A n))

/-- The inverse law for distributivity over `Σ`, in the direction that
`Lax149335Proofs.Term.distSigmaR_undistSigmaR` does not cover. -/
theorem undistSigmaR_distSigmaR (X A : Ty) (n : ℕ) :
    (undistSigmaR X A n ⨟ distSigmaR X A n) ≡ₜ Term.id (sigmaTy (X ⊗ A) n) := by
  obtain ⟨pi, -, h₁, h₂⟩ := lift_iso (distSigmaR X A n) (isLift_distSigmaR X A n)
  -- the two-sided inverse of a lift is unique, so `undistSigmaR` is `pi`
  have hpi : undistSigmaR X A n ≡ₜ pi := by
    calc undistSigmaR X A n ≡ₜ (Term.id (sigmaTy (X ⊗ A) n) ⨟ undistSigmaR X A n) :=
          PEq.symm (PEq.id_comp _)
      _ ≡ₜ ((pi ⨟ distSigmaR X A n) ⨟ undistSigmaR X A n) := PEq.compL _ (PEq.symm h₂)
      _ ≡ₜ (pi ⨟ (distSigmaR X A n ⨟ undistSigmaR X A n)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (pi ⨟ Term.id (X ⊗ sigmaTy A n)) :=
          PEq.compR _ (distSigmaR_undistSigmaR X A n)
      _ ≡ₜ pi := PEq.comp_id _
  exact (PEq.compL _ hpi).trans h₂

/-- `fromT` is a two-sided inverse of `toT`. -/
theorem fromT_toT (A : Ty) (n : ℕ) :
    (fromT A n ⨟ toT A n) ≡ₜ Term.id (tTy A n) := by
  have hmid : (sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n) ⨟
      sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n)) ≡ₜ Term.id (tTy A n) :=
    (PEq.sum_comp _ _ _ _).trans ((PEq.congr_sumF (PEq.id_comp _)
      (undistSigmaR_distSigmaR _ A n)).trans (PEq.sum_id _ _))
  calc (fromT A n ⨟ toT A n)
      ≡ₜ (sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n) ⨟
            (snoc (sigmaTy A n) ⨟ (unsnoc (sigmaTy A n) ⨟
              sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n)))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n) ⨟
            ((snoc (sigmaTy A n) ⨟ unsnoc (sigmaTy A n)) ⨟
              sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n) ⨟
            (Term.id (Ty.unit ⊕' (((sigmaTy A n)⋆) ⊗ sigmaTy A n)) ⨟
              sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n))) :=
        PEq.compR _ (PEq.compL _ (PEq.snoc_unsnoc _))
    _ ≡ₜ (sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n) ⨟
            sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n)) :=
        PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id (tTy A n) := hmid

/-- Cancelling a two-sided inverse in the middle of a composition. -/
theorem comp_cancel_mid {A B C D : Ty} {f : Term A B} {g : Term B C} {h : Term C B}
    {k : Term B D} (hgh : (g ⨟ h) ≡ₜ Term.id B) : ((f ⨟ g) ⨟ (h ⨟ k)) ≡ₜ (f ⨟ k) :=
  calc ((f ⨟ g) ⨟ (h ⨟ k)) ≡ₜ (f ⨟ (g ⨟ (h ⨟ k))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (f ⨟ ((g ⨟ h) ⨟ k)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (f ⨟ (Term.id B ⨟ k)) := PEq.compR _ (PEq.compL _ hgh)
    _ ≡ₜ (f ⨟ k) := PEq.compR _ (PEq.id_comp _)

/-- The inverse `unspref : T A ⇒ (Σ A)*` of the variant `spref` of the group prefix
multiplication used in the appendix. -/
def unspref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) : Term (tTy A n) ((sigmaTy A n)⋆) :=
  fromT A n ⨟ (listF (sigmaDec A n) ⨟ (unpref A G ⨟ listF (sigmaEnc A n)))

theorem spref_unspref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (spref A G ⨟ unspref A G) ≡ₜ Term.id ((sigmaTy A n)⋆) := by
  have hED : (listF (sigmaEnc A n) ⨟ listF (sigmaDec A n)) ≡ₜ Term.id ((A ⊗ Ty.finAlph n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaEnc_sigmaDec A n)).trans (PEq.list_id _))
  have hDE : (listF (sigmaDec A n) ⨟ listF (sigmaEnc A n)) ≡ₜ Term.id ((sigmaTy A n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaDec_sigmaEnc A n)).trans (PEq.list_id _))
  calc (spref A G ⨟ unspref A G)
      ≡ₜ (((listF (sigmaDec A n) ⨟ pref A G) ⨟ listF (sigmaEnc A n)) ⨟
            (listF (sigmaDec A n) ⨟ (unpref A G ⨟ listF (sigmaEnc A n)))) :=
        comp_cancel_mid (toT_fromT A n)
    _ ≡ₜ ((listF (sigmaDec A n) ⨟ pref A G) ⨟ (unpref A G ⨟ listF (sigmaEnc A n))) :=
        comp_cancel_mid hED
    _ ≡ₜ (listF (sigmaDec A n) ⨟ listF (sigmaEnc A n)) :=
        comp_cancel_mid (PEq.pref_unpref A G)
    _ ≡ₜ Term.id ((sigmaTy A n)⋆) := hDE

theorem unspref_spref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (unspref A G ⨟ spref A G) ≡ₜ Term.id (tTy A n) := by
  have hED : (listF (sigmaEnc A n) ⨟ listF (sigmaDec A n)) ≡ₜ Term.id ((A ⊗ Ty.finAlph n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaEnc_sigmaDec A n)).trans (PEq.list_id _))
  have hDE : (listF (sigmaDec A n) ⨟ listF (sigmaEnc A n)) ≡ₜ Term.id ((sigmaTy A n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaDec_sigmaEnc A n)).trans (PEq.list_id _))
  have hinner :
      ((unpref A G ⨟ listF (sigmaEnc A n)) ⨟ (listF (sigmaDec A n) ⨟ pref A G)) ≡ₜ
        Term.id ((A ⊗ Ty.finAlph n)⋆) :=
    (comp_cancel_mid hED).trans (PEq.unpref_pref A G)
  have houter :
      ((listF (sigmaDec A n) ⨟ (unpref A G ⨟ listF (sigmaEnc A n))) ⨟
        ((listF (sigmaDec A n) ⨟ pref A G) ⨟ listF (sigmaEnc A n))) ≡ₜ
          Term.id ((sigmaTy A n)⋆) :=
    (comp_cancel_mid hinner).trans hDE
  exact (comp_cancel_mid houter).trans (fromT_toT A n)

/-! ### The Σ-constructs are aperiodic -/

@[simp] theorem usesPref_distSigmaR (X A : Ty) : (n : ℕ) → usesPref (distSigmaR X A n) = false
  | 0 => rfl
  | (n + 1) => by simp [distSigmaR, usesPref, usesPref_distSigmaR X A n]

@[simp] theorem usesPref_toT (A : Ty) (n : ℕ) : usesPref (toT A n) = false := by
  simp [toT, usesPref]

@[simp] theorem usesPref_unspref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesPref (unspref A G) = false := by
  simp [unspref, usesPref]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
