import Lax149335Proofs.Appendix.Groups.SigmaTypes
import Lax149335Proofs.Appendix.Groups.Aperiodicity

/-!
# The coding terms of the appendix (appendix, *Grouplifts*)

The appendix relates the group prefix multiplication `pref` to its variant `spref` through
two isomorphisms:

* `A × G ≃ Σ A` (`Lax149335Proofs.Term.sigmaEnc`, `Lax149335Proofs.Term.sigmaDec`);
* `(Σ A)* ≃ T A` (`Lax149335Proofs.Term.toT`, `Lax149335Proofs.Term.fromT`).

This file collects those terms, their inverse laws and their aperiodicity.  They are used
both by the proof of the Simon lift lemma (`Lax149335Proofs.Appendix.Groups.SprefInverse`) and by the
grouplift-drop factorisation of `pref` (`Lax149335Proofs.Appendix.Groups.PrefAsSpref`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### The isomorphism `A × G ≃ Σ A` -/

/-- The co-projection into `Σ A` followed by the decoding is the annotated pairing. -/
theorem injSigma_sigmaDec (A : Ty) : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) →
    (injSigma A g ⨟ sigmaDec A n) ≡ₜ pairR (Term.id A) (constFin g)
  | 0, () => PEq.id_comp _
  | (_ + 1), .inl () => inl_either _ _
  | (n + 1), .inr g => by
      calc ((injSigma A g ⨟ inr A (sigmaTy A n)) ⨟ sigmaDec A (n + 1))
          ≡ₜ (injSigma A g ⨟ (inr A (sigmaTy A n) ⨟ sigmaDec A (n + 1))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (injSigma A g ⨟ (sigmaDec A n ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph n)))) :=
            PEq.compR _ (inr_either _ _)
        _ ≡ₜ ((injSigma A g ⨟ sigmaDec A n) ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph n))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (pairR (Term.id A) (constFin g) ⨟
              prodF (Term.id A) (inr Ty.unit (Ty.finAlph n))) :=
            PEq.compL _ (injSigma_sigmaDec A g)
        _ ≡ₜ pairR (Term.id A) (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) :=
            (pairR_prodF _ _ _ _).trans (pairR_congr (PEq.comp_id _) (PEq.refl _))

theorem sigmaEnc_sigmaDec (A : Ty) (n : ℕ) :
    (sigmaEnc A n ⨟ sigmaDec A n) ≡ₜ Term.id (A ⊗ Ty.finAlph n) := by
  refine caseR_ext _ _ (fun g => ?_)
  calc (pairR (Term.id A) (constFin g) ⨟ (sigmaEnc A n ⨟ sigmaDec A n))
      ≡ₜ ((pairR (Term.id A) (constFin g) ⨟ sigmaEnc A n) ⨟ sigmaDec A n) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.id A ⨟ injSigma A g) ⨟ sigmaDec A n) :=
        PEq.compL _ (pairR_caseR _ _ g)
    _ ≡ₜ (injSigma A g ⨟ sigmaDec A n) := PEq.compL _ (PEq.id_comp _)
    _ ≡ₜ pairR (Term.id A) (constFin g) := injSigma_sigmaDec A g
    _ ≡ₜ (pairR (Term.id A) (constFin g) ⨟ Term.id (A ⊗ Ty.finAlph n)) :=
        PEq.symm (PEq.comp_id _)

/-- Restricting the encoding to the summands other than the first one. -/
theorem prodF_inr_sigmaEnc (A : Ty) (n : ℕ) :
    (prodF (Term.id A) (inr Ty.unit (Ty.finAlph n)) ⨟ sigmaEnc A (n + 1)) ≡ₜ
      (sigmaEnc A n ⨟ inr A (sigmaTy A n)) := by
  refine caseR_ext _ _ (fun g => ?_)
  calc (pairR (Term.id A) (constFin g) ⨟
          (prodF (Term.id A) (inr Ty.unit (Ty.finAlph n)) ⨟ sigmaEnc A (n + 1)))
      ≡ₜ ((pairR (Term.id A) (constFin g) ⨟
          prodF (Term.id A) (inr Ty.unit (Ty.finAlph n))) ⨟ sigmaEnc A (n + 1)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (pairR (Term.id A) (constFin (n := n + 1) (.inr g)) ⨟ sigmaEnc A (n + 1)) :=
        PEq.compL _ ((pairR_prodF _ _ _ _).trans
          (pairR_congr (PEq.comp_id _) (PEq.refl _)))
    _ ≡ₜ (Term.id A ⨟ injSigma A (n := n + 1) (.inr g)) := pairR_caseR _ _ _
    _ ≡ₜ (injSigma A g ⨟ inr A (sigmaTy A n)) := PEq.id_comp _
    _ ≡ₜ ((Term.id A ⨟ injSigma A g) ⨟ inr A (sigmaTy A n)) :=
        PEq.compL _ (PEq.symm (PEq.id_comp _))
    _ ≡ₜ ((pairR (Term.id A) (constFin g) ⨟ sigmaEnc A n) ⨟ inr A (sigmaTy A n)) :=
        PEq.compL _ (PEq.symm (pairR_caseR _ _ g))
    _ ≡ₜ (pairR (Term.id A) (constFin g) ⨟ (sigmaEnc A n ⨟ inr A (sigmaTy A n))) :=
        PEq.comp_assoc _ _ _

theorem sigmaDec_sigmaEnc (A : Ty) : (n : ℕ) →
    (sigmaDec A n ⨟ sigmaEnc A n) ≡ₜ Term.id (sigmaTy A n)
  | 0 => (PEq.compR _ (PEq.comp_id _)).trans (pairR_fst _ _)
  | (n + 1) => by
      have hleft : (pairR (Term.id A) (inl Ty.unit (Ty.finAlph n)) ⨟ sigmaEnc A (n + 1)) ≡ₜ
          inl A (sigmaTy A n) :=
        (pairR_caseR _ _ (n := n + 1) (.inl ())).trans (PEq.id_comp _)
      have hright : ((sigmaDec A n ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph n))) ⨟
          sigmaEnc A (n + 1)) ≡ₜ inr A (sigmaTy A n) := by
        calc ((sigmaDec A n ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph n))) ⨟
                sigmaEnc A (n + 1))
            ≡ₜ (sigmaDec A n ⨟ (prodF (Term.id A) (inr Ty.unit (Ty.finAlph n)) ⨟
                sigmaEnc A (n + 1))) := PEq.comp_assoc _ _ _
          _ ≡ₜ (sigmaDec A n ⨟ (sigmaEnc A n ⨟ inr A (sigmaTy A n))) :=
              PEq.compR _ (prodF_inr_sigmaEnc A n)
          _ ≡ₜ ((sigmaDec A n ⨟ sigmaEnc A n) ⨟ inr A (sigmaTy A n)) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (Term.id (sigmaTy A n) ⨟ inr A (sigmaTy A n)) :=
              PEq.compL _ (sigmaDec_sigmaEnc A n)
          _ ≡ₜ inr A (sigmaTy A n) := PEq.id_comp _
      calc (sigmaDec A (n + 1) ⨟ sigmaEnc A (n + 1))
          ≡ₜ either (pairR (Term.id A) (inl Ty.unit (Ty.finAlph n)) ⨟ sigmaEnc A (n + 1))
              ((sigmaDec A n ⨟ prodF (Term.id A) (inr Ty.unit (Ty.finAlph n))) ⨟
                sigmaEnc A (n + 1)) := either_comp _ _ _
        _ ≡ₜ either (inl A (sigmaTy A n)) (inr A (sigmaTy A n)) := either_congr hleft hright
        _ ≡ₜ Term.id (sigmaTy A (n + 1)) := either_inl_inr _ _

/-! ### The isomorphism `(Σ A)* ≃ T A` -/

/-- The inverse of the distributivity of a product over `Σ`. -/
def undistSigmaR (X A : Ty) (n : ℕ) : Term (sigmaTy (X ⊗ A) n) (X ⊗ sigmaTy A n) :=
  sigmaCase (fun g => prodF (Term.id X) (injSigma A g))

theorem distSigmaR_undistSigmaR (X A : Ty) : (n : ℕ) →
    (distSigmaR X A n ⨟ undistSigmaR X A n) ≡ₜ Term.id (X ⊗ sigmaTy A n)
  | 0 => (PEq.id_comp _).trans (PEq.prod_id _ _)
  | (n + 1) => by
      have hcase :
          sigmaCase (fun g => prodF (Term.id X) (injSigma A g ⨟ inr A (sigmaTy A n))) ≡ₜ
            (undistSigmaR X A n ⨟ prodF (Term.id X) (inr A (sigmaTy A n))) :=
        PEq.symm ((sigmaCase_comp _ _).trans (sigmaCase_congr (fun g =>
          (PEq.prod_comp _ _ _ _).trans (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _)))))
      have hright :
          (distSigmaR X A n ⨟
              sigmaCase (fun g => prodF (Term.id X) (injSigma A g ⨟ inr A (sigmaTy A n)))) ≡ₜ
            prodF (Term.id X) (inr A (sigmaTy A n)) :=
        (PEq.compR _ hcase).trans ((PEq.symm (PEq.comp_assoc _ _ _)).trans
          ((PEq.compL _ (distSigmaR_undistSigmaR X A n)).trans (PEq.id_comp _)))
      calc (distSigmaR X A (n + 1) ⨟ undistSigmaR X A (n + 1))
          ≡ₜ (distR X A (sigmaTy A n) ⨟ (sumF (Term.id (X ⊗ A)) (distSigmaR X A n) ⨟
                undistSigmaR X A (n + 1))) := PEq.comp_assoc _ _ _
        _ ≡ₜ (distR X A (sigmaTy A n) ⨟
              either (Term.id (X ⊗ A) ⨟ prodF (Term.id X) (inl A (sigmaTy A n)))
                (distSigmaR X A n ⨟ sigmaCase (fun g =>
                  prodF (Term.id X) (injSigma A g ⨟ inr A (sigmaTy A n))))) :=
            PEq.compR _ (sumF_either _ _ _ _)
        _ ≡ₜ (distR X A (sigmaTy A n) ⨟ undistR X A (sigmaTy A n)) :=
            PEq.compR _ (either_congr (PEq.id_comp _) hright)
        _ ≡ₜ Term.id (X ⊗ sigmaTy A (n + 1)) := PEq.distR_undistR X A (sigmaTy A n)

/-- The inverse of `toT`. -/
def fromT (A : Ty) (n : ℕ) : Term (tTy A n) ((sigmaTy A n)⋆) :=
  sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n) ⨟ snoc (sigmaTy A n)

theorem toT_fromT (A : Ty) (n : ℕ) :
    (toT A n ⨟ fromT A n) ≡ₜ Term.id ((sigmaTy A n)⋆) := by
  have hmid : (sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n) ⨟
      sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n)) ≡ₜ
        Term.id (Ty.unit ⊕' (((sigmaTy A n)⋆) ⊗ sigmaTy A n)) :=
    (PEq.sum_comp _ _ _ _).trans ((PEq.congr_sumF (PEq.id_comp _)
      (distSigmaR_undistSigmaR _ A n)).trans (PEq.sum_id _ _))
  calc (toT A n ⨟ fromT A n)
      ≡ₜ (unsnoc (sigmaTy A n) ⨟ (sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n) ⨟
            (sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n) ⨟
              snoc (sigmaTy A n)))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unsnoc (sigmaTy A n) ⨟ ((sumF (Term.id Ty.unit) (distSigmaR ((sigmaTy A n)⋆) A n) ⨟
            sumF (Term.id Ty.unit) (undistSigmaR ((sigmaTy A n)⋆) A n)) ⨟
              snoc (sigmaTy A n))) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (unsnoc (sigmaTy A n) ⨟ (Term.id (Ty.unit ⊕' (((sigmaTy A n)⋆) ⊗ sigmaTy A n)) ⨟
            snoc (sigmaTy A n))) := PEq.compR _ (PEq.compL _ hmid)
    _ ≡ₜ (unsnoc (sigmaTy A n) ⨟ snoc (sigmaTy A n)) := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id ((sigmaTy A n)⋆) := PEq.unsnoc_snoc _

/-! ### Aperiodicity of the coding terms -/

theorem usesPref_injSigma (A : Ty) : {n : ℕ} → (g : ⟦Ty.finAlph n⟧) →
    usesPref (injSigma A g) = false
  | 0, _ => rfl
  | (_ + 1), .inl _ => rfl
  | (_ + 1), .inr g => by simp [injSigma, usesPref, usesPref_injSigma A g]

theorem usesPref_sigmaCase {A B : Ty} : {n : ℕ} → (t : ⟦Ty.finAlph n⟧ → Term A B) →
    (∀ g, usesPref (t g) = false) → usesPref (sigmaCase t) = false
  | 0, t, h => h ()
  | (_ + 1), t, h => by
      simp [sigmaCase, either, usesPref, h (.inl ()),
        usesPref_sigmaCase (fun g => t (.inr g)) (fun g => h (.inr g))]

@[simp] theorem usesPref_sigmaEnc (A : Ty) (n : ℕ) : usesPref (sigmaEnc A n) = false :=
  usesPref_caseR _ (fun g => usesPref_injSigma A g)

@[simp] theorem usesPref_sigmaDec (A : Ty) : (n : ℕ) → usesPref (sigmaDec A n) = false
  | 0 => rfl
  | (n + 1) => by simp [sigmaDec, either, usesPref, usesPref_sigmaDec A n]

@[simp] theorem usesPref_undistSigmaR (X A : Ty) (n : ℕ) :
    usesPref (undistSigmaR X A n) = false :=
  usesPref_sigmaCase _ (fun g => by simp [usesPref, usesPref_injSigma A g])

@[simp] theorem usesPref_fromT (A : Ty) (n : ℕ) : usesPref (fromT A n) = false := by
  simp [fromT, usesPref]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
