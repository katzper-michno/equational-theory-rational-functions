import Lax149335Proofs.Appendix.Naturality
import Lax149335Proofs.Appendix.ProjectionsCoherence
import Lax149335Proofs.Preliminaries.Injectivity

/-!
# Basic facts about the equational theory (appendix)

This file contains the lemmas of the appendix section "Basic facts" that are not already in
`Lax149335Proofs.EquationalTheory.DerivedRules` (case equivalence, uniqueness and functoriality of co-pairing)
or in `Lax149335Proofs.Appendix.Naturality` (naturality of `[]`, `prepend` and `pure`):

* the coherence law relating `fst` with the associator,
* distributivity of co-pairing and of concatenation over `distL` / `distR`,
* the `distL`-`fst` coherence law,
* the two facts about `binconcat` and the empty list.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### Associativity -/

/-- Coherence between the first projection, the associator and the product combinator. -/
theorem fst_prodF_assocR {A A' B B' C : Ty} (f : Term A A') (g : Term B B') :
    (fst (A ⊗ B) C ⨟ prodF f g) ≡ₜ (assocR A B C ⨟ prodF f (fst B C ⨟ g)) := by
  have key : (assocL A B C ⨟ (fst (A ⊗ B) C ⨟ prodF f g)) ≡ₜ prodF f (fst B C ⨟ g) := by
    calc (assocL A B C ⨟ (fst (A ⊗ B) C ⨟ prodF f g))
        ≡ₜ ((assocL A B C ⨟ fst (A ⊗ B) C) ⨟ prodF f g) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id A) (fst B C) ⨟ prodF f g) := PEq.compL _ (Term.assocL_fst A B C)
      _ ≡ₜ prodF (Term.id A ⨟ f) (fst B C ⨟ g) := PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF f (fst B C ⨟ g) := PEq.congr_prodF (PEq.id_comp _) (PEq.refl _)
  calc (fst (A ⊗ B) C ⨟ prodF f g)
      ≡ₜ (Term.id ((A ⊗ B) ⊗ C) ⨟ (fst (A ⊗ B) C ⨟ prodF f g)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((assocR A B C ⨟ assocL A B C) ⨟ (fst (A ⊗ B) C ⨟ prodF f g)) :=
        PEq.compL _ (PEq.symm (PEq.assocR_assocL A B C))
    _ ≡ₜ (assocR A B C ⨟ (assocL A B C ⨟ (fst (A ⊗ B) C ⨟ prodF f g))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (assocR A B C ⨟ prodF f (fst B C ⨟ g)) := PEq.compR _ key

/-- Coherence between the second projection and the associator: two successive second
projections are the left associator followed by one. -/
theorem snd_snd_assocL (A B C : Ty) :
    (snd A (B ⊗ C) ⨟ snd B C) ≡ₜ (assocL A B C ⨟ snd (A ⊗ B) C) := by
  have key : (assocR A B C ⨟ (snd A (B ⊗ C) ⨟ snd B C)) ≡ₜ snd (A ⊗ B) C := by
    calc (assocR A B C ⨟ (snd A (B ⊗ C) ⨟ snd B C))
        ≡ₜ ((assocR A B C ⨟ snd A (B ⊗ C)) ⨟ snd B C) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (snd A B) (Term.id C) ⨟ snd B C) := PEq.compL _ (Term.assocR_snd A B C)
      _ ≡ₜ (snd (A ⊗ B) C ⨟ Term.id C) := PEq.nat_snd _ _
      _ ≡ₜ snd (A ⊗ B) C := PEq.comp_id _
  calc (snd A (B ⊗ C) ⨟ snd B C)
      ≡ₜ (Term.id (A ⊗ (B ⊗ C)) ⨟ (snd A (B ⊗ C) ⨟ snd B C)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((assocL A B C ⨟ assocR A B C) ⨟ (snd A (B ⊗ C) ⨟ snd B C)) :=
        PEq.compL _ (PEq.symm (PEq.assocL_assocR A B C))
    _ ≡ₜ (assocL A B C ⨟ (assocR A B C ⨟ (snd A (B ⊗ C) ⨟ snd B C))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL A B C ⨟ snd (A ⊗ B) C) := PEq.compR _ key

/-! ### Distributivity -/

/-- The inverse of left distributivity absorbs the co-diagonal. -/
theorem undistL_codiag (A C : Ty) :
    (undistL A A C ⨟ prodF (codiag A) (Term.id C)) ≡ₜ codiag (A ⊗ C) := by
  calc (either (prodF (inl A A) (Term.id C)) (prodF (inr A A) (Term.id C)) ⨟
          prodF (codiag A) (Term.id C))
      ≡ₜ either (prodF (inl A A) (Term.id C) ⨟ prodF (codiag A) (Term.id C))
          (prodF (inr A A) (Term.id C) ⨟ prodF (codiag A) (Term.id C)) :=
        either_comp _ _ _
    _ ≡ₜ either (prodF (inl A A ⨟ codiag A) (Term.id C ⨟ Term.id C))
          (prodF (inr A A ⨟ codiag A) (Term.id C ⨟ Term.id C)) :=
        either_congr (PEq.prod_comp _ _ _ _) (PEq.prod_comp _ _ _ _)
    _ ≡ₜ either (prodF (Term.id A) (Term.id C)) (prodF (Term.id A) (Term.id C)) :=
        either_congr (PEq.congr_prodF (PEq.inl_codiag A) (PEq.id_comp _))
          (PEq.congr_prodF (PEq.inr_codiag A) (PEq.id_comp _))
    _ ≡ₜ either (Term.id (A ⊗ C)) (Term.id (A ⊗ C)) :=
        either_congr (PEq.prod_id _ _) (PEq.prod_id _ _)
    _ ≡ₜ (Term.id ((A ⊗ C) ⊕' (A ⊗ C)) ⨟ codiag (A ⊗ C)) :=
        PEq.compL _ (PEq.sum_id _ _)
    _ ≡ₜ codiag (A ⊗ C) := PEq.id_comp _

/-- The inverse of right distributivity absorbs the co-diagonal. -/
theorem undistR_codiag (A C : Ty) :
    (undistR A C C ⨟ prodF (Term.id A) (codiag C)) ≡ₜ codiag (A ⊗ C) := by
  calc (either (prodF (Term.id A) (inl C C)) (prodF (Term.id A) (inr C C)) ⨟
          prodF (Term.id A) (codiag C))
      ≡ₜ either (prodF (Term.id A) (inl C C) ⨟ prodF (Term.id A) (codiag C))
          (prodF (Term.id A) (inr C C) ⨟ prodF (Term.id A) (codiag C)) :=
        either_comp _ _ _
    _ ≡ₜ either (prodF (Term.id A ⨟ Term.id A) (inl C C ⨟ codiag C))
          (prodF (Term.id A ⨟ Term.id A) (inr C C ⨟ codiag C)) :=
        either_congr (PEq.prod_comp _ _ _ _) (PEq.prod_comp _ _ _ _)
    _ ≡ₜ either (prodF (Term.id A) (Term.id C)) (prodF (Term.id A) (Term.id C)) :=
        either_congr (PEq.congr_prodF (PEq.id_comp _) (PEq.inl_codiag C))
          (PEq.congr_prodF (PEq.id_comp _) (PEq.inr_codiag C))
    _ ≡ₜ either (Term.id (A ⊗ C)) (Term.id (A ⊗ C)) :=
        either_congr (PEq.prod_id _ _) (PEq.prod_id _ _)
    _ ≡ₜ (Term.id ((A ⊗ C) ⊕' (A ⊗ C)) ⨟ codiag (A ⊗ C)) :=
        PEq.compL _ (PEq.sum_id _ _)
    _ ≡ₜ codiag (A ⊗ C) := PEq.id_comp _

/-- Co-pairing distributes over the product combinator, on the left. -/
theorem prodF_either_distL {A₁ A₂ B C D : Ty} (f₁ : Term A₁ B) (f₂ : Term A₂ B)
    (f : Term C D) :
    prodF (either f₁ f₂) f ≡ₜ (distL A₁ A₂ C ⨟ either (prodF f₁ f) (prodF f₂ f)) := by
  have hundist :
      (undistL A₁ A₂ C ⨟ prodF (sumF f₁ f₂) f) ≡ₜ
        (sumF (prodF f₁ f) (prodF f₂ f) ⨟ undistL B B D) := by
    calc (either (prodF (inl A₁ A₂) (Term.id C)) (prodF (inr A₁ A₂) (Term.id C)) ⨟
            prodF (sumF f₁ f₂) f)
        ≡ₜ either (prodF (inl A₁ A₂) (Term.id C) ⨟ prodF (sumF f₁ f₂) f)
            (prodF (inr A₁ A₂) (Term.id C) ⨟ prodF (sumF f₁ f₂) f) := either_comp _ _ _
      _ ≡ₜ either (prodF (inl A₁ A₂ ⨟ sumF f₁ f₂) (Term.id C ⨟ f))
            (prodF (inr A₁ A₂ ⨟ sumF f₁ f₂) (Term.id C ⨟ f)) :=
          either_congr (PEq.prod_comp _ _ _ _) (PEq.prod_comp _ _ _ _)
      _ ≡ₜ either (prodF (f₁ ⨟ inl B B) f) (prodF (f₂ ⨟ inr B B) f) :=
          either_congr (PEq.congr_prodF (PEq.nat_inl _ _) (PEq.id_comp _))
            (PEq.congr_prodF (PEq.nat_inr _ _) (PEq.id_comp _))
      _ ≡ₜ either (prodF f₁ f ⨟ prodF (inl B B) (Term.id D))
            (prodF f₂ f ⨟ prodF (inr B B) (Term.id D)) :=
          either_congr
            (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.refl _) (PEq.comp_id _))))
            (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.refl _) (PEq.comp_id _))))
      _ ≡ₜ (sumF (prodF f₁ f) (prodF f₂ f) ⨟
            either (prodF (inl B B) (Term.id D)) (prodF (inr B B) (Term.id D))) :=
          PEq.symm (sumF_either _ _ _ _)
  calc prodF (either f₁ f₂) f
      ≡ₜ (Term.id ((A₁ ⊕' A₂) ⊗ C) ⨟ prodF (either f₁ f₂) f) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((distL A₁ A₂ C ⨟ undistL A₁ A₂ C) ⨟ prodF (either f₁ f₂) f) :=
        PEq.compL _ (PEq.symm (PEq.distL_undistL A₁ A₂ C))
    _ ≡ₜ (distL A₁ A₂ C ⨟ (undistL A₁ A₂ C ⨟ prodF (sumF f₁ f₂ ⨟ codiag B) f)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (distL A₁ A₂ C ⨟ (undistL A₁ A₂ C ⨟
          (prodF (sumF f₁ f₂) f ⨟ prodF (codiag B) (Term.id D)))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.comp_id _)))))
    _ ≡ₜ (distL A₁ A₂ C ⨟ ((undistL A₁ A₂ C ⨟ prodF (sumF f₁ f₂) f) ⨟
          prodF (codiag B) (Term.id D))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (distL A₁ A₂ C ⨟ ((sumF (prodF f₁ f) (prodF f₂ f) ⨟ undistL B B D) ⨟
          prodF (codiag B) (Term.id D))) := PEq.compR _ (PEq.compL _ hundist)
    _ ≡ₜ (distL A₁ A₂ C ⨟ (sumF (prodF f₁ f) (prodF f₂ f) ⨟
          (undistL B B D ⨟ prodF (codiag B) (Term.id D)))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (distL A₁ A₂ C ⨟ (sumF (prodF f₁ f) (prodF f₂ f) ⨟ codiag (B ⊗ D))) :=
        PEq.compR _ (PEq.compR _ (undistL_codiag B D))

/-- Co-pairing distributes over the product combinator, on the right. -/
theorem prodF_either_distR {A₁ A₂ B C D : Ty} (f₁ : Term A₁ B) (f₂ : Term A₂ B)
    (f : Term C D) :
    prodF f (either f₁ f₂) ≡ₜ (distR C A₁ A₂ ⨟ either (prodF f f₁) (prodF f f₂)) := by
  have hundist :
      (undistR C A₁ A₂ ⨟ prodF f (sumF f₁ f₂)) ≡ₜ
        (sumF (prodF f f₁) (prodF f f₂) ⨟ undistR D B B) := by
    calc (either (prodF (Term.id C) (inl A₁ A₂)) (prodF (Term.id C) (inr A₁ A₂)) ⨟
            prodF f (sumF f₁ f₂))
        ≡ₜ either (prodF (Term.id C) (inl A₁ A₂) ⨟ prodF f (sumF f₁ f₂))
            (prodF (Term.id C) (inr A₁ A₂) ⨟ prodF f (sumF f₁ f₂)) := either_comp _ _ _
      _ ≡ₜ either (prodF (Term.id C ⨟ f) (inl A₁ A₂ ⨟ sumF f₁ f₂))
            (prodF (Term.id C ⨟ f) (inr A₁ A₂ ⨟ sumF f₁ f₂)) :=
          either_congr (PEq.prod_comp _ _ _ _) (PEq.prod_comp _ _ _ _)
      _ ≡ₜ either (prodF f (f₁ ⨟ inl B B)) (prodF f (f₂ ⨟ inr B B)) :=
          either_congr (PEq.congr_prodF (PEq.id_comp _) (PEq.nat_inl _ _))
            (PEq.congr_prodF (PEq.id_comp _) (PEq.nat_inr _ _))
      _ ≡ₜ either (prodF f f₁ ⨟ prodF (Term.id D) (inl B B))
            (prodF f f₂ ⨟ prodF (Term.id D) (inr B B)) :=
          either_congr
            (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _))))
            (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _))))
      _ ≡ₜ (sumF (prodF f f₁) (prodF f f₂) ⨟
            either (prodF (Term.id D) (inl B B)) (prodF (Term.id D) (inr B B))) :=
          PEq.symm (sumF_either _ _ _ _)
  calc prodF f (either f₁ f₂)
      ≡ₜ (Term.id (C ⊗ (A₁ ⊕' A₂)) ⨟ prodF f (either f₁ f₂)) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((distR C A₁ A₂ ⨟ undistR C A₁ A₂) ⨟ prodF f (either f₁ f₂)) :=
        PEq.compL _ (PEq.symm (PEq.distR_undistR C A₁ A₂))
    _ ≡ₜ (distR C A₁ A₂ ⨟ (undistR C A₁ A₂ ⨟ prodF f (sumF f₁ f₂ ⨟ codiag B))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (distR C A₁ A₂ ⨟ (undistR C A₁ A₂ ⨟
          (prodF f (sumF f₁ f₂) ⨟ prodF (Term.id D) (codiag B)))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _)))))
    _ ≡ₜ (distR C A₁ A₂ ⨟ ((undistR C A₁ A₂ ⨟ prodF f (sumF f₁ f₂)) ⨟
          prodF (Term.id D) (codiag B))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (distR C A₁ A₂ ⨟ ((sumF (prodF f f₁) (prodF f f₂) ⨟ undistR D B B) ⨟
          prodF (Term.id D) (codiag B))) := PEq.compR _ (PEq.compL _ hundist)
    _ ≡ₜ (distR C A₁ A₂ ⨟ (sumF (prodF f f₁) (prodF f f₂) ⨟
          (undistR D B B ⨟ prodF (Term.id D) (codiag B)))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (distR C A₁ A₂ ⨟ (sumF (prodF f f₁) (prodF f f₂) ⨟ codiag (D ⊗ B))) :=
        PEq.compR _ (PEq.compR _ (undistR_codiag D B))

/-- Co-pairing distributes over concatenation of terms with list outputs. -/
theorem fdot_either_distL {A₁ A₂ C B : Ty} (f₁ : Term A₁ B⋆) (f₂ : Term A₂ B⋆)
    (f : Term C B⋆) :
    (either f₁ f₂ ⊙ f) ≡ₜ (distL A₁ A₂ C ⨟ either (f₁ ⊙ f) (f₂ ⊙ f)) := by
  calc (prodF (either f₁ f₂) f ⨟ binconcat B)
      ≡ₜ ((distL A₁ A₂ C ⨟ either (prodF f₁ f) (prodF f₂ f)) ⨟ binconcat B) :=
        PEq.compL _ (prodF_either_distL f₁ f₂ f)
    _ ≡ₜ (distL A₁ A₂ C ⨟ (either (prodF f₁ f) (prodF f₂ f) ⨟ binconcat B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (distL A₁ A₂ C ⨟ either (prodF f₁ f ⨟ binconcat B) (prodF f₂ f ⨟ binconcat B)) :=
        PEq.compR _ (either_comp _ _ _)

/-- The `distL`-`fst` coherence law. -/
theorem distL_fst (A B C : Ty) :
    (distL A B C ⨟ sumF (fst A C) (fst B C)) ≡ₜ fst (A ⊕' B) C := by
  have key : (undistL A B C ⨟ fst (A ⊕' B) C) ≡ₜ sumF (fst A C) (fst B C) := by
    calc (either (prodF (inl A B) (Term.id C)) (prodF (inr A B) (Term.id C)) ⨟
            fst (A ⊕' B) C)
        ≡ₜ either (prodF (inl A B) (Term.id C) ⨟ fst (A ⊕' B) C)
            (prodF (inr A B) (Term.id C) ⨟ fst (A ⊕' B) C) := either_comp _ _ _
      _ ≡ₜ either (fst A C ⨟ inl A B) (fst B C ⨟ inr A B) :=
          either_congr (PEq.nat_fst _ _) (PEq.nat_fst _ _)
      _ ≡ₜ (sumF (fst A C) (fst B C) ⨟ either (inl A B) (inr A B)) :=
          PEq.symm (sumF_either _ _ _ _)
      _ ≡ₜ (sumF (fst A C) (fst B C) ⨟ Term.id (A ⊕' B)) :=
          PEq.compR _ (either_inl_inr A B)
      _ ≡ₜ sumF (fst A C) (fst B C) := PEq.comp_id _
  calc (distL A B C ⨟ sumF (fst A C) (fst B C))
      ≡ₜ (distL A B C ⨟ (undistL A B C ⨟ fst (A ⊕' B) C)) := PEq.compR _ (PEq.symm key)
    _ ≡ₜ ((distL A B C ⨟ undistL A B C) ⨟ fst (A ⊕' B) C) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((A ⊕' B) ⊗ C) ⨟ fst (A ⊕' B) C) := PEq.compL _ (PEq.distL_undistL A B C)
    _ ≡ₜ fst (A ⊕' B) C := PEq.id_comp _

/-! ### Lists -/

/-- Concatenating with the empty list on the right is the first projection. -/
theorem binconcat_nil_fst (A : Ty) :
    (prodF (Term.id A⋆) (nilT A) ⨟ binconcat A) ≡ₜ fst A⋆ Ty.unit := by
  calc (prodF (Term.id A⋆) (nilT A) ⨟ binconcat A)
      ≡ₜ (Term.id (A⋆ ⊗ Ty.unit) ⨟ (prodF (Term.id A⋆) (nilT A) ⨟ binconcat A)) :=
        PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((fst A⋆ Ty.unit ⨟ unitR A⋆) ⨟ (prodF (Term.id A⋆) (nilT A) ⨟ binconcat A)) :=
        PEq.compL _ (PEq.symm (PEq.fst_unitR A⋆))
    _ ≡ₜ (fst A⋆ Ty.unit ⨟ (unitR A⋆ ⨟ (prodF (Term.id A⋆) (nilT A) ⨟ binconcat A))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (fst A⋆ Ty.unit ⨟ ((unitR A⋆ ⨟ prodF (Term.id A⋆) (nilT A)) ⨟ binconcat A)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (fst A⋆ Ty.unit ⨟ Term.id A⋆) := PEq.compR _ (PEq.binconcat_unitR A)
    _ ≡ₜ fst A⋆ Ty.unit := PEq.comp_id _

/-- Concatenating with the empty list on the left is the second projection. -/
theorem binconcat_nil_snd (A : Ty) :
    (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A) ≡ₜ snd Ty.unit A⋆ := by
  calc (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A)
      ≡ₜ (Term.id (Ty.unit ⊗ A⋆) ⨟ (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A)) :=
        PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((snd Ty.unit A⋆ ⨟ unitL A⋆) ⨟ (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A)) :=
        PEq.compL _ (PEq.symm (PEq.snd_unitL A⋆))
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ (unitL A⋆ ⨟ (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ ((unitL A⋆ ⨟ prodF (nilT A) (Term.id A⋆)) ⨟ binconcat A)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ Term.id A⋆) := PEq.compR _ (PEq.binconcat_unitL A)
    _ ≡ₜ snd Ty.unit A⋆ := PEq.comp_id _

/-- Concatenating with a constantly empty second component is the first projection. -/
theorem prodF_nilconst_binconcat {X Y A : Ty} (f : Term X A⋆) :
    (prodF f (toUnit Y ⨟ nilT A) ⨟ binconcat A) ≡ₜ (fst X Y ⨟ f) := by
  calc (prodF f (toUnit Y ⨟ nilT A) ⨟ binconcat A)
      ≡ₜ ((prodF f (toUnit Y) ⨟ prodF (Term.id A⋆) (nilT A)) ⨟ binconcat A) :=
        PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _))))
    _ ≡ₜ (prodF f (toUnit Y) ⨟ (prodF (Term.id A⋆) (nilT A) ⨟ binconcat A)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF f (toUnit Y) ⨟ fst A⋆ Ty.unit) := PEq.compR _ (binconcat_nil_fst A)
    _ ≡ₜ (fst X Y ⨟ f) := PEq.nat_fst _ _

/-- Concatenating two constantly empty lists gives the constantly empty list. -/
theorem nilconst_prodF_binconcat (X Y A : Ty) :
    (prodF (toUnit X ⨟ nilT A) (toUnit Y ⨟ nilT A) ⨟ binconcat A) ≡ₜ
      (toUnit (X ⊗ Y) ⨟ nilT A) := by
  calc (prodF (toUnit X ⨟ nilT A) (toUnit Y ⨟ nilT A) ⨟ binconcat A)
      ≡ₜ (fst X Y ⨟ (toUnit X ⨟ nilT A)) := prodF_nilconst_binconcat _
    _ ≡ₜ ((fst X Y ⨟ toUnit X) ⨟ nilT A) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (toUnit (X ⊗ Y) ⨟ nilT A) := PEq.compL _ (PEq.unit_unique _ _)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
