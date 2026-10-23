import Lax149335Proofs.EquationalTheory.Axioms

/-!
# Basic derived rules of the equational theory

A handful of consequences of Axioms 1-5 that are used over and over again: the computation
and uniqueness rules for co-pairing, the fact that the derived terms `comm`, `undistL`,
`undistR`, `shift` and `unshift` are (one-sided) inverses of the corresponding atomic
functions, and some abbreviations for equational reasoning.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace PEq

variable {A B C D : Ty}

/-- Rewriting on the left of a composition. -/
theorem compL {f f' : Term A B} (g : Term B C) (h : f ≡ₜ f') : (f ⨟ g) ≡ₜ (f' ⨟ g) :=
  PEq.congr_comp h (PEq.refl g)

/-- Rewriting on the right of a composition. -/
theorem compR (f : Term A B) {g g' : Term B C} (h : g ≡ₜ g') : (f ⨟ g) ≡ₜ (f ⨟ g') :=
  PEq.congr_comp (PEq.refl f) h

end PEq

namespace Term

variable {A B C : Ty}

/-- Composing with the identity on the left, in the reverse direction. -/
theorem id_comp_symm (f : Term A B) : f ≡ₜ (Term.id A ⨟ f) := PEq.symm (PEq.id_comp f)

/-- The computation rule for co-pairing on the left summand. -/
theorem inl_either {A₁ A₂ B : Ty} (f : Term A₁ B) (g : Term A₂ B) :
    (inl A₁ A₂ ⨟ either f g) ≡ₜ f := by
  calc (inl A₁ A₂ ⨟ (sumF f g ⨟ codiag B))
      ≡ₜ ((inl A₁ A₂ ⨟ sumF f g) ⨟ codiag B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((f ⨟ inl B B) ⨟ codiag B) := PEq.compL _ (PEq.nat_inl f g)
    _ ≡ₜ (f ⨟ (inl B B ⨟ codiag B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (f ⨟ Term.id B) := PEq.compR _ (PEq.inl_codiag B)
    _ ≡ₜ f := PEq.comp_id f

/-- The computation rule for co-pairing on the right summand. -/
theorem inr_either {A₁ A₂ B : Ty} (f : Term A₁ B) (g : Term A₂ B) :
    (inr A₁ A₂ ⨟ either f g) ≡ₜ g := by
  calc (inr A₁ A₂ ⨟ (sumF f g ⨟ codiag B))
      ≡ₜ ((inr A₁ A₂ ⨟ sumF f g) ⨟ codiag B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((g ⨟ inr B B) ⨟ codiag B) := PEq.compL _ (PEq.nat_inr f g)
    _ ≡ₜ (g ⨟ (inr B B ⨟ codiag B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (g ⨟ Term.id B) := PEq.compR _ (PEq.inr_codiag B)
    _ ≡ₜ g := PEq.comp_id g

/-- The uniqueness rule for co-pairing: every term out of a co-product is the co-pairing of
its two components. -/
theorem either_unique {A₁ A₂ B : Ty} (h : Term (A₁ ⊕' A₂) B) :
    h ≡ₜ either (inl A₁ A₂ ⨟ h) (inr A₁ A₂ ⨟ h) := by
  calc h ≡ₜ (Term.id (A₁ ⊕' A₂) ⨟ h) := id_comp_symm h
    _ ≡ₜ ((sumF (inl A₁ A₂) (inr A₁ A₂) ⨟ codiag (A₁ ⊕' A₂)) ⨟ h) :=
        PEq.compL _ (PEq.symm (PEq.sum_inl_inr_codiag A₁ A₂))
    _ ≡ₜ (sumF (inl A₁ A₂) (inr A₁ A₂) ⨟ (codiag (A₁ ⊕' A₂) ⨟ h)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (sumF (inl A₁ A₂) (inr A₁ A₂) ⨟ (sumF h h ⨟ codiag B)) :=
        PEq.compR _ (PEq.symm (PEq.nat_codiag h))
    _ ≡ₜ ((sumF (inl A₁ A₂) (inr A₁ A₂) ⨟ sumF h h) ⨟ codiag B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (sumF (inl A₁ A₂ ⨟ h) (inr A₁ A₂ ⨟ h) ⨟ codiag B) :=
        PEq.compL _ (PEq.sum_comp _ _ _ _)

/-- Congruence for co-pairing. -/
theorem either_congr {A₁ A₂ B : Ty} {f f' : Term A₁ B} {g g' : Term A₂ B}
    (hf : f ≡ₜ f') (hg : g ≡ₜ g') : either f g ≡ₜ either f' g' :=
  PEq.compL _ (PEq.congr_sumF hf hg)

/-- Two terms out of a co-product are provably equal as soon as their two components are. -/
theorem either_ext {A₁ A₂ B : Ty} (h h' : Term (A₁ ⊕' A₂) B)
    (hl : (inl A₁ A₂ ⨟ h) ≡ₜ (inl A₁ A₂ ⨟ h')) (hr : (inr A₁ A₂ ⨟ h) ≡ₜ (inr A₁ A₂ ⨟ h')) :
    h ≡ₜ h' :=
  (either_unique h).trans ((either_congr hl hr).trans (PEq.symm (either_unique h')))

/-- The co-pairing of the two co-projections is the identity. -/
theorem either_inl_inr (A B : Ty) : either (inl A B) (inr A B) ≡ₜ Term.id (A ⊕' B) :=
  PEq.sum_inl_inr_codiag A B

/-- Co-pairing absorbs a composition on the right. -/
theorem either_comp {A₁ A₂ B C : Ty} (f : Term A₁ B) (g : Term A₂ B) (h : Term B C) :
    (either f g ⨟ h) ≡ₜ either (f ⨟ h) (g ⨟ h) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl A₁ A₂ ⨟ (either f g ⨟ h)) ≡ₜ ((inl A₁ A₂ ⨟ either f g) ⨟ h) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (f ⨟ h) := PEq.compL _ (inl_either f g)
      _ ≡ₜ (inl A₁ A₂ ⨟ either (f ⨟ h) (g ⨟ h)) := PEq.symm (inl_either _ _)
  · calc (inr A₁ A₂ ⨟ (either f g ⨟ h)) ≡ₜ ((inr A₁ A₂ ⨟ either f g) ⨟ h) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (g ⨟ h) := PEq.compL _ (inr_either f g)
      _ ≡ₜ (inr A₁ A₂ ⨟ either (f ⨟ h) (g ⨟ h)) := PEq.symm (inr_either _ _)

/-- Composing the functorial action on co-products with a co-pairing. -/
theorem sumF_either {A₁ A₂ B₁ B₂ C : Ty} (f : Term A₁ B₁) (g : Term A₂ B₂)
    (h : Term B₁ C) (k : Term B₂ C) :
    (sumF f g ⨟ either h k) ≡ₜ either (f ⨟ h) (g ⨟ k) := by
  calc (sumF f g ⨟ (sumF h k ⨟ codiag C)) ≡ₜ ((sumF f g ⨟ sumF h k) ⨟ codiag C) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (sumF (f ⨟ h) (g ⨟ k) ⨟ codiag C) := PEq.compL _ (PEq.sum_comp _ _ _ _)

/-- Commutativity of the co-product is an involution. -/
theorem comm_comm (A B : Ty) : (comm A B ⨟ comm B A) ≡ₜ Term.id (A ⊕' B) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl A B ⨟ (comm A B ⨟ comm B A))
        ≡ₜ ((inl A B ⨟ comm A B) ⨟ comm B A) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (inr B A ⨟ comm B A) := PEq.compL _ (inl_either _ _)
      _ ≡ₜ inl A B := inr_either _ _
      _ ≡ₜ (inl A B ⨟ Term.id (A ⊕' B)) := PEq.symm (PEq.comp_id _)
  · calc (inr A B ⨟ (comm A B ⨟ comm B A))
        ≡ₜ ((inr A B ⨟ comm A B) ⨟ comm B A) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (inl B A ⨟ comm B A) := PEq.compL _ (inr_either _ _)
      _ ≡ₜ inr A B := inl_either _ _
      _ ≡ₜ (inr A B ⨟ Term.id (A ⊕' B)) := PEq.symm (PEq.comp_id _)

/-- `shift` followed by `unshift` is the identity. -/
theorem shift_unshift (A B : Ty) : (shift A B ⨟ unshift A B) ≡ₜ Term.id ((A ⊗ B)⋆) := by
  have hinner :
      ((assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)) ⨟
          (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)))
        ≡ₜ Term.id ((A ⊗ B) ⊗ (A ⊗ B)⋆) := by
    calc ((assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)) ⨟
            (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)))
        ≡ₜ (assocR A B ((A ⊗ B)⋆) ⨟ (prodF (Term.id A) (shiftL B A) ⨟
            (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (assocR A B ((A ⊗ B)⋆) ⨟ ((prodF (Term.id A) (shiftL B A) ⨟
            prodF (Term.id A) (shiftR B A)) ⨟ assocL A B ((A ⊗ B)⋆))) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (assocR A B ((A ⊗ B)⋆) ⨟ (prodF (Term.id A ⨟ Term.id A)
            (shiftL B A ⨟ shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆))) :=
          PEq.compR _ (PEq.compL _ (PEq.prod_comp _ _ _ _))
      _ ≡ₜ (assocR A B ((A ⊗ B)⋆) ⨟ (prodF (Term.id A) (Term.id (B ⊗ (A ⊗ B)⋆)) ⨟
            assocL A B ((A ⊗ B)⋆))) :=
          PEq.compR _ (PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (PEq.shiftL_shiftR B A)))
      _ ≡ₜ (assocR A B ((A ⊗ B)⋆) ⨟ (Term.id (A ⊗ (B ⊗ (A ⊗ B)⋆)) ⨟
            assocL A B ((A ⊗ B)⋆))) :=
          PEq.compR _ (PEq.compL _ (PEq.prod_id _ _))
      _ ≡ₜ (assocR A B ((A ⊗ B)⋆) ⨟ assocL A B ((A ⊗ B)⋆)) :=
          PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id ((A ⊗ B) ⊗ (A ⊗ B)⋆) := PEq.assocR_assocL A B ((A ⊗ B)⋆)
  calc (shift A B ⨟ unshift A B)
      ≡ₜ (uncons (A ⊗ B) ⨟ ((sumF (Term.id Ty.unit)
            (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)) ⨟
          sumF (Term.id Ty.unit)
            (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆))) ⨟ cons (A ⊗ B))) := by
        simp only [shift, unshift]
        calc ((uncons (A ⊗ B) ⨟ sumF (Term.id Ty.unit)
                (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A))) ⨟
              (sumF (Term.id Ty.unit)
                (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟ cons (A ⊗ B)))
            ≡ₜ (uncons (A ⊗ B) ⨟ (sumF (Term.id Ty.unit)
                (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)) ⨟
              (sumF (Term.id Ty.unit)
                (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟
                  cons (A ⊗ B)))) := PEq.comp_assoc _ _ _
          _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (uncons (A ⊗ B) ⨟ (sumF (Term.id Ty.unit ⨟ Term.id Ty.unit) _ ⨟ cons (A ⊗ B))) :=
        PEq.compR _ (PEq.compL _ (PEq.sum_comp _ _ _ _))
    _ ≡ₜ (uncons (A ⊗ B) ⨟ (sumF (Term.id Ty.unit) (Term.id ((A ⊗ B) ⊗ (A ⊗ B)⋆)) ⨟
          cons (A ⊗ B))) :=
        PEq.compR _ (PEq.compL _ (PEq.congr_sumF (PEq.id_comp _) hinner))
    _ ≡ₜ (uncons (A ⊗ B) ⨟ (Term.id (Ty.unit ⊕' ((A ⊗ B) ⊗ (A ⊗ B)⋆)) ⨟ cons (A ⊗ B))) :=
        PEq.compR _ (PEq.compL _ (PEq.sum_id _ _))
    _ ≡ₜ (uncons (A ⊗ B) ⨟ cons (A ⊗ B)) := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id ((A ⊗ B)⋆) := PEq.uncons_cons (A ⊗ B)

/-- `unshift` followed by `shift` is the identity. -/
theorem unshift_shift (A B : Ty) :
    (unshift A B ⨟ shift A B) ≡ₜ Term.id (Ty.unit ⊕' (A ⊗ ((B ⊗ A)⋆ ⊗ B))) := by
  have hinner :
      ((prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟
          (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)))
        ≡ₜ Term.id (A ⊗ ((B ⊗ A)⋆ ⊗ B)) := by
    calc ((prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟
            (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)))
        ≡ₜ (prodF (Term.id A) (shiftR B A) ⨟ (assocL A B ((A ⊗ B)⋆) ⨟
            (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (Term.id A) (shiftR B A) ⨟ ((assocL A B ((A ⊗ B)⋆) ⨟
            assocR A B ((A ⊗ B)⋆)) ⨟ prodF (Term.id A) (shiftL B A))) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (prodF (Term.id A) (shiftR B A) ⨟ (Term.id (A ⊗ (B ⊗ (A ⊗ B)⋆)) ⨟
            prodF (Term.id A) (shiftL B A))) :=
          PEq.compR _ (PEq.compL _ (PEq.assocL_assocR A B ((A ⊗ B)⋆)))
      _ ≡ₜ (prodF (Term.id A) (shiftR B A) ⨟ prodF (Term.id A) (shiftL B A)) :=
          PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ prodF (Term.id A ⨟ Term.id A) (shiftR B A ⨟ shiftL B A) :=
          PEq.prod_comp _ _ _ _
      _ ≡ₜ prodF (Term.id A) (Term.id ((B ⊗ A)⋆ ⊗ B)) :=
          PEq.congr_prodF (PEq.id_comp _) (PEq.shiftR_shiftL B A)
      _ ≡ₜ Term.id (A ⊗ ((B ⊗ A)⋆ ⊗ B)) := PEq.prod_id _ _
  calc (unshift A B ⨟ shift A B)
      ≡ₜ (sumF (Term.id Ty.unit) (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟
          ((cons (A ⊗ B) ⨟ uncons (A ⊗ B)) ⨟
            sumF (Term.id Ty.unit)
              (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)))) := by
        simp only [shift, unshift]
        calc ((sumF (Term.id Ty.unit)
                (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟ cons (A ⊗ B)) ⨟
              (uncons (A ⊗ B) ⨟ sumF (Term.id Ty.unit)
                (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A))))
            ≡ₜ (sumF (Term.id Ty.unit)
                (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟
              (cons (A ⊗ B) ⨟ (uncons (A ⊗ B) ⨟ sumF (Term.id Ty.unit)
                (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A))))) :=
              PEq.comp_assoc _ _ _
          _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (sumF (Term.id Ty.unit) (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟
          (Term.id (Ty.unit ⊕' ((A ⊗ B) ⊗ (A ⊗ B)⋆)) ⨟
            sumF (Term.id Ty.unit)
              (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A)))) :=
        PEq.compR _ (PEq.compL _ (PEq.cons_uncons (A ⊗ B)))
    _ ≡ₜ (sumF (Term.id Ty.unit) (prodF (Term.id A) (shiftR B A) ⨟ assocL A B ((A ⊗ B)⋆)) ⨟
          sumF (Term.id Ty.unit)
            (assocR A B ((A ⊗ B)⋆) ⨟ prodF (Term.id A) (shiftL B A))) :=
        PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ sumF (Term.id Ty.unit ⨟ Term.id Ty.unit) _ := PEq.sum_comp _ _ _ _
    _ ≡ₜ sumF (Term.id Ty.unit) (Term.id (A ⊗ ((B ⊗ A)⋆ ⊗ B))) :=
        PEq.congr_sumF (PEq.id_comp _) hinner
    _ ≡ₜ Term.id (Ty.unit ⊕' (A ⊗ ((B ⊗ A)⋆ ⊗ B))) := PEq.sum_id _ _

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
