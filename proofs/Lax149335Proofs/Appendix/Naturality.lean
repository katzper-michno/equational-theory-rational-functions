import Lax149335Proofs.EquationalTheory.DerivedRules

/-!
# Naturality of the derived list combinators

Axiom 3 postulates that each *atomic* function is a natural transformation.  The derived
terms `[]`, `pure`, `prepend` and `binconcat` are natural as well, and this is proved here.
These facts are the ones needed for the naturality of the concatenation maps of Section 5.1,
which is proved in the appendix of the paper.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

variable {A B : Ty}

/-- The empty list is natural. -/
theorem nilT_natural (f : Term A B) : (nilT A ⨟ listF f) ≡ₜ nilT B := by
  calc ((inl Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ listF f)
      ≡ₜ (inl Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ listF f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inl Ty.unit (A ⊗ A⋆) ⨟
          (sumF (Term.id Ty.unit) (prodF f (listF f)) ⨟ cons B)) :=
        PEq.compR _ (PEq.symm (PEq.nat_cons f))
    _ ≡ₜ ((inl Ty.unit (A ⊗ A⋆) ⨟ sumF (Term.id Ty.unit) (prodF f (listF f))) ⨟ cons B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.id Ty.unit ⨟ inl Ty.unit (B ⊗ B⋆)) ⨟ cons B) :=
        PEq.compL _ (PEq.nat_inl _ _)
    _ ≡ₜ (inl Ty.unit (B ⊗ B⋆) ⨟ cons B) := PEq.compL _ (PEq.id_comp _)

/-- Prepending is natural. -/
theorem prepend_natural (f : Term A B) :
    (prodF f (listF f) ⨟ prepend B) ≡ₜ (prepend A ⨟ listF f) := by
  calc (prodF f (listF f) ⨟ (inr Ty.unit (B ⊗ B⋆) ⨟ cons B))
      ≡ₜ ((prodF f (listF f) ⨟ inr Ty.unit (B ⊗ B⋆)) ⨟ cons B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((inr Ty.unit (A ⊗ A⋆) ⨟ sumF (Term.id Ty.unit) (prodF f (listF f))) ⨟ cons B) :=
        PEq.compL _ (PEq.symm (PEq.nat_inr _ _))
    _ ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ (sumF (Term.id Ty.unit) (prodF f (listF f)) ⨟ cons B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ listF f)) := PEq.compR _ (PEq.nat_cons f)
    _ ≡ₜ ((inr Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ listF f) := PEq.symm (PEq.comp_assoc _ _ _)

/-- The singleton list operation is natural. -/
theorem pureT_natural (f : Term A B) : (f ⨟ pureT B) ≡ₜ (pureT A ⨟ listF f) := by
  calc (f ⨟ ((unitR B ⨟ prodF (Term.id B) (nilT B)) ⨟ prepend B))
      ≡ₜ ((f ⨟ (unitR B ⨟ prodF (Term.id B) (nilT B))) ⨟ prepend B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((f ⨟ unitR B) ⨟ prodF (Term.id B) (nilT B)) ⨟ prepend B) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (((unitR A ⨟ prodF f (Term.id Ty.unit)) ⨟ prodF (Term.id B) (nilT B)) ⨟ prepend B) :=
        PEq.compL _ (PEq.compL _ (PEq.nat_unitR f))
    _ ≡ₜ ((unitR A ⨟ (prodF f (Term.id Ty.unit) ⨟ prodF (Term.id B) (nilT B))) ⨟ prepend B) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((unitR A ⨟ prodF (f ⨟ Term.id B) (Term.id Ty.unit ⨟ nilT B)) ⨟ prepend B) :=
        PEq.compL _ (PEq.compR _ (PEq.prod_comp _ _ _ _))
    _ ≡ₜ ((unitR A ⨟ prodF f (nilT B)) ⨟ prepend B) :=
        PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.comp_id _) (PEq.id_comp _)))
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A ⨟ f) (nilT A ⨟ listF f)) ⨟ prepend B) :=
        PEq.compL _ (PEq.compR _
          (PEq.congr_prodF (PEq.symm (PEq.id_comp _)) (PEq.symm (nilT_natural f))))
    _ ≡ₜ ((unitR A ⨟ (prodF (Term.id A) (nilT A) ⨟ prodF f (listF f))) ⨟ prepend B) :=
        PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
    _ ≡ₜ (((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟ prodF f (listF f)) ⨟ prepend B) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟ (prodF f (listF f) ⨟ prepend B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟ (prepend A ⨟ listF f)) :=
        PEq.compR _ (prepend_natural f)
    _ ≡ₜ (((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟ prepend A) ⨟ listF f) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-- Binary concatenation is natural. -/
theorem binconcat_natural (f : Term A B) :
    (prodF (listF f) (listF f) ⨟ binconcat B) ≡ₜ (binconcat A ⨟ listF f) := by
  calc (prodF (listF f) (listF f) ⨟
          ((prodF (Term.id B⋆) (pureT B⋆) ⨟ prepend B⋆) ⨟ concat B))
      ≡ₜ ((prodF (listF f) (listF f) ⨟ (prodF (Term.id B⋆) (pureT B⋆) ⨟ prepend B⋆)) ⨟
            concat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((prodF (listF f) (listF f) ⨟ prodF (Term.id B⋆) (pureT B⋆)) ⨟ prepend B⋆) ⨟
            concat B) := PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((prodF (listF f ⨟ Term.id B⋆) (listF f ⨟ pureT B⋆) ⨟ prepend B⋆) ⨟ concat B) :=
        PEq.compL _ (PEq.compL _ (PEq.prod_comp _ _ _ _))
    _ ≡ₜ ((prodF (Term.id A⋆ ⨟ listF f) (pureT A⋆ ⨟ listF (listF f)) ⨟ prepend B⋆) ⨟
            concat B) :=
        PEq.compL _ (PEq.compL _ (PEq.congr_prodF
          ((PEq.comp_id _).trans (PEq.symm (PEq.id_comp _))) (pureT_natural (listF f))))
    _ ≡ₜ ((((prodF (Term.id A⋆) (pureT A⋆)) ⨟ prodF (listF f) (listF (listF f))) ⨟
            prepend B⋆) ⨟ concat B) :=
        PEq.compL _ (PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _)))
    _ ≡ₜ ((prodF (Term.id A⋆) (pureT A⋆) ⨟
            (prodF (listF f) (listF (listF f)) ⨟ prepend B⋆)) ⨟ concat B) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF (Term.id A⋆) (pureT A⋆) ⨟ (prepend A⋆ ⨟ listF (listF f))) ⨟ concat B) :=
        PEq.compL _ (PEq.compR _ (prepend_natural (listF f)))
    _ ≡ₜ (((prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆) ⨟ listF (listF f)) ⨟ concat B) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆) ⨟ (listF (listF f) ⨟ concat B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ ((prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆) ⨟ (concat A ⨟ listF f)) :=
        PEq.compR _ (PEq.nat_concat f)
    _ ≡ₜ (((prodF (Term.id A⋆) (pureT A⋆) ⨟ prepend A⋆) ⨟ concat A) ⨟ listF f) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-- Concatenation of two terms with list outputs is natural. -/
theorem fdot_natural {A₁ A₂ : Ty} (f₁ : Term A₁ A⋆) (f₂ : Term A₂ A⋆) (f : Term A B) :
    ((prodF f₁ f₂ ⨟ binconcat A) ⨟ listF f) ≡ₜ
      (prodF (f₁ ⨟ listF f) (f₂ ⨟ listF f) ⨟ binconcat B) := by
  calc ((prodF f₁ f₂ ⨟ binconcat A) ⨟ listF f)
      ≡ₜ (prodF f₁ f₂ ⨟ (binconcat A ⨟ listF f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF f₁ f₂ ⨟ (prodF (listF f) (listF f) ⨟ binconcat B)) :=
        PEq.compR _ (PEq.symm (binconcat_natural f))
    _ ≡ₜ ((prodF f₁ f₂ ⨟ prodF (listF f) (listF f)) ⨟ binconcat B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (f₁ ⨟ listF f) (f₂ ⨟ listF f) ⨟ binconcat B) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)

end Term

/-- The concatenation map is a natural transformation: for every one-parameter type
constructor `F` and every rational term `f : A → B` the square of Section 5.1 commutes.
This is the naturality of concatenation maps discussed in the appendix. -/
theorem concatMap_natural (F : TyF) {A B : Ty} (f : Term A B) :
    (F.map f ⨟ F.concatMap B) ≡ₜ (F.concatMap A ⨟ listF f) := by
  induction F with
  | param => exact Term.pureT_natural f
  | unit =>
    calc (Term.id Ty.unit ⨟ nilT B) ≡ₜ nilT B := PEq.id_comp _
      _ ≡ₜ (nilT A ⨟ listF f) := PEq.symm (Term.nilT_natural f)
  | prod F G ihF ihG =>
    calc (prodF (F.map f) (G.map f) ⨟ (prodF (F.concatMap B) (G.concatMap B) ⨟ binconcat B))
        ≡ₜ ((prodF (F.map f) (G.map f) ⨟ prodF (F.concatMap B) (G.concatMap B)) ⨟
              binconcat B) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (F.map f ⨟ F.concatMap B) (G.map f ⨟ G.concatMap B) ⨟ binconcat B) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (F.concatMap A ⨟ listF f) (G.concatMap A ⨟ listF f) ⨟ binconcat B) :=
          PEq.compL _ (PEq.congr_prodF ihF ihG)
      _ ≡ₜ ((prodF (F.concatMap A) (G.concatMap A) ⨟ binconcat A) ⨟ listF f) :=
          PEq.symm (Term.fdot_natural _ _ f)
  | sum F G ihF ihG =>
    calc (sumF (F.map f) (G.map f) ⨟ Term.either (F.concatMap B) (G.concatMap B))
        ≡ₜ Term.either (F.map f ⨟ F.concatMap B) (G.map f ⨟ G.concatMap B) :=
          Term.sumF_either _ _ _ _
      _ ≡ₜ Term.either (F.concatMap A ⨟ listF f) (G.concatMap A ⨟ listF f) :=
          Term.either_congr ihF ihG
      _ ≡ₜ (Term.either (F.concatMap A) (G.concatMap A) ⨟ listF f) :=
          PEq.symm (Term.either_comp _ _ _)
  | list F ihF =>
    calc (listF (F.map f) ⨟ (listF (F.concatMap B) ⨟ concat B))
        ≡ₜ ((listF (F.map f) ⨟ listF (F.concatMap B)) ⨟ concat B) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (listF (F.map f ⨟ F.concatMap B) ⨟ concat B) := PEq.compL _ (PEq.list_comp _ _)
      _ ≡ₜ (listF (F.concatMap A ⨟ listF f) ⨟ concat B) := PEq.compL _ (PEq.congr_listF ihF)
      _ ≡ₜ ((listF (F.concatMap A) ⨟ listF (listF f)) ⨟ concat B) :=
          PEq.compL _ (PEq.symm (PEq.list_comp _ _))
      _ ≡ₜ (listF (F.concatMap A) ⨟ (listF (listF f) ⨟ concat B)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (listF (F.concatMap A) ⨟ (concat A ⨟ listF f)) := PEq.compR _ (PEq.nat_concat f)
      _ ≡ₜ ((listF (F.concatMap A) ⨟ concat A) ⨟ listF f) := PEq.symm (PEq.comp_assoc _ _ _)

end Lax149335Proofs

bridge_export Lax149335Proofs
