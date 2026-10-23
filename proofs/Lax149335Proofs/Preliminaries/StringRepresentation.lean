import Lax149335Proofs.Preliminaries.Injectivity
import Mathlib.Tactic.Set

/-!
# Injective string representations over a finite alphabet (Claim F.1)

This file contains the proof of Claim F.1 of the paper, the first step of the proof of
Lemma 5.6 in the appendix section *Injective string representations*: for every type `A`
there is a finite alphabet `Ā` and an injective aperiodic term `A → Ā*`.  The second step,
Claim F.2, and Lemma 5.6 itself (an injective aperiodic term into binary strings) are in
`Lax149335Proofs.Appendix.Bundles.Window`, since the proof of Claim F.2 given here uses the
injectivity half of the bundle lemma.

The proof follows the paper.  The induction produces an alphabet built from the unit type
using co-products only (`Lax149335Proofs.Ty.IsUnitSum`); such a type is then encoded into one of the
right-nested alphabets `Ty.finAlph n` used in the statement of the lemma.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- Types built from the unit type using co-products only; these are the alphabets that the
induction of Lemma 5.6 produces. -/
inductive Ty.IsUnitSum : Ty → Prop
  /-- The unit type is a sum of units. -/
  | unit : Ty.IsUnitSum Ty.unit
  /-- A co-product of sums of units is a sum of units. -/
  | sum {A B : Ty} : Ty.IsUnitSum A → Ty.IsUnitSum B → Ty.IsUnitSum (A ⊕' B)

namespace Term

/-! ### Associativity of the co-product -/

/-- The two associativity terms for the co-product are mutually inverse in one direction. -/
theorem sumAssocR_sumAssocL (A B C : Ty) :
    (sumAssocR A B C ⨟ sumAssocL A B C) ≡ₜ Term.id ((A ⊕' B) ⊕' C) := by
  refine either_ext _ _ ?_ ?_
  · have hinner :
        (either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C)) ⨟ sumAssocL A B C)
          ≡ₜ inl (A ⊕' B) C := by
      refine either_ext _ _ ?_ ?_
      · calc (inl A B ⨟ (either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C)) ⨟ sumAssocL A B C))
            ≡ₜ ((inl A B ⨟ either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C))) ⨟
                sumAssocL A B C) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (inl A (B ⊕' C) ⨟ sumAssocL A B C) := PEq.compL _ (inl_either _ _)
          _ ≡ₜ (inl A B ⨟ inl (A ⊕' B) C) := inl_either _ _
      · calc (inr A B ⨟ (either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C)) ⨟ sumAssocL A B C))
            ≡ₜ ((inr A B ⨟ either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C))) ⨟
                sumAssocL A B C) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((inl B C ⨟ inr A (B ⊕' C)) ⨟ sumAssocL A B C) := PEq.compL _ (inr_either _ _)
          _ ≡ₜ (inl B C ⨟ (inr A (B ⊕' C) ⨟ sumAssocL A B C)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (inl B C ⨟ either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C)) :=
              PEq.compR _ (inr_either _ _)
          _ ≡ₜ (inr A B ⨟ inl (A ⊕' B) C) := inl_either _ _
    calc (inl (A ⊕' B) C ⨟ (sumAssocR A B C ⨟ sumAssocL A B C))
        ≡ₜ ((inl (A ⊕' B) C ⨟ sumAssocR A B C) ⨟ sumAssocL A B C) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C)) ⨟ sumAssocL A B C) :=
          PEq.compL _ (inl_either _ _)
      _ ≡ₜ inl (A ⊕' B) C := hinner
      _ ≡ₜ (inl (A ⊕' B) C ⨟ Term.id ((A ⊕' B) ⊕' C)) := PEq.symm (PEq.comp_id _)
  · calc (inr (A ⊕' B) C ⨟ (sumAssocR A B C ⨟ sumAssocL A B C))
        ≡ₜ ((inr (A ⊕' B) C ⨟ sumAssocR A B C) ⨟ sumAssocL A B C) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((inr B C ⨟ inr A (B ⊕' C)) ⨟ sumAssocL A B C) := PEq.compL _ (inr_either _ _)
      _ ≡ₜ (inr B C ⨟ (inr A (B ⊕' C) ⨟ sumAssocL A B C)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inr B C ⨟ either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C)) :=
          PEq.compR _ (inr_either _ _)
      _ ≡ₜ inr (A ⊕' B) C := inr_either _ _
      _ ≡ₜ (inr (A ⊕' B) C ⨟ Term.id ((A ⊕' B) ⊕' C)) := PEq.symm (PEq.comp_id _)

/-- The two associativity terms for the co-product are mutually inverse in the other
direction as well. -/
theorem sumAssocL_sumAssocR (A B C : Ty) :
    (sumAssocL A B C ⨟ sumAssocR A B C) ≡ₜ Term.id (A ⊕' (B ⊕' C)) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl A (B ⊕' C) ⨟ (sumAssocL A B C ⨟ sumAssocR A B C))
        ≡ₜ ((inl A (B ⊕' C) ⨟ sumAssocL A B C) ⨟ sumAssocR A B C) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((inl A B ⨟ inl (A ⊕' B) C) ⨟ sumAssocR A B C) := PEq.compL _ (inl_either _ _)
      _ ≡ₜ (inl A B ⨟ (inl (A ⊕' B) C ⨟ sumAssocR A B C)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inl A B ⨟ either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C))) :=
          PEq.compR _ (inl_either _ _)
      _ ≡ₜ inl A (B ⊕' C) := inl_either _ _
      _ ≡ₜ (inl A (B ⊕' C) ⨟ Term.id (A ⊕' (B ⊕' C))) := PEq.symm (PEq.comp_id _)
  · have hinner :
        (either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C) ⨟ sumAssocR A B C) ≡ₜ
          inr A (B ⊕' C) := by
      refine either_ext _ _ ?_ ?_
      · calc (inl B C ⨟ (either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C) ⨟
              sumAssocR A B C))
            ≡ₜ ((inl B C ⨟ either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C)) ⨟
                sumAssocR A B C) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((inr A B ⨟ inl (A ⊕' B) C) ⨟ sumAssocR A B C) := PEq.compL _ (inl_either _ _)
          _ ≡ₜ (inr A B ⨟ (inl (A ⊕' B) C ⨟ sumAssocR A B C)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (inr A B ⨟ either (inl A (B ⊕' C)) (inl B C ⨟ inr A (B ⊕' C))) :=
              PEq.compR _ (inl_either _ _)
          _ ≡ₜ (inl B C ⨟ inr A (B ⊕' C)) := inr_either _ _
      · calc (inr B C ⨟ (either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C) ⨟
              sumAssocR A B C))
            ≡ₜ ((inr B C ⨟ either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C)) ⨟
                sumAssocR A B C) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (inr (A ⊕' B) C ⨟ sumAssocR A B C) := PEq.compL _ (inr_either _ _)
          _ ≡ₜ (inr B C ⨟ inr A (B ⊕' C)) := inr_either _ _
    calc (inr A (B ⊕' C) ⨟ (sumAssocL A B C ⨟ sumAssocR A B C))
        ≡ₜ ((inr A (B ⊕' C) ⨟ sumAssocL A B C) ⨟ sumAssocR A B C) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (either (inr A B ⨟ inl (A ⊕' B) C) (inr (A ⊕' B) C) ⨟ sumAssocR A B C) :=
          PEq.compL _ (inr_either _ _)
      _ ≡ₜ inr A (B ⊕' C) := hinner
      _ ≡ₜ (inr A (B ⊕' C) ⨟ Term.id (A ⊕' (B ⊕' C))) := PEq.symm (PEq.comp_id _)

/-! ### Two computation rules for list constructors -/

/-- Destructing the empty list. -/
theorem nilT_uncons (A : Ty) : (nilT A ⨟ uncons A) ≡ₜ inl Ty.unit (A ⊗ A⋆) := by
  calc ((inl Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ uncons A)
      ≡ₜ (inl Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ uncons A)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inl Ty.unit (A ⊗ A⋆) ⨟ Term.id (Ty.unit ⊕' (A ⊗ A⋆))) :=
        PEq.compR _ (PEq.cons_uncons A)
    _ ≡ₜ inl Ty.unit (A ⊗ A⋆) := PEq.comp_id _

/-- Destructing a singleton list. -/
theorem pureT_uncons (A : Ty) :
    (pureT A ⨟ uncons A) ≡ₜ (pairR (Term.id A) (nilT A) ⨟ inr Ty.unit (A ⊗ A⋆)) := by
  calc (((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟ (inr Ty.unit (A ⊗ A⋆) ⨟ cons A)) ⨟ uncons A)
      ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟
            ((inr Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟ uncons A)) := PEq.comp_assoc _ _ _
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟
            (inr Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟ uncons A))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟
            (inr Ty.unit (A ⊗ A⋆) ⨟ Term.id (Ty.unit ⊕' (A ⊗ A⋆)))) :=
        PEq.compR _ (PEq.compR _ (PEq.cons_uncons A))
    _ ≡ₜ ((unitR A ⨟ prodF (Term.id A) (nilT A)) ⨟ inr Ty.unit (A ⊗ A⋆)) :=
        PEq.compR _ (PEq.comp_id _)

/-! ### The provably injective term used in the induction step for co-products -/

/-- The term `C* + C* × (1 × C*) → C* × (1 × C*)*` of the induction step for co-products in
the proof of Lemma 5.6: the left summand is sent to a pair with the empty list, the right one
to a pair with a singleton list. -/
def dupCode (C : Ty) : Term (C⋆ ⊕' (C⋆ ⊗ (Ty.unit ⊗ C⋆))) (C⋆ ⊗ (Ty.unit ⊗ C⋆)⋆) :=
  either (pairR (Term.id C⋆) (nilT (Ty.unit ⊗ C⋆)))
    (prodF (Term.id C⋆) (pureT (Ty.unit ⊗ C⋆)))

/-- A one-sided inverse of `dupCode`: it inspects whether the second component is empty. -/
def dupDecode (C : Ty) : Term (C⋆ ⊗ (Ty.unit ⊗ C⋆)⋆) (C⋆ ⊕' (C⋆ ⊗ (Ty.unit ⊗ C⋆))) :=
  prodF (Term.id C⋆) (uncons (Ty.unit ⊗ C⋆)) ⨟
    (distR C⋆ Ty.unit ((Ty.unit ⊗ C⋆) ⊗ (Ty.unit ⊗ C⋆)⋆) ⨟
      either (fst C⋆ Ty.unit ⨟ inl C⋆ (C⋆ ⊗ (Ty.unit ⊗ C⋆)))
        (prodF (Term.id C⋆) (fst (Ty.unit ⊗ C⋆) ((Ty.unit ⊗ C⋆)⋆)) ⨟
          inr C⋆ (C⋆ ⊗ (Ty.unit ⊗ C⋆))))

/-- `dupCode` is provably injective, with `dupDecode` as a one-sided inverse. -/
theorem dupCode_dupDecode (C : Ty) :
    (dupCode C ⨟ dupDecode C) ≡ₜ Term.id (C⋆ ⊕' (C⋆ ⊗ (Ty.unit ⊗ C⋆))) := by
  set Y : Ty := Ty.unit ⊗ C⋆ with hY
  set E : Term ((C⋆ ⊗ Ty.unit) ⊕' (C⋆ ⊗ (Y ⊗ Y⋆))) (C⋆ ⊕' (C⋆ ⊗ Y)) :=
    either (fst C⋆ Ty.unit ⨟ inl C⋆ (C⋆ ⊗ Y))
      (prodF (Term.id C⋆) (fst Y (Y⋆)) ⨟ inr C⋆ (C⋆ ⊗ Y)) with hE
  have h1 : (pairR (Term.id C⋆) (nilT Y) ⨟ dupDecode C) ≡ₜ inl C⋆ (C⋆ ⊗ Y) := by
    calc (pairR (Term.id C⋆) (nilT Y) ⨟
            (prodF (Term.id C⋆) (uncons Y) ⨟ (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)))
        ≡ₜ ((pairR (Term.id C⋆) (nilT Y) ⨟ prodF (Term.id C⋆) (uncons Y)) ⨟
              (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairR (Term.id C⋆ ⨟ Term.id C⋆) (nilT Y ⨟ uncons Y) ⨟
              (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)) := PEq.compL _ (pairR_prodF _ _ _ _)
      _ ≡ₜ (pairR (Term.id C⋆) (inl Ty.unit (Y ⊗ Y⋆)) ⨟ (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)) :=
          PEq.compL _ (pairR_congr (PEq.id_comp _) (nilT_uncons Y))
      _ ≡ₜ (((unitR C⋆ ⨟ prodF (Term.id C⋆) (inl Ty.unit (Y ⊗ Y⋆))) ⨟
              distR C⋆ Ty.unit (Y ⊗ Y⋆)) ⨟ E) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((unitR C⋆ ⨟ (prodF (Term.id C⋆) (inl Ty.unit (Y ⊗ Y⋆)) ⨟
              distR C⋆ Ty.unit (Y ⊗ Y⋆))) ⨟ E) := PEq.compL _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((unitR C⋆ ⨟ inl (C⋆ ⊗ Ty.unit) (C⋆ ⊗ (Y ⊗ Y⋆))) ⨟ E) :=
          PEq.compL _ (PEq.compR _ (prodF_inl_distR C⋆ Ty.unit (Y ⊗ Y⋆)))
      _ ≡ₜ (unitR C⋆ ⨟ (inl (C⋆ ⊗ Ty.unit) (C⋆ ⊗ (Y ⊗ Y⋆)) ⨟ E)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (unitR C⋆ ⨟ (fst C⋆ Ty.unit ⨟ inl C⋆ (C⋆ ⊗ Y))) := PEq.compR _ (inl_either _ _)
      _ ≡ₜ ((unitR C⋆ ⨟ fst C⋆ Ty.unit) ⨟ inl C⋆ (C⋆ ⊗ Y)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id C⋆ ⨟ inl C⋆ (C⋆ ⊗ Y)) := PEq.compL _ (PEq.unitR_fst _)
      _ ≡ₜ inl C⋆ (C⋆ ⊗ Y) := PEq.id_comp _
  have h2 : (prodF (Term.id C⋆) (pureT Y) ⨟ dupDecode C) ≡ₜ inr C⋆ (C⋆ ⊗ Y) := by
    calc (prodF (Term.id C⋆) (pureT Y) ⨟
            (prodF (Term.id C⋆) (uncons Y) ⨟ (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)))
        ≡ₜ ((prodF (Term.id C⋆) (pureT Y) ⨟ prodF (Term.id C⋆) (uncons Y)) ⨟
              (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id C⋆ ⨟ Term.id C⋆) (pureT Y ⨟ uncons Y) ⨟
              (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)) := PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (Term.id C⋆ ⨟ Term.id C⋆)
              (pairR (Term.id Y) (nilT Y) ⨟ inr Ty.unit (Y ⊗ Y⋆)) ⨟
              (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)) :=
          PEq.compL _ (PEq.congr_prodF (PEq.refl _) (pureT_uncons Y))
      _ ≡ₜ ((prodF (Term.id C⋆) (pairR (Term.id Y) (nilT Y)) ⨟
              prodF (Term.id C⋆) (inr Ty.unit (Y ⊗ Y⋆))) ⨟
              (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E)) :=
          PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
      _ ≡ₜ (prodF (Term.id C⋆) (pairR (Term.id Y) (nilT Y)) ⨟
              (prodF (Term.id C⋆) (inr Ty.unit (Y ⊗ Y⋆)) ⨟
                (distR C⋆ Ty.unit (Y ⊗ Y⋆) ⨟ E))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (Term.id C⋆) (pairR (Term.id Y) (nilT Y)) ⨟
              ((prodF (Term.id C⋆) (inr Ty.unit (Y ⊗ Y⋆)) ⨟
                distR C⋆ Ty.unit (Y ⊗ Y⋆)) ⨟ E)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (prodF (Term.id C⋆) (pairR (Term.id Y) (nilT Y)) ⨟
              (inr (C⋆ ⊗ Ty.unit) (C⋆ ⊗ (Y ⊗ Y⋆)) ⨟ E)) :=
          PEq.compR _ (PEq.compL _ (prodF_inr_distR C⋆ Ty.unit (Y ⊗ Y⋆)))
      _ ≡ₜ (prodF (Term.id C⋆) (pairR (Term.id Y) (nilT Y)) ⨟
              (prodF (Term.id C⋆) (fst Y (Y⋆)) ⨟ inr C⋆ (C⋆ ⊗ Y))) :=
          PEq.compR _ (inr_either _ _)
      _ ≡ₜ ((prodF (Term.id C⋆) (pairR (Term.id Y) (nilT Y)) ⨟
              prodF (Term.id C⋆) (fst Y (Y⋆))) ⨟ inr C⋆ (C⋆ ⊗ Y)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id C⋆ ⨟ Term.id C⋆) (pairR (Term.id Y) (nilT Y) ⨟ fst Y (Y⋆)) ⨟
              inr C⋆ (C⋆ ⊗ Y)) := PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (Term.id C⋆) (Term.id Y) ⨟ inr C⋆ (C⋆ ⊗ Y)) :=
          PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (pairR_fst _ _))
      _ ≡ₜ (Term.id (C⋆ ⊗ Y) ⨟ inr C⋆ (C⋆ ⊗ Y)) := PEq.compL _ (PEq.prod_id _ _)
      _ ≡ₜ inr C⋆ (C⋆ ⊗ Y) := PEq.id_comp _
  refine either_ext _ _ ?_ ?_
  · calc (inl C⋆ (C⋆ ⊗ Y) ⨟ (dupCode C ⨟ dupDecode C))
        ≡ₜ ((inl C⋆ (C⋆ ⊗ Y) ⨟ dupCode C) ⨟ dupDecode C) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairR (Term.id C⋆) (nilT Y) ⨟ dupDecode C) := PEq.compL _ (inl_either _ _)
      _ ≡ₜ inl C⋆ (C⋆ ⊗ Y) := h1
      _ ≡ₜ (inl C⋆ (C⋆ ⊗ Y) ⨟ Term.id (C⋆ ⊕' (C⋆ ⊗ Y))) := PEq.symm (PEq.comp_id _)
  · calc (inr C⋆ (C⋆ ⊗ Y) ⨟ (dupCode C ⨟ dupDecode C))
        ≡ₜ ((inr C⋆ (C⋆ ⊗ Y) ⨟ dupCode C) ⨟ dupDecode C) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id C⋆) (pureT Y) ⨟ dupDecode C) := PEq.compL _ (inr_either _ _)
      _ ≡ₜ inr C⋆ (C⋆ ⊗ Y) := h2
      _ ≡ₜ (inr C⋆ (C⋆ ⊗ Y) ⨟ Term.id (C⋆ ⊕' (C⋆ ⊗ Y))) := PEq.symm (PEq.comp_id _)

end Term

/-- `dupCode` is provably injective. -/
theorem ProvablyInjective.dupCode (C : Ty) : ProvablyInjective (Term.dupCode C) :=
  ⟨Term.dupDecode C, Term.dupCode_dupDecode C⟩

/-- Associativity of the co-product is provably injective. -/
theorem ProvablyInjective.sumAssocR (A B C : Ty) : ProvablyInjective (Term.sumAssocR A B C) :=
  ⟨Term.sumAssocL A B C, Term.sumAssocR_sumAssocL A B C⟩

/-! ### From sums of units to the alphabets `finAlph n` -/

/-- Every co-product of a sum of units with a right-nested finite alphabet embeds provably
injectively into a right-nested finite alphabet. -/
theorem unitSum_sum_finAlph {S : Ty} (hS : Ty.IsUnitSum S) (m : ℕ) :
    ∃ (n : ℕ) (t : Term (S ⊕' Ty.finAlph m) (Ty.finAlph n)),
      IsAperiodic t ∧ ProvablyInjective t := by
  induction hS generalizing m with
  | unit => exact ⟨m + 1, Term.id (Ty.finAlph (m + 1)), rfl, ProvablyInjective.id _⟩
  | @sum P Q _ _ ihP ihQ =>
    obtain ⟨k, tQ, hapQ, hinjQ⟩ := ihQ m
    obtain ⟨n, tP, hapP, hinjP⟩ := ihP k
    refine ⟨n, Term.sumAssocR P Q (Ty.finAlph m) ⨟ (Term.sumF (Term.id P) tQ ⨟ tP), ?_, ?_⟩
    · simp only [Term.isAperiodic_comp, Term.isAperiodic_sumF]
      exact ⟨rfl, ⟨rfl, hapQ⟩, hapP⟩
    · exact ProvablyInjective.comp (ProvablyInjective.sumAssocR _ _ _)
        (ProvablyInjective.comp
          (ProvablyInjective.sumF (ProvablyInjective.id _) hinjQ) hinjP)

/-- Every sum of units embeds provably injectively into a right-nested finite alphabet. -/
theorem unitSum_finAlph {S : Ty} (hS : Ty.IsUnitSum S) :
    ∃ (n : ℕ) (t : Term S (Ty.finAlph n)), IsAperiodic t ∧ ProvablyInjective t := by
  obtain ⟨n, t, hap, hinj⟩ := unitSum_sum_finAlph hS 0
  refine ⟨n, Term.inl S (Ty.finAlph 0) ⨟ t, ?_, ?_⟩
  · simp only [Term.isAperiodic_comp]
    exact ⟨rfl, hap⟩
  · exact ProvablyInjective.comp (ProvablyInjective.inl _ _) hinj

/-! ### The induction of Lemma 5.6 -/

/-- The induction underlying Lemma 5.6: every type has a provably injective, aperiodic string
representation over an alphabet that is a sum of units. -/
theorem exists_unitSum_encoding (A : Ty) :
    ∃ (S : Ty) (enc : Term A S⋆), Ty.IsUnitSum S ∧ IsAperiodic enc ∧ ProvablyInjective enc := by
  induction A with
  | unit =>
    exact ⟨Ty.unit, Term.nilT Ty.unit, .unit, rfl, ⟨Term.toUnit Ty.unit⋆, PEq.unit_unique _ _⟩⟩
  | prod A B ihA ihB =>
    obtain ⟨SA, encA, hSA, hapA, hinjA⟩ := ihA
    obtain ⟨SB, encB, hSB, hapB, hinjB⟩ := ihB
    refine ⟨SA ⊕' SB,
      Term.prodF encA encB ⨟
        (Term.prodF (Term.id SA⋆) (Term.listF (Term.pairR (Term.id SB) (Term.nilT SA))) ⨟
          Term.unsplit SA SB),
      .sum hSA hSB, ?_, ?_⟩
    · simp only [Term.isAperiodic_comp, Term.isAperiodic_prodF, Term.isAperiodic_listF]
      exact ⟨⟨hapA, hapB⟩, ⟨⟨rfl, rfl⟩, rfl⟩⟩
    · exact ProvablyInjective.comp (ProvablyInjective.prodF hinjA hinjB)
        (ProvablyInjective.comp
          (ProvablyInjective.prodF (ProvablyInjective.id _)
            (ProvablyInjective.listF
              (ProvablyInjective.pairR _ _ (ProvablyInjective.id _))))
          (ProvablyInjective.unsplit _ _))
  | list A ih =>
    obtain ⟨SA, encA, hSA, hapA, hinjA⟩ := ih
    refine ⟨SA ⊕' Ty.unit,
      Term.listF encA ⨟
        (Term.pairL (Term.nilT SA) (Term.listF (Term.unitL SA⋆)) ⨟
          Term.unsplit SA Ty.unit),
      .sum hSA .unit, ?_, ?_⟩
    · simp only [Term.isAperiodic_comp, Term.isAperiodic_listF]
      exact ⟨hapA, rfl, rfl⟩
    · exact ProvablyInjective.comp (ProvablyInjective.listF hinjA)
        (ProvablyInjective.comp
          (ProvablyInjective.pairL _ _
            (ProvablyInjective.listF (ProvablyInjective.unitL _)))
          (ProvablyInjective.unsplit _ _))
  | sum A B ihA ihB =>
    obtain ⟨SA, encA, hSA, hapA, hinjA⟩ := ihA
    obtain ⟨SB, encB, hSB, hapB, hinjB⟩ := ihB
    refine ⟨(SA ⊕' SB) ⊕' Ty.unit,
      (Term.sumF encA encB ⨟
        Term.sumF (Term.listF (Term.inl SA SB)) (Term.listF (Term.inr SA SB))) ⨟
        (Term.sumF (Term.id (SA ⊕' SB)⋆) (Term.unitL (SA ⊕' SB)⋆) ⨟
          (Term.sumF (Term.id (SA ⊕' SB)⋆)
              (Term.pairL (Term.nilT (SA ⊕' SB)) (Term.id (Ty.unit ⊗ (SA ⊕' SB)⋆))) ⨟
            (Term.dupCode (SA ⊕' SB) ⨟ Term.unsplit (SA ⊕' SB) Ty.unit))),
      .sum (.sum hSA hSB) .unit, ?_, ?_⟩
    · simp only [Term.isAperiodic_comp, Term.isAperiodic_sumF, Term.isAperiodic_listF]
      exact ⟨⟨⟨hapA, hapB⟩, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
    · exact ProvablyInjective.comp
        (ProvablyInjective.comp (ProvablyInjective.sumF hinjA hinjB)
          (ProvablyInjective.sumF (ProvablyInjective.listF (ProvablyInjective.inl _ _))
            (ProvablyInjective.listF (ProvablyInjective.inr _ _))))
        (ProvablyInjective.comp
          (ProvablyInjective.sumF (ProvablyInjective.id _) (ProvablyInjective.unitL _))
          (ProvablyInjective.comp
            (ProvablyInjective.sumF (ProvablyInjective.id _)
              (ProvablyInjective.pairL _ _ (ProvablyInjective.id _)))
            (ProvablyInjective.comp (ProvablyInjective.dupCode _)
              (ProvablyInjective.unsplit _ _))))

/-- **Claim F.1.**  For every type `A` there is a finite alphabet `Ā` and an injective
aperiodic term `encA : A → Ā*`.  Together with Claim F.2
(`Lax149335Proofs.exists_injective_binary_of_finAlph`) it gives Lemma 5.6
(`Lax149335Proofs.exists_injective_binary_encoding`).  The completeness proof only needs this
finite-alphabet form, since Lemma 7.3 applies to every finite alphabet. -/
theorem exists_injective_encoding (A : Ty) :
    ∃ (n : ℕ) (enc : Term A (Ty.finAlph n)⋆), IsAperiodic enc ∧ ProvablyInjective enc := by
  obtain ⟨S, enc, hS, hap, hinj⟩ := exists_unitSum_encoding A
  obtain ⟨n, t, hapt, hinjt⟩ := unitSum_finAlph hS
  refine ⟨n, enc ⨟ Term.listF t, ?_, ?_⟩
  · simp only [Term.isAperiodic_comp, Term.isAperiodic_listF]
    exact ⟨hap, hapt⟩
  · exact ProvablyInjective.comp hinj (ProvablyInjective.listF hinjt)

end Lax149335Proofs

bridge_export Lax149335Proofs
