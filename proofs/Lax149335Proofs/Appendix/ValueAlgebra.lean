import Lax149335Proofs.Appendix.BasicFacts
import Mathlib.Tactic.Set

/-!
# Concatenation with values (Lemma 5.2)

Lemma 5.2 of the paper states the associativity and unit laws for concatenation of a term
with list outputs and a list value.  Its proof is "left to the reader" in the paper; it is
carried out here from the monoid axioms (Axiom 10), the unit and associativity axioms
(Axioms 4, 5, 7 and 8) and the projections coherence laws derived from them in
`Lax149335Proofs.Appendix.ProjectionsCoherence`.

The main work consists of three coherence laws (`Lax149335Proofs.Term.unitR_unitR_assocR`,
`Lax149335Proofs.Term.unitL_unitL_assocR`, `Lax149335Proofs.Term.unitL_unitR_assocR`) that describe how the
insertion of the unit type interacts with the associator; each of them is a statement about
terms into a type whose extra components are the unit type, so it can be proved by cancelling
the corresponding provable isomorphism (Lemma 5.5).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

variable {A B : Ty}

/-! ### Concatenation with a value on either side is a post-composition -/

/-- Appending a value is the same as post-composing with the term that appends it. -/
theorem dotR_eq_comp (f : Term A B⋆) (w : Value B⋆) :
    dotR f w ≡ₜ (f ⨟ dotR (Term.id B⋆) w) := by
  calc ((unitR A ⨟ prodF f w) ⨟ binconcat B)
      ≡ₜ ((unitR A ⨟ prodF (f ⨟ Term.id B⋆) (Term.id Ty.unit ⨟ w)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compR _
          (PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.symm (PEq.id_comp _))))
    _ ≡ₜ ((unitR A ⨟ (prodF f (Term.id Ty.unit) ⨟ prodF (Term.id B⋆) w)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
    _ ≡ₜ (((unitR A ⨟ prodF f (Term.id Ty.unit)) ⨟ prodF (Term.id B⋆) w) ⨟ binconcat B) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (((f ⨟ unitR B⋆) ⨟ prodF (Term.id B⋆) w) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compL _ (PEq.symm (PEq.nat_unitR f)))
    _ ≡ₜ ((f ⨟ (unitR B⋆ ⨟ prodF (Term.id B⋆) w)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (f ⨟ ((unitR B⋆ ⨟ prodF (Term.id B⋆) w) ⨟ binconcat B)) := PEq.comp_assoc _ _ _

/-- Prepending a value is the same as post-composing with the term that prepends it. -/
theorem dotL_eq_comp (w : Value B⋆) (f : Term A B⋆) :
    dotL w f ≡ₜ (f ⨟ dotL w (Term.id B⋆)) := by
  calc ((unitL A ⨟ prodF w f) ⨟ binconcat B)
      ≡ₜ ((unitL A ⨟ prodF (Term.id Ty.unit ⨟ w) (f ⨟ Term.id B⋆)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compR _
          (PEq.congr_prodF (PEq.symm (PEq.id_comp _)) (PEq.symm (PEq.comp_id _))))
    _ ≡ₜ ((unitL A ⨟ (prodF (Term.id Ty.unit) f ⨟ prodF w (Term.id B⋆))) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
    _ ≡ₜ (((unitL A ⨟ prodF (Term.id Ty.unit) f) ⨟ prodF w (Term.id B⋆)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (((f ⨟ unitL B⋆) ⨟ prodF w (Term.id B⋆)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compL _ (PEq.symm (PEq.nat_unitL f)))
    _ ≡ₜ ((f ⨟ (unitL B⋆ ⨟ prodF w (Term.id B⋆))) ⨟ binconcat B) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (f ⨟ ((unitL B⋆ ⨟ prodF w (Term.id B⋆)) ⨟ binconcat B)) := PEq.comp_assoc _ _ _

/-! ### The unit laws -/

/-- Appending the empty list changes nothing. -/
theorem dotR_nil (f : Term A B⋆) : dotR f (nilT B) ≡ₜ f := by
  calc ((unitR A ⨟ prodF f (nilT B)) ⨟ binconcat B)
      ≡ₜ ((unitR A ⨟ prodF (f ⨟ Term.id B⋆) (Term.id Ty.unit ⨟ nilT B)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compR _
          (PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.symm (PEq.id_comp _))))
    _ ≡ₜ ((unitR A ⨟ (prodF f (Term.id Ty.unit) ⨟ prodF (Term.id B⋆) (nilT B))) ⨟
          binconcat B) := PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
    _ ≡ₜ (((unitR A ⨟ prodF f (Term.id Ty.unit)) ⨟ prodF (Term.id B⋆) (nilT B)) ⨟
          binconcat B) := PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((unitR A ⨟ prodF f (Term.id Ty.unit)) ⨟
          (prodF (Term.id B⋆) (nilT B) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ ((unitR A ⨟ prodF f (Term.id Ty.unit)) ⨟ fst B⋆ Ty.unit) :=
        PEq.compR _ (binconcat_nil_fst B)
    _ ≡ₜ ((f ⨟ unitR B⋆) ⨟ fst B⋆ Ty.unit) := PEq.compL _ (PEq.symm (PEq.nat_unitR f))
    _ ≡ₜ (f ⨟ (unitR B⋆ ⨟ fst B⋆ Ty.unit)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (f ⨟ Term.id B⋆) := PEq.compR _ (PEq.unitR_fst B⋆)
    _ ≡ₜ f := PEq.comp_id f

/-- Prepending the empty list changes nothing. -/
theorem dotL_nil (f : Term A B⋆) : dotL (nilT B) f ≡ₜ f := by
  calc ((unitL A ⨟ prodF (nilT B) f) ⨟ binconcat B)
      ≡ₜ ((unitL A ⨟ prodF (Term.id Ty.unit ⨟ nilT B) (f ⨟ Term.id B⋆)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.compR _
          (PEq.congr_prodF (PEq.symm (PEq.id_comp _)) (PEq.symm (PEq.comp_id _))))
    _ ≡ₜ ((unitL A ⨟ (prodF (Term.id Ty.unit) f ⨟ prodF (nilT B) (Term.id B⋆))) ⨟
          binconcat B) := PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
    _ ≡ₜ (((unitL A ⨟ prodF (Term.id Ty.unit) f) ⨟ prodF (nilT B) (Term.id B⋆)) ⨟
          binconcat B) := PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((unitL A ⨟ prodF (Term.id Ty.unit) f) ⨟
          (prodF (nilT B) (Term.id B⋆) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ ((unitL A ⨟ prodF (Term.id Ty.unit) f) ⨟ snd Ty.unit B⋆) :=
        PEq.compR _ (binconcat_nil_snd B)
    _ ≡ₜ ((f ⨟ unitL B⋆) ⨟ snd Ty.unit B⋆) := PEq.compL _ (PEq.symm (PEq.nat_unitL f))
    _ ≡ₜ (f ⨟ (unitL B⋆ ⨟ snd Ty.unit B⋆)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (f ⨟ Term.id B⋆) := PEq.compR _ (PEq.unitL_snd B⋆)
    _ ≡ₜ f := PEq.comp_id f

/-! ### Three coherence laws for the unit type and the associator -/

/-- Two provably injective terms out of a type of the form `A ⊗ (1 ⊗ 1)`. -/
private theorem inj_A_unit_unit (A : Ty) :
    ProvablyInjective (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit) :=
  ProvablyInjective.comp
    (ProvablyInjective.prodF (ProvablyInjective.id A) ⟨unitR Ty.unit, PEq.fst_unitR Ty.unit⟩)
    ⟨unitR A, PEq.fst_unitR A⟩

private theorem inj_unit_unit_A (A : Ty) :
    ProvablyInjective (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A) :=
  ProvablyInjective.comp ⟨unitL (Ty.unit ⊗ A), PEq.snd_unitL (Ty.unit ⊗ A)⟩
    ⟨unitL A, PEq.snd_unitL A⟩

private theorem inj_unit_A_unit (A : Ty) :
    ProvablyInjective (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit) :=
  ProvablyInjective.comp ⟨unitL (A ⊗ Ty.unit), PEq.snd_unitL (A ⊗ Ty.unit)⟩
    ⟨unitR A, PEq.fst_unitR A⟩

/-- Coherence: inserting two units on the right and re-associating. -/
theorem unitR_unitR_assocR (A : Ty) :
    (unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ assocR A Ty.unit Ty.unit)) ≡ₜ
      (unitR A ⨟ prodF (Term.id A) (unitL Ty.unit)) := by
  refine ((cancel _ _).1 _ _ (inj_A_unit_unit A)).2 ?_
  have hL : ((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ assocR A Ty.unit Ty.unit)) ⨟
      (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit)) ≡ₜ Term.id A := by
    have hassoc : (assocR A Ty.unit Ty.unit ⨟ prodF (Term.id A) (fst Ty.unit Ty.unit)) ≡ₜ
        fst (A ⊗ Ty.unit) Ty.unit := by
      calc (assocR A Ty.unit Ty.unit ⨟ prodF (Term.id A) (fst Ty.unit Ty.unit))
          ≡ₜ (assocR A Ty.unit Ty.unit ⨟
              (assocL A Ty.unit Ty.unit ⨟ fst (A ⊗ Ty.unit) Ty.unit)) :=
            PEq.compR _ (PEq.symm (Term.assocL_fst A Ty.unit Ty.unit))
        _ ≡ₜ ((assocR A Ty.unit Ty.unit ⨟ assocL A Ty.unit Ty.unit) ⨟
              fst (A ⊗ Ty.unit) Ty.unit) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id ((A ⊗ Ty.unit) ⊗ Ty.unit) ⨟ fst (A ⊗ Ty.unit) Ty.unit) :=
            PEq.compL _ (PEq.assocR_assocL _ _ _)
        _ ≡ₜ fst (A ⊗ Ty.unit) Ty.unit := PEq.id_comp _
    calc ((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ assocR A Ty.unit Ty.unit)) ⨟
            (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit))
        ≡ₜ (unitR A ⨟ ((prodF (unitR A) (Term.id Ty.unit) ⨟ assocR A Ty.unit Ty.unit) ⨟
              (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ (assocR A Ty.unit Ty.unit ⨟
              (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit)))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟
              ((assocR A Ty.unit Ty.unit ⨟ prodF (Term.id A) (fst Ty.unit Ty.unit)) ⨟
                fst A Ty.unit))) :=
          PEq.compR _ (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _)))
      _ ≡ₜ (unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟
              (fst (A ⊗ Ty.unit) Ty.unit ⨟ fst A Ty.unit))) :=
          PEq.compR _ (PEq.compR _ (PEq.compL _ hassoc))
      _ ≡ₜ (unitR A ⨟ ((prodF (unitR A) (Term.id Ty.unit) ⨟ fst (A ⊗ Ty.unit) Ty.unit) ⨟
              fst A Ty.unit)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (unitR A ⨟ ((fst A Ty.unit ⨟ unitR A) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.compL _ (PEq.nat_fst _ _))
      _ ≡ₜ ((unitR A ⨟ (fst A Ty.unit ⨟ unitR A)) ⨟ fst A Ty.unit) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((unitR A ⨟ fst A Ty.unit) ⨟ unitR A) ⨟ fst A Ty.unit) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((Term.id A ⨟ unitR A) ⨟ fst A Ty.unit) :=
          PEq.compL _ (PEq.compL _ (PEq.unitR_fst A))
      _ ≡ₜ (unitR A ⨟ fst A Ty.unit) := PEq.compL _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := PEq.unitR_fst A
  have hR : ((unitR A ⨟ prodF (Term.id A) (unitL Ty.unit)) ⨟
      (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit)) ≡ₜ Term.id A := by
    calc ((unitR A ⨟ prodF (Term.id A) (unitL Ty.unit)) ⨟
            (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit))
        ≡ₜ (unitR A ⨟ (prodF (Term.id A) (unitL Ty.unit) ⨟
              (prodF (Term.id A) (fst Ty.unit Ty.unit) ⨟ fst A Ty.unit))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (unitR A ⨟ ((prodF (Term.id A) (unitL Ty.unit) ⨟
              prodF (Term.id A) (fst Ty.unit Ty.unit)) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (unitR A ⨟ (prodF (Term.id A ⨟ Term.id A)
              (unitL Ty.unit ⨟ fst Ty.unit Ty.unit) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.compL _ (PEq.prod_comp _ _ _ _))
      _ ≡ₜ (unitR A ⨟ (prodF (Term.id A) (Term.id Ty.unit) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.compL _ (PEq.congr_prodF (PEq.id_comp _)
            (PEq.unit_unique _ _)))
      _ ≡ₜ (unitR A ⨟ (Term.id (A ⊗ Ty.unit) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.compL _ (PEq.prod_id _ _))
      _ ≡ₜ (unitR A ⨟ fst A Ty.unit) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := PEq.unitR_fst A
  exact hL.trans (PEq.symm hR)

/-- Coherence: inserting two units on the left and re-associating. -/
theorem unitL_unitL_assocR (A : Ty) :
    (unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ assocR Ty.unit Ty.unit A)) ≡ₜ
      (unitL A ⨟ prodF (Term.id Ty.unit) (unitL A)) := by
  refine ((cancel _ _).1 _ _ (inj_unit_unit_A A)).2 ?_
  have hL : ((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ assocR Ty.unit Ty.unit A)) ⨟
      (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A)) ≡ₜ Term.id A := by
    calc ((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ assocR Ty.unit Ty.unit A)) ⨟
            (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A))
        ≡ₜ (unitL A ⨟ ((prodF (unitL Ty.unit) (Term.id A) ⨟ assocR Ty.unit Ty.unit A) ⨟
              (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ (assocR Ty.unit Ty.unit A ⨟
              (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A)))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟
              ((assocR Ty.unit Ty.unit A ⨟ snd Ty.unit (Ty.unit ⊗ A)) ⨟ snd Ty.unit A))) :=
          PEq.compR _ (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _)))
      _ ≡ₜ (unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟
              (prodF (snd Ty.unit Ty.unit) (Term.id A) ⨟ snd Ty.unit A))) :=
          PEq.compR _ (PEq.compR _ (PEq.compL _ (Term.assocR_snd Ty.unit Ty.unit A)))
      _ ≡ₜ (unitL A ⨟ ((prodF (unitL Ty.unit) (Term.id A) ⨟
              prodF (snd Ty.unit Ty.unit) (Term.id A)) ⨟ snd Ty.unit A)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (unitL A ⨟ (prodF (unitL Ty.unit ⨟ snd Ty.unit Ty.unit)
              (Term.id A ⨟ Term.id A) ⨟ snd Ty.unit A)) :=
          PEq.compR _ (PEq.compL _ (PEq.prod_comp _ _ _ _))
      _ ≡ₜ (unitL A ⨟ (prodF (Term.id Ty.unit) (Term.id A) ⨟ snd Ty.unit A)) :=
          PEq.compR _ (PEq.compL _ (PEq.congr_prodF (PEq.unitL_snd Ty.unit)
            (PEq.id_comp _)))
      _ ≡ₜ (unitL A ⨟ (Term.id (Ty.unit ⊗ A) ⨟ snd Ty.unit A)) :=
          PEq.compR _ (PEq.compL _ (PEq.prod_id _ _))
      _ ≡ₜ (unitL A ⨟ snd Ty.unit A) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := PEq.unitL_snd A
  have hR : ((unitL A ⨟ prodF (Term.id Ty.unit) (unitL A)) ⨟
      (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A)) ≡ₜ Term.id A := by
    calc ((unitL A ⨟ prodF (Term.id Ty.unit) (unitL A)) ⨟
            (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A))
        ≡ₜ (unitL A ⨟ (prodF (Term.id Ty.unit) (unitL A) ⨟
              (snd Ty.unit (Ty.unit ⊗ A) ⨟ snd Ty.unit A))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (unitL A ⨟ ((prodF (Term.id Ty.unit) (unitL A) ⨟ snd Ty.unit (Ty.unit ⊗ A)) ⨟
              snd Ty.unit A)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (unitL A ⨟ ((snd Ty.unit A ⨟ unitL A) ⨟ snd Ty.unit A)) :=
          PEq.compR _ (PEq.compL _ (PEq.nat_snd _ _))
      _ ≡ₜ (((unitL A ⨟ snd Ty.unit A) ⨟ unitL A) ⨟ snd Ty.unit A) := by
            calc (unitL A ⨟ ((snd Ty.unit A ⨟ unitL A) ⨟ snd Ty.unit A))
                ≡ₜ ((unitL A ⨟ (snd Ty.unit A ⨟ unitL A)) ⨟ snd Ty.unit A) :=
                  PEq.symm (PEq.comp_assoc _ _ _)
              _ ≡ₜ (((unitL A ⨟ snd Ty.unit A) ⨟ unitL A) ⨟ snd Ty.unit A) :=
                  PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((Term.id A ⨟ unitL A) ⨟ snd Ty.unit A) :=
          PEq.compL _ (PEq.compL _ (PEq.unitL_snd A))
      _ ≡ₜ (unitL A ⨟ snd Ty.unit A) := PEq.compL _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := PEq.unitL_snd A
  exact hL.trans (PEq.symm hR)

/-- Coherence: inserting a unit on either side and re-associating. -/
theorem unitL_unitR_assocR (A : Ty) :
    (unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ assocR Ty.unit A Ty.unit)) ≡ₜ
      (unitL A ⨟ prodF (Term.id Ty.unit) (unitR A)) := by
  refine ((cancel _ _).1 _ _ (inj_unit_A_unit A)).2 ?_
  have hL : ((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ assocR Ty.unit A Ty.unit)) ⨟
      (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit)) ≡ₜ Term.id A := by
    calc ((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ assocR Ty.unit A Ty.unit)) ⨟
            (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit))
        ≡ₜ (unitR A ⨟ ((prodF (unitL A) (Term.id Ty.unit) ⨟ assocR Ty.unit A Ty.unit) ⨟
              (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ (assocR Ty.unit A Ty.unit ⨟
              (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit)))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟
              ((assocR Ty.unit A Ty.unit ⨟ snd Ty.unit (A ⊗ Ty.unit)) ⨟ fst A Ty.unit))) :=
          PEq.compR _ (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _)))
      _ ≡ₜ (unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟
              (prodF (snd Ty.unit A) (Term.id Ty.unit) ⨟ fst A Ty.unit))) :=
          PEq.compR _ (PEq.compR _ (PEq.compL _ (Term.assocR_snd Ty.unit A Ty.unit)))
      _ ≡ₜ (unitR A ⨟ ((prodF (unitL A) (Term.id Ty.unit) ⨟
              prodF (snd Ty.unit A) (Term.id Ty.unit)) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (unitR A ⨟ (prodF (unitL A ⨟ snd Ty.unit A) (Term.id Ty.unit ⨟ Term.id Ty.unit) ⨟
              fst A Ty.unit)) := PEq.compR _ (PEq.compL _ (PEq.prod_comp _ _ _ _))
      _ ≡ₜ (unitR A ⨟ (prodF (Term.id A) (Term.id Ty.unit) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.compL _ (PEq.congr_prodF (PEq.unitL_snd A) (PEq.id_comp _)))
      _ ≡ₜ (unitR A ⨟ (Term.id (A ⊗ Ty.unit) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.compL _ (PEq.prod_id _ _))
      _ ≡ₜ (unitR A ⨟ fst A Ty.unit) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := PEq.unitR_fst A
  have hR : ((unitL A ⨟ prodF (Term.id Ty.unit) (unitR A)) ⨟
      (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit)) ≡ₜ Term.id A := by
    calc ((unitL A ⨟ prodF (Term.id Ty.unit) (unitR A)) ⨟
            (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit))
        ≡ₜ (unitL A ⨟ (prodF (Term.id Ty.unit) (unitR A) ⨟
              (snd Ty.unit (A ⊗ Ty.unit) ⨟ fst A Ty.unit))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (unitL A ⨟ ((prodF (Term.id Ty.unit) (unitR A) ⨟ snd Ty.unit (A ⊗ Ty.unit)) ⨟
              fst A Ty.unit)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (unitL A ⨟ ((snd Ty.unit A ⨟ unitR A) ⨟ fst A Ty.unit)) :=
          PEq.compR _ (PEq.compL _ (PEq.nat_snd _ _))
      _ ≡ₜ (((unitL A ⨟ snd Ty.unit A) ⨟ unitR A) ⨟ fst A Ty.unit) := by
            calc (unitL A ⨟ ((snd Ty.unit A ⨟ unitR A) ⨟ fst A Ty.unit))
                ≡ₜ ((unitL A ⨟ (snd Ty.unit A ⨟ unitR A)) ⨟ fst A Ty.unit) :=
                  PEq.symm (PEq.comp_assoc _ _ _)
              _ ≡ₜ (((unitL A ⨟ snd Ty.unit A) ⨟ unitR A) ⨟ fst A Ty.unit) :=
                  PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((Term.id A ⨟ unitR A) ⨟ fst A Ty.unit) :=
          PEq.compL _ (PEq.compL _ (PEq.unitL_snd A))
      _ ≡ₜ (unitR A ⨟ fst A Ty.unit) := PEq.compL _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := PEq.unitR_fst A
  exact hL.trans (PEq.symm hR)

/-! ### The associativity laws -/

/-- Associativity: appending two values one after the other. -/
theorem dotR_dotR (f : Term A B⋆) (w v : Value B⋆) :
    dotR (dotR f w) v ≡ₜ dotR f (dotL w v) := by
  have hL : dotR (dotR f w) v ≡ₜ
      (((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ assocR A Ty.unit Ty.unit)) ⨟
        prodF f (prodF w v)) ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
    calc ((unitR A ⨟ prodF ((unitR A ⨟ prodF f w) ⨟ binconcat B) v) ⨟ binconcat B)
        ≡ₜ ((unitR A ⨟ prodF (((unitR A ⨟ prodF f w)) ⨟ binconcat B)
              (v ⨟ Term.id B⋆)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.comp_id _))))
      _ ≡ₜ ((unitR A ⨟ (prodF (unitR A ⨟ prodF f w) v ⨟
              prodF (binconcat B) (Term.id B⋆))) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
      _ ≡ₜ (((unitR A ⨟ prodF (unitR A ⨟ prodF f w) v) ⨟
              prodF (binconcat B) (Term.id B⋆)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((unitR A ⨟ prodF (unitR A ⨟ prodF f w) v) ⨟
              (prodF (binconcat B) (Term.id B⋆) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((unitR A ⨟ prodF (unitR A ⨟ prodF f w) v) ⨟
              (assocR B⋆ B⋆ B⋆ ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) :=
          PEq.compR _ ((PEq.binconcat_assoc B).trans (PEq.comp_assoc _ _ _))
      _ ≡ₜ (((unitR A ⨟ prodF (unitR A ⨟ prodF f w) v) ⨟ assocR B⋆ B⋆ B⋆) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ prodF (prodF f w) v)) ⨟
              assocR B⋆ B⋆ B⋆) ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compL _ (PEq.compR _ (PEq.symm
            ((PEq.prod_comp _ _ _ _).trans (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))))))
      _ ≡ₜ ((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟
              (prodF (prodF f w) v ⨟ assocR B⋆ B⋆ B⋆))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
            refine PEq.compL _ ?_
            calc ((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ prodF (prodF f w) v)) ⨟
                    assocR B⋆ B⋆ B⋆)
                ≡ₜ (unitR A ⨟ ((prodF (unitR A) (Term.id Ty.unit) ⨟ prodF (prodF f w) v) ⨟
                      assocR B⋆ B⋆ B⋆)) := PEq.comp_assoc _ _ _
              _ ≡ₜ (unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟
                      (prodF (prodF f w) v ⨟ assocR B⋆ B⋆ B⋆))) :=
                  PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟
              (assocR A Ty.unit Ty.unit ⨟ prodF f (prodF w v)))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compR _ (PEq.compR _ (PEq.nat_assocR f w v)))
      _ ≡ₜ (((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟ assocR A Ty.unit Ty.unit)) ⨟
              prodF f (prodF w v)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
            refine PEq.compL _ ?_
            calc (unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟
                    (assocR A Ty.unit Ty.unit ⨟ prodF f (prodF w v))))
                ≡ₜ (unitR A ⨟ ((prodF (unitR A) (Term.id Ty.unit) ⨟
                      assocR A Ty.unit Ty.unit) ⨟ prodF f (prodF w v))) :=
                  PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
              _ ≡ₜ ((unitR A ⨟ (prodF (unitR A) (Term.id Ty.unit) ⨟
                      assocR A Ty.unit Ty.unit)) ⨟ prodF f (prodF w v)) :=
                  PEq.symm (PEq.comp_assoc _ _ _)
  have hR : dotR f (dotL w v) ≡ₜ
      (((unitR A ⨟ prodF (Term.id A) (unitL Ty.unit)) ⨟ prodF f (prodF w v)) ⨟
        (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
    calc ((unitR A ⨟ prodF f ((unitL Ty.unit ⨟ prodF w v) ⨟ binconcat B)) ⨟ binconcat B)
        ≡ₜ ((unitR A ⨟ prodF (f ⨟ Term.id B⋆)
              ((unitL Ty.unit ⨟ prodF w v) ⨟ binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.refl _)))
      _ ≡ₜ ((unitR A ⨟ (prodF f (unitL Ty.unit ⨟ prodF w v) ⨟
              prodF (Term.id B⋆) (binconcat B))) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
      _ ≡ₜ (((unitR A ⨟ prodF f (unitL Ty.unit ⨟ prodF w v)) ⨟
              prodF (Term.id B⋆) (binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((unitR A ⨟ prodF f (unitL Ty.unit ⨟ prodF w v)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((unitR A ⨟ (prodF (Term.id A) (unitL Ty.unit) ⨟ prodF f (prodF w v))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _)))))
      _ ≡ₜ (((unitR A ⨟ prodF (Term.id A) (unitL Ty.unit)) ⨟ prodF f (prodF w v)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
  exact hL.trans ((PEq.compL _ (PEq.compL _ (unitR_unitR_assocR A))).trans (PEq.symm hR))

/-- Associativity: prepending two values one after the other. -/
theorem dotL_dotL (w v : Value B⋆) (f : Term A B⋆) :
    dotL w (dotL v f) ≡ₜ dotL (dotL w v) f := by
  have hL : dotL w (dotL v f) ≡ₜ
      (((unitL A ⨟ prodF (Term.id Ty.unit) (unitL A)) ⨟ prodF w (prodF v f)) ⨟
        (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
    calc ((unitL A ⨟ prodF w ((unitL A ⨟ prodF v f) ⨟ binconcat B)) ⨟ binconcat B)
        ≡ₜ ((unitL A ⨟ prodF (w ⨟ Term.id B⋆)
              ((unitL A ⨟ prodF v f) ⨟ binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.refl _)))
      _ ≡ₜ ((unitL A ⨟ (prodF w (unitL A ⨟ prodF v f) ⨟
              prodF (Term.id B⋆) (binconcat B))) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
      _ ≡ₜ (((unitL A ⨟ prodF w (unitL A ⨟ prodF v f)) ⨟
              prodF (Term.id B⋆) (binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((unitL A ⨟ prodF w (unitL A ⨟ prodF v f)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((unitL A ⨟ (prodF (Term.id Ty.unit) (unitL A) ⨟ prodF w (prodF v f))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _)))))
      _ ≡ₜ (((unitL A ⨟ prodF (Term.id Ty.unit) (unitL A)) ⨟ prodF w (prodF v f)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
  have hR : dotL (dotL w v) f ≡ₜ
      (((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ assocR Ty.unit Ty.unit A)) ⨟
        prodF w (prodF v f)) ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
    calc ((unitL A ⨟ prodF ((unitL Ty.unit ⨟ prodF w v) ⨟ binconcat B) f) ⨟ binconcat B)
        ≡ₜ ((unitL A ⨟ prodF ((unitL Ty.unit ⨟ prodF w v) ⨟ binconcat B)
              (f ⨟ Term.id B⋆)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.comp_id _))))
      _ ≡ₜ ((unitL A ⨟ (prodF (unitL Ty.unit ⨟ prodF w v) f ⨟
              prodF (binconcat B) (Term.id B⋆))) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
      _ ≡ₜ (((unitL A ⨟ prodF (unitL Ty.unit ⨟ prodF w v) f) ⨟
              prodF (binconcat B) (Term.id B⋆)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((unitL A ⨟ prodF (unitL Ty.unit ⨟ prodF w v) f) ⨟
              (prodF (binconcat B) (Term.id B⋆) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((unitL A ⨟ prodF (unitL Ty.unit ⨟ prodF w v) f) ⨟
              (assocR B⋆ B⋆ B⋆ ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) :=
          PEq.compR _ ((PEq.binconcat_assoc B).trans (PEq.comp_assoc _ _ _))
      _ ≡ₜ (((unitL A ⨟ prodF (unitL Ty.unit ⨟ prodF w v) f) ⨟ assocR B⋆ B⋆ B⋆) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ prodF (prodF w v) f)) ⨟
              assocR B⋆ B⋆ B⋆) ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compL _ (PEq.compR _ (PEq.symm
            ((PEq.prod_comp _ _ _ _).trans (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))))))
      _ ≡ₜ ((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟
              (prodF (prodF w v) f ⨟ assocR B⋆ B⋆ B⋆))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
            refine PEq.compL _ ?_
            calc ((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ prodF (prodF w v) f)) ⨟
                    assocR B⋆ B⋆ B⋆)
                ≡ₜ (unitL A ⨟ ((prodF (unitL Ty.unit) (Term.id A) ⨟ prodF (prodF w v) f) ⨟
                      assocR B⋆ B⋆ B⋆)) := PEq.comp_assoc _ _ _
              _ ≡ₜ (unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟
                      (prodF (prodF w v) f ⨟ assocR B⋆ B⋆ B⋆))) :=
                  PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟
              (assocR Ty.unit Ty.unit A ⨟ prodF w (prodF v f)))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compR _ (PEq.compR _ (PEq.nat_assocR w v f)))
      _ ≡ₜ (((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟ assocR Ty.unit Ty.unit A)) ⨟
              prodF w (prodF v f)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
            refine PEq.compL _ ?_
            calc (unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟
                    (assocR Ty.unit Ty.unit A ⨟ prodF w (prodF v f))))
                ≡ₜ (unitL A ⨟ ((prodF (unitL Ty.unit) (Term.id A) ⨟
                      assocR Ty.unit Ty.unit A) ⨟ prodF w (prodF v f))) :=
                  PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
              _ ≡ₜ ((unitL A ⨟ (prodF (unitL Ty.unit) (Term.id A) ⨟
                      assocR Ty.unit Ty.unit A)) ⨟ prodF w (prodF v f)) :=
                  PEq.symm (PEq.comp_assoc _ _ _)
  exact hL.trans
    ((PEq.compL _ (PEq.compL _ (PEq.symm (unitL_unitL_assocR A)))).trans (PEq.symm hR))

/-- Associativity: prepending and appending a value commute. -/
theorem dotR_dotL (w : Value B⋆) (f : Term A B⋆) (v : Value B⋆) :
    dotR (dotL w f) v ≡ₜ dotL w (dotR f v) := by
  have hL : dotR (dotL w f) v ≡ₜ
      (((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ assocR Ty.unit A Ty.unit)) ⨟
        prodF w (prodF f v)) ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
    calc ((unitR A ⨟ prodF ((unitL A ⨟ prodF w f) ⨟ binconcat B) v) ⨟ binconcat B)
        ≡ₜ ((unitR A ⨟ prodF ((unitL A ⨟ prodF w f) ⨟ binconcat B)
              (v ⨟ Term.id B⋆)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.comp_id _))))
      _ ≡ₜ ((unitR A ⨟ (prodF (unitL A ⨟ prodF w f) v ⨟
              prodF (binconcat B) (Term.id B⋆))) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
      _ ≡ₜ (((unitR A ⨟ prodF (unitL A ⨟ prodF w f) v) ⨟
              prodF (binconcat B) (Term.id B⋆)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((unitR A ⨟ prodF (unitL A ⨟ prodF w f) v) ⨟
              (prodF (binconcat B) (Term.id B⋆) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((unitR A ⨟ prodF (unitL A ⨟ prodF w f) v) ⨟
              (assocR B⋆ B⋆ B⋆ ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) :=
          PEq.compR _ ((PEq.binconcat_assoc B).trans (PEq.comp_assoc _ _ _))
      _ ≡ₜ (((unitR A ⨟ prodF (unitL A ⨟ prodF w f) v) ⨟ assocR B⋆ B⋆ B⋆) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ prodF (prodF w f) v)) ⨟
              assocR B⋆ B⋆ B⋆) ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compL _ (PEq.compR _ (PEq.symm
            ((PEq.prod_comp _ _ _ _).trans (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))))))
      _ ≡ₜ ((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟
              (prodF (prodF w f) v ⨟ assocR B⋆ B⋆ B⋆))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
            refine PEq.compL _ ?_
            calc ((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ prodF (prodF w f) v)) ⨟
                    assocR B⋆ B⋆ B⋆)
                ≡ₜ (unitR A ⨟ ((prodF (unitL A) (Term.id Ty.unit) ⨟ prodF (prodF w f) v) ⨟
                      assocR B⋆ B⋆ B⋆)) := PEq.comp_assoc _ _ _
              _ ≡ₜ (unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟
                      (prodF (prodF w f) v ⨟ assocR B⋆ B⋆ B⋆))) :=
                  PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟
              (assocR Ty.unit A Ty.unit ⨟ prodF w (prodF f v)))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compR _ (PEq.compR _ (PEq.nat_assocR w f v)))
      _ ≡ₜ (((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟ assocR Ty.unit A Ty.unit)) ⨟
              prodF w (prodF f v)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
            refine PEq.compL _ ?_
            calc (unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟
                    (assocR Ty.unit A Ty.unit ⨟ prodF w (prodF f v))))
                ≡ₜ (unitR A ⨟ ((prodF (unitL A) (Term.id Ty.unit) ⨟
                      assocR Ty.unit A Ty.unit) ⨟ prodF w (prodF f v))) :=
                  PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
              _ ≡ₜ ((unitR A ⨟ (prodF (unitL A) (Term.id Ty.unit) ⨟
                      assocR Ty.unit A Ty.unit)) ⨟ prodF w (prodF f v)) :=
                  PEq.symm (PEq.comp_assoc _ _ _)
  have hR : dotL w (dotR f v) ≡ₜ
      (((unitL A ⨟ prodF (Term.id Ty.unit) (unitR A)) ⨟ prodF w (prodF f v)) ⨟
        (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := by
    calc ((unitL A ⨟ prodF w ((unitR A ⨟ prodF f v) ⨟ binconcat B)) ⨟ binconcat B)
        ≡ₜ ((unitL A ⨟ prodF (w ⨟ Term.id B⋆)
              ((unitR A ⨟ prodF f v) ⨟ binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.refl _)))
      _ ≡ₜ ((unitL A ⨟ (prodF w (unitR A ⨟ prodF f v) ⨟
              prodF (Term.id B⋆) (binconcat B))) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.symm (PEq.prod_comp _ _ _ _)))
      _ ≡ₜ (((unitL A ⨟ prodF w (unitR A ⨟ prodF f v)) ⨟
              prodF (Term.id B⋆) (binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((unitL A ⨟ prodF w (unitR A ⨟ prodF f v)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
      _ ≡ₜ ((unitL A ⨟ (prodF (Term.id Ty.unit) (unitR A) ⨟ prodF w (prodF f v))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
            (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _)))))
      _ ≡ₜ (((unitL A ⨟ prodF (Term.id Ty.unit) (unitR A)) ⨟ prodF w (prodF f v)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
  exact hL.trans ((PEq.compL _ (PEq.compL _ (unitL_unitR_assocR A))).trans (PEq.symm hR))

/-! ### The concatenation combinator -/

/-- Associativity of the concatenation combinator. -/
theorem fdot_assoc {X Y Z D : Ty} (c₁ : Term X D⋆) (c₂ : Term Y D⋆) (c₃ : Term Z D⋆) :
    ((c₁ ⊙ c₂) ⊙ c₃) ≡ₜ (assocR X Y Z ⨟ (c₁ ⊙ (c₂ ⊙ c₃))) := by
  calc (prodF (prodF c₁ c₂ ⨟ binconcat D) c₃ ⨟ binconcat D)
      ≡ₜ ((prodF (prodF c₁ c₂) c₃ ⨟ prodF (binconcat D) (Term.id D⋆)) ⨟ binconcat D) :=
        PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.comp_id _))))
    _ ≡ₜ (prodF (prodF c₁ c₂) c₃ ⨟ (prodF (binconcat D) (Term.id D⋆) ⨟ binconcat D)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (prodF c₁ c₂) c₃ ⨟
          (assocR D⋆ D⋆ D⋆ ⨟ (prodF (Term.id D⋆) (binconcat D) ⨟ binconcat D))) :=
        PEq.compR _ ((PEq.binconcat_assoc D).trans (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((prodF (prodF c₁ c₂) c₃ ⨟ assocR D⋆ D⋆ D⋆) ⨟
          (prodF (Term.id D⋆) (binconcat D) ⨟ binconcat D)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((assocR X Y Z ⨟ prodF c₁ (prodF c₂ c₃)) ⨟
          (prodF (Term.id D⋆) (binconcat D) ⨟ binconcat D)) :=
        PEq.compL _ (PEq.nat_assocR c₁ c₂ c₃)
    _ ≡ₜ (assocR X Y Z ⨟ ((prodF c₁ (prodF c₂ c₃) ⨟ prodF (Term.id D⋆) (binconcat D)) ⨟
          binconcat D)) := by
          calc ((assocR X Y Z ⨟ prodF c₁ (prodF c₂ c₃)) ⨟
                  (prodF (Term.id D⋆) (binconcat D) ⨟ binconcat D))
              ≡ₜ (assocR X Y Z ⨟ (prodF c₁ (prodF c₂ c₃) ⨟
                    (prodF (Term.id D⋆) (binconcat D) ⨟ binconcat D))) := PEq.comp_assoc _ _ _
            _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (assocR X Y Z ⨟ (prodF (c₁ ⨟ Term.id D⋆) (prodF c₂ c₃ ⨟ binconcat D) ⨟
          binconcat D)) := PEq.compR _ (PEq.compL _ (PEq.prod_comp _ _ _ _))
    _ ≡ₜ (assocR X Y Z ⨟ (prodF c₁ (prodF c₂ c₃ ⨟ binconcat D) ⨟ binconcat D)) :=
        PEq.compR _ (PEq.compL _ (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _)))

/-- Concatenating with the empty list on the right. -/
theorem fdot_nil_right {X D : Ty} (c : Term X D⋆) :
    (c ⊙ nilT D) ≡ₜ (fst X Ty.unit ⨟ c) := by
  calc (prodF c (nilT D) ⨟ binconcat D)
      ≡ₜ (prodF c (toUnit Ty.unit ⨟ nilT D) ⨟ binconcat D) :=
        PEq.compL _ (PEq.congr_prodF (PEq.refl _)
          (PEq.symm ((PEq.compL _ (PEq.unit_unique (toUnit Ty.unit) (Term.id Ty.unit))).trans
            (PEq.id_comp _))))
    _ ≡ₜ (fst X Ty.unit ⨟ c) := prodF_nilconst_binconcat c

/-- Concatenating with the empty list on the left. -/
theorem fdot_nil_left {Z D : Ty} (c : Term Z D⋆) :
    (nilT D ⊙ c) ≡ₜ (snd Ty.unit Z ⨟ c) := by
  calc (prodF (nilT D) c ⨟ binconcat D)
      ≡ₜ ((prodF (Term.id Ty.unit) c ⨟ prodF (nilT D) (Term.id D⋆)) ⨟ binconcat D) :=
        PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.id_comp _) (PEq.comp_id _))))
    _ ≡ₜ (prodF (Term.id Ty.unit) c ⨟ (prodF (nilT D) (Term.id D⋆) ⨟ binconcat D)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.id Ty.unit) c ⨟ snd Ty.unit D⋆) :=
        PEq.compR _ (binconcat_nil_snd D)
    _ ≡ₜ (snd Ty.unit Z ⨟ c) := PEq.nat_snd _ _

/-- The last law of Lemma 5.2: a value can be moved between the two arguments of the
concatenation combinator. -/
theorem fdot_dotR_dotL {A₁ A₂ : Ty} (f : Term A₁ B⋆) (g : Term A₂ B⋆) (w : Value B⋆) :
    fdot (dotR f w) g ≡ₜ fdot f (dotL w g) := by
  -- both sides factor through `f × g`
  have key : (prodF (dotR (Term.id B⋆) w) (Term.id B⋆) ⨟ binconcat B) ≡ₜ
      (prodF (Term.id B⋆) (dotL w (Term.id B⋆)) ⨟ binconcat B) := by
    have hL : (prodF (dotR (Term.id B⋆) w) (Term.id B⋆) ⨟ binconcat B) ≡ₜ
        ((prodF (unitR B⋆) (Term.id B⋆) ⨟ assocR B⋆ Ty.unit B⋆) ⨟
          (prodF (Term.id B⋆) (prodF w (Term.id B⋆)) ⨟
            (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) := by
      calc (prodF ((unitR B⋆ ⨟ prodF (Term.id B⋆) w) ⨟ binconcat B) (Term.id B⋆) ⨟
              binconcat B)
          ≡ₜ ((prodF (unitR B⋆ ⨟ prodF (Term.id B⋆) w) (Term.id B⋆) ⨟
              prodF (binconcat B) (Term.id B⋆)) ⨟ binconcat B) :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.refl _) (PEq.comp_id _))))
        _ ≡ₜ (prodF (unitR B⋆ ⨟ prodF (Term.id B⋆) w) (Term.id B⋆) ⨟
              (prodF (binconcat B) (Term.id B⋆) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (prodF (unitR B⋆ ⨟ prodF (Term.id B⋆) w) (Term.id B⋆) ⨟
              (assocR B⋆ B⋆ B⋆ ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) :=
            PEq.compR _ ((PEq.binconcat_assoc B).trans (PEq.comp_assoc _ _ _))
        _ ≡ₜ ((prodF (unitR B⋆) (Term.id B⋆) ⨟
              prodF (prodF (Term.id B⋆) w) (Term.id B⋆)) ⨟
              (assocR B⋆ B⋆ B⋆ ⨟ (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))))
        _ ≡ₜ (prodF (unitR B⋆) (Term.id B⋆) ⨟
              ((prodF (prodF (Term.id B⋆) w) (Term.id B⋆) ⨟ assocR B⋆ B⋆ B⋆) ⨟
                (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) := by
              calc ((prodF (unitR B⋆) (Term.id B⋆) ⨟
                      prodF (prodF (Term.id B⋆) w) (Term.id B⋆)) ⨟
                      (assocR B⋆ B⋆ B⋆ ⨟
                        (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)))
                  ≡ₜ (prodF (unitR B⋆) (Term.id B⋆) ⨟
                      (prodF (prodF (Term.id B⋆) w) (Term.id B⋆) ⨟
                        (assocR B⋆ B⋆ B⋆ ⨟
                          (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)))) :=
                    PEq.comp_assoc _ _ _
                _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (prodF (unitR B⋆) (Term.id B⋆) ⨟
              ((assocR B⋆ Ty.unit B⋆ ⨟ prodF (Term.id B⋆) (prodF w (Term.id B⋆))) ⨟
                (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) :=
            PEq.compR _ (PEq.compL _ (PEq.nat_assocR (Term.id B⋆) w (Term.id B⋆)))
        _ ≡ₜ ((prodF (unitR B⋆) (Term.id B⋆) ⨟ assocR B⋆ Ty.unit B⋆) ⨟
              (prodF (Term.id B⋆) (prodF w (Term.id B⋆)) ⨟
                (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) := by
              calc (prodF (unitR B⋆) (Term.id B⋆) ⨟
                      ((assocR B⋆ Ty.unit B⋆ ⨟ prodF (Term.id B⋆) (prodF w (Term.id B⋆))) ⨟
                        (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)))
                  ≡ₜ (prodF (unitR B⋆) (Term.id B⋆) ⨟
                      (assocR B⋆ Ty.unit B⋆ ⨟ (prodF (Term.id B⋆) (prodF w (Term.id B⋆)) ⨟
                        (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)))) :=
                    PEq.compR _ (PEq.comp_assoc _ _ _)
                _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
    have hR : (prodF (Term.id B⋆) (dotL w (Term.id B⋆)) ⨟ binconcat B) ≡ₜ
        (prodF (Term.id B⋆) (unitL B⋆) ⨟
          (prodF (Term.id B⋆) (prodF w (Term.id B⋆)) ⨟
            (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) := by
      calc (prodF (Term.id B⋆) ((unitL B⋆ ⨟ prodF w (Term.id B⋆)) ⨟ binconcat B) ⨟
              binconcat B)
          ≡ₜ ((prodF (Term.id B⋆) (unitL B⋆ ⨟ prodF w (Term.id B⋆)) ⨟
              prodF (Term.id B⋆) (binconcat B)) ⨟ binconcat B) :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.comp_id _) (PEq.refl _))))
        _ ≡ₜ (prodF (Term.id B⋆) (unitL B⋆ ⨟ prodF w (Term.id B⋆)) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
        _ ≡ₜ ((prodF (Term.id B⋆) (unitL B⋆) ⨟
              prodF (Term.id B⋆) (prodF w (Term.id B⋆))) ⨟
              (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B)) :=
            PEq.compL _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
              (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))))
        _ ≡ₜ (prodF (Term.id B⋆) (unitL B⋆) ⨟
              (prodF (Term.id B⋆) (prodF w (Term.id B⋆)) ⨟
                (prodF (Term.id B⋆) (binconcat B) ⨟ binconcat B))) := PEq.comp_assoc _ _ _
    exact hL.trans ((PEq.compL _ (unitR_assocR B⋆ B⋆)).trans (PEq.symm hR))
  calc (prodF (dotR f w) g ⨟ binconcat B)
      ≡ₜ (prodF (f ⨟ dotR (Term.id B⋆) w) (g ⨟ Term.id B⋆) ⨟ binconcat B) :=
        PEq.compL _ (PEq.congr_prodF (dotR_eq_comp f w) (PEq.symm (PEq.comp_id _)))
    _ ≡ₜ ((prodF f g ⨟ prodF (dotR (Term.id B⋆) w) (Term.id B⋆)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.symm (PEq.prod_comp _ _ _ _))
    _ ≡ₜ (prodF f g ⨟ (prodF (dotR (Term.id B⋆) w) (Term.id B⋆) ⨟ binconcat B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF f g ⨟ (prodF (Term.id B⋆) (dotL w (Term.id B⋆)) ⨟ binconcat B)) :=
        PEq.compR _ key
    _ ≡ₜ ((prodF f g ⨟ prodF (Term.id B⋆) (dotL w (Term.id B⋆))) ⨟ binconcat B) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (f ⨟ Term.id B⋆) (g ⨟ dotL w (Term.id B⋆)) ⨟ binconcat B) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (prodF f (dotL w g) ⨟ binconcat B) :=
        PEq.compL _ (PEq.congr_prodF (PEq.comp_id _) (PEq.symm (dotL_eq_comp w g)))

end Term

/-- **Lemma 5.2.**  The associativity laws for concatenation with values. -/
theorem value_assoc {A A' B : Ty} (f : Term A B⋆) (g : Term A' B⋆) (w v : Value B⋆) :
    (dotR (dotR f w) v ≡ₜ dotR f (dotL w v)) ∧
    (dotL w (dotL v f) ≡ₜ dotL (dotL w v) f) ∧
    (dotR f (nilT B) ≡ₜ f) ∧
    (dotL (nilT B) f ≡ₜ f) ∧
    (dotR (dotL w f) v ≡ₜ dotL w (dotR f v)) ∧
    (fdot (dotR f w) g ≡ₜ fdot f (dotL w g)) :=
  ⟨Term.dotR_dotR f w v, Term.dotL_dotL w v f, Term.dotR_nil f, Term.dotL_nil f,
    Term.dotR_dotL w f v, Term.fdot_dotR_dotL f g w⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
