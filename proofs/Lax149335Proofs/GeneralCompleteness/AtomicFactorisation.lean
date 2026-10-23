import Lax149335Proofs.Appendix.ValueNormalisation
import Lax149335Proofs.Appendix.BasicFacts
import Mathlib.Tactic.Set

/-!
# Factorising the atomic functions into lifts and drops

This file provides the equational content of the base cases of the lift-drop factorisation
(Lemma 7.4): every atomic function of Figure 1, apart from the group prefix multiplication,
is provably equal to a composition of prime lift and prime drop functions of Table 1.

The classes of lifts and drops themselves are defined in `Lax149335Proofs.GeneralCompleteness.Statements`,
which imports this file; here only the provable equalities are established, with the
right-hand sides written out explicitly.

The two constructors `cons` and `snoc` are co-pairings of the empty list and of
`prepend`/`append`, all of which are drops; the two destructors `uncons` and `unsnoc` are
obtained from the lift `shift` by decorating the list with units; and the two bracket shifts
`shiftL`, `shiftR` are obtained from `shift` and the appending of one element.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Retractions of the co-projections -/

/-- The right co-projection has a left inverse, obtained from a default value. -/
theorem inr_retract (A B : Ty) :
    (inr A B ⨟ either (anyTerm A B) (Term.id B)) ≡ₜ Term.id B :=
  inr_either _ _

/-- A left inverse of `prepend`: take the list apart and use a default value on the empty
list. -/
def unprepend (A : Ty) : Term A⋆ (A ⊗ A⋆) :=
  uncons A ⨟ either (defaultValue (A ⊗ A⋆)) (Term.id (A ⊗ A⋆))

/-- `unprepend` is a left inverse of `prepend`. -/
theorem prepend_unprepend (A : Ty) : (prepend A ⨟ unprepend A) ≡ₜ Term.id (A ⊗ A⋆) := by
  calc ((inr Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟
        (uncons A ⨟ either (defaultValue (A ⊗ A⋆)) (Term.id (A ⊗ A⋆))))
      ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ ((cons A ⨟ uncons A) ⨟
          either (defaultValue (A ⊗ A⋆)) (Term.id (A ⊗ A⋆)))) := by
        calc ((inr Ty.unit (A ⊗ A⋆) ⨟ cons A) ⨟
              (uncons A ⨟ either (defaultValue (A ⊗ A⋆)) (Term.id (A ⊗ A⋆))))
            ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ (cons A ⨟
                (uncons A ⨟ either (defaultValue (A ⊗ A⋆)) (Term.id (A ⊗ A⋆))))) :=
              PEq.comp_assoc _ _ _
          _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ (Term.id (Ty.unit ⊕' (A ⊗ A⋆)) ⨟
          either (defaultValue (A ⊗ A⋆)) (Term.id (A ⊗ A⋆)))) :=
        PEq.compR _ (PEq.compL _ (PEq.cons_uncons A))
    _ ≡ₜ (inr Ty.unit (A ⊗ A⋆) ⨟ either (defaultValue (A ⊗ A⋆)) (Term.id (A ⊗ A⋆))) :=
        PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id (A ⊗ A⋆) := inr_either _ _

/-- `prepend` is provably injective: it is `Right` followed by the isomorphism `cons`. -/
theorem prepend_injective (A : Ty) : ProvablyInjective (prepend A) :=
  ⟨unprepend A, prepend_unprepend A⟩

/-! ### The empty list, `cons` and `snoc` -/

/-- The empty list is a drop: it is the empty case of `unshift`, with the units erased. -/
theorem nilT_unshift (A : Ty) :
    nilT A ≡ₜ ((inl Ty.unit (A ⊗ ((Ty.unit ⊗ A)⋆ ⊗ Ty.unit)) ⨟ unshift A Ty.unit) ⨟
      listF (fst A Ty.unit)) := by
  have h : (inl Ty.unit (A ⊗ ((Ty.unit ⊗ A)⋆ ⊗ Ty.unit)) ⨟ unshift A Ty.unit) ≡ₜ
      nilT (A ⊗ Ty.unit) := by
    calc (inl Ty.unit (A ⊗ ((Ty.unit ⊗ A)⋆ ⊗ Ty.unit)) ⨟
          (sumF (Term.id Ty.unit)
              (prodF (Term.id A) (shiftR Ty.unit A) ⨟
                assocL A Ty.unit ((A ⊗ Ty.unit)⋆)) ⨟
            cons (A ⊗ Ty.unit)))
        ≡ₜ ((inl Ty.unit (A ⊗ ((Ty.unit ⊗ A)⋆ ⊗ Ty.unit)) ⨟
              sumF (Term.id Ty.unit)
                (prodF (Term.id A) (shiftR Ty.unit A) ⨟
                  assocL A Ty.unit ((A ⊗ Ty.unit)⋆))) ⨟
            cons (A ⊗ Ty.unit)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((Term.id Ty.unit ⨟ inl Ty.unit ((A ⊗ Ty.unit) ⊗ (A ⊗ Ty.unit)⋆)) ⨟
            cons (A ⊗ Ty.unit)) := PEq.compL _ (PEq.nat_inl _ _)
      _ ≡ₜ (inl Ty.unit ((A ⊗ Ty.unit) ⊗ (A ⊗ Ty.unit)⋆) ⨟ cons (A ⊗ Ty.unit)) :=
          PEq.compL _ (PEq.id_comp _)
  calc nilT A ≡ₜ (nilT (A ⊗ Ty.unit) ⨟ listF (fst A Ty.unit)) :=
        PEq.symm (nilT_natural (fst A Ty.unit))
    _ ≡ₜ _ := PEq.compL _ (PEq.symm h)

/-- `cons` is the co-pairing of the empty list and of `prepend`. -/
theorem cons_either (A : Ty) : cons A ≡ₜ either (nilT A) (prepend A) :=
  either_unique (cons A)

/-- `snoc` is the co-pairing of the empty list and of `append`. -/
theorem snoc_either (A : Ty) : snoc A ≡ₜ either (nilT A) (append A) := by
  refine PEq.trans (either_unique (snoc A)) (either_congr ?_ (PEq.refl _))
  exact PEq.inl_snoc_cons A

/-! ### Erasing units -/

/-- Erasing the unit components of a list bracketed as `(1 × A)* × 1`. -/
def eraseL (A : Ty) : Term ((Ty.unit ⊗ A)⋆ ⊗ Ty.unit) A⋆ :=
  fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)

/-- Decorating a list with units on the left and erasing them again is the identity. -/
theorem packL_eraseL (A : Ty) : (packL A ⨟ eraseL A) ≡ₜ Term.id A⋆ := by
  calc ((listF (unitL A) ⨟ unitR ((Ty.unit ⊗ A)⋆)) ⨟
        (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))
      ≡ₜ (listF (unitL A) ⨟ (unitR ((Ty.unit ⊗ A)⋆) ⨟
          (fst ((Ty.unit ⊗ A)⋆) Ty.unit ⨟ listF (snd Ty.unit A)))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF (unitL A) ⨟ ((unitR ((Ty.unit ⊗ A)⋆) ⨟ fst ((Ty.unit ⊗ A)⋆) Ty.unit) ⨟
          listF (snd Ty.unit A))) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (listF (unitL A) ⨟ (Term.id ((Ty.unit ⊗ A)⋆) ⨟ listF (snd Ty.unit A))) :=
        PEq.compR _ (PEq.compL _ (PEq.unitR_fst _))
    _ ≡ₜ (listF (unitL A) ⨟ listF (snd Ty.unit A)) := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ listF (unitL A ⨟ snd Ty.unit A) := PEq.list_comp _ _
    _ ≡ₜ listF (Term.id A) := PEq.congr_listF (PEq.unitL_snd A)
    _ ≡ₜ Term.id A⋆ := PEq.list_id A

/-- Decorating the second component of a pair with units, shifting the brackets and erasing
the units again is the second projection. -/
theorem shiftL_eraseL (A : Ty) :
    (prodF (Term.id Ty.unit) (listF (unitR A)) ⨟ (shiftL Ty.unit A ⨟ eraseL A)) ≡ₜ
      snd Ty.unit A⋆ := by
  have h1 : prodF (Term.id Ty.unit) (listF (unitR A)) ≡ₜ (snd Ty.unit A⋆ ⨟ packR A) := by
    calc prodF (Term.id Ty.unit) (listF (unitR A))
        ≡ₜ (prodF (Term.id Ty.unit) (listF (unitR A)) ⨟ Term.id (Ty.unit ⊗ (A ⊗ Ty.unit)⋆)) :=
          PEq.symm (PEq.comp_id _)
      _ ≡ₜ (prodF (Term.id Ty.unit) (listF (unitR A)) ⨟
            (snd Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ unitL ((A ⊗ Ty.unit)⋆))) :=
          PEq.compR _ (PEq.symm (PEq.snd_unitL _))
      _ ≡ₜ ((prodF (Term.id Ty.unit) (listF (unitR A)) ⨟ snd Ty.unit ((A ⊗ Ty.unit)⋆)) ⨟
            unitL ((A ⊗ Ty.unit)⋆)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((snd Ty.unit A⋆ ⨟ listF (unitR A)) ⨟ unitL ((A ⊗ Ty.unit)⋆)) :=
          PEq.compL _ (PEq.nat_snd _ _)
      _ ≡ₜ (snd Ty.unit A⋆ ⨟ (listF (unitR A) ⨟ unitL ((A ⊗ Ty.unit)⋆))) :=
          PEq.comp_assoc _ _ _
  calc (prodF (Term.id Ty.unit) (listF (unitR A)) ⨟ (shiftL Ty.unit A ⨟ eraseL A))
      ≡ₜ ((snd Ty.unit A⋆ ⨟ packR A) ⨟ (shiftL Ty.unit A ⨟ eraseL A)) := PEq.compL _ h1
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ (packR A ⨟ (shiftL Ty.unit A ⨟ eraseL A))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ ((packR A ⨟ shiftL Ty.unit A) ⨟ eraseL A)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ (packL A ⨟ eraseL A)) := PEq.compR _ (PEq.compL _ (shift_ones A))
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ Term.id A⋆) := PEq.compR _ (packL_eraseL A)
    _ ≡ₜ snd Ty.unit A⋆ := PEq.comp_id _

/-! ### Two consequences of the monoid axioms -/

/-- The second projection out of `1 × A*` concatenates with the empty list. -/
theorem snd_nil_binconcat (A : Ty) :
    snd Ty.unit A⋆ ≡ₜ (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A) := by
  calc snd Ty.unit A⋆
      ≡ₜ (snd Ty.unit A⋆ ⨟ Term.id A⋆) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (snd Ty.unit A⋆ ⨟ ((unitL A⋆ ⨟ prodF (nilT A) (Term.id A⋆)) ⨟ binconcat A)) :=
        PEq.compR _ (PEq.symm (PEq.binconcat_unitL A))
    _ ≡ₜ ((snd Ty.unit A⋆ ⨟ (unitL A⋆ ⨟ prodF (nilT A) (Term.id A⋆))) ⨟ binconcat A) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((snd Ty.unit A⋆ ⨟ unitL A⋆) ⨟ prodF (nilT A) (Term.id A⋆)) ⨟ binconcat A) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((Term.id (Ty.unit ⊗ A⋆) ⨟ prodF (nilT A) (Term.id A⋆)) ⨟ binconcat A) :=
        PEq.compL _ (PEq.compL _ (PEq.snd_unitL A⋆))
    _ ≡ₜ (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A) := PEq.compL _ (PEq.id_comp _)

/-- A singleton list, concatenated with the empty list on the right. -/
theorem unitR_pure_nil (A : Ty) :
    ((unitR A ⨟ prodF (pureT A) (nilT A)) ⨟ binconcat A) ≡ₜ pureT A := by
  have hsplit : prodF (pureT A) (nilT A) ≡ₜ
      (prodF (pureT A) (Term.id Ty.unit) ⨟ prodF (Term.id A⋆) (nilT A)) := by
    calc prodF (pureT A) (nilT A)
        ≡ₜ prodF (pureT A ⨟ Term.id A⋆) (Term.id Ty.unit ⨟ nilT A) :=
          PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.symm (PEq.id_comp _))
      _ ≡ₜ _ := PEq.symm (PEq.prod_comp _ _ _ _)
  calc ((unitR A ⨟ prodF (pureT A) (nilT A)) ⨟ binconcat A)
      ≡ₜ ((unitR A ⨟ (prodF (pureT A) (Term.id Ty.unit) ⨟ prodF (Term.id A⋆) (nilT A))) ⨟
          binconcat A) := PEq.compL _ (PEq.compR _ hsplit)
    _ ≡ₜ (((unitR A ⨟ prodF (pureT A) (Term.id Ty.unit)) ⨟ prodF (Term.id A⋆) (nilT A)) ⨟
          binconcat A) := PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (((pureT A ⨟ unitR A⋆) ⨟ prodF (Term.id A⋆) (nilT A)) ⨟ binconcat A) :=
        PEq.compL _ (PEq.compL _ (PEq.symm (PEq.nat_unitR _)))
    _ ≡ₜ ((pureT A ⨟ (unitR A⋆ ⨟ prodF (Term.id A⋆) (nilT A))) ⨟ binconcat A) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (pureT A ⨟ ((unitR A⋆ ⨟ prodF (Term.id A⋆) (nilT A)) ⨟ binconcat A)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (pureT A ⨟ Term.id A⋆) := PEq.compR _ (PEq.binconcat_unitR A)
    _ ≡ₜ pureT A := PEq.comp_id _

/-! ### `uncons` -/

/-- The key computation for the factorisation of `uncons`: decorating a pair with units,
shifting the brackets and erasing the units again is the identity. -/
theorem uncons_core (A : Ty) :
    ((prodF (unitR A) (listF (unitR A)) ⨟
        (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) ⨟
      prodF (Term.id A) (eraseL A)) ≡ₜ Term.id (A ⊗ A⋆) := by
  -- the two halves of the composite are merged into one
  have hmerge : ((prodF (unitR A) (listF (unitR A)) ⨟
        (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) ⨟
      prodF (Term.id A) (eraseL A)) ≡ₜ
      (prodF (unitR A) (listF (unitR A)) ⨟
        (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟
          prodF (Term.id A) (shiftL Ty.unit A ⨟ eraseL A))) := by
    calc ((prodF (unitR A) (listF (unitR A)) ⨟
          (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) ⨟
        prodF (Term.id A) (eraseL A))
        ≡ₜ (prodF (unitR A) (listF (unitR A)) ⨟
            ((assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A)) ⨟
              prodF (Term.id A) (eraseL A))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (unitR A) (listF (unitR A)) ⨟
            (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟
              (prodF (Term.id A) (shiftL Ty.unit A) ⨟ prodF (Term.id A) (eraseL A)))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (unitR A) (listF (unitR A)) ⨟
            (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟
              prodF (Term.id A ⨟ Term.id A) (shiftL Ty.unit A ⨟ eraseL A))) :=
          PEq.compR _ (PEq.compR _ (PEq.prod_comp _ _ _ _))
      _ ≡ₜ _ := PEq.compR _ (PEq.compR _
            (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _)))
  -- the associator is fed with the undecorated list
  have hstep : (prodF (unitR A) (listF (unitR A)) ⨟ assocR A Ty.unit ((A ⊗ Ty.unit)⋆)) ≡ₜ
      ((prodF (unitR A) (Term.id A⋆) ⨟ assocR A Ty.unit A⋆) ⨟
        prodF (Term.id A) (prodF (Term.id Ty.unit) (listF (unitR A)))) := by
    have h0 : prodF (unitR A) (listF (unitR A)) ≡ₜ
        (prodF (unitR A) (Term.id A⋆) ⨟
          prodF (prodF (Term.id A) (Term.id Ty.unit)) (listF (unitR A))) := by
      calc prodF (unitR A) (listF (unitR A))
          ≡ₜ prodF (unitR A ⨟ Term.id (A ⊗ Ty.unit)) (Term.id A⋆ ⨟ listF (unitR A)) :=
            PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.symm (PEq.id_comp _))
        _ ≡ₜ prodF (unitR A ⨟ prodF (Term.id A) (Term.id Ty.unit))
              (Term.id A⋆ ⨟ listF (unitR A)) :=
            PEq.congr_prodF (PEq.compR _ (PEq.symm (PEq.prod_id _ _))) (PEq.refl _)
        _ ≡ₜ _ := PEq.symm (PEq.prod_comp _ _ _ _)
    calc (prodF (unitR A) (listF (unitR A)) ⨟ assocR A Ty.unit ((A ⊗ Ty.unit)⋆))
        ≡ₜ ((prodF (unitR A) (Term.id A⋆) ⨟
            prodF (prodF (Term.id A) (Term.id Ty.unit)) (listF (unitR A))) ⨟
            assocR A Ty.unit ((A ⊗ Ty.unit)⋆)) := PEq.compL _ h0
      _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟
            (prodF (prodF (Term.id A) (Term.id Ty.unit)) (listF (unitR A)) ⨟
              assocR A Ty.unit ((A ⊗ Ty.unit)⋆))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟
            (assocR A Ty.unit A⋆ ⨟
              prodF (Term.id A) (prodF (Term.id Ty.unit) (listF (unitR A))))) :=
          PEq.compR _ (PEq.nat_assocR _ _ _)
      _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
  -- it suffices to prove the equality after the provably injective term `prepend`
  refine ((cancel _ (Term.id (A ⊗ A⋆))).1 _ (prepend A) (prepend_injective A)).2 ?_
  refine PEq.trans ?_ (PEq.symm (PEq.id_comp (prepend A)))
  calc (((prodF (unitR A) (listF (unitR A)) ⨟
          (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) ⨟
        prodF (Term.id A) (eraseL A)) ⨟ prepend A)
      ≡ₜ ((prodF (unitR A) (listF (unitR A)) ⨟
          (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟
            prodF (Term.id A) (shiftL Ty.unit A ⨟ eraseL A))) ⨟ prepend A) :=
        PEq.compL _ hmerge
    _ ≡ₜ (prodF (unitR A) (listF (unitR A)) ⨟
          ((assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟
            prodF (Term.id A) (shiftL Ty.unit A ⨟ eraseL A)) ⨟ prepend A)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (unitR A) (listF (unitR A)) ⨟
          (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟
            (prodF (Term.id A) (shiftL Ty.unit A ⨟ eraseL A) ⨟ prepend A))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (unitR A) (listF (unitR A)) ⨟
          (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟
            (prodF (pureT A) (shiftL Ty.unit A ⨟ eraseL A) ⨟ binconcat A))) := by
        refine PEq.compR _ (PEq.compR _ ?_)
        calc (prodF (Term.id A) (shiftL Ty.unit A ⨟ eraseL A) ⨟ prepend A)
            ≡ₜ (prodF (Term.id A) (shiftL Ty.unit A ⨟ eraseL A) ⨟
                (prodF (pureT A) (Term.id A⋆) ⨟ binconcat A)) :=
              PEq.compR _ (PEq.prepend_def A)
          _ ≡ₜ ((prodF (Term.id A) (shiftL Ty.unit A ⨟ eraseL A) ⨟
                prodF (pureT A) (Term.id A⋆)) ⨟ binconcat A) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (prodF (Term.id A ⨟ pureT A) ((shiftL Ty.unit A ⨟ eraseL A) ⨟ Term.id A⋆) ⨟
                binconcat A) := PEq.compL _ (PEq.prod_comp _ _ _ _)
          _ ≡ₜ _ := PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (PEq.comp_id _))
    _ ≡ₜ ((prodF (unitR A) (listF (unitR A)) ⨟ assocR A Ty.unit ((A ⊗ Ty.unit)⋆)) ⨟
          (prodF (pureT A) (shiftL Ty.unit A ⨟ eraseL A) ⨟ binconcat A)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((prodF (unitR A) (Term.id A⋆) ⨟ assocR A Ty.unit A⋆) ⨟
            prodF (Term.id A) (prodF (Term.id Ty.unit) (listF (unitR A)))) ⨟
          (prodF (pureT A) (shiftL Ty.unit A ⨟ eraseL A) ⨟ binconcat A)) :=
        PEq.compL _ hstep
    _ ≡ₜ ((prodF (unitR A) (Term.id A⋆) ⨟ assocR A Ty.unit A⋆) ⨟
          (prodF (Term.id A) (prodF (Term.id Ty.unit) (listF (unitR A))) ⨟
            (prodF (pureT A) (shiftL Ty.unit A ⨟ eraseL A) ⨟ binconcat A))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ ((prodF (unitR A) (Term.id A⋆) ⨟ assocR A Ty.unit A⋆) ⨟
          (prodF (pureT A) (snd Ty.unit A⋆) ⨟ binconcat A)) := by
        refine PEq.compR _ ?_
        calc (prodF (Term.id A) (prodF (Term.id Ty.unit) (listF (unitR A))) ⨟
              (prodF (pureT A) (shiftL Ty.unit A ⨟ eraseL A) ⨟ binconcat A))
            ≡ₜ ((prodF (Term.id A) (prodF (Term.id Ty.unit) (listF (unitR A))) ⨟
                prodF (pureT A) (shiftL Ty.unit A ⨟ eraseL A)) ⨟ binconcat A) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (prodF (Term.id A ⨟ pureT A)
                (prodF (Term.id Ty.unit) (listF (unitR A)) ⨟
                  (shiftL Ty.unit A ⨟ eraseL A)) ⨟ binconcat A) :=
              PEq.compL _ (PEq.prod_comp _ _ _ _)
          _ ≡ₜ (prodF (pureT A) (snd Ty.unit A⋆) ⨟ binconcat A) :=
              PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (shiftL_eraseL A))
    _ ≡ₜ ((prodF (unitR A) (Term.id A⋆) ⨟ assocR A Ty.unit A⋆) ⨟
          ((prodF (pureT A) (prodF (nilT A) (Term.id A⋆)) ⨟
            prodF (Term.id A⋆) (binconcat A)) ⨟ binconcat A)) := by
        refine PEq.compR _ (PEq.compL _ ?_)
        calc prodF (pureT A) (snd Ty.unit A⋆)
            ≡ₜ prodF (pureT A) (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A) :=
              PEq.congr_prodF (PEq.refl _) (snd_nil_binconcat A)
          _ ≡ₜ prodF (pureT A ⨟ Term.id A⋆)
                (prodF (nilT A) (Term.id A⋆) ⨟ binconcat A) :=
              PEq.congr_prodF (PEq.symm (PEq.comp_id _)) (PEq.refl _)
          _ ≡ₜ _ := PEq.symm (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟
          ((assocR A Ty.unit A⋆ ⨟ prodF (pureT A) (prodF (nilT A) (Term.id A⋆))) ⨟
            (prodF (Term.id A⋆) (binconcat A) ⨟ binconcat A))) := by
        calc ((prodF (unitR A) (Term.id A⋆) ⨟ assocR A Ty.unit A⋆) ⨟
              ((prodF (pureT A) (prodF (nilT A) (Term.id A⋆)) ⨟
                prodF (Term.id A⋆) (binconcat A)) ⨟ binconcat A))
            ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟ (assocR A Ty.unit A⋆ ⨟
                ((prodF (pureT A) (prodF (nilT A) (Term.id A⋆)) ⨟
                  prodF (Term.id A⋆) (binconcat A)) ⨟ binconcat A))) :=
              PEq.comp_assoc _ _ _
          _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟ ((assocR A Ty.unit A⋆ ⨟
                (prodF (pureT A) (prodF (nilT A) (Term.id A⋆)) ⨟
                  prodF (Term.id A⋆) (binconcat A))) ⨟ binconcat A)) :=
              PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟
                (((assocR A Ty.unit A⋆ ⨟ prodF (pureT A) (prodF (nilT A) (Term.id A⋆))) ⨟
                  prodF (Term.id A⋆) (binconcat A)) ⨟ binconcat A)) :=
              PEq.compR _ (PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _)))
          _ ≡ₜ _ := PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟
          ((prodF (prodF (pureT A) (nilT A)) (Term.id A⋆) ⨟ assocR A⋆ A⋆ A⋆) ⨟
            (prodF (Term.id A⋆) (binconcat A) ⨟ binconcat A))) :=
        PEq.compR _ (PEq.compL _ (PEq.symm (PEq.nat_assocR _ _ _)))
    _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟
          (prodF (prodF (pureT A) (nilT A)) (Term.id A⋆) ⨟
            ((assocR A⋆ A⋆ A⋆ ⨟ prodF (Term.id A⋆) (binconcat A)) ⨟ binconcat A))) := by
        refine PEq.compR _ ?_
        calc ((prodF (prodF (pureT A) (nilT A)) (Term.id A⋆) ⨟ assocR A⋆ A⋆ A⋆) ⨟
              (prodF (Term.id A⋆) (binconcat A) ⨟ binconcat A))
            ≡ₜ (prodF (prodF (pureT A) (nilT A)) (Term.id A⋆) ⨟ (assocR A⋆ A⋆ A⋆ ⨟
                (prodF (Term.id A⋆) (binconcat A) ⨟ binconcat A))) := PEq.comp_assoc _ _ _
          _ ≡ₜ _ := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (prodF (unitR A) (Term.id A⋆) ⨟
          (prodF (prodF (pureT A) (nilT A)) (Term.id A⋆) ⨟
            (prodF (binconcat A) (Term.id A⋆) ⨟ binconcat A))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm (PEq.binconcat_assoc A)))
    _ ≡ₜ (((prodF (unitR A) (Term.id A⋆) ⨟ prodF (prodF (pureT A) (nilT A)) (Term.id A⋆)) ⨟
            prodF (binconcat A) (Term.id A⋆)) ⨟ binconcat A) := by
        calc (prodF (unitR A) (Term.id A⋆) ⨟
              (prodF (prodF (pureT A) (nilT A)) (Term.id A⋆) ⨟
                (prodF (binconcat A) (Term.id A⋆) ⨟ binconcat A)))
            ≡ₜ ((prodF (unitR A) (Term.id A⋆) ⨟
                prodF (prodF (pureT A) (nilT A)) (Term.id A⋆)) ⨟
                (prodF (binconcat A) (Term.id A⋆) ⨟ binconcat A)) :=
              PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (((unitR A ⨟ prodF (pureT A) (nilT A)) ⨟ binconcat A))
          ((Term.id A⋆ ⨟ Term.id A⋆) ⨟ Term.id A⋆) ⨟ binconcat A) := by
        refine PEq.compL _ ?_
        calc ((prodF (unitR A) (Term.id A⋆) ⨟ prodF (prodF (pureT A) (nilT A)) (Term.id A⋆)) ⨟
              prodF (binconcat A) (Term.id A⋆))
            ≡ₜ (prodF (unitR A ⨟ prodF (pureT A) (nilT A)) (Term.id A⋆ ⨟ Term.id A⋆) ⨟
                prodF (binconcat A) (Term.id A⋆)) := PEq.compL _ (PEq.prod_comp _ _ _ _)
          _ ≡ₜ _ := PEq.prod_comp _ _ _ _
    _ ≡ₜ (prodF (pureT A) (Term.id A⋆) ⨟ binconcat A) :=
        PEq.compL _ (PEq.congr_prodF (unitR_pure_nil A)
          ((PEq.compL _ (PEq.id_comp _)).trans (PEq.id_comp _)))
    _ ≡ₜ prepend A := PEq.symm (PEq.prepend_def A)

/-- **`uncons` factorises as a lift followed by a drop**: decorate the list with units, apply
the lift `shift`, and erase the units again. -/
theorem uncons_factor (A : Ty) :
    uncons A ≡ₜ ((listF (unitR A) ⨟ shift A Ty.unit) ⨟
      sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))) := by
  have hS : (cons (A ⊗ Ty.unit) ⨟ shift A Ty.unit) ≡ₜ
      sumF (Term.id Ty.unit)
        (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A)) := by
    calc (cons (A ⊗ Ty.unit) ⨟ (uncons (A ⊗ Ty.unit) ⨟
          sumF (Term.id Ty.unit)
            (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))))
        ≡ₜ ((cons (A ⊗ Ty.unit) ⨟ uncons (A ⊗ Ty.unit)) ⨟
            sumF (Term.id Ty.unit)
              (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id (Ty.unit ⊕' ((A ⊗ Ty.unit) ⊗ (A ⊗ Ty.unit)⋆)) ⨟
            sumF (Term.id Ty.unit)
              (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) :=
          PEq.compL _ (PEq.cons_uncons _)
      _ ≡ₜ _ := PEq.id_comp _
  have hcons : (cons A ⨟ ((listF (unitR A) ⨟ shift A Ty.unit) ⨟
      sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A)))) ≡ₜ
      Term.id (Ty.unit ⊕' (A ⊗ A⋆)) := by
    calc (cons A ⨟ ((listF (unitR A) ⨟ shift A Ty.unit) ⨟
          sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))))
        ≡ₜ ((cons A ⨟ (listF (unitR A) ⨟ shift A Ty.unit)) ⨟
            sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (((cons A ⨟ listF (unitR A)) ⨟ shift A Ty.unit) ⨟
            sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))) :=
          PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (((sumF (Term.id Ty.unit) (prodF (unitR A) (listF (unitR A))) ⨟
            cons (A ⊗ Ty.unit)) ⨟ shift A Ty.unit) ⨟
            sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))) :=
          PEq.compL _ (PEq.compL _ (PEq.symm (PEq.nat_cons (unitR A))))
      _ ≡ₜ ((sumF (Term.id Ty.unit) (prodF (unitR A) (listF (unitR A))) ⨟
            (cons (A ⊗ Ty.unit) ⨟ shift A Ty.unit)) ⨟
            sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))) :=
          PEq.compL _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((sumF (Term.id Ty.unit) (prodF (unitR A) (listF (unitR A))) ⨟
            sumF (Term.id Ty.unit)
              (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) ⨟
            sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))) :=
          PEq.compL _ (PEq.compR _ hS)
      _ ≡ₜ (sumF (Term.id Ty.unit ⨟ Term.id Ty.unit)
            (prodF (unitR A) (listF (unitR A)) ⨟
              (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) ⨟
            sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))) :=
          PEq.compL _ (PEq.sum_comp _ _ _ _)
      _ ≡ₜ sumF ((Term.id Ty.unit ⨟ Term.id Ty.unit) ⨟ Term.id Ty.unit)
            ((prodF (unitR A) (listF (unitR A)) ⨟
              (assocR A Ty.unit ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id A) (shiftL Ty.unit A))) ⨟
              prodF (Term.id A) (eraseL A)) := PEq.sum_comp _ _ _ _
      _ ≡ₜ sumF (Term.id Ty.unit) (Term.id (A ⊗ A⋆)) :=
          PEq.congr_sumF (PEq.unit_unique _ _) (uncons_core A)
      _ ≡ₜ Term.id (Ty.unit ⊕' (A ⊗ A⋆)) := PEq.sum_id _ _
  calc uncons A ≡ₜ (uncons A ⨟ Term.id (Ty.unit ⊕' (A ⊗ A⋆))) := PEq.symm (PEq.comp_id _)
    _ ≡ₜ (uncons A ⨟ (cons A ⨟ ((listF (unitR A) ⨟ shift A Ty.unit) ⨟
          sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A))))) :=
        PEq.compR _ (PEq.symm hcons)
    _ ≡ₜ ((uncons A ⨟ cons A) ⨟ ((listF (unitR A) ⨟ shift A Ty.unit) ⨟
          sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A)))) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id A⋆ ⨟ ((listF (unitR A) ⨟ shift A Ty.unit) ⨟
          sumF (Term.id Ty.unit) (prodF (Term.id A) (eraseL A)))) :=
        PEq.compL _ (PEq.uncons_cons A)
    _ ≡ₜ _ := PEq.id_comp _

/-! ### `unsnoc` -/

/-- A homomorphism built from a singleton is a list map. -/
theorem homT_comp_pureT {A B : Ty} (f : Term A B) : homT (f ⨟ pureT B) ≡ₜ listF f := by
  calc (listF (f ⨟ pureT B) ⨟ concat B)
      ≡ₜ ((listF f ⨟ listF (pureT B)) ⨟ concat B) :=
        PEq.compL _ (PEq.symm (PEq.list_comp _ _))
    _ ≡ₜ (listF f ⨟ (listF (pureT B) ⨟ concat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (listF f ⨟ Term.id B⋆) := PEq.compR _ (PEq.listF_pure_concat B)
    _ ≡ₜ listF f := PEq.comp_id _

/-- **Axiom 15 read through the letters-and-separators homomorphism.**  Shifting the brackets
of a list of pairs whose second components are units does not change the underlying list,
with the extra element moved from the right end to the left end. -/
theorem shiftR_pure_snd (A : Ty) :
    (shiftR A Ty.unit ⨟ (pureT A ⊙ listF (snd Ty.unit A))) ≡ₜ
      (listF (fst A Ty.unit) ⊙ pureT A) := by
  set d : Term (A ⊕' Ty.unit) A⋆ := either (pureT A) (nilT A) with hd
  have hl : (inl A Ty.unit ⨟ d) ≡ₜ pureT A := inl_either _ _
  have hr : (inr A Ty.unit ⨟ d) ≡ₜ nilT A := inr_either _ _
  have hR : (cmR A Ty.unit ⨟ homT d) ≡ₜ (pureT A ⊙ listF (snd Ty.unit A)) := by
    calc (cmR A Ty.unit ⨟ homT d)
        ≡ₜ ((inl A Ty.unit ⨟ d) ⊙ homT ((inr A Ty.unit ⨟ d) ⊙ (inl A Ty.unit ⨟ d))) :=
          cmR_comp_homT d
      _ ≡ₜ (pureT A ⊙ homT (nilT A ⊙ pureT A)) :=
          fdot_congr hl (homT_congr (fdot_congr hr hl))
      _ ≡ₜ (pureT A ⊙ homT (snd Ty.unit A ⨟ pureT A)) :=
          fdot_congr (PEq.refl _) (homT_congr (fdot_nil_left _))
      _ ≡ₜ (pureT A ⊙ listF (snd Ty.unit A)) :=
          fdot_congr (PEq.refl _) (homT_comp_pureT _)
  have hL : (cmL A Ty.unit ⨟ homT d) ≡ₜ (listF (fst A Ty.unit) ⊙ pureT A) := by
    calc (cmL A Ty.unit ⨟ homT d)
        ≡ₜ (homT ((inl A Ty.unit ⨟ d) ⊙ (inr A Ty.unit ⨟ d)) ⊙ (inl A Ty.unit ⨟ d)) :=
          cmL_comp_homT d
      _ ≡ₜ (homT (pureT A ⊙ nilT A) ⊙ pureT A) :=
          fdot_congr (homT_congr (fdot_congr hl hr)) hl
      _ ≡ₜ (homT (fst A Ty.unit ⨟ pureT A) ⊙ pureT A) :=
          fdot_congr (homT_congr (fdot_nil_right _)) (PEq.refl _)
      _ ≡ₜ (listF (fst A Ty.unit) ⊙ pureT A) :=
          fdot_congr (homT_comp_pureT _) (PEq.refl _)
  calc (shiftR A Ty.unit ⨟ (pureT A ⊙ listF (snd Ty.unit A)))
      ≡ₜ (shiftR A Ty.unit ⨟ (cmR A Ty.unit ⨟ homT d)) := PEq.compR _ (PEq.symm hR)
    _ ≡ₜ ((shiftR A Ty.unit ⨟ cmR A Ty.unit) ⨟ homT d) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (cmL A Ty.unit ⨟ homT d) := PEq.compL _ (PEq.shiftR_content A Ty.unit)
    _ ≡ₜ _ := hL

/-- Prepending an element to a list decorated with units. -/
theorem snd_fdot_prepend (A : Ty) :
    (snd Ty.unit (A ⊗ (Ty.unit ⊗ A)⋆) ⨟ (pureT A ⊙ listF (snd Ty.unit A))) ≡ₜ
      (assocL Ty.unit A ((Ty.unit ⊗ A)⋆) ⨟
        (prepend (Ty.unit ⊗ A) ⨟ listF (snd Ty.unit A))) := by
  have hstep : (prodF (Term.id A) (listF (snd Ty.unit A)) ⨟ prepend A) ≡ₜ
      (pureT A ⊙ listF (snd Ty.unit A)) := by
    calc (prodF (Term.id A) (listF (snd Ty.unit A)) ⨟ prepend A)
        ≡ₜ (prodF (Term.id A) (listF (snd Ty.unit A)) ⨟
            (prodF (pureT A) (Term.id A⋆) ⨟ binconcat A)) :=
          PEq.compR _ (PEq.prepend_def A)
      _ ≡ₜ ((prodF (Term.id A) (listF (snd Ty.unit A)) ⨟ prodF (pureT A) (Term.id A⋆)) ⨟
            binconcat A) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id A ⨟ pureT A) (listF (snd Ty.unit A) ⨟ Term.id A⋆) ⨟
            binconcat A) := PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (pureT A) (listF (snd Ty.unit A)) ⨟ binconcat A) :=
          PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (PEq.comp_id _))
  calc (snd Ty.unit (A ⊗ (Ty.unit ⊗ A)⋆) ⨟ (pureT A ⊙ listF (snd Ty.unit A)))
      ≡ₜ (snd Ty.unit (A ⊗ (Ty.unit ⊗ A)⋆) ⨟
          (prodF (Term.id A) (listF (snd Ty.unit A)) ⨟ prepend A)) :=
        PEq.compR _ (PEq.symm hstep)
    _ ≡ₜ ((assocL Ty.unit A ((Ty.unit ⊗ A)⋆) ⨟
            prodF (snd Ty.unit A) (Term.id ((Ty.unit ⊗ A)⋆))) ⨟
          (prodF (Term.id A) (listF (snd Ty.unit A)) ⨟ prepend A)) :=
        PEq.compL _ (PEq.symm (Term.assocL_snd Ty.unit A ((Ty.unit ⊗ A)⋆)))
    _ ≡ₜ (assocL Ty.unit A ((Ty.unit ⊗ A)⋆) ⨟
          (prodF (snd Ty.unit A) (Term.id ((Ty.unit ⊗ A)⋆)) ⨟
            (prodF (Term.id A) (listF (snd Ty.unit A)) ⨟ prepend A))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL Ty.unit A ((Ty.unit ⊗ A)⋆) ⨟
          ((prodF (snd Ty.unit A) (Term.id ((Ty.unit ⊗ A)⋆)) ⨟
            prodF (Term.id A) (listF (snd Ty.unit A))) ⨟ prepend A)) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (assocL Ty.unit A ((Ty.unit ⊗ A)⋆) ⨟
          (prodF (snd Ty.unit A ⨟ Term.id A)
            (Term.id ((Ty.unit ⊗ A)⋆) ⨟ listF (snd Ty.unit A)) ⨟ prepend A)) :=
        PEq.compR _ (PEq.compL _ (PEq.prod_comp _ _ _ _))
    _ ≡ₜ (assocL Ty.unit A ((Ty.unit ⊗ A)⋆) ⨟
          (prodF (snd Ty.unit A) (listF (snd Ty.unit A)) ⨟ prepend A)) :=
        PEq.compR _ (PEq.compL _ (PEq.congr_prodF (PEq.comp_id _) (PEq.id_comp _)))
    _ ≡ₜ _ := PEq.compR _ (prepend_natural (snd Ty.unit A))

/-- The key computation for the factorisation of `unsnoc`: the drop that erases the units
from the output of `shift`, followed by `snoc`, is the drop `unshift` with the units
erased. -/
theorem unsnoc_key (A : Ty) :
    (sumF (Term.id Ty.unit)
        (snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟ prodF (listF (fst A Ty.unit)) (Term.id A)) ⨟
      snoc A) ≡ₜ (unshift Ty.unit A ⨟ listF (snd Ty.unit A)) := by
  set h : Term (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) (A⋆ ⊗ A) :=
    snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟ prodF (listF (fst A Ty.unit)) (Term.id A) with hh
  set g : Term (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ((Ty.unit ⊗ A) ⊗ (Ty.unit ⊗ A)⋆) :=
    prodF (Term.id Ty.unit) (shiftR A Ty.unit) ⨟ assocL Ty.unit A ((Ty.unit ⊗ A)⋆) with hg
  refine either_ext _ _ ?_ ?_
  · -- the empty list
    have hLeft : (inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
        (sumF (Term.id Ty.unit) h ⨟ snoc A)) ≡ₜ nilT A := by
      calc (inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ (sumF (Term.id Ty.unit) h ⨟ snoc A))
          ≡ₜ ((inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ sumF (Term.id Ty.unit) h) ⨟
              snoc A) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((Term.id Ty.unit ⨟ inl Ty.unit (A⋆ ⊗ A)) ⨟ snoc A) :=
            PEq.compL _ (PEq.nat_inl _ _)
        _ ≡ₜ (inl Ty.unit (A⋆ ⊗ A) ⨟ snoc A) := PEq.compL _ (PEq.id_comp _)
        _ ≡ₜ nilT A := PEq.inl_snoc_cons A
    have hRight : (inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
        (unshift Ty.unit A ⨟ listF (snd Ty.unit A))) ≡ₜ nilT A := by
      have hnil : (inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ unshift Ty.unit A) ≡ₜ
          nilT (Ty.unit ⊗ A) := by
        calc (inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
              (sumF (Term.id Ty.unit) g ⨟ cons (Ty.unit ⊗ A)))
            ≡ₜ ((inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ sumF (Term.id Ty.unit) g) ⨟
                cons (Ty.unit ⊗ A)) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((Term.id Ty.unit ⨟ inl Ty.unit ((Ty.unit ⊗ A) ⊗ (Ty.unit ⊗ A)⋆)) ⨟
                cons (Ty.unit ⊗ A)) := PEq.compL _ (PEq.nat_inl _ _)
          _ ≡ₜ (inl Ty.unit ((Ty.unit ⊗ A) ⊗ (Ty.unit ⊗ A)⋆) ⨟ cons (Ty.unit ⊗ A)) :=
              PEq.compL _ (PEq.id_comp _)
      calc (inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
            (unshift Ty.unit A ⨟ listF (snd Ty.unit A)))
          ≡ₜ ((inl Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ unshift Ty.unit A) ⨟
              listF (snd Ty.unit A)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (nilT (Ty.unit ⊗ A) ⨟ listF (snd Ty.unit A)) := PEq.compL _ hnil
        _ ≡ₜ nilT A := nilT_natural _
    exact hLeft.trans (PEq.symm hRight)
  · -- a non-empty list
    have hLeft : (inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
        (sumF (Term.id Ty.unit) h ⨟ snoc A)) ≡ₜ (h ⨟ append A) := by
      calc (inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ (sumF (Term.id Ty.unit) h ⨟ snoc A))
          ≡ₜ ((inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ sumF (Term.id Ty.unit) h) ⨟
              snoc A) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((h ⨟ inr Ty.unit (A⋆ ⊗ A)) ⨟ snoc A) := PEq.compL _ (PEq.nat_inr _ _)
        _ ≡ₜ (h ⨟ (inr Ty.unit (A⋆ ⊗ A) ⨟ snoc A)) := PEq.comp_assoc _ _ _
    have hRight : (inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
        (unshift Ty.unit A ⨟ listF (snd Ty.unit A))) ≡ₜ
        ((g ⨟ prepend (Ty.unit ⊗ A)) ⨟ listF (snd Ty.unit A)) := by
      have hpre : (inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ unshift Ty.unit A) ≡ₜ
          (g ⨟ prepend (Ty.unit ⊗ A)) := by
        calc (inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
              (sumF (Term.id Ty.unit) g ⨟ cons (Ty.unit ⊗ A)))
            ≡ₜ ((inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ sumF (Term.id Ty.unit) g) ⨟
                cons (Ty.unit ⊗ A)) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((g ⨟ inr Ty.unit ((Ty.unit ⊗ A) ⊗ (Ty.unit ⊗ A)⋆)) ⨟ cons (Ty.unit ⊗ A)) :=
              PEq.compL _ (PEq.nat_inr _ _)
          _ ≡ₜ (g ⨟ (inr Ty.unit ((Ty.unit ⊗ A) ⊗ (Ty.unit ⊗ A)⋆) ⨟ cons (Ty.unit ⊗ A))) :=
              PEq.comp_assoc _ _ _
      calc (inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟
            (unshift Ty.unit A ⨟ listF (snd Ty.unit A)))
          ≡ₜ ((inr Ty.unit (Ty.unit ⊗ ((A ⊗ Ty.unit)⋆ ⊗ A)) ⨟ unshift Ty.unit A) ⨟
              listF (snd Ty.unit A)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ _ := PEq.compL _ hpre
    -- the two sides agree because of Axiom 15
    have hmain : (h ⨟ append A) ≡ₜ ((g ⨟ prepend (Ty.unit ⊗ A)) ⨟ listF (snd Ty.unit A)) := by
      have hstep : (prodF (listF (fst A Ty.unit)) (Term.id A) ⨟ append A) ≡ₜ
          (listF (fst A Ty.unit) ⊙ pureT A) := by
        calc (prodF (listF (fst A Ty.unit)) (Term.id A) ⨟ append A)
            ≡ₜ (prodF (listF (fst A Ty.unit)) (Term.id A) ⨟
                (prodF (Term.id A⋆) (pureT A) ⨟ binconcat A)) :=
              PEq.compR _ (PEq.append_def A)
          _ ≡ₜ ((prodF (listF (fst A Ty.unit)) (Term.id A) ⨟ prodF (Term.id A⋆) (pureT A)) ⨟
                binconcat A) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (prodF (listF (fst A Ty.unit) ⨟ Term.id A⋆) (Term.id A ⨟ pureT A) ⨟
                binconcat A) := PEq.compL _ (PEq.prod_comp _ _ _ _)
          _ ≡ₜ (listF (fst A Ty.unit) ⊙ pureT A) :=
              PEq.compL _ (PEq.congr_prodF (PEq.comp_id _) (PEq.id_comp _))
      calc (h ⨟ append A)
          ≡ₜ (snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟
              (prodF (listF (fst A Ty.unit)) (Term.id A) ⨟ append A)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟ (listF (fst A Ty.unit) ⊙ pureT A)) :=
            PEq.compR _ hstep
        _ ≡ₜ (snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟
              (shiftR A Ty.unit ⨟ (pureT A ⊙ listF (snd Ty.unit A)))) :=
            PEq.compR _ (PEq.symm (shiftR_pure_snd A))
        _ ≡ₜ ((snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟ shiftR A Ty.unit) ⨟
              (pureT A ⊙ listF (snd Ty.unit A))) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((prodF (Term.id Ty.unit) (shiftR A Ty.unit) ⨟
              snd Ty.unit (A ⊗ (Ty.unit ⊗ A)⋆)) ⨟ (pureT A ⊙ listF (snd Ty.unit A))) :=
            PEq.compL _ (PEq.symm (PEq.nat_snd _ _))
        _ ≡ₜ (prodF (Term.id Ty.unit) (shiftR A Ty.unit) ⨟
              (snd Ty.unit (A ⊗ (Ty.unit ⊗ A)⋆) ⨟ (pureT A ⊙ listF (snd Ty.unit A)))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (prodF (Term.id Ty.unit) (shiftR A Ty.unit) ⨟
              (assocL Ty.unit A ((Ty.unit ⊗ A)⋆) ⨟
                (prepend (Ty.unit ⊗ A) ⨟ listF (snd Ty.unit A)))) :=
            PEq.compR _ (snd_fdot_prepend A)
        _ ≡ₜ ((prodF (Term.id Ty.unit) (shiftR A Ty.unit) ⨟
              assocL Ty.unit A ((Ty.unit ⊗ A)⋆)) ⨟
              (prepend (Ty.unit ⊗ A) ⨟ listF (snd Ty.unit A))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((g ⨟ prepend (Ty.unit ⊗ A)) ⨟ listF (snd Ty.unit A)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
    exact hLeft.trans (hmain.trans (PEq.symm hRight))

/-- **`unsnoc` factorises as a lift followed by a drop**: decorate the list with units on the
left, apply the lift `shift`, and erase the units again. -/
theorem unsnoc_factor (A : Ty) :
    unsnoc A ≡ₜ ((listF (unitL A) ⨟ shift Ty.unit A) ⨟
      sumF (Term.id Ty.unit)
        (snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟
          prodF (listF (fst A Ty.unit)) (Term.id A))) := by
  set X : Term A⋆ (Ty.unit ⊕' (A⋆ ⊗ A)) :=
    (listF (unitL A) ⨟ shift Ty.unit A) ⨟
      sumF (Term.id Ty.unit)
        (snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟
          prodF (listF (fst A Ty.unit)) (Term.id A)) with hX
  have hXsnoc : (X ⨟ snoc A) ≡ₜ Term.id A⋆ := by
    calc (X ⨟ snoc A)
        ≡ₜ ((listF (unitL A) ⨟ shift Ty.unit A) ⨟
            (sumF (Term.id Ty.unit)
              (snd Ty.unit (((A ⊗ Ty.unit)⋆) ⊗ A) ⨟
                prodF (listF (fst A Ty.unit)) (Term.id A)) ⨟ snoc A)) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ ((listF (unitL A) ⨟ shift Ty.unit A) ⨟
            (unshift Ty.unit A ⨟ listF (snd Ty.unit A))) := PEq.compR _ (unsnoc_key A)
      _ ≡ₜ (listF (unitL A) ⨟ (shift Ty.unit A ⨟
            (unshift Ty.unit A ⨟ listF (snd Ty.unit A)))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (listF (unitL A) ⨟ ((shift Ty.unit A ⨟ unshift Ty.unit A) ⨟
            listF (snd Ty.unit A))) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (listF (unitL A) ⨟ (Term.id ((Ty.unit ⊗ A)⋆) ⨟ listF (snd Ty.unit A))) :=
          PEq.compR _ (PEq.compL _ (shift_unshift Ty.unit A))
      _ ≡ₜ (listF (unitL A) ⨟ listF (snd Ty.unit A)) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ listF (unitL A ⨟ snd Ty.unit A) := PEq.list_comp _ _
      _ ≡ₜ listF (Term.id A) := PEq.congr_listF (PEq.unitL_snd A)
      _ ≡ₜ Term.id A⋆ := PEq.list_id A
  calc unsnoc A ≡ₜ (Term.id A⋆ ⨟ unsnoc A) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((X ⨟ snoc A) ⨟ unsnoc A) := PEq.compL _ (PEq.symm hXsnoc)
    _ ≡ₜ (X ⨟ (snoc A ⨟ unsnoc A)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (X ⨟ Term.id (Ty.unit ⊕' (A⋆ ⊗ A))) := PEq.compR _ (PEq.snoc_unsnoc A)
    _ ≡ₜ X := PEq.comp_id _

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
