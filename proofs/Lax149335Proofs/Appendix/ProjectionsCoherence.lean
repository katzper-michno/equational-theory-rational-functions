import Lax149335Proofs.EquationalTheory.DerivedRules

/-!
# The projections coherence laws

Product associativity is axiomatised by Mac Lane's pentagon (Axiom 7) together with Mac Lane's
triangle (Axiom 8), which says that
`assocL A 1 C ⨟ (fst A 1 × id C) ≡ id A × snd 1 C`.

This file derives from these axioms the three *projections coherence laws*
```
assocL A B C ⨟ (fst A B × id C) ≡ id A × snd B C
assocL A B C ⨟ (snd A B × id C) ≡ snd A (B ⊗ C)
assocL A B C ⨟ fst (A ⊗ B) C     ≡ id A × fst B C
```
which strengthen the triangle and its "unit on the left or right" variants by replacing the
discarded unit type by an arbitrary type.  The variants of the triangle with the unit on the
left or on the right (`Lax149335Proofs.Term.triangle_left`, `Lax149335Proofs.Term.triangle_right`) are
derived first, by an argument in the spirit of Kelly's redundancy result; the coherence laws
then follow using naturality of the projections (Axiom 3).

A few consequences that are used throughout the formalisation are also recorded here: the
mirror images `Lax149335Proofs.Term.assocR_snd` of the second law and `Lax149335Proofs.Term.assocR_snd_fst`
of the first law, and the form `Lax149335Proofs.Term.unitR_assocR` of the triangle that uses the two
units `unitR` and `unitL`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

open Lax149335Proofs

variable {A B C : Ty}

/-! ### Cancelling isomorphisms and unit factors -/

/-- Cancel a post-composed term that has a right inverse. -/
private theorem cancel_right_iso {X Y Z : Ty} {u v : Term X Y} (p : Term Y Z) (q : Term Z Y)
    (hpq : (p ⨟ q) ≡ₜ Term.id Y) (h : (u ⨟ p) ≡ₜ (v ⨟ p)) : u ≡ₜ v :=
  calc u ≡ₜ (u ⨟ Term.id Y) := PEq.symm (PEq.comp_id u)
    _ ≡ₜ (u ⨟ (p ⨟ q)) := PEq.compR _ (PEq.symm hpq)
    _ ≡ₜ ((u ⨟ p) ⨟ q) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((v ⨟ p) ⨟ q) := PEq.compL _ h
    _ ≡ₜ (v ⨟ (p ⨟ q)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (v ⨟ Term.id Y) := PEq.compR _ hpq
    _ ≡ₜ v := PEq.comp_id v

/-- Cancel a pre-composed term that has a left inverse. -/
private theorem cancel_left_iso {X Y Z : Ty} {u v : Term Y Z} (p : Term X Y) (q : Term Y X)
    (hqp : (q ⨟ p) ≡ₜ Term.id Y) (h : (p ⨟ u) ≡ₜ (p ⨟ v)) : u ≡ₜ v :=
  calc u ≡ₜ (Term.id Y ⨟ u) := PEq.symm (PEq.id_comp u)
    _ ≡ₜ ((q ⨟ p) ⨟ u) := PEq.compL _ (PEq.symm hqp)
    _ ≡ₜ (q ⨟ (p ⨟ u)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (q ⨟ (p ⨟ v)) := PEq.compR _ h
    _ ≡ₜ ((q ⨟ p) ⨟ v) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id Y ⨟ v) := PEq.compL _ hqp
    _ ≡ₜ v := PEq.id_comp v

/-- A unit factor on the right may be cancelled: this uses that `unitR` is a natural
isomorphism. -/
private theorem cancel_prodF_unitR {X Y : Ty} {u v : Term X Y}
    (h : prodF u (Term.id Ty.unit) ≡ₜ prodF v (Term.id Ty.unit)) : u ≡ₜ v := by
  have key : ∀ w : Term X Y,
      ((unitR X ⨟ prodF w (Term.id Ty.unit)) ⨟ fst Y Ty.unit) ≡ₜ w := by
    intro w
    calc ((unitR X ⨟ prodF w (Term.id Ty.unit)) ⨟ fst Y Ty.unit)
        ≡ₜ ((w ⨟ unitR Y) ⨟ fst Y Ty.unit) := PEq.compL _ (PEq.symm (PEq.nat_unitR w))
      _ ≡ₜ (w ⨟ (unitR Y ⨟ fst Y Ty.unit)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (w ⨟ Term.id Y) := PEq.compR _ (PEq.unitR_fst Y)
      _ ≡ₜ w := PEq.comp_id w
  exact (PEq.symm (key u)).trans
    ((PEq.compL _ (PEq.compR _ h)).trans (key v))

/-- A unit factor on the left may be cancelled: this uses that `unitL` is a natural
isomorphism. -/
private theorem cancel_prodF_unitL {X Y : Ty} {u v : Term X Y}
    (h : prodF (Term.id Ty.unit) u ≡ₜ prodF (Term.id Ty.unit) v) : u ≡ₜ v := by
  have key : ∀ w : Term X Y,
      ((unitL X ⨟ prodF (Term.id Ty.unit) w) ⨟ snd Ty.unit Y) ≡ₜ w := by
    intro w
    calc ((unitL X ⨟ prodF (Term.id Ty.unit) w) ⨟ snd Ty.unit Y)
        ≡ₜ ((w ⨟ unitL Y) ⨟ snd Ty.unit Y) := PEq.compL _ (PEq.symm (PEq.nat_unitL w))
      _ ≡ₜ (w ⨟ (unitL Y ⨟ snd Ty.unit Y)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (w ⨟ Term.id Y) := PEq.compR _ (PEq.unitL_snd Y)
      _ ≡ₜ w := PEq.comp_id w
  exact (PEq.symm (key u)).trans
    ((PEq.compL _ (PEq.compR _ h)).trans (key v))

/-! ### The unit on the left or on the right -/

/-- Inserting a unit on the right of `X` and re-associating: the isomorphism form of the
triangle axiom at `(X, 1)`. -/
theorem unitR_prod_unit (X : Ty) :
    prodF (unitR X) (Term.id Ty.unit) ≡ₜ
      (prodF (Term.id X) (unitR Ty.unit) ⨟ assocL X Ty.unit Ty.unit) := by
  refine cancel_right_iso (prodF (fst X Ty.unit) (Term.id Ty.unit))
    (prodF (unitR X) (Term.id Ty.unit)) ?_ ?_
  · exact (PEq.prod_comp _ _ _ _).trans
      ((PEq.congr_prodF (PEq.fst_unitR X) (PEq.id_comp _)).trans (PEq.prod_id _ _))
  · calc (prodF (unitR X) (Term.id Ty.unit) ⨟ prodF (fst X Ty.unit) (Term.id Ty.unit))
        ≡ₜ prodF (unitR X ⨟ fst X Ty.unit) (Term.id Ty.unit ⨟ Term.id Ty.unit) :=
          PEq.prod_comp _ _ _ _
      _ ≡ₜ Term.id (X ⊗ Ty.unit) :=
          (PEq.congr_prodF (PEq.unitR_fst X) (PEq.id_comp _)).trans (PEq.prod_id _ _)
      _ ≡ₜ prodF (Term.id X) (Term.id Ty.unit) := PEq.symm (PEq.prod_id _ _)
      _ ≡ₜ prodF (Term.id X ⨟ Term.id X) (unitR Ty.unit ⨟ snd Ty.unit Ty.unit) :=
          PEq.congr_prodF (PEq.symm (PEq.id_comp _)) (PEq.unit_unique _ _)
      _ ≡ₜ (prodF (Term.id X) (unitR Ty.unit) ⨟ prodF (Term.id X) (snd Ty.unit Ty.unit)) :=
          PEq.symm (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (Term.id X) (unitR Ty.unit) ⨟
            (assocL X Ty.unit Ty.unit ⨟ prodF (fst X Ty.unit) (Term.id Ty.unit))) :=
          PEq.compR _ (PEq.symm (PEq.triangle X Ty.unit))
      _ ≡ₜ ((prodF (Term.id X) (unitR Ty.unit) ⨟ assocL X Ty.unit Ty.unit) ⨟
            prodF (fst X Ty.unit) (Term.id Ty.unit)) := PEq.symm (PEq.comp_assoc _ _ _)

/-- Inserting a unit on the right of a product: the unit may be inserted before or after
forming the product.  This is the isomorphism form of the "unit on the right" triangle. -/
theorem unitR_prod (A B : Ty) :
    unitR (A ⊗ B) ≡ₜ (prodF (Term.id A) (unitR B) ⨟ assocL A B Ty.unit) := by
  refine cancel_prodF_unitR ?_
  refine cancel_left_iso (assocL A B Ty.unit) (assocR A B Ty.unit)
    (PEq.assocR_assocL A B Ty.unit) ?_
  calc (assocL A B Ty.unit ⨟ prodF (unitR (A ⊗ B)) (Term.id Ty.unit))
      ≡ₜ (assocL A B Ty.unit ⨟ (prodF (Term.id (A ⊗ B)) (unitR Ty.unit) ⨟
          assocL (A ⊗ B) Ty.unit Ty.unit)) := PEq.compR _ (unitR_prod_unit (A ⊗ B))
    _ ≡ₜ ((assocL A B Ty.unit ⨟ prodF (Term.id (A ⊗ B)) (unitR Ty.unit)) ⨟
          assocL (A ⊗ B) Ty.unit Ty.unit) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((assocL A B Ty.unit ⨟ prodF (prodF (Term.id A) (Term.id B)) (unitR Ty.unit)) ⨟
          assocL (A ⊗ B) Ty.unit Ty.unit) :=
        PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.symm (PEq.prod_id A B)) (PEq.refl _)))
    _ ≡ₜ ((prodF (Term.id A) (prodF (Term.id B) (unitR Ty.unit)) ⨟
          assocL A B (Ty.unit ⊗ Ty.unit)) ⨟ assocL (A ⊗ B) Ty.unit Ty.unit) :=
        PEq.compL _ (PEq.symm (PEq.nat_assocL (Term.id A) (Term.id B) (unitR Ty.unit)))
    _ ≡ₜ (prodF (Term.id A) (prodF (Term.id B) (unitR Ty.unit)) ⨟
          (assocL A B (Ty.unit ⊗ Ty.unit) ⨟ assocL (A ⊗ B) Ty.unit Ty.unit)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.id A) (prodF (Term.id B) (unitR Ty.unit)) ⨟
          ((prodF (Term.id A) (assocL B Ty.unit Ty.unit) ⨟ assocL A (B ⊗ Ty.unit) Ty.unit) ⨟
            prodF (assocL A B Ty.unit) (Term.id Ty.unit))) :=
        PEq.compR _ (PEq.symm (PEq.pentagon A B Ty.unit Ty.unit))
    _ ≡ₜ (prodF (Term.id A) (prodF (Term.id B) (unitR Ty.unit)) ⨟
          (prodF (Term.id A) (assocL B Ty.unit Ty.unit) ⨟
            (assocL A (B ⊗ Ty.unit) Ty.unit ⨟ prodF (assocL A B Ty.unit) (Term.id Ty.unit)))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF (Term.id A) (prodF (Term.id B) (unitR Ty.unit)) ⨟
          prodF (Term.id A) (assocL B Ty.unit Ty.unit)) ⨟
            (assocL A (B ⊗ Ty.unit) Ty.unit ⨟ prodF (assocL A B Ty.unit) (Term.id Ty.unit))) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (Term.id A) (prodF (unitR B) (Term.id Ty.unit)) ⨟
          (assocL A (B ⊗ Ty.unit) Ty.unit ⨟ prodF (assocL A B Ty.unit) (Term.id Ty.unit))) :=
        PEq.compL _ ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.id_comp _) (PEq.symm (unitR_prod_unit B))))
    _ ≡ₜ ((prodF (Term.id A) (prodF (unitR B) (Term.id Ty.unit)) ⨟
          assocL A (B ⊗ Ty.unit) Ty.unit) ⨟ prodF (assocL A B Ty.unit) (Term.id Ty.unit)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((assocL A B Ty.unit ⨟ prodF (prodF (Term.id A) (unitR B)) (Term.id Ty.unit)) ⨟
          prodF (assocL A B Ty.unit) (Term.id Ty.unit)) :=
        PEq.compL _ (PEq.nat_assocL (Term.id A) (unitR B) (Term.id Ty.unit))
    _ ≡ₜ (assocL A B Ty.unit ⨟ (prodF (prodF (Term.id A) (unitR B)) (Term.id Ty.unit) ⨟
          prodF (assocL A B Ty.unit) (Term.id Ty.unit))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL A B Ty.unit ⨟
          prodF (prodF (Term.id A) (unitR B) ⨟ assocL A B Ty.unit) (Term.id Ty.unit)) :=
        PEq.compR _ ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _)))

/-- **Unit on the right.**  The variant of Mac Lane's triangle in which the discarded unit is
the last component of the product. -/
theorem triangle_right (A B : Ty) :
    (assocL A B Ty.unit ⨟ fst (A ⊗ B) Ty.unit) ≡ₜ prodF (Term.id A) (fst B Ty.unit) := by
  refine cancel_left_iso (prodF (Term.id A) (unitR B)) (prodF (Term.id A) (fst B Ty.unit))
    ?_ ?_
  · exact (PEq.prod_comp _ _ _ _).trans
      ((PEq.congr_prodF (PEq.id_comp _) (PEq.fst_unitR B)).trans (PEq.prod_id _ _))
  · calc (prodF (Term.id A) (unitR B) ⨟ (assocL A B Ty.unit ⨟ fst (A ⊗ B) Ty.unit))
        ≡ₜ ((prodF (Term.id A) (unitR B) ⨟ assocL A B Ty.unit) ⨟ fst (A ⊗ B) Ty.unit) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (unitR (A ⊗ B) ⨟ fst (A ⊗ B) Ty.unit) :=
          PEq.compL _ (PEq.symm (unitR_prod A B))
      _ ≡ₜ Term.id (A ⊗ B) := PEq.unitR_fst _
      _ ≡ₜ prodF (Term.id A ⨟ Term.id A) (unitR B ⨟ fst B Ty.unit) :=
          PEq.symm ((PEq.congr_prodF (PEq.id_comp _) (PEq.unitR_fst B)).trans
            (PEq.prod_id _ _))
      _ ≡ₜ (prodF (Term.id A) (unitR B) ⨟ prodF (Term.id A) (fst B Ty.unit)) :=
          PEq.symm (PEq.prod_comp _ _ _ _)

/-- **Unit on the left.**  The variant of Mac Lane's triangle in which the discarded unit is
the first component of the product.  This is the argument of Kelly: the pentagon at
`(1, 1, B, C)`, together with naturality of the associator and two instances of the triangle
axiom, forces the missing triangle to commute. -/
theorem triangle_left (B C : Ty) :
    (assocL Ty.unit B C ⨟ prodF (snd Ty.unit B) (Term.id C)) ≡ₜ snd Ty.unit (B ⊗ C) := by
  refine PEq.symm (cancel_prodF_unitL ?_)
  refine cancel_right_iso (assocL Ty.unit B C) (assocR Ty.unit B C)
    (PEq.assocL_assocR Ty.unit B C) ?_
  calc (prodF (Term.id Ty.unit) (snd Ty.unit (B ⊗ C)) ⨟ assocL Ty.unit B C)
      ≡ₜ ((assocL Ty.unit Ty.unit (B ⊗ C) ⨟
          prodF (fst Ty.unit Ty.unit) (Term.id (B ⊗ C))) ⨟ assocL Ty.unit B C) :=
        PEq.compL _ (PEq.symm (PEq.triangle Ty.unit (B ⊗ C)))
    _ ≡ₜ (assocL Ty.unit Ty.unit (B ⊗ C) ⨟
          (prodF (fst Ty.unit Ty.unit) (Term.id (B ⊗ C)) ⨟ assocL Ty.unit B C)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (assocL Ty.unit Ty.unit (B ⊗ C) ⨟
          (prodF (fst Ty.unit Ty.unit) (prodF (Term.id B) (Term.id C)) ⨟
            assocL Ty.unit B C)) :=
        PEq.compR _ (PEq.compL _ (PEq.congr_prodF (PEq.refl _) (PEq.symm (PEq.prod_id B C))))
    _ ≡ₜ (assocL Ty.unit Ty.unit (B ⊗ C) ⨟ (assocL (Ty.unit ⊗ Ty.unit) B C ⨟
          prodF (prodF (fst Ty.unit Ty.unit) (Term.id B)) (Term.id C))) :=
        PEq.compR _ (PEq.nat_assocL (fst Ty.unit Ty.unit) (Term.id B) (Term.id C))
    _ ≡ₜ ((assocL Ty.unit Ty.unit (B ⊗ C) ⨟ assocL (Ty.unit ⊗ Ty.unit) B C) ⨟
          prodF (prodF (fst Ty.unit Ty.unit) (Term.id B)) (Term.id C)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((prodF (Term.id Ty.unit) (assocL Ty.unit B C) ⨟
          assocL Ty.unit (Ty.unit ⊗ B) C) ⨟
            prodF (assocL Ty.unit Ty.unit B) (Term.id C)) ⨟
          prodF (prodF (fst Ty.unit Ty.unit) (Term.id B)) (Term.id C)) :=
        PEq.compL _ (PEq.symm (PEq.pentagon Ty.unit Ty.unit B C))
    _ ≡ₜ ((prodF (Term.id Ty.unit) (assocL Ty.unit B C) ⨟
          (assocL Ty.unit (Ty.unit ⊗ B) C ⨟
            prodF (assocL Ty.unit Ty.unit B) (Term.id C))) ⨟
          prodF (prodF (fst Ty.unit Ty.unit) (Term.id B)) (Term.id C)) :=
        PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (Term.id Ty.unit) (assocL Ty.unit B C) ⨟
          ((assocL Ty.unit (Ty.unit ⊗ B) C ⨟ prodF (assocL Ty.unit Ty.unit B) (Term.id C)) ⨟
            prodF (prodF (fst Ty.unit Ty.unit) (Term.id B)) (Term.id C))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.id Ty.unit) (assocL Ty.unit B C) ⨟
          (assocL Ty.unit (Ty.unit ⊗ B) C ⨟ (prodF (assocL Ty.unit Ty.unit B) (Term.id C) ⨟
            prodF (prodF (fst Ty.unit Ty.unit) (Term.id B)) (Term.id C)))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (Term.id Ty.unit) (assocL Ty.unit B C) ⨟
          (assocL Ty.unit (Ty.unit ⊗ B) C ⨟
            prodF (prodF (Term.id Ty.unit) (snd Ty.unit B)) (Term.id C))) :=
        PEq.compR _ (PEq.compR _ ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.triangle Ty.unit B) (PEq.id_comp _))))
    _ ≡ₜ (prodF (Term.id Ty.unit) (assocL Ty.unit B C) ⨟
          (prodF (Term.id Ty.unit) (prodF (snd Ty.unit B) (Term.id C)) ⨟
            assocL Ty.unit B C)) :=
        PEq.compR _ (PEq.symm
          (PEq.nat_assocL (Term.id Ty.unit) (snd Ty.unit B) (Term.id C)))
    _ ≡ₜ ((prodF (Term.id Ty.unit) (assocL Ty.unit B C) ⨟
          prodF (Term.id Ty.unit) (prodF (snd Ty.unit B) (Term.id C))) ⨟
            assocL Ty.unit B C) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (Term.id Ty.unit)
          (assocL Ty.unit B C ⨟ prodF (snd Ty.unit B) (Term.id C)) ⨟ assocL Ty.unit B C) :=
        PEq.compL _ ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _)))

/-! ### The projections coherence laws -/

/-- **First projections coherence law.**  Exchanging a first projection with the left
associator: the middle component of a triple may be discarded either before or after
reassociating.  This is Mac Lane's triangle with the discarded unit replaced by an arbitrary
type. -/
theorem assocL_fst_snd (X W Y : Ty) :
    (assocL X W Y ⨟ prodF (fst X W) (Term.id Y)) ≡ₜ prodF (Term.id X) (snd W Y) := by
  have hfst : (prodF (Term.id X) (toUnit W) ⨟ fst X Ty.unit) ≡ₜ fst X W :=
    (PEq.nat_fst (Term.id X) (toUnit W)).trans (PEq.comp_id _)
  calc (assocL X W Y ⨟ prodF (fst X W) (Term.id Y))
      ≡ₜ (assocL X W Y ⨟
          prodF (prodF (Term.id X) (toUnit W) ⨟ fst X Ty.unit) (Term.id Y)) :=
        PEq.compR _ (PEq.congr_prodF (PEq.symm hfst) (PEq.refl _))
    _ ≡ₜ (assocL X W Y ⨟ (prodF (prodF (Term.id X) (toUnit W)) (Term.id Y) ⨟
          prodF (fst X Ty.unit) (Term.id Y))) :=
        PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))))
    _ ≡ₜ ((assocL X W Y ⨟ prodF (prodF (Term.id X) (toUnit W)) (Term.id Y)) ⨟
          prodF (fst X Ty.unit) (Term.id Y)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF (Term.id X) (prodF (toUnit W) (Term.id Y)) ⨟ assocL X Ty.unit Y) ⨟
          prodF (fst X Ty.unit) (Term.id Y)) :=
        PEq.compL _ (PEq.symm (PEq.nat_assocL (Term.id X) (toUnit W) (Term.id Y)))
    _ ≡ₜ (prodF (Term.id X) (prodF (toUnit W) (Term.id Y)) ⨟
          (assocL X Ty.unit Y ⨟ prodF (fst X Ty.unit) (Term.id Y))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.id X) (prodF (toUnit W) (Term.id Y)) ⨟
          prodF (Term.id X) (snd Ty.unit Y)) := PEq.compR _ (PEq.triangle X Y)
    _ ≡ₜ prodF (Term.id X ⨟ Term.id X) (prodF (toUnit W) (Term.id Y) ⨟ snd Ty.unit Y) :=
        PEq.prod_comp _ _ _ _
    _ ≡ₜ prodF (Term.id X) (snd W Y) :=
        PEq.congr_prodF (PEq.id_comp _)
          ((PEq.nat_snd (toUnit W) (Term.id Y)).trans (PEq.comp_id _))

/-- **Second projections coherence law.**  Discarding the first component of a triple may be
done either in one step or after reassociating. -/
theorem assocL_snd (X W Y : Ty) :
    (assocL X W Y ⨟ prodF (snd X W) (Term.id Y)) ≡ₜ snd X (W ⊗ Y) := by
  have hsnd : (prodF (toUnit X) (Term.id W) ⨟ snd Ty.unit W) ≡ₜ snd X W :=
    (PEq.nat_snd (toUnit X) (Term.id W)).trans (PEq.comp_id _)
  calc (assocL X W Y ⨟ prodF (snd X W) (Term.id Y))
      ≡ₜ (assocL X W Y ⨟
          prodF (prodF (toUnit X) (Term.id W) ⨟ snd Ty.unit W) (Term.id Y)) :=
        PEq.compR _ (PEq.congr_prodF (PEq.symm hsnd) (PEq.refl _))
    _ ≡ₜ (assocL X W Y ⨟ (prodF (prodF (toUnit X) (Term.id W)) (Term.id Y) ⨟
          prodF (snd Ty.unit W) (Term.id Y))) :=
        PEq.compR _ (PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))))
    _ ≡ₜ ((assocL X W Y ⨟ prodF (prodF (toUnit X) (Term.id W)) (Term.id Y)) ⨟
          prodF (snd Ty.unit W) (Term.id Y)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((prodF (toUnit X) (prodF (Term.id W) (Term.id Y)) ⨟ assocL Ty.unit W Y) ⨟
          prodF (snd Ty.unit W) (Term.id Y)) :=
        PEq.compL _ (PEq.symm (PEq.nat_assocL (toUnit X) (Term.id W) (Term.id Y)))
    _ ≡ₜ (prodF (toUnit X) (prodF (Term.id W) (Term.id Y)) ⨟
          (assocL Ty.unit W Y ⨟ prodF (snd Ty.unit W) (Term.id Y))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (toUnit X) (Term.id (W ⊗ Y)) ⨟ snd Ty.unit (W ⊗ Y)) :=
        PEq.congr_comp (PEq.congr_prodF (PEq.refl _) (PEq.prod_id W Y)) (triangle_left W Y)
    _ ≡ₜ snd X (W ⊗ Y) := (PEq.nat_snd (toUnit X) (Term.id (W ⊗ Y))).trans (PEq.comp_id _)

/-- **Third projections coherence law.**  Discarding the last component of a triple may be
done either in one step or after reassociating. -/
theorem assocL_fst (X W Y : Ty) :
    (assocL X W Y ⨟ fst (X ⊗ W) Y) ≡ₜ prodF (Term.id X) (fst W Y) := by
  have hfst :
      (prodF (Term.id (X ⊗ W)) (toUnit Y) ⨟ fst (X ⊗ W) Ty.unit) ≡ₜ fst (X ⊗ W) Y :=
    (PEq.nat_fst (Term.id (X ⊗ W)) (toUnit Y)).trans (PEq.comp_id _)
  calc (assocL X W Y ⨟ fst (X ⊗ W) Y)
      ≡ₜ (assocL X W Y ⨟ (prodF (Term.id (X ⊗ W)) (toUnit Y) ⨟ fst (X ⊗ W) Ty.unit)) :=
        PEq.compR _ (PEq.symm hfst)
    _ ≡ₜ ((assocL X W Y ⨟ prodF (Term.id (X ⊗ W)) (toUnit Y)) ⨟ fst (X ⊗ W) Ty.unit) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((assocL X W Y ⨟ prodF (prodF (Term.id X) (Term.id W)) (toUnit Y)) ⨟
          fst (X ⊗ W) Ty.unit) :=
        PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.symm (PEq.prod_id X W)) (PEq.refl _)))
    _ ≡ₜ ((prodF (Term.id X) (prodF (Term.id W) (toUnit Y)) ⨟ assocL X W Ty.unit) ⨟
          fst (X ⊗ W) Ty.unit) :=
        PEq.compL _ (PEq.symm (PEq.nat_assocL (Term.id X) (Term.id W) (toUnit Y)))
    _ ≡ₜ (prodF (Term.id X) (prodF (Term.id W) (toUnit Y)) ⨟
          (assocL X W Ty.unit ⨟ fst (X ⊗ W) Ty.unit)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.id X) (prodF (Term.id W) (toUnit Y)) ⨟
          prodF (Term.id X) (fst W Ty.unit)) := PEq.compR _ (triangle_right X W)
    _ ≡ₜ prodF (Term.id X ⨟ Term.id X) (prodF (Term.id W) (toUnit Y) ⨟ fst W Ty.unit) :=
        PEq.prod_comp _ _ _ _
    _ ≡ₜ prodF (Term.id X) (fst W Y) :=
        PEq.congr_prodF (PEq.id_comp _)
          ((PEq.nat_fst (Term.id W) (toUnit Y)).trans (PEq.comp_id _))

/-! ### Consequences -/

/-- The mirror image of the second coherence law, for the right associator. -/
theorem assocR_snd (X W Y : Ty) :
    (assocR X W Y ⨟ snd X (W ⊗ Y)) ≡ₜ prodF (snd X W) (Term.id Y) := by
  calc (assocR X W Y ⨟ snd X (W ⊗ Y))
      ≡ₜ (assocR X W Y ⨟ (assocL X W Y ⨟ prodF (snd X W) (Term.id Y))) :=
        PEq.compR _ (PEq.symm (assocL_snd X W Y))
    _ ≡ₜ ((assocR X W Y ⨟ assocL X W Y) ⨟ prodF (snd X W) (Term.id Y)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((X ⊗ W) ⊗ Y) ⨟ prodF (snd X W) (Term.id Y)) :=
        PEq.compL _ (PEq.assocR_assocL _ _ _)
    _ ≡ₜ prodF (snd X W) (Term.id Y) := PEq.id_comp _

/-- The mirror image of the first coherence law: exchanging a second projection with the right
associator. -/
theorem assocR_snd_fst (X W Y : Ty) :
    (assocR X W Y ⨟ prodF (Term.id X) (snd W Y)) ≡ₜ prodF (fst X W) (Term.id Y) := by
  calc (assocR X W Y ⨟ prodF (Term.id X) (snd W Y))
      ≡ₜ (assocR X W Y ⨟ (assocL X W Y ⨟ prodF (fst X W) (Term.id Y))) :=
        PEq.compR _ (PEq.symm (assocL_fst_snd X W Y))
    _ ≡ₜ ((assocR X W Y ⨟ assocL X W Y) ⨟ prodF (fst X W) (Term.id Y)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((X ⊗ W) ⊗ Y) ⨟ prodF (fst X W) (Term.id Y)) :=
        PEq.compL _ (PEq.assocR_assocL _ _ _)
    _ ≡ₜ prodF (fst X W) (Term.id Y) := PEq.id_comp _

/-- The form of the triangle identity that uses the two units: inserting a unit on the right of
`X` and re-associating is the same as inserting it on the left of `Y`.  It is the isomorphism
form of the first projections coherence law at the unit type. -/
theorem unitR_assocR (X Y : Ty) :
    (prodF (unitR X) (Term.id Y) ⨟ assocR X Ty.unit Y) ≡ₜ prodF (Term.id X) (unitL Y) := by
  refine cancel_right_iso (prodF (Term.id X) (snd Ty.unit Y))
    (prodF (Term.id X) (unitL Y)) ?_ ?_
  · exact (PEq.prod_comp _ _ _ _).trans
      ((PEq.congr_prodF (PEq.id_comp _) (PEq.snd_unitL Y)).trans (PEq.prod_id _ _))
  · have hR : (prodF (Term.id X) (unitL Y) ⨟ prodF (Term.id X) (snd Ty.unit Y)) ≡ₜ
        Term.id (X ⊗ Y) :=
      (PEq.prod_comp _ _ _ _).trans
        ((PEq.congr_prodF (PEq.id_comp _) (PEq.unitL_snd Y)).trans (PEq.prod_id _ _))
    refine PEq.trans ?_ (PEq.symm hR)
    calc ((prodF (unitR X) (Term.id Y) ⨟ assocR X Ty.unit Y) ⨟
          prodF (Term.id X) (snd Ty.unit Y))
        ≡ₜ (prodF (unitR X) (Term.id Y) ⨟
            (assocR X Ty.unit Y ⨟ prodF (Term.id X) (snd Ty.unit Y))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (unitR X) (Term.id Y) ⨟
            (assocR X Ty.unit Y ⨟ (assocL X Ty.unit Y ⨟
              prodF (fst X Ty.unit) (Term.id Y)))) :=
          PEq.compR _ (PEq.compR _ (PEq.symm (assocL_fst_snd X Ty.unit Y)))
      _ ≡ₜ (prodF (unitR X) (Term.id Y) ⨟ ((assocR X Ty.unit Y ⨟ assocL X Ty.unit Y) ⨟
            prodF (fst X Ty.unit) (Term.id Y))) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (prodF (unitR X) (Term.id Y) ⨟ prodF (fst X Ty.unit) (Term.id Y)) :=
          PEq.compR _ ((PEq.compL _ (PEq.assocR_assocL _ _ _)).trans (PEq.id_comp _))
      _ ≡ₜ Term.id (X ⊗ Y) :=
          (PEq.prod_comp _ _ _ _).trans
            ((PEq.congr_prodF (PEq.unitR_fst X) (PEq.id_comp _)).trans (PEq.prod_id _ _))

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
