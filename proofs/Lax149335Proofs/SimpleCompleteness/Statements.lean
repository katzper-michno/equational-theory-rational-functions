import Lax149335Proofs.Preliminaries.Overview
import Lax149335Proofs.Preliminaries.HomCombinator
import Lax149335Proofs.Appendix.ShiftOnes
import Mathlib.Tactic.Set
import Mathlib.Order.MinMax

/-!
# Completeness for simple rational terms (Section 6)

Simple rational terms are re-read inside the compositional syntax of Section 3, the three
conjugacy relations of Section 6 are defined, and the statements of Lemma 6.1, Lemma 6.2,
Definition 6.3, Lemma 6.4, Lemma 6.5, Claim 6.6 and Lemma 6.7 are given.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! **Lemma 6.1 (Completeness for simple rational terms)** is stated and proved as
`Lax149335Proofs.completeness_simple` in `Lax149335Proofs.SimpleCompleteness.Proof`: its proof is an
induction on the list nesting depth of the input type which uses the lemmas of the present
file, so it cannot be stated here. -/

/-- **Lemma 6.2.**  The variant of the conjugacy rule in which the assumption is strengthened
from provable conjugacy to syntactic conjugacy.

As the proof in the appendix shows, neither the assumption that `B` is a finite alphabet nor
the assumption that `h` is a simple rational term is needed, so they have been dropped from
the statement: the equality holds for every term `h : A → B*` and every value `w`. -/
theorem conjugacy_of_syntactic {A B : Ty} (h : Term A B⋆) (w : Value B⋆) :
    dotR (homT (dotL w h)) w ≡ₜ dotL w (homT (dotR h w)) := by
  set W : Ty := (B⋆ ⊗ B⋆)⋆ with hW
  set K : Term ((A ⊗ Ty.unit)⋆) W := listF (prodF h w) with hK
  set K' : Term ((Ty.unit ⊗ A)⋆) W := listF (prodF w h) with hK'
  -- the left-hand path of the diagram
  have hstepL : (K ⨟ pairL w (Term.id W)) ≡ₜ (unitL ((A ⊗ Ty.unit)⋆) ⨟ prodF w K) := by
    calc (K ⨟ (unitL W ⨟ prodF w (Term.id W)))
        ≡ₜ ((K ⨟ unitL W) ⨟ prodF w (Term.id W)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((unitL ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id Ty.unit) K) ⨟ prodF w (Term.id W)) :=
          PEq.compL _ (PEq.nat_unitL K)
      _ ≡ₜ (unitL ((A ⊗ Ty.unit)⋆) ⨟ (prodF (Term.id Ty.unit) K ⨟ prodF w (Term.id W))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (unitL ((A ⊗ Ty.unit)⋆) ⨟ prodF (Term.id Ty.unit ⨟ w) (K ⨟ Term.id W)) :=
          PEq.compR _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (unitL ((A ⊗ Ty.unit)⋆) ⨟ prodF w K) :=
          PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) (PEq.comp_id _))
  have hgcR : (pairL w (Term.id W) ⨟ gconcR B) ≡ₜ dotL w (homT (binconcat B)) := by
    calc (pairL w (Term.id W) ⨟ (prodF (Term.id B⋆) (homT (binconcat B)) ⨟ binconcat B))
        ≡ₜ ((pairL w (Term.id W) ⨟ prodF (Term.id B⋆) (homT (binconcat B))) ⨟
            binconcat B) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairL (w ⨟ Term.id B⋆) (Term.id W ⨟ homT (binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (Term.pairL_prodF _ _ _ _)
      _ ≡ₜ (pairL w (homT (binconcat B)) ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.comp_id _) (PEq.id_comp _)))
  have hP : (Term.packR A ⨟ (prodF w K ⨟ gconcR B)) ≡ₜ dotL w (homT (dotR h w)) := by
    calc ((listF (unitR A) ⨟ unitL ((A ⊗ Ty.unit)⋆)) ⨟ (prodF w K ⨟ gconcR B))
        ≡ₜ (listF (unitR A) ⨟ (unitL ((A ⊗ Ty.unit)⋆) ⨟ (prodF w K ⨟ gconcR B))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (listF (unitR A) ⨟ ((unitL ((A ⊗ Ty.unit)⋆) ⨟ prodF w K) ⨟ gconcR B)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (listF (unitR A) ⨟ ((K ⨟ pairL w (Term.id W)) ⨟ gconcR B)) :=
          PEq.compR _ (PEq.compL _ (PEq.symm hstepL))
      _ ≡ₜ (listF (unitR A) ⨟ (K ⨟ (pairL w (Term.id W) ⨟ gconcR B))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (listF (unitR A) ⨟ (K ⨟ dotL w (homT (binconcat B)))) :=
          PEq.compR _ (PEq.compR _ hgcR)
      _ ≡ₜ ((listF (unitR A) ⨟ K) ⨟ dotL w (homT (binconcat B))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (listF (pairR h w) ⨟ dotL w (homT (binconcat B))) :=
          PEq.compL _ (PEq.list_comp _ _)
      _ ≡ₜ (listF (pairR h w) ⨟ (homT (binconcat B) ⨟ dotL w (Term.id B⋆))) :=
          PEq.compR _ (Term.dotL_eq_comp w (homT (binconcat B)))
      _ ≡ₜ ((listF (pairR h w) ⨟ homT (binconcat B)) ⨟ dotL w (Term.id B⋆)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (homT (dotR h w) ⨟ dotL w (Term.id B⋆)) :=
          PEq.compL _ (PEq.symm (Term.homT_precomp (pairR h w) (binconcat B)))
      _ ≡ₜ dotL w (homT (dotR h w)) :=
          PEq.symm (Term.dotL_eq_comp w (homT (dotR h w)))
  -- the right-hand path of the diagram
  have hstepR : (K' ⨟ pairR (Term.id W) w) ≡ₜ (unitR ((Ty.unit ⊗ A)⋆) ⨟ prodF K' w) := by
    calc (K' ⨟ (unitR W ⨟ prodF (Term.id W) w))
        ≡ₜ ((K' ⨟ unitR W) ⨟ prodF (Term.id W) w) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((unitR ((Ty.unit ⊗ A)⋆) ⨟ prodF K' (Term.id Ty.unit)) ⨟ prodF (Term.id W) w) :=
          PEq.compL _ (PEq.nat_unitR K')
      _ ≡ₜ (unitR ((Ty.unit ⊗ A)⋆) ⨟ (prodF K' (Term.id Ty.unit) ⨟ prodF (Term.id W) w)) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (unitR ((Ty.unit ⊗ A)⋆) ⨟ prodF (K' ⨟ Term.id W) (Term.id Ty.unit ⨟ w)) :=
          PEq.compR _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (unitR ((Ty.unit ⊗ A)⋆) ⨟ prodF K' w) :=
          PEq.compR _ (PEq.congr_prodF (PEq.comp_id _) (PEq.id_comp _))
  have hgcL : (pairR (Term.id W) w ⨟ gconcL B) ≡ₜ dotR (homT (binconcat B)) w := by
    calc (pairR (Term.id W) w ⨟ (prodF (homT (binconcat B)) (Term.id B⋆) ⨟ binconcat B))
        ≡ₜ ((pairR (Term.id W) w ⨟ prodF (homT (binconcat B)) (Term.id B⋆)) ⨟
            binconcat B) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (pairR (Term.id W ⨟ homT (binconcat B)) (w ⨟ Term.id B⋆) ⨟ binconcat B) :=
          PEq.compL _ (Term.pairR_prodF _ _ _ _)
      _ ≡ₜ (pairR (homT (binconcat B)) w ⨟ binconcat B) :=
          PEq.compL _ (PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) (PEq.comp_id _)))
  have hQ : (Term.packL A ⨟ (prodF K' w ⨟ gconcL B)) ≡ₜ dotR (homT (dotL w h)) w := by
    calc ((listF (unitL A) ⨟ unitR ((Ty.unit ⊗ A)⋆)) ⨟ (prodF K' w ⨟ gconcL B))
        ≡ₜ (listF (unitL A) ⨟ (unitR ((Ty.unit ⊗ A)⋆) ⨟ (prodF K' w ⨟ gconcL B))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (listF (unitL A) ⨟ ((unitR ((Ty.unit ⊗ A)⋆) ⨟ prodF K' w) ⨟ gconcL B)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (listF (unitL A) ⨟ ((K' ⨟ pairR (Term.id W) w) ⨟ gconcL B)) :=
          PEq.compR _ (PEq.compL _ (PEq.symm hstepR))
      _ ≡ₜ (listF (unitL A) ⨟ (K' ⨟ (pairR (Term.id W) w ⨟ gconcL B))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (listF (unitL A) ⨟ (K' ⨟ dotR (homT (binconcat B)) w)) :=
          PEq.compR _ (PEq.compR _ hgcL)
      _ ≡ₜ ((listF (unitL A) ⨟ K') ⨟ dotR (homT (binconcat B)) w) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (listF (pairL w h) ⨟ dotR (homT (binconcat B)) w) :=
          PEq.compL _ (PEq.list_comp _ _)
      _ ≡ₜ (listF (pairL w h) ⨟ (homT (binconcat B) ⨟ dotR (Term.id B⋆) w)) :=
          PEq.compR _ (Term.dotR_eq_comp (homT (binconcat B)) w)
      _ ≡ₜ ((listF (pairL w h) ⨟ homT (binconcat B)) ⨟ dotR (Term.id B⋆) w) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (homT (dotL w h) ⨟ dotR (Term.id B⋆) w) :=
          PEq.compL _ (PEq.symm (Term.homT_precomp (pairL w h) (binconcat B)))
      _ ≡ₜ dotR (homT (dotL w h)) w :=
          PEq.symm (Term.dotR_eq_comp (homT (dotL w h)) w)
  -- the two paths agree, by "shift ones" and naturality of `shiftL`
  have hPQ : (Term.packL A ⨟ (prodF K' w ⨟ gconcL B)) ≡ₜ
      (Term.packR A ⨟ (prodF w K ⨟ gconcR B)) := by
    calc (Term.packL A ⨟ (prodF K' w ⨟ gconcL B))
        ≡ₜ ((Term.packR A ⨟ shiftL Ty.unit A) ⨟ (prodF K' w ⨟ gconcL B)) :=
          PEq.compL _ (PEq.symm (Term.shift_ones A))
      _ ≡ₜ (Term.packR A ⨟ (shiftL Ty.unit A ⨟ (prodF K' w ⨟ gconcL B))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.packR A ⨟ ((shiftL Ty.unit A ⨟ prodF K' w) ⨟ gconcL B)) :=
          PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (Term.packR A ⨟ ((prodF w K ⨟ shiftL B⋆ B⋆) ⨟ gconcL B)) :=
          PEq.compR _ (PEq.compL _ (PEq.symm (PEq.nat_shiftL w h)))
      _ ≡ₜ (Term.packR A ⨟ (prodF w K ⨟ (shiftL B⋆ B⋆ ⨟ gconcL B))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.packR A ⨟ (prodF w K ⨟ gconcR B)) :=
          PEq.compR _ (PEq.compR _ (Term.shiftL_gconc B))
  exact (PEq.symm hQ).trans (hPQ.trans hP)

/-! ### `n`-ary co-pairing

The `n`-ary co-pairings `either_n f₁ ⋯ fₙ` used in Lemmas 6.4 and 6.5 are described by a
head term together with a list of further terms, one for each remaining summand of the input
type. -/

/-! ### An equational toolkit for co-pairings

The proof of Lemma 6.5 below has to split the input type of a co-pairing into the summands on
which both terms produce the empty list and the remaining ones.  The lemmas of this section
provide the equational facts about co-products and empty constants that the splitting
argument needs. -/

namespace Term

/-- Two empty constants on the two summands of a co-product make one empty constant. -/
theorem either_nilconst (E N B : Ty) :
    either (toUnit E ⨟ nilT B) (toUnit N ⨟ nilT B) ≡ₜ (toUnit (E ⊕' N) ⨟ nilT B) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl E N ⨟ either (toUnit E ⨟ nilT B) (toUnit N ⨟ nilT B))
        ≡ₜ (toUnit E ⨟ nilT B) := inl_either _ _
      _ ≡ₜ ((inl E N ⨟ toUnit (E ⊕' N)) ⨟ nilT B) :=
          PEq.compL _ (PEq.symm (PEq.unit_unique (inl E N ⨟ toUnit (E ⊕' N)) (toUnit E)))
      _ ≡ₜ (inl E N ⨟ (toUnit (E ⊕' N) ⨟ nilT B)) := PEq.comp_assoc _ _ _
  · calc (inr E N ⨟ either (toUnit E ⨟ nilT B) (toUnit N ⨟ nilT B))
        ≡ₜ (toUnit N ⨟ nilT B) := inr_either _ _
      _ ≡ₜ ((inr E N ⨟ toUnit (E ⊕' N)) ⨟ nilT B) :=
          PEq.compL _ (PEq.symm (PEq.unit_unique (inr E N ⨟ toUnit (E ⊕' N)) (toUnit N)))
      _ ≡ₜ (inr E N ⨟ (toUnit (E ⊕' N) ⨟ nilT B)) := PEq.comp_assoc _ _ _

/-- The rotation `A + (E + N) → E + (A + N)` of a co-product, as a derived term. -/
def sumRot (A E N : Ty) : Term (A ⊕' (E ⊕' N)) (E ⊕' (A ⊕' N)) :=
  either (inl A N ⨟ inr E (A ⊕' N))
    (either (inl E (A ⊕' N)) (inr A N ⨟ inr E (A ⊕' N)))

/-- The two rotations of a co-product are mutually inverse. -/
theorem sumRot_sumRot (A E N : Ty) :
    (sumRot A E N ⨟ sumRot E A N) ≡ₜ Term.id (A ⊕' (E ⊕' N)) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl A (E ⊕' N) ⨟ (sumRot A E N ⨟ sumRot E A N))
        ≡ₜ ((inl A (E ⊕' N) ⨟ sumRot A E N) ⨟ sumRot E A N) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((inl A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N) := PEq.compL _ (inl_either _ _)
      _ ≡ₜ (inl A N ⨟ (inr E (A ⊕' N) ⨟ sumRot E A N)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inl A N ⨟ either (inl A (E ⊕' N)) (inr E N ⨟ inr A (E ⊕' N))) :=
          PEq.compR _ (inr_either _ _)
      _ ≡ₜ inl A (E ⊕' N) := inl_either _ _
      _ ≡ₜ (inl A (E ⊕' N) ⨟ Term.id (A ⊕' (E ⊕' N))) := PEq.symm (PEq.comp_id _)
  · have hinner :
        (either (inl E (A ⊕' N)) (inr A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N) ≡ₜ
          inr A (E ⊕' N) := by
      refine either_ext _ _ ?_ ?_
      · calc (inl E N ⨟ (either (inl E (A ⊕' N)) (inr A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N))
            ≡ₜ ((inl E N ⨟ either (inl E (A ⊕' N)) (inr A N ⨟ inr E (A ⊕' N))) ⨟
                sumRot E A N) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ (inl E (A ⊕' N) ⨟ sumRot E A N) := PEq.compL _ (inl_either _ _)
          _ ≡ₜ (inl E N ⨟ inr A (E ⊕' N)) := inl_either _ _
      · calc (inr E N ⨟ (either (inl E (A ⊕' N)) (inr A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N))
            ≡ₜ ((inr E N ⨟ either (inl E (A ⊕' N)) (inr A N ⨟ inr E (A ⊕' N))) ⨟
                sumRot E A N) := PEq.symm (PEq.comp_assoc _ _ _)
          _ ≡ₜ ((inr A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N) := PEq.compL _ (inr_either _ _)
          _ ≡ₜ (inr A N ⨟ (inr E (A ⊕' N) ⨟ sumRot E A N)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (inr A N ⨟ either (inl A (E ⊕' N)) (inr E N ⨟ inr A (E ⊕' N))) :=
              PEq.compR _ (inr_either _ _)
          _ ≡ₜ (inr E N ⨟ inr A (E ⊕' N)) := inr_either _ _
    calc (inr A (E ⊕' N) ⨟ (sumRot A E N ⨟ sumRot E A N))
        ≡ₜ ((inr A (E ⊕' N) ⨟ sumRot A E N) ⨟ sumRot E A N) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (either (inl E (A ⊕' N)) (inr A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N) :=
          PEq.compL _ (inr_either _ _)
      _ ≡ₜ inr A (E ⊕' N) := hinner
      _ ≡ₜ (inr A (E ⊕' N) ⨟ Term.id (A ⊕' (E ⊕' N))) := PEq.symm (PEq.comp_id _)

/-- Appending a value to the empty constant. -/
theorem dotR_nilconst (A B : Ty) (w : Value B⋆) :
    dotR (toUnit A ⨟ nilT B) w ≡ₜ (toUnit A ⨟ w) := by
  calc ((unitR A ⨟ prodF (toUnit A ⨟ nilT B) w) ⨟ binconcat B)
      ≡ₜ (unitR A ⨟ (prodF (toUnit A ⨟ nilT B) w ⨟ binconcat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR A ⨟ (snd A Ty.unit ⨟ w)) := PEq.compR _ (prodF_nilconst_binconcat_left w)
    _ ≡ₜ ((unitR A ⨟ snd A Ty.unit) ⨟ w) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (toUnit A ⨟ w) :=
        PEq.compL _ (PEq.unit_unique (unitR A ⨟ snd A Ty.unit) (toUnit A))

/-- Prepending a value to the empty constant. -/
theorem dotL_nilconst (A B : Ty) (w : Value B⋆) :
    dotL w (toUnit A ⨟ nilT B) ≡ₜ (toUnit A ⨟ w) := by
  calc ((unitL A ⨟ prodF w (toUnit A ⨟ nilT B)) ⨟ binconcat B)
      ≡ₜ (unitL A ⨟ (prodF w (toUnit A ⨟ nilT B) ⨟ binconcat B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitL A ⨟ (fst Ty.unit A ⨟ w)) := PEq.compR _ (prodF_nilconst_binconcat w)
    _ ≡ₜ ((unitL A ⨟ fst Ty.unit A) ⨟ w) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (toUnit A ⨟ w) :=
        PEq.compL _ (PEq.unit_unique (unitL A ⨟ fst Ty.unit A) (toUnit A))

/-- Conjugacy is preserved by precomposition. -/
theorem conj_precomp {X Y B : Ty} (p : Term X Y) (F G : Term Y B⋆) (w : Value B⋆)
    (h : dotR F w ≡ₜ dotL w G) : dotR (p ⨟ F) w ≡ₜ dotL w (p ⨟ G) := by
  calc dotR (p ⨟ F) w ≡ₜ ((p ⨟ F) ⨟ dotR (Term.id B⋆) w) := dotR_eq_comp _ _
    _ ≡ₜ (p ⨟ (F ⨟ dotR (Term.id B⋆) w)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (p ⨟ dotR F w) := PEq.compR _ (PEq.symm (dotR_eq_comp _ _))
    _ ≡ₜ (p ⨟ dotL w G) := PEq.compR _ h
    _ ≡ₜ (p ⨟ (G ⨟ dotL w (Term.id B⋆))) := PEq.compR _ (dotL_eq_comp _ _)
    _ ≡ₜ ((p ⨟ G) ⨟ dotL w (Term.id B⋆)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ dotL w (p ⨟ G) := PEq.symm (dotL_eq_comp _ _)

/-- Conjugacy of two homomorphisms is inherited from conjugacy of two homomorphisms they
factor through. -/
theorem conj_of_factor {X Y B : Ty} (p : Term X Y) (F G : Term X B⋆) (F' G' : Term Y B⋆)
    (w : Value B⋆) (hF : F ≡ₜ (p ⨟ F')) (hG : G ≡ₜ (p ⨟ G'))
    (h : dotR F' w ≡ₜ dotL w G') : dotR F w ≡ₜ dotL w G := by
  calc dotR F w ≡ₜ (F ⨟ dotR (Term.id B⋆) w) := dotR_eq_comp _ _
    _ ≡ₜ ((p ⨟ F') ⨟ dotR (Term.id B⋆) w) := PEq.compL _ hF
    _ ≡ₜ dotR (p ⨟ F') w := PEq.symm (dotR_eq_comp _ _)
    _ ≡ₜ dotL w (p ⨟ G') := conj_precomp p F' G' w h
    _ ≡ₜ ((p ⨟ G') ⨟ dotL w (Term.id B⋆)) := dotL_eq_comp _ _
    _ ≡ₜ (G ⨟ dotL w (Term.id B⋆)) := PEq.compL _ (PEq.symm hG)
    _ ≡ₜ dotL w G := PEq.symm (dotL_eq_comp _ _)

/-- Rotating a co-product before a three-fold co-pairing. -/
theorem sumRot_either {A E N C : Ty} (f : Term A C) (x : Term E C) (y : Term N C) :
    (sumRot E A N ⨟ either f (either x y)) ≡ₜ either x (either f y) := by
  refine either_ext _ _ ?_ ?_
  · calc (inl E (A ⊕' N) ⨟ (sumRot E A N ⨟ either f (either x y)))
        ≡ₜ ((inl E (A ⊕' N) ⨟ sumRot E A N) ⨟ either f (either x y)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((inl E N ⨟ inr A (E ⊕' N)) ⨟ either f (either x y)) :=
          PEq.compL _ (inl_either _ _)
      _ ≡ₜ (inl E N ⨟ (inr A (E ⊕' N) ⨟ either f (either x y))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inl E N ⨟ either x y) := PEq.compR _ (inr_either _ _)
      _ ≡ₜ x := inl_either _ _
      _ ≡ₜ (inl E (A ⊕' N) ⨟ either x (either f y)) := PEq.symm (inl_either _ _)
  · refine either_ext _ _ ?_ ?_
    · calc (inl A N ⨟ (inr E (A ⊕' N) ⨟ (sumRot E A N ⨟ either f (either x y))))
          ≡ₜ ((inl A N ⨟ inr E (A ⊕' N)) ⨟ (sumRot E A N ⨟ either f (either x y))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (((inl A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N) ⨟ either f (either x y)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inl A N ⨟ (inr E (A ⊕' N) ⨟ sumRot E A N)) ⨟ either f (either x y)) :=
            PEq.compL _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inl A N ⨟ either (inl A (E ⊕' N)) (inr E N ⨟ inr A (E ⊕' N))) ⨟
              either f (either x y)) := PEq.compL _ (PEq.compR _ (inr_either _ _))
        _ ≡ₜ (inl A (E ⊕' N) ⨟ either f (either x y)) := PEq.compL _ (inl_either _ _)
        _ ≡ₜ f := inl_either _ _
        _ ≡ₜ (inl A N ⨟ either f y) := PEq.symm (inl_either _ _)
        _ ≡ₜ (inl A N ⨟ (inr E (A ⊕' N) ⨟ either x (either f y))) :=
            PEq.compR _ (PEq.symm (inr_either _ _))
    · calc (inr A N ⨟ (inr E (A ⊕' N) ⨟ (sumRot E A N ⨟ either f (either x y))))
          ≡ₜ ((inr A N ⨟ inr E (A ⊕' N)) ⨟ (sumRot E A N ⨟ either f (either x y))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (((inr A N ⨟ inr E (A ⊕' N)) ⨟ sumRot E A N) ⨟ either f (either x y)) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inr A N ⨟ (inr E (A ⊕' N) ⨟ sumRot E A N)) ⨟ either f (either x y)) :=
            PEq.compL _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inr A N ⨟ either (inl A (E ⊕' N)) (inr E N ⨟ inr A (E ⊕' N))) ⨟
              either f (either x y)) := PEq.compL _ (PEq.compR _ (inr_either _ _))
        _ ≡ₜ ((inr E N ⨟ inr A (E ⊕' N)) ⨟ either f (either x y)) :=
            PEq.compL _ (inr_either _ _)
        _ ≡ₜ (inr E N ⨟ (inr A (E ⊕' N) ⨟ either f (either x y))) := PEq.comp_assoc _ _ _
        _ ≡ₜ (inr E N ⨟ either x y) := PEq.compR _ (inr_either _ _)
        _ ≡ₜ y := inr_either _ _
        _ ≡ₜ (inr A N ⨟ either f y) := PEq.symm (inr_either _ _)
        _ ≡ₜ (inr A N ⨟ (inr E (A ⊕' N) ⨟ either x (either f y))) :=
            PEq.compR _ (PEq.symm (inr_either _ _))

/-- Re-associating a co-product before a three-fold co-pairing. -/
theorem sumAssocR_either {A E N C : Ty} (f : Term A C) (x : Term E C) (y : Term N C) :
    (sumAssocR A E N ⨟ either f (either x y)) ≡ₜ either (either f x) y := by
  refine either_ext _ _ ?_ ?_
  · refine either_ext _ _ ?_ ?_
    · calc (inl A E ⨟ (inl (A ⊕' E) N ⨟ (sumAssocR A E N ⨟ either f (either x y))))
          ≡ₜ (((inl A E ⨟ inl (A ⊕' E) N) ⨟ sumAssocR A E N) ⨟ either f (either x y)) := by
            calc (inl A E ⨟ (inl (A ⊕' E) N ⨟ (sumAssocR A E N ⨟ either f (either x y))))
                ≡ₜ ((inl A E ⨟ inl (A ⊕' E) N) ⨟
                    (sumAssocR A E N ⨟ either f (either x y))) :=
                  PEq.symm (PEq.comp_assoc _ _ _)
              _ ≡ₜ (((inl A E ⨟ inl (A ⊕' E) N) ⨟ sumAssocR A E N) ⨟
                    either f (either x y)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inl A E ⨟ (inl (A ⊕' E) N ⨟ sumAssocR A E N)) ⨟ either f (either x y)) :=
            PEq.compL _ (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inl A E ⨟ either (inl A (E ⊕' N)) (inl E N ⨟ inr A (E ⊕' N))) ⨟
              either f (either x y)) := PEq.compL _ (PEq.compR _ (inl_either _ _))
        _ ≡ₜ (inl A (E ⊕' N) ⨟ either f (either x y)) := PEq.compL _ (inl_either _ _)
        _ ≡ₜ f := inl_either _ _
        _ ≡ₜ (inl A E ⨟ either f x) := PEq.symm (inl_either _ _)
        _ ≡ₜ (inl A E ⨟ (inl (A ⊕' E) N ⨟ either (either f x) y)) :=
            PEq.compR _ (PEq.symm (inl_either _ _))
    · calc (inr A E ⨟ (inl (A ⊕' E) N ⨟ (sumAssocR A E N ⨟ either f (either x y))))
          ≡ₜ ((inr A E ⨟ (inl (A ⊕' E) N ⨟ sumAssocR A E N)) ⨟ either f (either x y)) := by
            calc (inr A E ⨟ (inl (A ⊕' E) N ⨟ (sumAssocR A E N ⨟ either f (either x y))))
                ≡ₜ (inr A E ⨟ ((inl (A ⊕' E) N ⨟ sumAssocR A E N) ⨟
                    either f (either x y))) :=
                  PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
              _ ≡ₜ ((inr A E ⨟ (inl (A ⊕' E) N ⨟ sumAssocR A E N)) ⨟
                    either f (either x y)) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((inr A E ⨟ either (inl A (E ⊕' N)) (inl E N ⨟ inr A (E ⊕' N))) ⨟
              either f (either x y)) := PEq.compL _ (PEq.compR _ (inl_either _ _))
        _ ≡ₜ ((inl E N ⨟ inr A (E ⊕' N)) ⨟ either f (either x y)) :=
            PEq.compL _ (inr_either _ _)
        _ ≡ₜ (inl E N ⨟ (inr A (E ⊕' N) ⨟ either f (either x y))) := PEq.comp_assoc _ _ _
        _ ≡ₜ (inl E N ⨟ either x y) := PEq.compR _ (inr_either _ _)
        _ ≡ₜ x := inl_either _ _
        _ ≡ₜ (inr A E ⨟ either f x) := PEq.symm (inr_either _ _)
        _ ≡ₜ (inr A E ⨟ (inl (A ⊕' E) N ⨟ either (either f x) y)) :=
            PEq.compR _ (PEq.symm (inl_either _ _))
  · calc (inr (A ⊕' E) N ⨟ (sumAssocR A E N ⨟ either f (either x y)))
        ≡ₜ ((inr (A ⊕' E) N ⨟ sumAssocR A E N) ⨟ either f (either x y)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((inr E N ⨟ inr A (E ⊕' N)) ⨟ either f (either x y)) :=
          PEq.compL _ (inr_either _ _)
      _ ≡ₜ (inr E N ⨟ (inr A (E ⊕' N) ⨟ either f (either x y))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (inr E N ⨟ either x y) := PEq.compR _ (inr_either _ _)
      _ ≡ₜ y := inr_either _ _
      _ ≡ₜ (inr (A ⊕' E) N ⨟ either (either f x) y) := PEq.symm (inr_either _ _)

end Term

/-- The type of the co-pairing after the empty summands have been separated: the co-product
of the empty part, if there is one, with the nonempty part. -/
def optSum : Option Ty → Ty → Ty
  | none, N => N
  | some E, N => E ⊕' N

/-- The co-pairing on `optSum E N` whose empty part is the empty constant. -/
def optNilCase {B : Ty} : (E : Option Ty) → (N : Ty) → Term N B⋆ → Term (optSum E N) B⋆
  | none, _, f => f
  | some E, _, f => Term.either (Term.toUnit E ⨟ Term.nilT B) f

/-- The co-projection of the nonempty part into `optSum E N`. -/
def optInj : (E : Option Ty) → (N : Ty) → Term N (optSum E N)
  | none, N => Term.id N
  | some E, N => Term.inr E N

/-- The co-projection of the nonempty part cancels the empty part. -/
theorem optInj_optNilCase {B : Ty} (E : Option Ty) (N : Ty) (f : Term N B⋆) :
    (optInj E N ⨟ optNilCase E N f) ≡ₜ f := by
  cases E with
  | none => exact PEq.id_comp f
  | some E => exact Term.inr_either _ _

/-- **Claim 6.6.**  If the input type is decomposed as `E + N`, where the case `f_E` on `E`
is the empty constant, then `hom f` factors through `hom f_N`. -/
theorem hom_factors {B E N : Ty} (fE : Term E B⋆) (fN : Term N B⋆)
    (hfE : fE ≡ₜ toUnit E ⨟ nilT B) :
    homT (Term.either fE fN) ≡ₜ
      (block E N ⨟ snd E⋆ ((N ⊗ E⋆)⋆) ⨟ listF (fst N E⋆) ⨟ homT fN) := by
  set f : Term (E ⊕' N) B⋆ := Term.either fE fN with hf
  -- the empty case contributes nothing
  have hE : homT (Term.inl E N ⨟ f) ≡ₜ (toUnit E⋆ ⨟ nilT B) :=
    (Term.homT_congr ((Term.inl_either fE fN).trans hfE)).trans (Term.homT_nilconst E B)
  have hN : (Term.inr E N ⨟ f) ≡ₜ fN := Term.inr_either fE fN
  -- the middle face of the diagram
  have hmid : ((Term.inr E N ⨟ f) ⊙ homT (Term.inl E N ⨟ f)) ≡ₜ (fst N E⋆ ⨟ fN) :=
    (Term.fdot_congr hN hE).trans (Term.prodF_nilconst_binconcat fN)
  -- the lowermost face of the diagram
  have hlow : (homT (Term.inl E N ⨟ f) ⊙ homT (fst N E⋆ ⨟ fN)) ≡ₜ
      (snd E⋆ ((N ⊗ E⋆)⋆) ⨟ (listF (fst N E⋆) ⨟ homT fN)) := by
    refine (Term.fdot_congr hE (PEq.refl _)).trans ?_
    refine (Term.prodF_nilconst_binconcat_left (homT (fst N E⋆ ⨟ fN))).trans ?_
    exact PEq.compR _ (Term.homT_precomp (fst N E⋆) fN)
  -- the uppermost face of the diagram is naturality of `block`
  calc homT f ≡ₜ (Term.id ((E ⊕' N)⋆) ⨟ homT f) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((block E N ⨟ unblock E N) ⨟ homT f) :=
        PEq.compL _ (PEq.symm (PEq.block_unblock E N))
    _ ≡ₜ (block E N ⨟ (unblock E N ⨟ homT f)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (block E N ⨟ (homT (Term.inl E N ⨟ f) ⊙
          homT ((Term.inr E N ⨟ f) ⊙ homT (Term.inl E N ⨟ f)))) :=
        PEq.compR _ (Term.unblock_comp_homT f)
    _ ≡ₜ (block E N ⨟ (homT (Term.inl E N ⨟ f) ⊙ homT (fst N E⋆ ⨟ fN))) :=
        PEq.compR _ (Term.fdot_congr (PEq.refl _) (Term.homT_congr hmid))
    _ ≡ₜ (block E N ⨟ (snd E⋆ ((N ⊗ E⋆)⋆) ⨟ (listF (fst N E⋆) ⨟ homT fN))) :=
        PEq.compR _ hlow
    _ ≡ₜ ((block E N ⨟ snd E⋆ ((N ⊗ E⋆)⋆)) ⨟ (listF (fst N E⋆) ⨟ homT fN)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((block E N ⨟ snd E⋆ ((N ⊗ E⋆)⋆)) ⨟ listF (fst N E⋆)) ⨟ homT fN) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-! ### Extracting the values of the short cases (the appendix lemma behind Lemma 6.4) -/

/-- The list nesting depth of a co-product of a list of types. -/
theorem sumTyOf_listDepth_le {n : ℕ} : (C₀ : Ty) → (Cs : List Ty) → C₀.listDepth ≤ n →
    (∀ C ∈ Cs, Ty.listDepth C ≤ n) → (sumTyOf C₀ Cs).listDepth ≤ n
  | _, [], h, _ => h
  | C₀, (C :: Cs), h, hCs => by
      have := sumTyOf_listDepth_le C Cs (hCs C (by simp)) (fun C' hC' => hCs C' (by simp [hC']))
      simp only [sumTyOf, Ty.listDepth, max_le_iff]
      exact ⟨h, this⟩

/-! ### Separating the empty summands (the proof of Lemma 6.5) -/

/-- If two terms always produce outputs of the same length, then one of them never produces
the empty list as soon as the other one does not. -/
theorem nonempty_transfer {A B : Ty} {f g : Term A B⋆}
    (hlen : ∀ x : ⟦A⟧, (f.den x).length = (g.den x).length) (hf : NonemptyOutput f) :
    NonemptyOutput g := by
  intro x hx
  refine hf x ?_
  have h := hlen x
  rw [hx] at h
  simpa using h

/-- If two terms always produce outputs of the same length and one of them always produces
the empty list, then so does the other one. -/
theorem empty_transfer {A B : Ty} {f g : Term A B⋆}
    (hlen : ∀ x : ⟦A⟧, (f.den x).length = (g.den x).length) (hf : ∀ x : ⟦A⟧, f.den x = []) :
    ∀ x : ⟦A⟧, g.den x = [] := by
  intro x
  have h := hlen x
  rw [hf x] at h
  simpa using h.symm

/-- **The dichotomy for `k`-guarded terms.**  For `k > 0`, a `k`-guarded term either never
produces the empty list, or it is provably the empty constant (and then always produces the
empty list): a long term produces at least `k` letters, and a constant term is provably the
empty constant as soon as its value is the empty list, by the normalisation of values. -/
theorem kguarded_dichotomy {A B : Ty} {k : ℕ} (hk : 0 < k) {f : Term A B⋆}
    (hf : KGuarded k B f) :
    NonemptyOutput f ∨ ((f ≡ₜ (toUnit A ⨟ nilT B)) ∧ ∀ x : ⟦A⟧, f.den x = []) := by
  rcases hf with ⟨v, rfl⟩ | ⟨u, v, h, -, -, hv, rfl⟩
  · by_cases hvz : v.den () = []
    · refine Or.inr ⟨PEq.compR _ ?_, ?_⟩
      · have hc := computes v ()
        rw [hvz] at hc
        simpa using (PEq.symm (PEq.id_comp v)).trans hc
      · intro x; simpa using hvz
    · refine Or.inl ?_
      intro x hx
      exact hvz (by simpa using hx)
  · refine Or.inl ?_
    intro x hx
    have h1 : ((Term.dotR (Term.dotL u h) v).den x).length = 0 := by rw [hx]; rfl
    have h2 : ((Term.dotR (Term.dotL u h) v).den x).length =
        (u.den ()).length + (h.den x).length + (v.den ()).length := by
      simp [List.length_append]
      omega
    have h3 : (v.den ()).length = k := hv
    omega

/-- **The splitting of a co-pairing into its empty and its nonempty summands.**  Let `f` and
`g` be co-pairings of `k`-guarded terms which produce outputs of the same length.  Then
either both of them are provably the empty constant, or the input type is provably isomorphic
to a co-product `E + N`, in which `N` is again a co-product of summands of the original type
and both `f` and `g` restrict on `E` to the empty constant and on `N` to co-pairings of
`k`-guarded terms that never produce the empty list. -/
theorem empty_split {B : Ty} {k : ℕ} (hk : 0 < k) :
    ∀ (As : List Ty) (A₀ : Ty) (f₀ g₀ : Term A₀ B⋆) (fs gs : Cases B⋆ As),
      KGuarded k B f₀ → KGuarded k B g₀ →
      fs.All (fun _ f => KGuarded k B f) → gs.All (fun _ g => KGuarded k B g) →
      (∀ x : ⟦sumTyOf A₀ As⟧,
          ((copair f₀ fs).den x).length = ((copair g₀ gs).den x).length) →
      ((copair f₀ fs ≡ₜ (toUnit (sumTyOf A₀ As) ⨟ nilT B)) ∧
          (copair g₀ gs ≡ₜ (toUnit (sumTyOf A₀ As) ⨟ nilT B))) ∨
      (∃ (E : Option Ty) (A₀' : Ty) (As' : List Ty) (f₀' g₀' : Term A₀' B⋆)
          (fs' gs' : Cases B⋆ As')
          (r : Term (sumTyOf A₀ As) (optSum E (sumTyOf A₀' As')))
          (r' : Term (optSum E (sumTyOf A₀' As')) (sumTyOf A₀ As)),
        (sumTyOf A₀' As').listDepth ≤ (sumTyOf A₀ As).listDepth ∧
        (r ⨟ r') ≡ₜ Term.id (sumTyOf A₀ As) ∧
        KGuarded k B f₀' ∧ KGuarded k B g₀' ∧
        fs'.All (fun _ f => KGuarded k B f) ∧ gs'.All (fun _ g => KGuarded k B g) ∧
        NonemptyOutput f₀' ∧ NonemptyOutput g₀' ∧
        fs'.All (fun _ f => NonemptyOutput f) ∧ gs'.All (fun _ g => NonemptyOutput g) ∧
        ((r' ⨟ copair f₀ fs) ≡ₜ optNilCase E (sumTyOf A₀' As') (copair f₀' fs')) ∧
        ((r' ⨟ copair g₀ gs) ≡ₜ optNilCase E (sumTyOf A₀' As') (copair g₀' gs'))) := by
  intro As
  induction As with
  | nil =>
      intro A₀ f₀ g₀ fs gs hf₀ hg₀ _ _ hlen
      match fs, gs with
      | Cases.nil, Cases.nil =>
      have hcp : copair f₀ (Cases.nil (B := B⋆)) = f₀ := rfl
      have hcq : copair g₀ (Cases.nil (B := B⋆)) = g₀ := rfl
      rw [hcp, hcq] at hlen ⊢
      have hlen' : ∀ x : ⟦A₀⟧, (f₀.den x).length = (g₀.den x).length := hlen
      rcases kguarded_dichotomy hk hf₀ with hne | ⟨hfe, hfz⟩
      · refine Or.inr ⟨none, A₀, [], f₀, g₀, Cases.nil, Cases.nil, Term.id A₀, Term.id A₀,
          le_rfl, PEq.comp_id _, hf₀, hg₀, trivial, trivial, hne, nonempty_transfer hlen' hne,
          trivial, trivial, PEq.id_comp _, PEq.id_comp _⟩
      · have hgz := empty_transfer hlen' hfz
        have hge : g₀ ≡ₜ (toUnit A₀ ⨟ nilT B) := by
          rcases kguarded_dichotomy hk hg₀ with hne | ⟨hge, -⟩
          · exact absurd (hgz (Ty.someElem A₀)) (hne _)
          · exact hge
        exact Or.inl ⟨hfe, hge⟩
  | cons A₁ As₁ ih =>
      intro A₀ f₀ g₀ fs gs hf₀ hg₀ hfs hgs hlen
      match fs, gs with
      | Cases.cons f₁ fs₁, Cases.cons g₁ gs₁ =>
      obtain ⟨hf₁, hfs₁⟩ := hfs
      obtain ⟨hg₁, hgs₁⟩ := hgs
      set Rest : Ty := sumTyOf A₁ As₁ with hRest
      set fR : Term Rest B⋆ := copair f₁ fs₁ with hfR
      set gR : Term Rest B⋆ := copair g₁ gs₁ with hgR
      have hlenE : ∀ x : ⟦A₀ ⊕' Rest⟧,
          ((Term.either f₀ fR).den x).length = ((Term.either g₀ gR).den x).length := hlen
      have hlenL : ∀ x : ⟦A₀⟧, (f₀.den x).length = (g₀.den x).length := by
        intro x; simpa using hlenE (Sum.inl x)
      have hlenR : ∀ y : ⟦Rest⟧, (fR.den y).length = (gR.den y).length := by
        intro y; simpa using hlenE (Sum.inr y)
      have hcp : copair f₀ (Cases.cons f₁ fs₁) = Term.either f₀ fR := rfl
      have hcq : copair g₀ (Cases.cons g₁ gs₁) = Term.either g₀ gR := rfl
      rw [hcp, hcq]
      rcases ih A₁ f₁ g₁ fs₁ gs₁ hf₁ hg₁ hfs₁ hgs₁ hlenR with
        ⟨hfRe, hgRe⟩ |
        ⟨E₁, A₀'', As'', f₀'', g₀'', fs'', gs'', r₁, r₁', hd'', hrr₁, hkf'', hkg'', hkfs'',
          hkgs'', hnf'', hng'', hnfs'', hngs'', heqf'', heqg''⟩
      · -- every summand of the tail is empty
        rcases kguarded_dichotomy hk hf₀ with hne | ⟨hfe, hfz⟩
        · -- the head is nonempty: it becomes the only nonempty summand
          have hgne : NonemptyOutput g₀ := nonempty_transfer hlenL hne
          refine Or.inr ⟨some Rest, A₀, [], f₀, g₀, Cases.nil, Cases.nil,
            Term.comm A₀ Rest, Term.comm Rest A₀,
            by simp only [sumTyOf, Ty.listDepth]; omega,
            Term.comm_comm A₀ Rest,
            hf₀, hg₀, trivial, trivial, hne, hgne, trivial, trivial, ?_, ?_⟩
          · calc (Term.comm Rest A₀ ⨟ Term.either f₀ fR)
                ≡ₜ Term.either (Term.inr A₀ Rest ⨟ Term.either f₀ fR)
                    (Term.inl A₀ Rest ⨟ Term.either f₀ fR) := Term.either_comp _ _ _
              _ ≡ₜ Term.either fR f₀ :=
                  Term.either_congr (Term.inr_either _ _) (Term.inl_either _ _)
              _ ≡ₜ Term.either (toUnit Rest ⨟ nilT B) f₀ :=
                  Term.either_congr hfRe (PEq.refl _)
          · calc (Term.comm Rest A₀ ⨟ Term.either g₀ gR)
                ≡ₜ Term.either (Term.inr A₀ Rest ⨟ Term.either g₀ gR)
                    (Term.inl A₀ Rest ⨟ Term.either g₀ gR) := Term.either_comp _ _ _
              _ ≡ₜ Term.either gR g₀ :=
                  Term.either_congr (Term.inr_either _ _) (Term.inl_either _ _)
              _ ≡ₜ Term.either (toUnit Rest ⨟ nilT B) g₀ :=
                  Term.either_congr hgRe (PEq.refl _)
        · -- everything is empty
          have hgz := empty_transfer hlenL hfz
          have hge : g₀ ≡ₜ (toUnit A₀ ⨟ nilT B) := by
            rcases kguarded_dichotomy hk hg₀ with hne | ⟨hge, -⟩
            · exact absurd (hgz (Ty.someElem A₀)) (hne _)
            · exact hge
          refine Or.inl ⟨?_, ?_⟩
          · exact (Term.either_congr hfe hfRe).trans (Term.either_nilconst A₀ Rest B)
          · exact (Term.either_congr hge hgRe).trans (Term.either_nilconst A₀ Rest B)
      · -- the tail has nonempty summands
        rcases kguarded_dichotomy hk hf₀ with hne | ⟨hfe, hfz⟩
        · -- the head is nonempty and is prepended to the nonempty part
          have hgne : NonemptyOutput g₀ := nonempty_transfer hlenL hne
          cases E₁ with
          | none =>
              refine Or.inr ⟨none, A₀, A₀'' :: As'', f₀, g₀, Cases.cons f₀'' fs'',
                Cases.cons g₀'' gs'', Term.sumF (Term.id A₀) r₁, Term.sumF (Term.id A₀) r₁',
                by simp only [sumTyOf, Ty.listDepth] at hd'' ⊢; omega, ?_, hf₀, hg₀, ⟨hkf'', hkfs''⟩, ⟨hkg'', hkgs''⟩, hne, hgne,
                ⟨hnf'', hnfs''⟩, ⟨hng'', hngs''⟩, ?_, ?_⟩
              · exact (PEq.sum_comp _ _ _ _).trans
                  ((PEq.congr_sumF (PEq.comp_id _) hrr₁).trans (PEq.sum_id A₀ Rest))
              · exact (Term.sumF_either _ _ _ _).trans
                  (Term.either_congr (PEq.id_comp _) heqf'')
              · exact (Term.sumF_either _ _ _ _).trans
                  (Term.either_congr (PEq.id_comp _) heqg'')
          | some E =>
              refine Or.inr ⟨some E, A₀, A₀'' :: As'', f₀, g₀, Cases.cons f₀'' fs'',
                Cases.cons g₀'' gs'',
                Term.sumF (Term.id A₀) r₁ ⨟ Term.sumRot A₀ E (sumTyOf A₀'' As''),
                Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟ Term.sumF (Term.id A₀) r₁',
                by simp only [sumTyOf, Ty.listDepth] at hd'' ⊢; omega, ?_, hf₀, hg₀, ⟨hkf'', hkfs''⟩, ⟨hkg'', hkgs''⟩, hne, hgne,
                ⟨hnf'', hnfs''⟩, ⟨hng'', hngs''⟩, ?_, ?_⟩
              · calc ((Term.sumF (Term.id A₀) r₁ ⨟ Term.sumRot A₀ E (sumTyOf A₀'' As'')) ⨟
                      (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟ Term.sumF (Term.id A₀) r₁'))
                    ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟ (Term.sumRot A₀ E (sumTyOf A₀'' As'') ⨟
                        (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟
                          Term.sumF (Term.id A₀) r₁'))) := PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟
                        ((Term.sumRot A₀ E (sumTyOf A₀'' As'') ⨟
                          Term.sumRot E A₀ (sumTyOf A₀'' As'')) ⨟
                          Term.sumF (Term.id A₀) r₁')) :=
                      PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
                  _ ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟
                        (Term.id (A₀ ⊕' (E ⊕' sumTyOf A₀'' As'')) ⨟
                          Term.sumF (Term.id A₀) r₁')) :=
                      PEq.compR _ (PEq.compL _ (Term.sumRot_sumRot _ _ _))
                  _ ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟ Term.sumF (Term.id A₀) r₁') :=
                      PEq.compR _ (PEq.id_comp _)
                  _ ≡ₜ Term.sumF (Term.id A₀ ⨟ Term.id A₀) (r₁ ⨟ r₁') :=
                      PEq.sum_comp _ _ _ _
                  _ ≡ₜ Term.sumF (Term.id A₀) (Term.id Rest) :=
                      PEq.congr_sumF (PEq.comp_id _) hrr₁
                  _ ≡ₜ Term.id (A₀ ⊕' Rest) := PEq.sum_id A₀ Rest
              · calc ((Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟ Term.sumF (Term.id A₀) r₁') ⨟
                      Term.either f₀ fR)
                    ≡ₜ (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟
                        (Term.sumF (Term.id A₀) r₁' ⨟ Term.either f₀ fR)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟
                        Term.either (Term.id A₀ ⨟ f₀) (r₁' ⨟ fR)) :=
                      PEq.compR _ (Term.sumF_either _ _ _ _)
                  _ ≡ₜ (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟
                        Term.either f₀ (Term.either (toUnit E ⨟ nilT B)
                          (copair f₀'' fs''))) :=
                      PEq.compR _ (Term.either_congr (PEq.id_comp _) heqf'')
                  _ ≡ₜ Term.either (toUnit E ⨟ nilT B)
                        (Term.either f₀ (copair f₀'' fs'')) :=
                      Term.sumRot_either _ _ _
              · calc ((Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟ Term.sumF (Term.id A₀) r₁') ⨟
                      Term.either g₀ gR)
                    ≡ₜ (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟
                        (Term.sumF (Term.id A₀) r₁' ⨟ Term.either g₀ gR)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟
                        Term.either (Term.id A₀ ⨟ g₀) (r₁' ⨟ gR)) :=
                      PEq.compR _ (Term.sumF_either _ _ _ _)
                  _ ≡ₜ (Term.sumRot E A₀ (sumTyOf A₀'' As'') ⨟
                        Term.either g₀ (Term.either (toUnit E ⨟ nilT B)
                          (copair g₀'' gs''))) :=
                      PEq.compR _ (Term.either_congr (PEq.id_comp _) heqg'')
                  _ ≡ₜ Term.either (toUnit E ⨟ nilT B)
                        (Term.either g₀ (copair g₀'' gs'')) :=
                      Term.sumRot_either _ _ _
        · -- the head is empty and joins the empty part
          have hgz := empty_transfer hlenL hfz
          have hge : g₀ ≡ₜ (toUnit A₀ ⨟ nilT B) := by
            rcases kguarded_dichotomy hk hg₀ with hne | ⟨hge, -⟩
            · exact absurd (hgz (Ty.someElem A₀)) (hne _)
            · exact hge
          cases E₁ with
          | none =>
              refine Or.inr ⟨some A₀, A₀'', As'', f₀'', g₀'', fs'', gs'',
                Term.sumF (Term.id A₀) r₁, Term.sumF (Term.id A₀) r₁',
                by simp only [sumTyOf, Ty.listDepth] at hd'' ⊢; omega, ?_, hkf'', hkg'', hkfs'', hkgs'', hnf'', hng'', hnfs'', hngs'', ?_, ?_⟩
              · exact (PEq.sum_comp _ _ _ _).trans
                  ((PEq.congr_sumF (PEq.comp_id _) hrr₁).trans (PEq.sum_id A₀ Rest))
              · exact (Term.sumF_either _ _ _ _).trans
                  (Term.either_congr ((PEq.id_comp _).trans hfe) heqf'')
              · exact (Term.sumF_either _ _ _ _).trans
                  (Term.either_congr ((PEq.id_comp _).trans hge) heqg'')
          | some E =>
              refine Or.inr ⟨some (A₀ ⊕' E), A₀'', As'', f₀'', g₀'', fs'', gs'',
                Term.sumF (Term.id A₀) r₁ ⨟ Term.sumAssocL A₀ E (sumTyOf A₀'' As''),
                Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟ Term.sumF (Term.id A₀) r₁',
                by simp only [sumTyOf, Ty.listDepth] at hd'' ⊢; omega, ?_, hkf'', hkg'', hkfs'', hkgs'', hnf'', hng'', hnfs'', hngs'', ?_, ?_⟩
              · calc ((Term.sumF (Term.id A₀) r₁ ⨟ Term.sumAssocL A₀ E (sumTyOf A₀'' As'')) ⨟
                      (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                        Term.sumF (Term.id A₀) r₁'))
                    ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟
                        (Term.sumAssocL A₀ E (sumTyOf A₀'' As'') ⨟
                          (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                            Term.sumF (Term.id A₀) r₁'))) := PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟
                        ((Term.sumAssocL A₀ E (sumTyOf A₀'' As'') ⨟
                          Term.sumAssocR A₀ E (sumTyOf A₀'' As'')) ⨟
                          Term.sumF (Term.id A₀) r₁')) :=
                      PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
                  _ ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟
                        (Term.id (A₀ ⊕' (E ⊕' sumTyOf A₀'' As'')) ⨟
                          Term.sumF (Term.id A₀) r₁')) :=
                      PEq.compR _ (PEq.compL _ (Term.sumAssocL_sumAssocR _ _ _))
                  _ ≡ₜ (Term.sumF (Term.id A₀) r₁ ⨟ Term.sumF (Term.id A₀) r₁') :=
                      PEq.compR _ (PEq.id_comp _)
                  _ ≡ₜ Term.sumF (Term.id A₀ ⨟ Term.id A₀) (r₁ ⨟ r₁') :=
                      PEq.sum_comp _ _ _ _
                  _ ≡ₜ Term.sumF (Term.id A₀) (Term.id Rest) :=
                      PEq.congr_sumF (PEq.comp_id _) hrr₁
                  _ ≡ₜ Term.id (A₀ ⊕' Rest) := PEq.sum_id A₀ Rest
              · calc ((Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                      Term.sumF (Term.id A₀) r₁') ⨟ Term.either f₀ fR)
                    ≡ₜ (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                        (Term.sumF (Term.id A₀) r₁' ⨟ Term.either f₀ fR)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                        Term.either (Term.id A₀ ⨟ f₀) (r₁' ⨟ fR)) :=
                      PEq.compR _ (Term.sumF_either _ _ _ _)
                  _ ≡ₜ (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                        Term.either (toUnit A₀ ⨟ nilT B)
                          (Term.either (toUnit E ⨟ nilT B) (copair f₀'' fs''))) :=
                      PEq.compR _ (Term.either_congr ((PEq.id_comp _).trans hfe) heqf'')
                  _ ≡ₜ Term.either (Term.either (toUnit A₀ ⨟ nilT B) (toUnit E ⨟ nilT B))
                        (copair f₀'' fs'') := Term.sumAssocR_either _ _ _
                  _ ≡ₜ Term.either (toUnit (A₀ ⊕' E) ⨟ nilT B) (copair f₀'' fs'') :=
                      Term.either_congr (Term.either_nilconst A₀ E B) (PEq.refl _)
              · calc ((Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                      Term.sumF (Term.id A₀) r₁') ⨟ Term.either g₀ gR)
                    ≡ₜ (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                        (Term.sumF (Term.id A₀) r₁' ⨟ Term.either g₀ gR)) :=
                      PEq.comp_assoc _ _ _
                  _ ≡ₜ (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                        Term.either (Term.id A₀ ⨟ g₀) (r₁' ⨟ gR)) :=
                      PEq.compR _ (Term.sumF_either _ _ _ _)
                  _ ≡ₜ (Term.sumAssocR A₀ E (sumTyOf A₀'' As'') ⨟
                        Term.either (toUnit A₀ ⨟ nilT B)
                          (Term.either (toUnit E ⨟ nilT B) (copair g₀'' gs''))) :=
                      PEq.compR _ (Term.either_congr ((PEq.id_comp _).trans hge) heqg'')
                  _ ≡ₜ Term.either (Term.either (toUnit A₀ ⨟ nilT B) (toUnit E ⨟ nilT B))
                        (copair g₀'' gs'') := Term.sumAssocR_either _ _ _
                  _ ≡ₜ Term.either (toUnit (A₀ ⊕' E) ⨟ nilT B) (copair g₀'' gs'') :=
                      Term.either_congr (Term.either_nilconst A₀ E B) (PEq.refl _)

/-- The map that erases the empty part of a co-product from a list. -/
def optDrop : (E : Option Ty) → (N : Ty) → Term ((optSum E N)⋆) (N⋆)
  | none, N => Term.id (N⋆)
  | some E, N => (Term.block E N ⨟ Term.snd E⋆ ((N ⊗ E⋆)⋆)) ⨟ Term.listF (Term.fst N E⋆)

/-- A homomorphism whose empty part is the empty constant factors through the homomorphism of
its nonempty part; this is Claim 6.6, taken as the hypothesis `h66`, read through
`optNilCase`. -/
theorem homT_optNilCase (h66 : type_of% @Lax149335.EmptySummands.hom_factors) {B : Ty}
    (E : Option Ty) (N : Ty) (F : Term N B⋆) :
    homT (optNilCase E N F) ≡ₜ (optDrop E N ⨟ homT F) := by
  cases E with
  | none => exact PEq.symm (PEq.id_comp _)
  | some E => exact h66 (toUnit E ⨟ nilT B) F (PEq.refl _)

/-- **Lemma 6.5.**  One can further assume without loss of generality that all the summands
`fᵢ` and `gᵢ` are nonempty.

The proof splits the input type into the summands on which both terms produce the empty list
and the remaining ones (`Lax149335Proofs.empty_split`), and then removes the first group with
Claim 6.6.  The assumption that `B` is a finite alphabet is not needed and has been dropped
from the statement.

The remaining summands are summands of the original input type, so any bound `D` on the list
nesting depth of the input type is preserved; this is recorded in the statement because the
proof of Lemma 6.1 needs it.

Claim 6.6 is taken as the hypothesis `h66`; `Lax149335Proofs.wlog_nonempty` below discharges
it. -/
theorem wlog_nonempty_of (h66 : type_of% @Lax149335.EmptySummands.hom_factors) {B : Ty} (w : Value B⋆) (hw : 0 < valLength w) (D : ℕ)
    (H : ∀ (A₀ : Ty) (As : List Ty) (f₀ g₀ : Term A₀ B⋆) (fs gs : Cases B⋆ As),
      (sumTyOf A₀ As).listDepth ≤ D →
      KGuarded (valLength w) B f₀ → KGuarded (valLength w) B g₀ →
      fs.All (fun _ f => KGuarded (valLength w) B f) →
      gs.All (fun _ g => KGuarded (valLength w) B g) →
      NonemptyOutput f₀ → NonemptyOutput g₀ →
      fs.All (fun _ f => NonemptyOutput f) → gs.All (fun _ g => NonemptyOutput g) →
      dotR (copair f₀ fs) w ≡ₜ dotL w (copair g₀ gs) →
      dotR (homT (copair f₀ fs)) w ≡ₜ dotL w (homT (copair g₀ gs)))
    (A₀ : Ty) (As : List Ty) (f₀ g₀ : Term A₀ B⋆) (fs gs : Cases B⋆ As)
    (hD : (sumTyOf A₀ As).listDepth ≤ D)
    (hf₀ : KGuarded (valLength w) B f₀) (hg₀ : KGuarded (valLength w) B g₀)
    (hfs : fs.All (fun _ f => KGuarded (valLength w) B f))
    (hgs : gs.All (fun _ g => KGuarded (valLength w) B g))
    (hfg : dotR (copair f₀ fs) w ≡ₜ dotL w (copair g₀ gs)) :
    dotR (homT (copair f₀ fs)) w ≡ₜ dotL w (homT (copair g₀ gs)) := by
  -- the two terms produce outputs of the same length
  have hlen : ∀ x : ⟦sumTyOf A₀ As⟧,
      ((copair f₀ fs).den x).length = ((copair g₀ gs).den x).length := by
    intro x
    have h := congrFun (PEq.sound hfg) x
    simp only [Term.den_dotR, Term.den_dotL] at h
    have h2 := congrArg List.length h
    simp only [List.append_eq, List.length_append] at h2
    omega
  rcases empty_split hw As A₀ f₀ g₀ fs gs hf₀ hg₀ hfs hgs hlen with
    ⟨hfe, hge⟩ |
    ⟨E, A₀', As', f₀', g₀', fs', gs', r, r', hd', hrr, hkf, hkg, hkfs, hkgs, hnf, hng, hnfs,
      hngs, heqf, heqg⟩
  · -- every summand is empty: both homomorphisms are the empty constant
    have hF : homT (copair f₀ fs) ≡ₜ (toUnit (sumTyOf A₀ As)⋆ ⨟ nilT B) :=
      (Term.homT_congr hfe).trans (Term.homT_nilconst _ B)
    have hG : homT (copair g₀ gs) ≡ₜ (toUnit (sumTyOf A₀ As)⋆ ⨟ nilT B) :=
      (Term.homT_congr hge).trans (Term.homT_nilconst _ B)
    calc dotR (homT (copair f₀ fs)) w
        ≡ₜ dotR (toUnit (sumTyOf A₀ As)⋆ ⨟ nilT B) w := Term.dotR_congr hF (PEq.refl _)
      _ ≡ₜ (toUnit (sumTyOf A₀ As)⋆ ⨟ w) := Term.dotR_nilconst _ _ _
      _ ≡ₜ dotL w (toUnit (sumTyOf A₀ As)⋆ ⨟ nilT B) := PEq.symm (Term.dotL_nilconst _ _ _)
      _ ≡ₜ dotL w (homT (copair g₀ gs)) := Term.dotL_congr (PEq.refl _) (PEq.symm hG)
  · -- the empty summands are separated off and removed
    have hs : ∀ (F : Term (sumTyOf A₀ As) B⋆) (F' : Term (sumTyOf A₀' As') B⋆),
        (r' ⨟ F) ≡ₜ optNilCase E (sumTyOf A₀' As') F' →
        ((optInj E (sumTyOf A₀' As') ⨟ r') ⨟ F) ≡ₜ F' := by
      intro F F' h
      calc ((optInj E (sumTyOf A₀' As') ⨟ r') ⨟ F)
          ≡ₜ (optInj E (sumTyOf A₀' As') ⨟ (r' ⨟ F)) := PEq.comp_assoc _ _ _
        _ ≡ₜ (optInj E (sumTyOf A₀' As') ⨟ optNilCase E (sumTyOf A₀' As') F') :=
            PEq.compR _ h
        _ ≡ₜ F' := optInj_optNilCase E _ F'
    have hconj : dotR (copair f₀' fs') w ≡ₜ dotL w (copair g₀' gs') :=
      (Term.dotR_congr (PEq.symm (hs _ _ heqf)) (PEq.refl _)).trans
        ((Term.conj_precomp _ _ _ w hfg).trans (Term.dotL_congr (PEq.refl _) (hs _ _ heqg)))
    have hH := H A₀' As' f₀' g₀' fs' gs' (le_trans hd' hD) hkf hkg hkfs hkgs hnf hng hnfs
      hngs hconj
    have key : ∀ (F : Term (sumTyOf A₀ As) B⋆) (F' : Term (sumTyOf A₀' As') B⋆),
        (r' ⨟ F) ≡ₜ optNilCase E (sumTyOf A₀' As') F' →
        homT F ≡ₜ ((Term.listF r ⨟ optDrop E (sumTyOf A₀' As')) ⨟ homT F') := by
      intro F F' h
      calc homT F ≡ₜ homT (Term.id (sumTyOf A₀ As) ⨟ F) :=
            Term.homT_congr (PEq.symm (PEq.id_comp F))
        _ ≡ₜ homT ((r ⨟ r') ⨟ F) := Term.homT_congr (PEq.compL _ (PEq.symm hrr))
        _ ≡ₜ homT (r ⨟ (r' ⨟ F)) := Term.homT_congr (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.listF r ⨟ homT (r' ⨟ F)) := Term.homT_precomp _ _
        _ ≡ₜ (Term.listF r ⨟ homT (optNilCase E (sumTyOf A₀' As') F')) :=
            PEq.compR _ (Term.homT_congr h)
        _ ≡ₜ (Term.listF r ⨟ (optDrop E (sumTyOf A₀' As') ⨟ homT F')) :=
            PEq.compR _ (homT_optNilCase h66 E _ F')
        _ ≡ₜ ((Term.listF r ⨟ optDrop E (sumTyOf A₀' As')) ⨟ homT F') :=
            PEq.symm (PEq.comp_assoc _ _ _)
    exact Term.conj_of_factor _ _ _ _ _ w (key _ _ heqf) (key _ _ heqg) hH

/-- **Lemma 6.5.**  The reduction to nonempty summands. -/
theorem wlog_nonempty : type_of% @Lax149335.NonemptyReduction.wlog_nonempty :=
  wlog_nonempty_of hom_factors

end Lax149335Proofs

bridge_export Lax149335Proofs
