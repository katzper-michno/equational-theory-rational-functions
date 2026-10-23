import Lax149335Proofs.Preliminaries.Injectivity
import Lax149335Proofs.EquationalTheory.DerivedRules
import Lax149335Proofs.Appendix.ShiftOnes

/-!
# Terms over a finite alphabet

The appendix uses freely that duplication and commutativity are admissible for the letters of
a finite alphabet: this is how the auxiliary terms `repeat` and `divide` of the definition of
the unprefixing operation are built, out of the case reasoning combinators
`Lax149335Proofs.Term.caseR` and `Lax149335Proofs.Term.caseL` of `Lax149335Proofs.Terms.Derived`.

This file develops the equational toolkit for those combinators: how they compute on the
values `constFin g` that pick out a letter, and the corresponding extensionality principles,
which say that a term out of `X × Ā` (respectively `Ā × X`) is determined by its restrictions
to the letters of `Ā`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Pre-composing a pairing with a value -/

/-- Pre-composing a right pairing. -/
theorem comp_pairR {Z A B C : Ty} (f : Term Z A) (u : Term A B) (v : Value C) :
    (f ⨟ pairR u v) ≡ₜ pairR (f ⨟ u) v := by
  calc (f ⨟ (unitR A ⨟ prodF u v))
      ≡ₜ ((f ⨟ unitR A) ⨟ prodF u v) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((unitR Z ⨟ prodF f (Term.id Ty.unit)) ⨟ prodF u v) :=
        PEq.compL _ (PEq.nat_unitR f)
    _ ≡ₜ (unitR Z ⨟ (prodF f (Term.id Ty.unit) ⨟ prodF u v)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR Z ⨟ prodF (f ⨟ u) (Term.id Ty.unit ⨟ v)) := PEq.compR _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (unitR Z ⨟ prodF (f ⨟ u) v) :=
        PEq.compR _ (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _))

/-- Pre-composing a left pairing. -/
theorem comp_pairL {Z A B C : Ty} (f : Term Z A) (v : Value C) (u : Term A B) :
    (f ⨟ pairL v u) ≡ₜ pairL v (f ⨟ u) := by
  calc (f ⨟ (unitL A ⨟ prodF v u))
      ≡ₜ ((f ⨟ unitL A) ⨟ prodF v u) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((unitL Z ⨟ prodF (Term.id Ty.unit) f) ⨟ prodF v u) :=
        PEq.compL _ (PEq.nat_unitL f)
    _ ≡ₜ (unitL Z ⨟ (prodF (Term.id Ty.unit) f ⨟ prodF v u)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (unitL Z ⨟ prodF (Term.id Ty.unit ⨟ v) (f ⨟ u)) := PEq.compR _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ (unitL Z ⨟ prodF v (f ⨟ u)) :=
        PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))

/-- Congruence for left pairing. -/
theorem pairL_congr {A B C : Ty} {v v' : Value C} {f f' : Term A B}
    (hv : v ≡ₜ v') (hf : f ≡ₜ f') : pairL v f ≡ₜ pairL v' f' :=
  PEq.compR _ (PEq.congr_prodF hv hf)

/-- `(id,1)` can be cancelled on the left. -/
theorem cancel_unitR {X B : Ty} {p q : Term (X ⊗ Ty.unit) B}
    (h : (unitR X ⨟ p) ≡ₜ (unitR X ⨟ q)) : p ≡ₜ q := by
  calc p ≡ₜ (Term.id (X ⊗ Ty.unit) ⨟ p) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((fst X Ty.unit ⨟ unitR X) ⨟ p) := PEq.compL _ (PEq.symm (PEq.fst_unitR X))
    _ ≡ₜ (fst X Ty.unit ⨟ (unitR X ⨟ p)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (fst X Ty.unit ⨟ (unitR X ⨟ q)) := PEq.compR _ h
    _ ≡ₜ ((fst X Ty.unit ⨟ unitR X) ⨟ q) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id (X ⊗ Ty.unit) ⨟ q) := PEq.compL _ (PEq.fst_unitR X)
    _ ≡ₜ q := PEq.id_comp _

/-- Distributivity on the left undoes the left co-projection. -/
theorem prodF_inl_distL (A B C : Ty) :
    (prodF (inl A B) (Term.id C) ⨟ distL A B C) ≡ₜ inl (A ⊗ C) (B ⊗ C) := by
  calc (prodF (inl A B) (Term.id C) ⨟ distL A B C)
      ≡ₜ ((inl (A ⊗ C) (B ⊗ C) ⨟ undistL A B C) ⨟ distL A B C) :=
        PEq.compL _ (PEq.symm (inl_either _ _))
    _ ≡ₜ (inl (A ⊗ C) (B ⊗ C) ⨟ (undistL A B C ⨟ distL A B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inl (A ⊗ C) (B ⊗ C) ⨟ Term.id ((A ⊗ C) ⊕' (B ⊗ C))) :=
        PEq.compR _ (PEq.undistL_distL A B C)
    _ ≡ₜ inl (A ⊗ C) (B ⊗ C) := PEq.comp_id _

/-- Distributivity on the left undoes the right co-projection. -/
theorem prodF_inr_distL (A B C : Ty) :
    (prodF (inr A B) (Term.id C) ⨟ distL A B C) ≡ₜ inr (A ⊗ C) (B ⊗ C) := by
  calc (prodF (inr A B) (Term.id C) ⨟ distL A B C)
      ≡ₜ ((inr (A ⊗ C) (B ⊗ C) ⨟ undistL A B C) ⨟ distL A B C) :=
        PEq.compL _ (PEq.symm (inr_either _ _))
    _ ≡ₜ (inr (A ⊗ C) (B ⊗ C) ⨟ (undistL A B C ⨟ distL A B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inr (A ⊗ C) (B ⊗ C) ⨟ Term.id ((A ⊗ C) ⊕' (B ⊗ C))) :=
        PEq.compR _ (PEq.undistL_distL A B C)
    _ ≡ₜ inr (A ⊗ C) (B ⊗ C) := PEq.comp_id _

/-! ### Case reasoning on the right component -/

/-- Case reasoning computes on the letters of the alphabet. -/
theorem pairR_caseR {Z A B : Ty} : {n : ℕ} → (t : ⟦Ty.finAlph n⟧ → Term A B) → (u : Term Z A) →
    (g : ⟦Ty.finAlph n⟧) → (pairR u (constFin g) ⨟ caseR t) ≡ₜ (u ⨟ t g)
  | 0, t, u, () => by
      calc (pairR u (Term.id Ty.unit) ⨟ (fst A Ty.unit ⨟ t ()))
          ≡ₜ ((pairR u (Term.id Ty.unit) ⨟ fst A Ty.unit) ⨟ t ()) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (u ⨟ t ()) := PEq.compL _ (pairR_fst _ _)
  | (n + 1), t, u, .inl () => by
      have hsplit : (pairR u (inl Ty.unit (Ty.finAlph n)) ⨟ distR A Ty.unit (Ty.finAlph n)) ≡ₜ
          (pairR u (Term.id Ty.unit) ⨟ inl (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n)) := by
        calc (pairR u (inl Ty.unit (Ty.finAlph n)) ⨟ distR A Ty.unit (Ty.finAlph n))
            ≡ₜ ((pairR u (Term.id Ty.unit) ⨟
                prodF (Term.id A) (inl Ty.unit (Ty.finAlph n))) ⨟
                distR A Ty.unit (Ty.finAlph n)) :=
              PEq.compL _ (PEq.symm ((pairR_prodF _ _ _ _).trans
                (pairR_congr (PEq.comp_id _) (PEq.id_comp _))))
          _ ≡ₜ (pairR u (Term.id Ty.unit) ⨟
                (prodF (Term.id A) (inl Ty.unit (Ty.finAlph n)) ⨟
                  distR A Ty.unit (Ty.finAlph n))) := PEq.comp_assoc _ _ _
          _ ≡ₜ (pairR u (Term.id Ty.unit) ⨟ inl (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n)) :=
              PEq.compR _ (prodF_inl_distR A Ty.unit (Ty.finAlph n))
      calc (pairR u (inl Ty.unit (Ty.finAlph n)) ⨟
              (distR A Ty.unit (Ty.finAlph n) ⨟
                either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g => t (.inr g)))))
          ≡ₜ ((pairR u (inl Ty.unit (Ty.finAlph n)) ⨟ distR A Ty.unit (Ty.finAlph n)) ⨟
              either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g => t (.inr g)))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((pairR u (Term.id Ty.unit) ⨟ inl (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n)) ⨟
              either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g => t (.inr g)))) :=
            PEq.compL _ hsplit
        _ ≡ₜ (pairR u (Term.id Ty.unit) ⨟ (inl (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n) ⨟
              either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g => t (.inr g))))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (pairR u (Term.id Ty.unit) ⨟ (fst A Ty.unit ⨟ t (.inl ()))) :=
            PEq.compR _ (inl_either _ _)
        _ ≡ₜ ((pairR u (Term.id Ty.unit) ⨟ fst A Ty.unit) ⨟ t (.inl ())) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (u ⨟ t (.inl ())) := PEq.compL _ (pairR_fst _ _)
  | (n + 1), t, u, .inr g => by
      have hsplit : (pairR u (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) ⨟
          distR A Ty.unit (Ty.finAlph n)) ≡ₜ
          (pairR u (constFin g) ⨟ inr (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n)) := by
        calc (pairR u (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) ⨟
                distR A Ty.unit (Ty.finAlph n))
            ≡ₜ ((pairR u (constFin g) ⨟
                prodF (Term.id A) (inr Ty.unit (Ty.finAlph n))) ⨟
                distR A Ty.unit (Ty.finAlph n)) :=
              PEq.compL _ (PEq.symm ((pairR_prodF _ _ _ _).trans
                (pairR_congr (PEq.comp_id _) (PEq.refl _))))
          _ ≡ₜ (pairR u (constFin g) ⨟
                (prodF (Term.id A) (inr Ty.unit (Ty.finAlph n)) ⨟
                  distR A Ty.unit (Ty.finAlph n))) := PEq.comp_assoc _ _ _
          _ ≡ₜ (pairR u (constFin g) ⨟ inr (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n)) :=
              PEq.compR _ (prodF_inr_distR A Ty.unit (Ty.finAlph n))
      calc (pairR u (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) ⨟
              (distR A Ty.unit (Ty.finAlph n) ⨟
                either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g' => t (.inr g')))))
          ≡ₜ ((pairR u (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) ⨟
              distR A Ty.unit (Ty.finAlph n)) ⨟
              either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g' => t (.inr g')))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((pairR u (constFin g) ⨟ inr (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n)) ⨟
              either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g' => t (.inr g')))) :=
            PEq.compL _ hsplit
        _ ≡ₜ (pairR u (constFin g) ⨟ (inr (A ⊗ Ty.unit) (A ⊗ Ty.finAlph n) ⨟
              either (fst A Ty.unit ⨟ t (.inl ())) (caseR (fun g' => t (.inr g'))))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (pairR u (constFin g) ⨟ caseR (fun g' => t (.inr g'))) :=
            PEq.compR _ (inr_either _ _)
        _ ≡ₜ (u ⨟ t (.inr g)) := pairR_caseR (fun g' => t (.inr g')) u g

/-- **Extensionality for the right component.**  A term out of `X × Ā`, with `Ā` a finite
alphabet, is determined by its restrictions to the letters of `Ā`. -/
theorem caseR_ext {X B : Ty} : {n : ℕ} → (u v : Term (X ⊗ Ty.finAlph n) B) →
    (∀ g : ⟦Ty.finAlph n⟧,
      (pairR (Term.id X) (constFin g) ⨟ u) ≡ₜ (pairR (Term.id X) (constFin g) ⨟ v)) →
    u ≡ₜ v
  | 0, u, v, h => by
      have h0 := h ()
      have hid : pairR (Term.id X) (Term.id Ty.unit) ≡ₜ unitR X :=
        (PEq.compR _ (PEq.prod_id X Ty.unit)).trans (PEq.comp_id _)
      exact cancel_unitR ((PEq.compL _ (PEq.symm hid)).trans
        (h0.trans (PEq.compL _ hid)))
  | (n + 1), u, v, h => by
      -- the two restrictions along the co-projections of the alphabet
      have hleft : (prodF (Term.id X) (inl Ty.unit (Ty.finAlph n)) ⨟ u) ≡ₜ
          (prodF (Term.id X) (inl Ty.unit (Ty.finAlph n)) ⨟ v) := by
        refine cancel_unitR ?_
        have e : (unitR X ⨟ (prodF (Term.id X) (inl Ty.unit (Ty.finAlph n)) ⨟ u)) ≡ₜ
            (pairR (Term.id X) (constFin (n := n + 1) (.inl ())) ⨟ u) :=
          PEq.symm (PEq.comp_assoc _ _ _)
        have e' : (unitR X ⨟ (prodF (Term.id X) (inl Ty.unit (Ty.finAlph n)) ⨟ v)) ≡ₜ
            (pairR (Term.id X) (constFin (n := n + 1) (.inl ())) ⨟ v) :=
          PEq.symm (PEq.comp_assoc _ _ _)
        exact e.trans ((h (.inl ())).trans (PEq.symm e'))
      have hright : (prodF (Term.id X) (inr Ty.unit (Ty.finAlph n)) ⨟ u) ≡ₜ
          (prodF (Term.id X) (inr Ty.unit (Ty.finAlph n)) ⨟ v) := by
        refine caseR_ext _ _ (fun g => ?_)
        have e : ∀ w : Term (X ⊗ Ty.finAlph (n + 1)) B,
            (pairR (Term.id X) (constFin g) ⨟
              (prodF (Term.id X) (inr Ty.unit (Ty.finAlph n)) ⨟ w)) ≡ₜ
              (pairR (Term.id X) (constFin (n := n + 1) (.inr g)) ⨟ w) := by
          intro w
          calc (pairR (Term.id X) (constFin g) ⨟
                  (prodF (Term.id X) (inr Ty.unit (Ty.finAlph n)) ⨟ w))
              ≡ₜ ((pairR (Term.id X) (constFin g) ⨟
                  prodF (Term.id X) (inr Ty.unit (Ty.finAlph n))) ⨟ w) :=
                PEq.symm (PEq.comp_assoc _ _ _)
            _ ≡ₜ (pairR (Term.id X) (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) ⨟ w) :=
                PEq.compL _ ((pairR_prodF _ _ _ _).trans
                  (pairR_congr (PEq.comp_id _) (PEq.refl _)))
        exact (e u).trans ((h (.inr g)).trans (PEq.symm (e v)))
      -- and now the two terms agree
      have key : (undistR X Ty.unit (Ty.finAlph n) ⨟ u) ≡ₜ
          (undistR X Ty.unit (Ty.finAlph n) ⨟ v) :=
        (either_comp _ _ _).trans ((either_congr hleft hright).trans
          (PEq.symm (either_comp _ _ _)))
      calc u ≡ₜ (Term.id (X ⊗ (Ty.unit ⊕' Ty.finAlph n)) ⨟ u) := PEq.symm (PEq.id_comp _)
        _ ≡ₜ ((distR X Ty.unit (Ty.finAlph n) ⨟ undistR X Ty.unit (Ty.finAlph n)) ⨟ u) :=
            PEq.compL _ (PEq.symm (PEq.distR_undistR _ _ _))
        _ ≡ₜ (distR X Ty.unit (Ty.finAlph n) ⨟ (undistR X Ty.unit (Ty.finAlph n) ⨟ u)) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (distR X Ty.unit (Ty.finAlph n) ⨟ (undistR X Ty.unit (Ty.finAlph n) ⨟ v)) :=
            PEq.compR _ key
        _ ≡ₜ ((distR X Ty.unit (Ty.finAlph n) ⨟ undistR X Ty.unit (Ty.finAlph n)) ⨟ v) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id (X ⊗ (Ty.unit ⊕' Ty.finAlph n)) ⨟ v) :=
            PEq.compL _ (PEq.distR_undistR _ _ _)
        _ ≡ₜ v := PEq.id_comp _

/-! ### Case reasoning on the left component -/

/-- Case reasoning on the left computes on the letters of the alphabet. -/
theorem pairL_caseL {Z A B : Ty} : {n : ℕ} → (t : ⟦Ty.finAlph n⟧ → Term A B) → (u : Term Z A) →
    (g : ⟦Ty.finAlph n⟧) → (pairL (constFin g) u ⨟ caseL t) ≡ₜ (u ⨟ t g)
  | 0, t, u, () => by
      calc (pairL (Term.id Ty.unit) u ⨟ (snd Ty.unit A ⨟ t ()))
          ≡ₜ ((pairL (Term.id Ty.unit) u ⨟ snd Ty.unit A) ⨟ t ()) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (u ⨟ t ()) := PEq.compL _ (pairL_snd _ _)
  | (n + 1), t, u, .inl () => by
      have hsplit : (pairL (inl Ty.unit (Ty.finAlph n)) u ⨟ distL Ty.unit (Ty.finAlph n) A) ≡ₜ
          (pairL (Term.id Ty.unit) u ⨟ inl (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A)) := by
        calc (pairL (inl Ty.unit (Ty.finAlph n)) u ⨟ distL Ty.unit (Ty.finAlph n) A)
            ≡ₜ ((pairL (Term.id Ty.unit) u ⨟
                prodF (inl Ty.unit (Ty.finAlph n)) (Term.id A)) ⨟
                distL Ty.unit (Ty.finAlph n) A) :=
              PEq.compL _ (PEq.symm ((pairL_prodF _ _ _ _).trans
                (pairL_congr (PEq.id_comp _) (PEq.comp_id _))))
          _ ≡ₜ (pairL (Term.id Ty.unit) u ⨟
                (prodF (inl Ty.unit (Ty.finAlph n)) (Term.id A) ⨟
                  distL Ty.unit (Ty.finAlph n) A)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (pairL (Term.id Ty.unit) u ⨟ inl (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A)) :=
              PEq.compR _ (prodF_inl_distL Ty.unit (Ty.finAlph n) A)
      calc (pairL (inl Ty.unit (Ty.finAlph n)) u ⨟
              (distL Ty.unit (Ty.finAlph n) A ⨟
                either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g => t (.inr g)))))
          ≡ₜ ((pairL (inl Ty.unit (Ty.finAlph n)) u ⨟ distL Ty.unit (Ty.finAlph n) A) ⨟
              either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g => t (.inr g)))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((pairL (Term.id Ty.unit) u ⨟ inl (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A)) ⨟
              either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g => t (.inr g)))) :=
            PEq.compL _ hsplit
        _ ≡ₜ (pairL (Term.id Ty.unit) u ⨟ (inl (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A) ⨟
              either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g => t (.inr g))))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (pairL (Term.id Ty.unit) u ⨟ (snd Ty.unit A ⨟ t (.inl ()))) :=
            PEq.compR _ (inl_either _ _)
        _ ≡ₜ ((pairL (Term.id Ty.unit) u ⨟ snd Ty.unit A) ⨟ t (.inl ())) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (u ⨟ t (.inl ())) := PEq.compL _ (pairL_snd _ _)
  | (n + 1), t, u, .inr g => by
      have hsplit : (pairL (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) u ⨟
          distL Ty.unit (Ty.finAlph n) A) ≡ₜ
          (pairL (constFin g) u ⨟ inr (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A)) := by
        calc (pairL (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) u ⨟
                distL Ty.unit (Ty.finAlph n) A)
            ≡ₜ ((pairL (constFin g) u ⨟
                prodF (inr Ty.unit (Ty.finAlph n)) (Term.id A)) ⨟
                distL Ty.unit (Ty.finAlph n) A) :=
              PEq.compL _ (PEq.symm ((pairL_prodF _ _ _ _).trans
                (pairL_congr (PEq.refl _) (PEq.comp_id _))))
          _ ≡ₜ (pairL (constFin g) u ⨟
                (prodF (inr Ty.unit (Ty.finAlph n)) (Term.id A) ⨟
                  distL Ty.unit (Ty.finAlph n) A)) := PEq.comp_assoc _ _ _
          _ ≡ₜ (pairL (constFin g) u ⨟ inr (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A)) :=
              PEq.compR _ (prodF_inr_distL Ty.unit (Ty.finAlph n) A)
      calc (pairL (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) u ⨟
              (distL Ty.unit (Ty.finAlph n) A ⨟
                either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g' => t (.inr g')))))
          ≡ₜ ((pairL (constFin g ⨟ inr Ty.unit (Ty.finAlph n)) u ⨟
              distL Ty.unit (Ty.finAlph n) A) ⨟
              either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g' => t (.inr g')))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ ((pairL (constFin g) u ⨟ inr (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A)) ⨟
              either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g' => t (.inr g')))) :=
            PEq.compL _ hsplit
        _ ≡ₜ (pairL (constFin g) u ⨟ (inr (Ty.unit ⊗ A) (Ty.finAlph n ⊗ A) ⨟
              either (snd Ty.unit A ⨟ t (.inl ())) (caseL (fun g' => t (.inr g'))))) :=
            PEq.comp_assoc _ _ _
        _ ≡ₜ (pairL (constFin g) u ⨟ caseL (fun g' => t (.inr g'))) :=
            PEq.compR _ (inr_either _ _)
        _ ≡ₜ (u ⨟ t (.inr g)) := pairL_caseL (fun g' => t (.inr g')) u g

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
