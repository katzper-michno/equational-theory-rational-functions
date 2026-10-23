import Lax149335Proofs.Appendix.Groups.ShiftScan
import Lax149335Proofs.Appendix.Naturality

/-!
# Unprefixing, read as a scan (appendix, *Unprefixing*)

The unprefixing operation `unpref` of `Lax149335Proofs.Terms.Derived` is built from `shiftL`.  This
file rewrites it as a *scan*, in the sense of `Lax149335Proofs.Appendix.Groups.ShiftScan`:

* the list `[(a₁,g₁),…,(a_k,g_k)]` is first annotated, by `Lax149335Proofs.Term.annot`, into the
  list `[((g₁,a₁),g₁),…,((g_k,a_k),g_k)]` of pairs whose carry is the group element;
* the scan `shiftL` shifts the carries by one position, starting from the group identity;
* the result is post-processed by `Lax149335Proofs.Term.postUnpref`, which forgets the final carry
  and divides in each pair.

The main results are `Lax149335Proofs.Term.unpref_eq_scan`, which is that factorisation, and
`Lax149335Proofs.Term.scanL_iotaBlock`, which computes the scan of a block of the special form used
in the appendix: a list whose last pair has a fixed group element `g`.  For such a block the
final carry of the scan is the *value* `g`, which is what makes it possible to run the scan
over a concatenation of blocks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Two cancellation rules for the unit type -/

/-- Terms into `1 × B` are determined by their second component. -/
theorem eq_of_comp_snd {A B : Ty} {p q : Term A (Ty.unit ⊗ B)}
    (h : (p ⨟ snd Ty.unit B) ≡ₜ (q ⨟ snd Ty.unit B)) : p ≡ₜ q :=
  ((cancel p q).1 _ (snd Ty.unit B) ⟨unitL B, PEq.snd_unitL B⟩).2 h

/-! ### Re-associating a pairing with two values -/

/-- Re-associating to the right turns `((v,u),w)` into `(v,(u,w))`. -/
theorem pairR_pairL_assocR {Z A B C : Ty} (v : Value C) (u : Term Z A) (w : Value B) :
    (pairR (pairL v u) w ⨟ assocR C A B) ≡ₜ pairL v (pairR u w) := by
  -- the coherence map `Z → 1 × (Z × 1)` used by either side
  have hcoh : (unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟ assocR Ty.unit Z Ty.unit)) ≡ₜ
      (unitL Z ⨟ prodF (Term.id Ty.unit) (unitR Z)) := by
    refine eq_of_comp_snd ?_
    calc ((unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟ assocR Ty.unit Z Ty.unit)) ⨟
          snd Ty.unit (Z ⊗ Ty.unit))
        ≡ₜ (unitR Z ⨟ ((prodF (unitL Z) (Term.id Ty.unit) ⨟ assocR Ty.unit Z Ty.unit) ⨟
            snd Ty.unit (Z ⊗ Ty.unit))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟
            (assocR Ty.unit Z Ty.unit ⨟ snd Ty.unit (Z ⊗ Ty.unit)))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟
            prodF (snd Ty.unit Z) (Term.id Ty.unit))) :=
          PEq.compR _ (PEq.compR _ (Term.assocR_snd _ _ _))
      _ ≡ₜ (unitR Z ⨟ prodF (unitL Z ⨟ snd Ty.unit Z) (Term.id Ty.unit ⨟ Term.id Ty.unit)) :=
          PEq.compR _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (unitR Z ⨟ prodF (Term.id Z) (Term.id Ty.unit)) :=
          PEq.compR _ (PEq.congr_prodF (PEq.unitL_snd Z) (PEq.id_comp _))
      _ ≡ₜ (unitR Z ⨟ Term.id (Z ⊗ Ty.unit)) := PEq.compR _ (PEq.prod_id _ _)
      _ ≡ₜ unitR Z := PEq.comp_id _
      _ ≡ₜ (Term.id Z ⨟ unitR Z) := PEq.symm (PEq.id_comp _)
      _ ≡ₜ ((unitL Z ⨟ snd Ty.unit Z) ⨟ unitR Z) := PEq.compL _ (PEq.symm (PEq.unitL_snd Z))
      _ ≡ₜ (unitL Z ⨟ (snd Ty.unit Z ⨟ unitR Z)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (unitL Z ⨟ (prodF (Term.id Ty.unit) (unitR Z) ⨟ snd Ty.unit (Z ⊗ Ty.unit))) :=
          PEq.compR _ (PEq.symm (PEq.nat_snd _ _))
      _ ≡ₜ ((unitL Z ⨟ prodF (Term.id Ty.unit) (unitR Z)) ⨟ snd Ty.unit (Z ⊗ Ty.unit)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
  calc ((unitR Z ⨟ prodF (unitL Z ⨟ prodF v u) w) ⨟ assocR C A B)
      ≡ₜ ((unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟ prodF (prodF v u) w)) ⨟
          assocR C A B) := by
        refine PEq.compL _ (PEq.compR _ ?_)
        exact PEq.symm ((PEq.prod_comp _ _ _ _).trans
          (PEq.congr_prodF (PEq.refl _) (PEq.id_comp _)))
    _ ≡ₜ (unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟
          (prodF (prodF v u) w ⨟ assocR C A B))) := by
        calc ((unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟ prodF (prodF v u) w)) ⨟
              assocR C A B)
            ≡ₜ (unitR Z ⨟ ((prodF (unitL Z) (Term.id Ty.unit) ⨟ prodF (prodF v u) w) ⨟
                assocR C A B)) := PEq.comp_assoc _ _ _
          _ ≡ₜ _ := PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ (unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟
          (assocR Ty.unit Z Ty.unit ⨟ prodF v (prodF u w)))) :=
        PEq.compR _ (PEq.compR _ (PEq.nat_assocR _ _ _))
    _ ≡ₜ ((unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟ assocR Ty.unit Z Ty.unit)) ⨟
          prodF v (prodF u w)) := by
        calc (unitR Z ⨟ (prodF (unitL Z) (Term.id Ty.unit) ⨟
              (assocR Ty.unit Z Ty.unit ⨟ prodF v (prodF u w))))
            ≡ₜ (unitR Z ⨟ ((prodF (unitL Z) (Term.id Ty.unit) ⨟ assocR Ty.unit Z Ty.unit) ⨟
                prodF v (prodF u w))) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
          _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((unitL Z ⨟ prodF (Term.id Ty.unit) (unitR Z)) ⨟ prodF v (prodF u w)) :=
        PEq.compL _ hcoh
    _ ≡ₜ (unitL Z ⨟ (prodF (Term.id Ty.unit) (unitR Z) ⨟ prodF v (prodF u w))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (unitL Z ⨟ prodF (Term.id Ty.unit ⨟ v) (unitR Z ⨟ prodF u w)) :=
        PEq.compR _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ pairL v (pairR u w) :=
        PEq.compR _ (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))

/-- Re-associating to the left turns `(v,(u,w))` into `((v,u),w)`. -/
theorem pairL_pairR_assocL {Z A B C : Ty} (v : Value C) (u : Term Z A) (w : Value B) :
    (pairL v (pairR u w) ⨟ assocL C A B) ≡ₜ pairR (pairL v u) w := by
  refine ((cancel _ _).1 _ (assocR C A B) ⟨assocL C A B, PEq.assocR_assocL C A B⟩).2 ?_
  calc ((pairL v (pairR u w) ⨟ assocL C A B) ⨟ assocR C A B)
      ≡ₜ (pairL v (pairR u w) ⨟ (assocL C A B ⨟ assocR C A B)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (pairL v (pairR u w) ⨟ Term.id (C ⊗ (A ⊗ B))) :=
        PEq.compR _ (PEq.assocL_assocR _ _ _)
    _ ≡ₜ pairL v (pairR u w) := PEq.comp_id _
    _ ≡ₜ (pairR (pairL v u) w ⨟ assocR C A B) := PEq.symm (pairR_pairL_assocR v u w)

/-- A product with a value in the second component is a right pairing. -/
theorem prodF_id_value {A C : Ty} (v : Value C) :
    prodF (Term.id A) v ≡ₜ pairR (fst A Ty.unit) v := by
  calc prodF (Term.id A) v
      ≡ₜ (Term.id (A ⊗ Ty.unit) ⨟ prodF (Term.id A) v) := PEq.symm (PEq.id_comp _)
    _ ≡ₜ ((fst A Ty.unit ⨟ unitR A) ⨟ prodF (Term.id A) v) :=
        PEq.compL _ (PEq.symm (PEq.fst_unitR A))
    _ ≡ₜ (fst A Ty.unit ⨟ (unitR A ⨟ prodF (Term.id A) v)) := PEq.comp_assoc _ _ _
    _ ≡ₜ pairR (fst A Ty.unit ⨟ Term.id A) v := comp_pairR _ _ _
    _ ≡ₜ pairR (fst A Ty.unit) v := pairR_congr (PEq.comp_id _) (PEq.refl _)

/-! ### Unprefixing as a scan -/

/-- The annotation of a list of pairs: each pair `(a,g)` is turned into the pair
`((g,a),g)`, whose carry is the group element. -/
def annot (A : Ty) (n : ℕ) :
    Term ((A ⊗ Ty.finAlph n)⋆) (((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n)⋆) :=
  listF (grepeat A n ⨟ assocL (Ty.finAlph n) A (Ty.finAlph n))

/-- The post-processing of the scan: the final carry is forgotten and the group elements are
divided. -/
def postUnpref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆ ⊗ Ty.finAlph n) ((A ⊗ Ty.finAlph n)⋆) :=
  fst _ _ ⨟ listF (gdiv A G)

/-- **Unprefixing is a scan.**  `unpref` annotates its input, runs the scan `shiftL` from the
group identity, and post-processes the outcome. -/
theorem unpref_eq_scan (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    unpref A G ≡ₜ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A)
      (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (annot A n) ⨟ postUnpref A G) := by
  have hpre : ((listF (grepeat A n) ⨟ listF (assocL (Ty.finAlph n) A (Ty.finAlph n))) ⨟
      pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧)))
        (Term.id ((((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n))⋆))) ≡ₜ
      pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (annot A n) := by
    calc ((listF (grepeat A n) ⨟ listF (assocL (Ty.finAlph n) A (Ty.finAlph n))) ⨟
          pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (Term.id _))
        ≡ₜ pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧)))
            ((listF (grepeat A n) ⨟ listF (assocL (Ty.finAlph n) A (Ty.finAlph n))) ⨟
              Term.id _) := comp_pairL _ _ _
      _ ≡ₜ pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧)))
            (listF (grepeat A n) ⨟ listF (assocL (Ty.finAlph n) A (Ty.finAlph n))) :=
          pairL_congr (PEq.refl _) (PEq.comp_id _)
      _ ≡ₜ pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (annot A n) :=
          pairL_congr (PEq.refl _) (PEq.list_comp _ _)
  calc unpref A G
      ≡ₜ (((pairL (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (annot A n) ⨟
            shiftL (Ty.finAlph n) (Ty.finAlph n ⊗ A)) ⨟
          fst ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) (Ty.finAlph n)) ⨟
            listF (gdiv A G)) := PEq.compL _ (PEq.compL _ (PEq.compL _ hpre))
    _ ≡ₜ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A)
            (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) (annot A n) ⨟
          (fst ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) (Ty.finAlph n) ⨟ listF (gdiv A G))) :=
        PEq.comp_assoc _ _ _

/-! ### The scan of a block -/

/-- The `Y`-part of the last pair of a block: the pair `(g,a)`. -/
def yPart (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) : Term (A ⊗ Ty.unit) (Ty.finAlph n ⊗ A) :=
  pairL (constFin g) (fst A Ty.unit)

/-- The last pair of a block, as a one-element list. -/
def lastPair (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) :
    Term (A ⊗ Ty.unit) ((A ⊗ Ty.finAlph n)⋆) :=
  prodF (Term.id A) (constFin g) ⨟ pureT (A ⊗ Ty.finAlph n)

/-- A block: a list of pairs together with one more pair whose group element is the fixed
letter `g`. -/
def iotaBlock (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) :
    Term (((A ⊗ Ty.finAlph n)⋆) ⊗ (A ⊗ Ty.unit)) ((A ⊗ Ty.finAlph n)⋆) :=
  Term.id ((A ⊗ Ty.finAlph n)⋆) ⊙ lastPair A g

/-- The annotation of the last pair of a block. -/
theorem lastPair_annot (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) :
    (lastPair A g ⨟ annot A n) ≡ₜ
      (pairR (yPart A g) (constFin g) ⨟ pureT ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n)) := by
  have hstep : (prodF (Term.id A) (constFin g) ⨟
      (grepeat A n ⨟ assocL (Ty.finAlph n) A (Ty.finAlph n))) ≡ₜ
      pairR (yPart A g) (constFin g) := by
    calc (prodF (Term.id A) (constFin g) ⨟
          (grepeat A n ⨟ assocL (Ty.finAlph n) A (Ty.finAlph n)))
        ≡ₜ ((prodF (Term.id A) (constFin g) ⨟ grepeat A n) ⨟
            assocL (Ty.finAlph n) A (Ty.finAlph n)) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((pairR (fst A Ty.unit) (constFin g) ⨟ grepeat A n) ⨟
            assocL (Ty.finAlph n) A (Ty.finAlph n)) :=
          PEq.compL _ (PEq.compL _ (prodF_id_value _))
      _ ≡ₜ ((fst A Ty.unit ⨟
            pairL (constFin g) (pairR (Term.id A) (constFin g))) ⨟
            assocL (Ty.finAlph n) A (Ty.finAlph n)) :=
          PEq.compL _ (pairR_caseR _ _ g)
      _ ≡ₜ (pairL (constFin g) (fst A Ty.unit ⨟ pairR (Term.id A) (constFin g)) ⨟
            assocL (Ty.finAlph n) A (Ty.finAlph n)) := PEq.compL _ (comp_pairL _ _ _)
      _ ≡ₜ (pairL (constFin g) (pairR (fst A Ty.unit) (constFin g)) ⨟
            assocL (Ty.finAlph n) A (Ty.finAlph n)) :=
          PEq.compL _ (pairL_congr (PEq.refl _)
            ((comp_pairR _ _ _).trans (pairR_congr (PEq.comp_id _) (PEq.refl _))))
      _ ≡ₜ pairR (pairL (constFin g) (fst A Ty.unit)) (constFin g) :=
          pairL_pairR_assocL _ _ _
  calc ((prodF (Term.id A) (constFin g) ⨟ pureT (A ⊗ Ty.finAlph n)) ⨟ annot A n)
      ≡ₜ (prodF (Term.id A) (constFin g) ⨟ (pureT (A ⊗ Ty.finAlph n) ⨟
          listF (grepeat A n ⨟ assocL (Ty.finAlph n) A (Ty.finAlph n)))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (prodF (Term.id A) (constFin g) ⨟
          ((grepeat A n ⨟ assocL (Ty.finAlph n) A (Ty.finAlph n)) ⨟
            pureT ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n))) :=
        PEq.compR _ (PEq.symm (pureT_natural _))
    _ ≡ₜ ((prodF (Term.id A) (constFin g) ⨟
          (grepeat A n ⨟ assocL (Ty.finAlph n) A (Ty.finAlph n))) ⨟
            pureT ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (pairR (yPart A g) (constFin g) ⨟
          pureT ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n)) := PEq.compL _ hstep

/-- The annotation of a block. -/
theorem iotaBlock_annot (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) :
    (iotaBlock A g ⨟ annot A n) ≡ₜ
      (annot A n ⊙ (pairR (yPart A g) (constFin g) ⨟
        pureT ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n))) := by
  calc ((Term.id ((A ⊗ Ty.finAlph n)⋆) ⊙ lastPair A g) ⨟ annot A n)
      ≡ₜ ((Term.id ((A ⊗ Ty.finAlph n)⋆) ⨟ annot A n) ⊙ (lastPair A g ⨟ annot A n)) :=
        fdot_comp_listF _ _ _
    _ ≡ₜ (annot A n ⊙ (pairR (yPart A g) (constFin g) ⨟
          pureT ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n))) :=
        fdot_congr (PEq.id_comp _) (lastPair_annot A g)

/-- The list produced by the scan of a block. -/
def blockScan (A : Ty) {n : ℕ} (v : Value (Ty.finAlph n)) (g : ⟦Ty.finAlph n⟧) :
    Term (((A ⊗ Ty.finAlph n)⋆) ⊗ (A ⊗ Ty.unit))
      ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) :=
  snocScan (Ty.finAlph n) (Ty.finAlph n ⊗ A) v (annot A n) (yPart A g)

/-- **The scan of a block.**  Since the group element of the last pair of a block is the
fixed letter `g`, the final carry of the scan of a block is the value `g`. -/
theorem scanL_iotaBlock (A : Ty) {n : ℕ} (v : Value (Ty.finAlph n)) (g : ⟦Ty.finAlph n⟧) :
    scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) v (iotaBlock A g ⨟ annot A n) ≡ₜ
      pairR (blockScan A v g) (constFin g) := by
  calc scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) v (iotaBlock A g ⨟ annot A n)
      ≡ₜ scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) v
          (annot A n ⊙ (pairR (yPart A g) (constFin g) ⨟
            pureT ((Ty.finAlph n ⊗ A) ⊗ Ty.finAlph n))) :=
        PEq.compL _ (pairL_congr (PEq.refl _) (iotaBlock_annot A g))
    _ ≡ₜ pairR (blockScan A v g) (constFin g) := scanL_snoc _ _ _ _

/-- The content of the annotated block, as it is used for the concatenation of a list of
blocks. -/
def blockContent (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) :
    Term (((A ⊗ Ty.finAlph n)⋆) ⊗ (A ⊗ Ty.unit))
      ((Ty.finAlph n ⊕' (Ty.finAlph n ⊗ A))⋆) :=
  (annot A n ⨟ cListYX (Ty.finAlph n) (Ty.finAlph n ⊗ A)) ⊙
    (yPart A g ⨟ (inr (Ty.finAlph n) (Ty.finAlph n ⊗ A) ⨟
      pureT (Ty.finAlph n ⊕' (Ty.finAlph n ⊗ A))))

/-- **The scan of the concatenation of a list of blocks all ending with the same group
element `g`, started from the carry `g`.**  The final carry is again `g`, and the list
produced is the concatenation of the lists produced by the individual blocks. -/
theorem scanL_homT_iotaBlock (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) :
    scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin g)
        (homT (iotaBlock A g ⨟ annot A n)) ≡ₜ
      pairR (homT (blockScan A (constFin g) g)) (constFin g) := by
  refine scanL_homT (constFin g) _ _ (blockContent A g) ?_ ?_
  · exact content_snocScan _ _ _
  · exact (PEq.compL _ (iotaBlock_annot A g)).trans (content_fdot_sing _ _ _)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
