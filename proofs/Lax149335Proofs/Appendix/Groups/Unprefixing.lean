import Lax149335Proofs.Appendix.ConcatenationMaps
import Lax149335Proofs.Appendix.Groups.FiniteAlphabet
import Lax149335Proofs.Appendix.Groups.UnprefixingScan
import Mathlib.Tactic.Set
import Mathlib.Algebra.Group.Basic

/-!
# Unprefixing (appendix, *Unprefixing*)

The appendix section on unprefixing gives an explicit definition of the inverse `unpref` of
the group prefix multiplication, proves that the group prefix multiplication is natural (in
the type parameter and in the group), and proves two results in which unprefixing is
distributed over concatenation.

The explicit definition of `unpref` (Definition *Unprefixing operation* of the appendix) is
already part of the syntax of this formalisation, as `Lax149335Proofs.Term.unpref` in
`Lax149335Proofs.Terms.Derived`; the auxiliary terms `repeat` and `divide` of that definition are
`Lax149335Proofs.Term.grepeat` and `Lax149335Proofs.Term.gdiv`.

This file proves the two distributivity results, `Lax149335Proofs.Term.unpref_concat` and
`Lax149335Proofs.Term.unpref_commutes_with_concat`, which are the ones the development uses; their
denotational counterparts are in `Lax149335Proofs.Appendix.Groups.UnprefixingSemantics`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Distributing unprefixing over concatenation

For the distributivity results, the appendix uses a stronger typing for lists of pairs, in
which the last element of the list is a fixed group element `g`:
`T g = (A × G)* × A × 1`, together with its injection `ι_g : T g ↪ (A × G)*`. -/

/-- The type `T g = (A × G)* × A × 1` of the appendix: nonempty lists of pairs in which the
group element of the last pair is fixed (and therefore not written). -/
def TgTy (A : Ty) (n : ℕ) : Ty := ((A ⊗ Ty.finAlph n)⋆) ⊗ (A ⊗ Ty.unit)

/-- The injection `ι_g : T g ↪ (A × G)*`, which appends the pair `(a, g)`. -/
def iotaG (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) : Term (TgTy A n) ((A ⊗ Ty.finAlph n)⋆) :=
  prodF (Term.id ((A ⊗ Ty.finAlph n)⋆)) (prodF (Term.id A) (constFin g)) ⨟
    append (A ⊗ Ty.finAlph n)

/-! ### Blocks and their scans

The proofs of the distributivity results read `unpref` as a *scan*, as in
`Lax149335Proofs.Appendix.Groups.UnprefixingScan`: the input list is annotated with the group
element of each pair, the term `shiftL` shifts these annotations by one position, and the
outcome is post-processed.  A block `ι_g` is a list with one more pair at the end, whose
group element is the fixed letter `g`; the scan of such a block therefore ends with the
carry `g`, and blocks can be chained. -/

/-- The injection `ι_g` appends one pair to a list, which is the shape of the terms the scan
lemmas apply to. -/
theorem iotaG_eq_iotaBlock {A : Ty} {n : ℕ} (g : ⟦Ty.finAlph n⟧) :
    iotaG A g ≡ₜ iotaBlock A g := by
  calc (prodF (Term.id ((A ⊗ Ty.finAlph n)⋆)) (prodF (Term.id A) (constFin g)) ⨟
        append (A ⊗ Ty.finAlph n))
      ≡ₜ (prodF (Term.id ((A ⊗ Ty.finAlph n)⋆)) (prodF (Term.id A) (constFin g)) ⨟
          (prodF (Term.id ((A ⊗ Ty.finAlph n)⋆)) (pureT (A ⊗ Ty.finAlph n)) ⨟
            binconcat (A ⊗ Ty.finAlph n))) := PEq.compR _ (PEq.append_def _)
    _ ≡ₜ ((prodF (Term.id ((A ⊗ Ty.finAlph n)⋆)) (prodF (Term.id A) (constFin g)) ⨟
          prodF (Term.id ((A ⊗ Ty.finAlph n)⋆)) (pureT (A ⊗ Ty.finAlph n))) ⨟
            binconcat (A ⊗ Ty.finAlph n)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (Term.id ((A ⊗ Ty.finAlph n)⋆) ⨟ Term.id ((A ⊗ Ty.finAlph n)⋆))
          (lastPair A g) ⨟ binconcat (A ⊗ Ty.finAlph n)) :=
        PEq.compL _ (PEq.prod_comp _ _ _ _)
    _ ≡ₜ iotaBlock A g := PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (PEq.refl _))

/-- **The scan of a block.**  The final carry of the scan of an annotated block is the value
`g` of its last pair. -/
theorem scanL_iotaG {A : Ty} {n : ℕ} (v : Value (Ty.finAlph n)) (g : ⟦Ty.finAlph n⟧) :
    scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) v (iotaG A g ⨟ annot A n) ≡ₜ
      pairR (blockScan A v g) (constFin g) :=
  (scanL_congr v (PEq.compL _ (iotaG_eq_iotaBlock g))).trans (scanL_iotaBlock A v g)

/-- **Unprefixing a block.**  Unprefixing a block is the scan of the block, post-processed
by the division. -/
theorem iotaG_unpref {A : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (g : ⟦Ty.finAlph n⟧) :
    (iotaG A g ⨟ unpref A G) ≡ₜ
      (blockScan A (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧))) g ⨟ listF (gdiv A G)) := by
  letI := G
  calc (iotaG A g ⨟ unpref A G)
      ≡ₜ (iotaG A g ⨟ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A)
          (constFin (1 : ⟦Ty.finAlph n⟧)) (annot A n) ⨟ postUnpref A G)) :=
        PEq.compR _ (unpref_eq_scan A G)
    _ ≡ₜ ((iotaG A g ⨟ scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A)
          (constFin (1 : ⟦Ty.finAlph n⟧)) (annot A n)) ⨟ postUnpref A G) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
          (iotaG A g ⨟ annot A n) ⨟ postUnpref A G) := PEq.compL _ (comp_scanL _ _ _)
    _ ≡ₜ (pairR (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) g) (constFin g) ⨟
          postUnpref A G) := PEq.compL _ (scanL_iotaG _ g)
    _ ≡ₜ ((pairR (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) g) (constFin g) ⨟
          fst ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) (Ty.finAlph n)) ⨟ listF (gdiv A G)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) g ⨟ listF (gdiv A G)) :=
        PEq.compL _ (pairR_fst _ _)

/-- **Unprefixing a concatenation of blocks that all end with the group identity.** -/
theorem homT_iotaG_unpref {A : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (homT (iotaG A (letI := G; (1 : ⟦Ty.finAlph n⟧))) ⨟ unpref A G) ≡ₜ
      (homT (blockScan A (constFin (letI := G; (1 : ⟦Ty.finAlph n⟧)))
        (letI := G; (1 : ⟦Ty.finAlph n⟧))) ⨟ listF (gdiv A G)) := by
  letI := G
  calc (homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟ unpref A G)
      ≡ₜ (homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A)
          (constFin (1 : ⟦Ty.finAlph n⟧)) (annot A n) ⨟ postUnpref A G)) :=
        PEq.compR _ (unpref_eq_scan A G)
    _ ≡ₜ ((homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟ scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A)
          (constFin (1 : ⟦Ty.finAlph n⟧)) (annot A n)) ⨟ postUnpref A G) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
          (homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟ annot A n) ⨟ postUnpref A G) :=
        PEq.compL _ (comp_scanL _ _ _)
    _ ≡ₜ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
          (homT (iotaBlock A (1 : ⟦Ty.finAlph n⟧) ⨟ annot A n)) ⨟ postUnpref A G) :=
        PEq.compL _ (scanL_congr _ ((homT_comp_listF _ _).trans
          (homT_congr (PEq.compL _ (iotaG_eq_iotaBlock _)))))
    _ ≡ₜ (pairR (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)))
          (constFin (1 : ⟦Ty.finAlph n⟧)) ⨟ postUnpref A G) :=
        PEq.compL _ (scanL_homT_iotaBlock A (1 : ⟦Ty.finAlph n⟧))
    _ ≡ₜ ((pairR (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)))
          (constFin (1 : ⟦Ty.finAlph n⟧)) ⨟
          fst ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) (Ty.finAlph n)) ⨟ listF (gdiv A G)) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)) ⨟
          listF (gdiv A G)) := PEq.compL _ (pairR_fst _ _)

/-- **Lemma (unprefixing distributed over general concatenation)** (appendix,
*Unprefixing*).  Unprefixing commutes with the concatenation of a list of lists, provided
that each of them ends with the group identity. -/
theorem unpref_concat {A : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (listF (iotaG A (letI := G; (1 : ⟦Ty.finAlph n⟧))) ⨟
        (concat (A ⊗ Ty.finAlph n) ⨟ unpref A G)) ≡ₜ
      (listF (iotaG A (letI := G; (1 : ⟦Ty.finAlph n⟧))) ⨟
        (listF (unpref A G) ⨟ concat (A ⊗ Ty.finAlph n))) := by
  letI := G
  calc (listF (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟
        (concat (A ⊗ Ty.finAlph n) ⨟ unpref A G))
      ≡ₜ (homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟ unpref A G) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)) ⨟
          listF (gdiv A G)) := homT_iotaG_unpref G
    _ ≡ₜ homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧) ⨟
          listF (gdiv A G)) := homT_comp_listF _ _
    _ ≡ₜ homT (iotaG A (1 : ⟦Ty.finAlph n⟧) ⨟ unpref A G) :=
        homT_congr (PEq.symm (iotaG_unpref G (1 : ⟦Ty.finAlph n⟧)))
    _ ≡ₜ (listF (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟
          (listF (unpref A G) ⨟ concat (A ⊗ Ty.finAlph n))) := homT_precomp _ _

/-- **Lemma (`unpref` commutes with concatenation)** (appendix, *Proof of the bundle
lemma*).  The combination of the two previous lemmas: unprefixing commutes with the
concatenation map `(A × G)** × (A × G)* → (A × G)*`, provided that all the lists in the
first component end with the group identity. -/
theorem unpref_commutes_with_concat {A : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (prodF (listF (iotaG A (letI := G; (1 : ⟦Ty.finAlph n⟧))))
          (Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
        ((concat (A ⊗ Ty.finAlph n) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟ unpref A G)) ≡ₜ
      (prodF (listF (iotaG A (letI := G; (1 : ⟦Ty.finAlph n⟧))))
          (Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
        (prodF (listF (unpref A G)) (unpref A G) ⨟
          (concat (A ⊗ Ty.finAlph n) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)))) := by
  letI := G
  calc (prodF (listF (iotaG A (1 : ⟦Ty.finAlph n⟧))) (Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
        ((concat (A ⊗ Ty.finAlph n) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟ unpref A G))
      ≡ₜ ((prodF (listF (iotaG A (1 : ⟦Ty.finAlph n⟧))) (Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
          (concat (A ⊗ Ty.finAlph n) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆))) ⨟ unpref A G) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (((listF (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟ concat (A ⊗ Ty.finAlph n)) ⊙
          (Term.id ((A ⊗ Ty.finAlph n)⋆) ⨟ Term.id ((A ⊗ Ty.finAlph n)⋆))) ⨟
          unpref A G) := PEq.compL _ (fdot_precomp _ _ _ _)
    _ ≡ₜ ((homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
          unpref A G) := PEq.compL _ (fdot_congr (PEq.refl _) (PEq.id_comp _))
    _ ≡ₜ ((homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
          (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
            (annot A n) ⨟ postUnpref A G)) := PEq.compR _ (unpref_eq_scan A G)
    _ ≡ₜ (((homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
          scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
            (annot A n)) ⨟ postUnpref A G) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
          ((homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
            annot A n) ⨟ postUnpref A G) := PEq.compL _ (comp_scanL _ _ _)
    _ ≡ₜ (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
          (homT (iotaBlock A (1 : ⟦Ty.finAlph n⟧) ⨟ annot A n) ⊙ annot A n) ⨟
          postUnpref A G) :=
        PEq.compL _ (scanL_congr _ ((fdot_comp_listF _ _ _).trans
          (fdot_congr ((homT_comp_listF _ _).trans
            (homT_congr (PEq.compL _ (iotaG_eq_iotaBlock _)))) (PEq.id_comp _))))
    _ ≡ₜ ((prodF (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)))
            (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
              (annot A n)) ⨟ catScan (Ty.finAlph n) (Ty.finAlph n ⊗ A)) ⨟
          postUnpref A G) :=
        PEq.compL _ (scanL_fdot_gen _ _ _ _ _ (scanL_homT_iotaBlock A (1 : ⟦Ty.finAlph n⟧)))
    _ ≡ₜ (prodF (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)))
            (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
              (annot A n)) ⨟
          ((catScan (Ty.finAlph n) (Ty.finAlph n ⊗ A) ⨟
            fst ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) (Ty.finAlph n)) ⨟
              listF (gdiv A G))) :=
        (PEq.comp_assoc _ _ _).trans (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _)))
    _ ≡ₜ (prodF (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)))
            (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
              (annot A n)) ⨟
          ((Term.id ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) ⊙
            fst ((Ty.finAlph n ⊗ (Ty.finAlph n ⊗ A))⋆) (Ty.finAlph n)) ⨟
              listF (gdiv A G))) := PEq.compR _ (PEq.compL _ (catScan_fst _ _))
    _ ≡ₜ (prodF (homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)))
            (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
              (annot A n)) ⨟ (listF (gdiv A G) ⊙ postUnpref A G)) :=
        PEq.compR _ ((fdot_comp_listF _ _ _).trans
          (fdot_congr (PEq.id_comp _) (PEq.refl _)))
    _ ≡ₜ ((homT (blockScan A (constFin (1 : ⟦Ty.finAlph n⟧)) (1 : ⟦Ty.finAlph n⟧)) ⨟
            listF (gdiv A G)) ⊙
          (scanL (Ty.finAlph n) (Ty.finAlph n ⊗ A) (constFin (1 : ⟦Ty.finAlph n⟧))
            (annot A n) ⨟ postUnpref A G)) := fdot_precomp _ _ _ _
    _ ≡ₜ ((homT (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟ unpref A G) ⊙ unpref A G) :=
        fdot_congr (PEq.symm (homT_iotaG_unpref G)) (PEq.symm (unpref_eq_scan A G))
    _ ≡ₜ ((listF (iotaG A (1 : ⟦Ty.finAlph n⟧)) ⨟
            (listF (unpref A G) ⨟ concat (A ⊗ Ty.finAlph n))) ⊙
          (Term.id ((A ⊗ Ty.finAlph n)⋆) ⨟ unpref A G)) :=
        fdot_congr ((PEq.comp_assoc _ _ _).trans (unpref_concat G))
          (PEq.symm (PEq.id_comp _))
    _ ≡ₜ (prodF (listF (iotaG A (1 : ⟦Ty.finAlph n⟧))) (Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
          ((listF (unpref A G) ⨟ concat (A ⊗ Ty.finAlph n)) ⊙ unpref A G)) :=
        PEq.symm (fdot_precomp _ _ _ _)
    _ ≡ₜ (prodF (listF (iotaG A (1 : ⟦Ty.finAlph n⟧))) (Term.id ((A ⊗ Ty.finAlph n)⋆)) ⨟
          (prodF (listF (unpref A G)) (unpref A G) ⨟
            (concat (A ⊗ Ty.finAlph n) ⊙ Term.id ((A ⊗ Ty.finAlph n)⋆)))) :=
        PEq.compR _ (PEq.symm ((fdot_precomp _ _ _ _).trans
          (fdot_congr (PEq.refl _) (PEq.comp_id _))))

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
