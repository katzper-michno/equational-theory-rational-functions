/-
Copyright (c) 2025.  Formalisation of *The equational theory of rational
string-to-string functions*.
-/
import Lax149335Proofs.Appendix.Drops.SplitPeel
import Mathlib.Tactic.Set

/-!
# The content algebra of the co-domain of `split`

This file contains the computations in the monoid of contents `(S+T)*` that the case *Split*
of the exchange lemma needs.  A *split pair* `(a, m) : S* × (T × S*)*` has the content
`a m` (`Lax149335Proofs.Term.unsplit`); a split pair *with a last block* `((a,m), z)` has the
content `a m z` (`Lax149335Proofs.Term.unsplitB`).  The file proves:

* the merge laws: the concatenation of two such contents is again one of them, provided the
  left factor ends with a block, since a block absorbs a following word of letters of `S`
  (`Lax149335Proofs.Term.fdot_zBlock_sWord`);
* the star laws: the concatenation of a *list* of contents.  For a word of letters of `S`
  this is again such a word (`Lax149335Proofs.Term.homT_sWord`); for a content with a last block it
  is either empty or again such a content (`Lax149335Proofs.Term.homT_unsplitB`), which is proved
  from the general shape of a homomorphic image of a concatenation
  (`Lax149335Proofs.Term.homT_fdot`) through the co-domain of `shift`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

variable {S T : Ty}

namespace Term

/-- Pre-composing the left factor of a concatenation. -/
theorem fdot_precompL {X X' Y D : Ty} (f : Term X X') (x : Term X' D⋆) (y : Term Y D⋆) :
    ((f ⨟ x) ⊙ y) ≡ₜ (prodF f (Term.id Y) ⨟ (x ⊙ y)) :=
  PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr (PEq.refl _) (PEq.id_comp _)))

/-- Pre-composing the right factor of a concatenation. -/
theorem fdot_precompR {X Y Y' D : Ty} (g : Term Y Y') (x : Term X D⋆) (y : Term Y' D⋆) :
    (x ⊙ (g ⨟ y)) ≡ₜ (prodF (Term.id X) g ⨟ (x ⊙ y)) :=
  PEq.symm ((fdot_precomp _ _ _ _).trans (fdot_congr (PEq.id_comp _) (PEq.refl _)))

/-- The content of a list of blocks together with a distinguished last block. -/
def zWordB (S T : Ty) : Term ((ZTy S T)⋆ ⊗ ZTy S T) ((S ⊕' T)⋆) := zWord S T ⊙ zBlock S T

/-- The content of a split pair together with a distinguished last block. -/
def unsplitB (S T : Ty) : Term (splitCod S T ⊗ ZTy S T) ((S ⊕' T)⋆) :=
  Term.unsplit S T ⊙ zBlock S T

/-- Appending a word of letters of `S` to a block. -/
def zSnoc (S T : Ty) : Term (ZTy S T ⊗ S⋆) (ZTy S T) :=
  assocR T S⋆ S⋆ ⨟ prodF (Term.id T) (binconcat S)

theorem isDrop_zSnoc (S T : Ty) : IsDrop (zSnoc S T) :=
  IsDrop.comp (IsDrop.assocR _ _ _) (IsDrop.prodF (IsDrop.id _) (IsDrop.binconcat _))

/-- Appending a block to a split pair. -/
def appendBlock (S T : Ty) : Term (splitCod S T ⊗ ZTy S T) (splitCod S T) :=
  assocR S⋆ ((ZTy S T)⋆) (ZTy S T) ⨟
    prodF (Term.id S⋆) (prodF (Term.id ((ZTy S T)⋆)) (pureT (ZTy S T)) ⨟ binconcat (ZTy S T))

theorem isDrop_appendBlock (S T : Ty) : IsDrop (appendBlock S T) :=
  IsDrop.comp (IsDrop.assocR _ _ _)
    (IsDrop.prodF (IsDrop.id _)
      (IsDrop.comp (IsDrop.prodF (IsDrop.id _) (IsDrop.pureT _)) (IsDrop.binconcat _)))

/-! ### The merge laws of the content algebra -/

/-- Concatenating two words of letters of `S`. -/
theorem fdot_sWord_sWord (S T : Ty) :
    (sWord S T ⊙ sWord S T) ≡ₜ (binconcat S ⨟ sWord S T) :=
  PEq.symm (homT_binconcat _)

/-- Concatenating two lists of blocks. -/
theorem fdot_zWord_zWord (S T : Ty) :
    (zWord S T ⊙ zWord S T) ≡ₜ (binconcat (ZTy S T) ⨟ zWord S T) :=
  PEq.symm (homT_binconcat _)

/-- **A block followed by a word of letters of `S` is a block.** -/
theorem fdot_zBlock_sWord (S T : Ty) :
    (zBlock S T ⊙ sWord S T) ≡ₜ (zSnoc S T ⨟ zBlock S T) := by
  calc ((tLetter S T ⊙ sWord S T) ⊙ sWord S T)
      ≡ₜ (assocR T S⋆ S⋆ ⨟ (tLetter S T ⊙ (sWord S T ⊙ sWord S T))) := fdot_assoc _ _ _
    _ ≡ₜ (assocR T S⋆ S⋆ ⨟ (tLetter S T ⊙ (binconcat S ⨟ sWord S T))) :=
        PEq.compR _ (fdot_congr (PEq.refl _) (fdot_sWord_sWord S T))
    _ ≡ₜ (assocR T S⋆ S⋆ ⨟ (prodF (Term.id T) (binconcat S) ⨟ (tLetter S T ⊙ sWord S T))) :=
        PEq.compR _ (fdot_precompR _ _ _)
    _ ≡ₜ (zSnoc S T ⨟ zBlock S T) := PEq.symm (PEq.comp_assoc _ _ _)

/-- A word of letters of `S` followed by a split pair is a split pair. -/
theorem fdot_sWord_unsplit (S T : Ty) :
    (sWord S T ⊙ Term.unsplit S T) ≡ₜ
      ((assocL S⋆ S⋆ ((ZTy S T)⋆) ⨟ prodF (binconcat S) (Term.id ((ZTy S T)⋆))) ⨟
        Term.unsplit S T) := by
  calc (sWord S T ⊙ (sWord S T ⊙ zWord S T))
      ≡ₜ (assocL S⋆ S⋆ ((ZTy S T)⋆) ⨟ ((sWord S T ⊙ sWord S T) ⊙ zWord S T)) :=
        fdot_assoc' _ _ _
    _ ≡ₜ (assocL S⋆ S⋆ ((ZTy S T)⋆) ⨟ ((binconcat S ⨟ sWord S T) ⊙ zWord S T)) :=
        PEq.compR _ (fdot_congr (fdot_sWord_sWord S T) (PEq.refl _))
    _ ≡ₜ (assocL S⋆ S⋆ ((ZTy S T)⋆) ⨟
          (prodF (binconcat S) (Term.id ((ZTy S T)⋆)) ⨟ (sWord S T ⊙ zWord S T))) :=
        PEq.compR _ (fdot_precompL _ _ _)
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-- A split pair followed by a list of blocks is a split pair. -/
theorem fdot_unsplit_zWord (S T : Ty) :
    (Term.unsplit S T ⊙ zWord S T) ≡ₜ
      ((assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
        prodF (Term.id S⋆) (binconcat (ZTy S T))) ⨟ Term.unsplit S T) := by
  calc ((sWord S T ⊙ zWord S T) ⊙ zWord S T)
      ≡ₜ (assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟ (sWord S T ⊙ (zWord S T ⊙ zWord S T))) :=
        fdot_assoc _ _ _
    _ ≡ₜ (assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
          (sWord S T ⊙ (binconcat (ZTy S T) ⨟ zWord S T))) :=
        PEq.compR _ (fdot_congr (PEq.refl _) (fdot_zWord_zWord S T))
    _ ≡ₜ (assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
          (prodF (Term.id S⋆) (binconcat (ZTy S T)) ⨟ (sWord S T ⊙ zWord S T))) :=
        PEq.compR _ (fdot_precompR _ _ _)
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-- **A block followed by a split pair is a list of blocks.** -/
theorem fdot_zBlock_unsplit (S T : Ty) :
    (zBlock S T ⊙ Term.unsplit S T) ≡ₜ
      ((assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
        (prodF (zSnoc S T ⨟ pureT (ZTy S T)) (Term.id ((ZTy S T)⋆)) ⨟
          binconcat (ZTy S T))) ⨟ zWord S T) := by
  calc (zBlock S T ⊙ (sWord S T ⊙ zWord S T))
      ≡ₜ (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟ ((zBlock S T ⊙ sWord S T) ⊙ zWord S T)) :=
        fdot_assoc' _ _ _
    _ ≡ₜ (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟ ((zSnoc S T ⨟ zBlock S T) ⊙ zWord S T)) :=
        PEq.compR _ (fdot_congr (fdot_zBlock_sWord S T) (PEq.refl _))
    _ ≡ₜ (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
          (((zSnoc S T ⨟ pureT (ZTy S T)) ⨟ zWord S T) ⊙ zWord S T)) :=
        PEq.compR _ (fdot_congr
          ((PEq.compR _ (PEq.symm pureT_zWord)).trans (PEq.symm (PEq.comp_assoc _ _ _)))
          (PEq.refl _))
    _ ≡ₜ (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
          (prodF (zSnoc S T ⨟ pureT (ZTy S T)) (Term.id ((ZTy S T)⋆)) ⨟
            (zWord S T ⊙ zWord S T))) :=
        PEq.compR _ (fdot_precompL _ _ _)
    _ ≡ₜ (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
          (prodF (zSnoc S T ⨟ pureT (ZTy S T)) (Term.id ((ZTy S T)⋆)) ⨟
            (binconcat (ZTy S T) ⨟ zWord S T))) :=
        PEq.compR _ (PEq.compR _ (fdot_zWord_zWord S T))
    _ ≡ₜ _ := by
        refine (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))).trans ?_
        exact PEq.symm (PEq.comp_assoc _ _ _)

/-- A split pair with a distinguished last block is a split pair. -/
theorem appendBlock_unsplit (S T : Ty) :
    (appendBlock S T ⨟ Term.unsplit S T) ≡ₜ unsplitB S T := by
  have h1 : ((prodF (Term.id ((ZTy S T)⋆)) (pureT (ZTy S T)) ⨟ binconcat (ZTy S T)) ⨟
      zWord S T) ≡ₜ zWordB S T := by
    calc ((prodF (Term.id ((ZTy S T)⋆)) (pureT (ZTy S T)) ⨟ binconcat (ZTy S T)) ⨟ zWord S T)
        ≡ₜ (prodF (Term.id ((ZTy S T)⋆)) (pureT (ZTy S T)) ⨟
            (binconcat (ZTy S T) ⨟ zWord S T)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (Term.id ((ZTy S T)⋆)) (pureT (ZTy S T)) ⨟ (zWord S T ⊙ zWord S T)) :=
          PEq.compR _ (PEq.symm (fdot_zWord_zWord S T))
      _ ≡ₜ ((Term.id ((ZTy S T)⋆) ⨟ zWord S T) ⊙ (pureT (ZTy S T) ⨟ zWord S T)) :=
          fdot_precomp _ _ _ _
      _ ≡ₜ (zWord S T ⊙ zBlock S T) := fdot_congr (PEq.id_comp _) pureT_zWord
  calc (appendBlock S T ⨟ Term.unsplit S T)
      ≡ₜ (assocR S⋆ ((ZTy S T)⋆) (ZTy S T) ⨟
          (prodF (Term.id S⋆) (prodF (Term.id ((ZTy S T)⋆)) (pureT (ZTy S T)) ⨟
            binconcat (ZTy S T)) ⨟ (sWord S T ⊙ zWord S T))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (assocR S⋆ ((ZTy S T)⋆) (ZTy S T) ⨟
          ((Term.id S⋆ ⨟ sWord S T) ⊙
            ((prodF (Term.id ((ZTy S T)⋆)) (pureT (ZTy S T)) ⨟ binconcat (ZTy S T)) ⨟
              zWord S T))) := PEq.compR _ (fdot_precomp _ _ _ _)
    _ ≡ₜ (assocR S⋆ ((ZTy S T)⋆) (ZTy S T) ⨟ (sWord S T ⊙ (zWord S T ⊙ zBlock S T))) :=
        PEq.compR _ (fdot_congr (PEq.id_comp _) h1)
    _ ≡ₜ unsplitB S T := PEq.symm (fdot_assoc _ _ _)

/-- A split pair with a last block followed by a word of letters of `S`. -/
theorem fdot_unsplitB_sWord (S T : Ty) :
    ∃ d : Term ((splitCod S T ⊗ ZTy S T) ⊗ S⋆) (splitCod S T ⊗ ZTy S T),
      IsDrop d ∧ (unsplitB S T ⊙ sWord S T) ≡ₜ (d ⨟ unsplitB S T) := by
  refine ⟨assocR (splitCod S T) (ZTy S T) S⋆ ⨟
    prodF (Term.id (splitCod S T)) (zSnoc S T),
    IsDrop.comp (IsDrop.assocR _ _ _) (IsDrop.prodF (IsDrop.id _) (isDrop_zSnoc S T)), ?_⟩
  calc ((Term.unsplit S T ⊙ zBlock S T) ⊙ sWord S T)
      ≡ₜ (assocR (splitCod S T) (ZTy S T) S⋆ ⨟
          (Term.unsplit S T ⊙ (zBlock S T ⊙ sWord S T))) := fdot_assoc _ _ _
    _ ≡ₜ (assocR (splitCod S T) (ZTy S T) S⋆ ⨟
          (Term.unsplit S T ⊙ (zSnoc S T ⨟ zBlock S T))) :=
        PEq.compR _ (fdot_congr (PEq.refl _) (fdot_zBlock_sWord S T))
    _ ≡ₜ (assocR (splitCod S T) (ZTy S T) S⋆ ⨟
          (prodF (Term.id (splitCod S T)) (zSnoc S T) ⨟
            (Term.unsplit S T ⊙ zBlock S T))) := PEq.compR _ (fdot_precompR _ _ _)
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-- A split pair with a last block followed by a split pair. -/
theorem fdot_unsplitB_unsplit (S T : Ty) :
    ∃ d : Term ((splitCod S T ⊗ ZTy S T) ⊗ splitCod S T) (splitCod S T),
      IsDrop d ∧ (unsplitB S T ⊙ Term.unsplit S T) ≡ₜ (d ⨟ Term.unsplit S T) := by
  refine ⟨assocR (splitCod S T) (ZTy S T) (splitCod S T) ⨟
    (prodF (Term.id (splitCod S T))
      (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
        (prodF (zSnoc S T ⨟ pureT (ZTy S T)) (Term.id ((ZTy S T)⋆)) ⨟
          binconcat (ZTy S T))) ⨟
      (assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
        prodF (Term.id S⋆) (binconcat (ZTy S T)))), ?_, ?_⟩
  · refine IsDrop.comp (IsDrop.assocR _ _ _) (IsDrop.comp (IsDrop.prodF (IsDrop.id _) ?_) ?_)
    · exact IsDrop.comp (IsDrop.assocL _ _ _)
        (IsDrop.comp (IsDrop.prodF (IsDrop.comp (isDrop_zSnoc S T) (IsDrop.pureT _))
          (IsDrop.id _)) (IsDrop.binconcat _))
    · exact IsDrop.comp (IsDrop.assocR _ _ _)
        (IsDrop.prodF (IsDrop.id _) (IsDrop.binconcat _))
  calc ((Term.unsplit S T ⊙ zBlock S T) ⊙ Term.unsplit S T)
      ≡ₜ (assocR (splitCod S T) (ZTy S T) (splitCod S T) ⨟
          (Term.unsplit S T ⊙ (zBlock S T ⊙ Term.unsplit S T))) := fdot_assoc _ _ _
    _ ≡ₜ (assocR (splitCod S T) (ZTy S T) (splitCod S T) ⨟
          (Term.unsplit S T ⊙
            ((assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
              (prodF (zSnoc S T ⨟ pureT (ZTy S T)) (Term.id ((ZTy S T)⋆)) ⨟
                binconcat (ZTy S T))) ⨟ zWord S T))) :=
        PEq.compR _ (fdot_congr (PEq.refl _) (fdot_zBlock_unsplit S T))
    _ ≡ₜ (assocR (splitCod S T) (ZTy S T) (splitCod S T) ⨟
          (prodF (Term.id (splitCod S T))
            (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
              (prodF (zSnoc S T ⨟ pureT (ZTy S T)) (Term.id ((ZTy S T)⋆)) ⨟
                binconcat (ZTy S T))) ⨟ (Term.unsplit S T ⊙ zWord S T))) :=
        PEq.compR _ (fdot_precompR _ _ _)
    _ ≡ₜ (assocR (splitCod S T) (ZTy S T) (splitCod S T) ⨟
          (prodF (Term.id (splitCod S T))
            (assocL (ZTy S T) S⋆ ((ZTy S T)⋆) ⨟
              (prodF (zSnoc S T ⨟ pureT (ZTy S T)) (Term.id ((ZTy S T)⋆)) ⨟
                binconcat (ZTy S T))) ⨟
            ((assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
              prodF (Term.id S⋆) (binconcat (ZTy S T))) ⨟ Term.unsplit S T))) :=
        PEq.compR _ (PEq.compR _ (fdot_unsplit_zWord S T))
    _ ≡ₜ _ := by
        refine (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))).trans ?_
        exact PEq.symm (PEq.comp_assoc _ _ _)

/-- A split pair followed by a list of blocks with a last block. -/
theorem fdot_unsplit_zWordB (S T : Ty) :
    ∃ d : Term (splitCod S T ⊗ ((ZTy S T)⋆ ⊗ ZTy S T)) (splitCod S T ⊗ ZTy S T),
      IsDrop d ∧ (Term.unsplit S T ⊙ zWordB S T) ≡ₜ (d ⨟ unsplitB S T) := by
  refine ⟨assocL (splitCod S T) ((ZTy S T)⋆) (ZTy S T) ⨟
    prodF (assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
      prodF (Term.id S⋆) (binconcat (ZTy S T))) (Term.id (ZTy S T)),
    IsDrop.comp (IsDrop.assocL _ _ _)
      (IsDrop.prodF (IsDrop.comp (IsDrop.assocR _ _ _)
        (IsDrop.prodF (IsDrop.id _) (IsDrop.binconcat _))) (IsDrop.id _)), ?_⟩
  calc (Term.unsplit S T ⊙ (zWord S T ⊙ zBlock S T))
      ≡ₜ (assocL (splitCod S T) ((ZTy S T)⋆) (ZTy S T) ⨟
          ((Term.unsplit S T ⊙ zWord S T) ⊙ zBlock S T)) := fdot_assoc' _ _ _
    _ ≡ₜ (assocL (splitCod S T) ((ZTy S T)⋆) (ZTy S T) ⨟
          (((assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
            prodF (Term.id S⋆) (binconcat (ZTy S T))) ⨟ Term.unsplit S T) ⊙ zBlock S T)) :=
        PEq.compR _ (fdot_congr (fdot_unsplit_zWord S T) (PEq.refl _))
    _ ≡ₜ (assocL (splitCod S T) ((ZTy S T)⋆) (ZTy S T) ⨟
          (prodF (assocR S⋆ ((ZTy S T)⋆) ((ZTy S T)⋆) ⨟
            prodF (Term.id S⋆) (binconcat (ZTy S T))) (Term.id (ZTy S T)) ⨟
            (Term.unsplit S T ⊙ zBlock S T))) := PEq.compR _ (fdot_precompL _ _ _)
    _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)

/-! ### Homomorphic images of contents -/

/-- The homomorphism extending a homomorphism. -/
theorem homT_homT {A B : Ty} (f : Term A B⋆) : homT (homT f) ≡ₜ (concat A ⨟ homT f) := by
  have hid : homT (Term.id A⋆) ≡ₜ concat A :=
    (PEq.compL _ (PEq.list_id A⋆)).trans (PEq.id_comp _)
  calc homT (homT f)
      ≡ₜ homT (Term.id A⋆ ⨟ homT f) := homT_congr (PEq.symm (PEq.id_comp _))
    _ ≡ₜ (homT (Term.id A⋆) ⨟ homT f) := PEq.symm (homT_comp _ _)
    _ ≡ₜ (concat A ⨟ homT f) := PEq.compL _ hid

/-- The concatenation of a list of words of letters of `S`. -/
theorem homT_sWord (S T : Ty) : homT (sWord S T) ≡ₜ (concat S ⨟ sWord S T) :=
  homT_homT _

/-- The concatenation of a list of lists of blocks. -/
theorem homT_zWord (S T : Ty) : homT (zWord S T) ≡ₜ (concat (ZTy S T) ⨟ zWord S T) :=
  homT_homT _

/-- The content of a list of pairs, read through a co-pairing. -/
theorem pairContent_comp_homT {A B C : Ty} (p : Term A C⋆) (q : Term B C⋆) :
    (pairContent A B ⨟ homT (Term.either p q)) ≡ₜ homT (p ⊙ q) := by
  set k : Term (A ⊕' B) C⋆ := Term.either p q with hk
  have hl : ((inl A B ⨟ pureT (A ⊕' B)) ⨟ homT k) ≡ₜ p :=
    (pure_homT_comp _ _).trans (inl_either _ _)
  have hr : ((inr A B ⨟ pureT (A ⊕' B)) ⨟ homT k) ≡ₜ q :=
    (pure_homT_comp _ _).trans (inr_either _ _)
  show (homT ((inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))) ⨟ homT k) ≡ₜ homT (p ⊙ q)
  calc (homT ((inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))) ⨟ homT k)
      ≡ₜ homT (((inl A B ⨟ pureT (A ⊕' B)) ⊙ (inr A B ⨟ pureT (A ⊕' B))) ⨟ homT k) :=
        homT_comp _ _
    _ ≡ₜ homT (((inl A B ⨟ pureT (A ⊕' B)) ⨟ homT k) ⊙
          ((inr A B ⨟ pureT (A ⊕' B)) ⨟ homT k)) := homT_congr (fdot_comp_homT _ _ _)
    _ ≡ₜ homT (p ⊙ q) := homT_congr (fdot_congr hl hr)

/-- The content of the codomain of `shift`, read through a co-pairing. -/
theorem shiftContent_comp_homT {A B C : Ty} (p : Term A C⋆) (q : Term B C⋆) :
    (shiftContent A B ⨟ homT (Term.either p q)) ≡ₜ
      Term.either (nilT C) (p ⊙ (homT (q ⊙ p) ⊙ q)) := by
  set k : Term (A ⊕' B) C⋆ := Term.either p q with hk
  have hl : ((inl A B ⨟ pureT (A ⊕' B)) ⨟ homT k) ≡ₜ p :=
    (pure_homT_comp _ _).trans (inl_either _ _)
  have hr : ((inr A B ⨟ pureT (A ⊕' B)) ⨟ homT k) ≡ₜ q :=
    (pure_homT_comp _ _).trans (inr_either _ _)
  have hmid : (homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⨟ homT k) ≡ₜ
      homT (q ⊙ p) := by
    calc (homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⨟ homT k)
        ≡ₜ homT (((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⨟ homT k) :=
          homT_comp _ _
      _ ≡ₜ homT (((inr A B ⨟ pureT (A ⊕' B)) ⨟ homT k) ⊙
            ((inl A B ⨟ pureT (A ⊕' B)) ⨟ homT k)) := homT_congr (fdot_comp_homT _ _ _)
      _ ≡ₜ homT (q ⊙ p) := homT_congr (fdot_congr hr hl)
  show (Term.either (nilT (A ⊕' B))
      ((inl A B ⨟ pureT (A ⊕' B)) ⊙
        (homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⊙
          (inr A B ⨟ pureT (A ⊕' B)))) ⨟ homT k) ≡ₜ _
  calc (Term.either (nilT (A ⊕' B))
        ((inl A B ⨟ pureT (A ⊕' B)) ⊙
          (homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⊙
            (inr A B ⨟ pureT (A ⊕' B)))) ⨟ homT k)
      ≡ₜ Term.either (nilT (A ⊕' B) ⨟ homT k)
          (((inl A B ⨟ pureT (A ⊕' B)) ⊙
            (homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⊙
              (inr A B ⨟ pureT (A ⊕' B)))) ⨟ homT k) := either_comp _ _ _
    _ ≡ₜ Term.either (nilT C)
          (((inl A B ⨟ pureT (A ⊕' B)) ⨟ homT k) ⊙
            ((homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⊙
              (inr A B ⨟ pureT (A ⊕' B))) ⨟ homT k)) :=
        either_congr (homT_nil _) (fdot_comp_homT _ _ _)
    _ ≡ₜ Term.either (nilT C)
          (p ⊙ ((homT ((inr A B ⨟ pureT (A ⊕' B)) ⊙ (inl A B ⨟ pureT (A ⊕' B))) ⨟ homT k) ⊙
            ((inr A B ⨟ pureT (A ⊕' B)) ⨟ homT k))) :=
        either_congr (PEq.refl _) (fdot_congr hl (fdot_comp_homT _ _ _))
    _ ≡ₜ Term.either (nilT C) (p ⊙ (homT (q ⊙ p) ⊙ q)) :=
        either_congr (PEq.refl _) (fdot_congr (PEq.refl _) (fdot_congr hmid hr))

/-- **The homomorphism extending a concatenation of two contents**: the concatenation of a
list of pairs is the content of the first component, the alternating contents of the
following pairs, and the content of the last second component. -/
theorem homT_fdot {V₁ V₂ C : Ty} (x : Term V₁ C⋆) (y : Term V₂ C⋆) :
    homT (x ⊙ y) ≡ₜ
      (Term.shift V₁ V₂ ⨟ Term.either (nilT C) (x ⊙ (homT (y ⊙ x) ⊙ y))) := by
  calc homT (x ⊙ y)
      ≡ₜ (pairContent V₁ V₂ ⨟ homT (Term.either x y)) :=
        PEq.symm (pairContent_comp_homT x y)
    _ ≡ₜ ((Term.shift V₁ V₂ ⨟ shiftContent V₁ V₂) ⨟ homT (Term.either x y)) :=
        PEq.compL _ (PEq.symm (Term.shift_rebracketing V₁ V₂))
    _ ≡ₜ (Term.shift V₁ V₂ ⨟ (shiftContent V₁ V₂ ⨟ homT (Term.either x y))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.shift V₁ V₂ ⨟ Term.either (nilT C) (x ⊙ (homT (y ⊙ x) ⊙ y))) :=
        PEq.compR _ (shiftContent_comp_homT x y)

/-- **The homomorphism extending the content of a split pair with a last block**: the
concatenation of a list of such contents is empty, or again such a content. -/
theorem homT_unsplitB (S T : Ty) :
    ∃ e : Term (splitCod S T ⊗ (((ZTy S T) ⊗ splitCod S T)⋆ ⊗ ZTy S T))
        (splitCod S T ⊗ ZTy S T),
      IsDrop e ∧ homT (unsplitB S T) ≡ₜ
        (Term.shift (splitCod S T) (ZTy S T) ⨟
          Term.either (nilT (S ⊕' T)) (e ⨟ unsplitB S T)) := by
  obtain ⟨dBP, hdBP, heBP⟩ :
      ∃ d : Term (ZTy S T ⊗ splitCod S T) ((ZTy S T)⋆),
        IsDrop d ∧ (zBlock S T ⊙ Term.unsplit S T) ≡ₜ (d ⨟ zWord S T) :=
    ⟨_, IsDrop.comp (IsDrop.assocL _ _ _)
      (IsDrop.comp (IsDrop.prodF (IsDrop.comp (isDrop_zSnoc S T) (IsDrop.pureT _))
        (IsDrop.id _)) (IsDrop.binconcat _)), fdot_zBlock_unsplit S T⟩
  obtain ⟨dPZB, hdPZB, hePZB⟩ := fdot_unsplit_zWordB S T
  set w : Term (((ZTy S T) ⊗ splitCod S T)⋆) ((ZTy S T)⋆) :=
    listF dBP ⨟ concat (ZTy S T) with hw
  have hwd : IsDrop w := IsDrop.comp (IsDrop.listF hdBP) (IsDrop.concat _)
  have hmid : homT (zBlock S T ⊙ Term.unsplit S T) ≡ₜ (w ⨟ zWord S T) := by
    calc homT (zBlock S T ⊙ Term.unsplit S T)
        ≡ₜ homT (dBP ⨟ zWord S T) := homT_congr heBP
      _ ≡ₜ (listF dBP ⨟ homT (zWord S T)) := homT_precomp _ _
      _ ≡ₜ (listF dBP ⨟ (concat (ZTy S T) ⨟ zWord S T)) := PEq.compR _ (homT_zWord S T)
      _ ≡ₜ (w ⨟ zWord S T) := PEq.symm (PEq.comp_assoc _ _ _)
  refine ⟨prodF (Term.id (splitCod S T)) (prodF w (Term.id (ZTy S T))) ⨟ dPZB,
    IsDrop.comp (IsDrop.prodF (IsDrop.id _) (IsDrop.prodF hwd (IsDrop.id _))) hdPZB, ?_⟩
  have hbody : (Term.unsplit S T ⊙ (homT (zBlock S T ⊙ Term.unsplit S T) ⊙ zBlock S T)) ≡ₜ
      ((prodF (Term.id (splitCod S T)) (prodF w (Term.id (ZTy S T))) ⨟ dPZB) ⨟
        unsplitB S T) := by
    calc (Term.unsplit S T ⊙ (homT (zBlock S T ⊙ Term.unsplit S T) ⊙ zBlock S T))
        ≡ₜ (Term.unsplit S T ⊙ ((w ⨟ zWord S T) ⊙ zBlock S T)) :=
          fdot_congr (PEq.refl _) (fdot_congr hmid (PEq.refl _))
      _ ≡ₜ (Term.unsplit S T ⊙ (prodF w (Term.id (ZTy S T)) ⨟ zWordB S T)) :=
          fdot_congr (PEq.refl _) (fdot_precompL _ _ _)
      _ ≡ₜ (prodF (Term.id (splitCod S T)) (prodF w (Term.id (ZTy S T))) ⨟
            (Term.unsplit S T ⊙ zWordB S T)) := fdot_precompR _ _ _
      _ ≡ₜ (prodF (Term.id (splitCod S T)) (prodF w (Term.id (ZTy S T))) ⨟
            (dPZB ⨟ unsplitB S T)) := PEq.compR _ hePZB
      _ ≡ₜ _ := PEq.symm (PEq.comp_assoc _ _ _)
  calc homT (unsplitB S T)
      ≡ₜ (Term.shift (splitCod S T) (ZTy S T) ⨟
          Term.either (nilT (S ⊕' T))
            (Term.unsplit S T ⊙
              (homT (zBlock S T ⊙ Term.unsplit S T) ⊙ zBlock S T))) :=
        homT_fdot _ _
    _ ≡ₜ _ := PEq.compR _ (either_congr (PEq.refl _) hbody)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
