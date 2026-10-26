import Lax149335Proofs.SimpleCompleteness.JointCasesDepth
import Mathlib.Tactic.Set

/-!
# Peeling one block off a list over a co-product

Let `E` and `N` be two types and let `h = either [] f` be a term on `E + N` whose case on `E`
is the empty constant.  The proof of value extraction decomposes the homomorphism `hom h` on
`(E + N)*` by peeling off, from the left or from the right, one *block*: a maximal run of
elements of `E` followed (or preceded) by one element of `N`.

This file provides the two corresponding provable isomorphisms

* `Lax149335Proofs.unpeelL : E* + ((E* × N) × (E + N)*) → (E + N)*`,
* `Lax149335Proofs.unpeelR : E* + ((E + N)* × (N × E*)) → (E + N)*`,

together with the two equations describing the effect of `hom h` after them.  Both types
occurring in the co-product have the list nesting depth of `(E + N)*`, which is what makes
this decomposition usable in the proof of value extraction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Provable isomorphisms among the atomic terms -/

namespace ProvableIso

theorem unitR (A : Ty) : ProvableIso (Term.unitR A) :=
  ⟨Term.fst A Ty.unit, PEq.unitR_fst A, PEq.fst_unitR A⟩

theorem fst_unit (A : Ty) : ProvableIso (Term.fst A Ty.unit) :=
  ⟨Term.unitR A, PEq.fst_unitR A, PEq.unitR_fst A⟩

theorem snd_unit (A : Ty) : ProvableIso (Term.snd Ty.unit A) :=
  ⟨Term.unitL A, PEq.snd_unitL A, PEq.unitL_snd A⟩

theorem assocR (A B C : Ty) : ProvableIso (Term.assocR A B C) :=
  ⟨Term.assocL A B C, PEq.assocR_assocL A B C, PEq.assocL_assocR A B C⟩

theorem assocL (A B C : Ty) : ProvableIso (Term.assocL A B C) :=
  ⟨Term.assocR A B C, PEq.assocL_assocR A B C, PEq.assocR_assocL A B C⟩

theorem cons (A : Ty) : ProvableIso (Term.cons A) :=
  ⟨Term.uncons A, PEq.cons_uncons A, PEq.uncons_cons A⟩

theorem snoc (A : Ty) : ProvableIso (Term.snoc A) :=
  ⟨Term.unsnoc A, PEq.snoc_unsnoc A, PEq.unsnoc_snoc A⟩

theorem block (A B : Ty) : ProvableIso (Term.block A B) :=
  ⟨Term.unblock A B, PEq.block_unblock A B, PEq.unblock_block A B⟩

theorem unblock (A B : Ty) : ProvableIso (Term.unblock A B) :=
  ⟨Term.block A B, PEq.unblock_block A B, PEq.block_unblock A B⟩

end ProvableIso

/-! ### Two general equalities for the concatenation combinator -/

namespace Term

variable {B : Ty}

/-- Pre-composing both factors of a concatenation. -/
theorem fdot_comp_both {W₁ W₂ X₁ X₂ : Ty} (p : Term W₁ X₁) (q : Term W₂ X₂)
    (x : Term X₁ B⋆) (y : Term X₂ B⋆) :
    (prodF p q ⨟ (x ⊙ y)) ≡ₜ ((p ⨟ x) ⊙ (q ⨟ y)) := by
  calc (prodF p q ⨟ (prodF x y ⨟ binconcat B))
      ≡ₜ ((prodF p q ⨟ prodF x y) ⨟ binconcat B) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (prodF (p ⨟ x) (q ⨟ y) ⨟ binconcat B) := PEq.compL _ (PEq.prod_comp _ _ _ _)

/-- A homomorphism on a list built by `cons`. -/
theorem homT_cons {A : Ty} (f : Term A B⋆) :
    (cons A ⨟ homT f) ≡ₜ either (nilT B) (f ⊙ homT f) := by
  have hc : cons A ≡ₜ either (nilT A) (prepend A) := by
    calc cons A ≡ₜ (Term.id (Ty.unit ⊕' (A ⊗ A⋆)) ⨟ cons A) := PEq.symm (PEq.id_comp _)
      _ ≡ₜ (either (inl Ty.unit (A ⊗ A⋆)) (inr Ty.unit (A ⊗ A⋆)) ⨟ cons A) :=
          PEq.compL _ (PEq.symm (either_inl_inr _ _))
      _ ≡ₜ either (inl Ty.unit (A ⊗ A⋆) ⨟ cons A) (inr Ty.unit (A ⊗ A⋆) ⨟ cons A) :=
          either_comp _ _ _
  have hp : (prepend A ⨟ homT f) ≡ₜ (f ⊙ homT f) := by
    calc (prepend A ⨟ homT f)
        ≡ₜ ((prodF (pureT A) (Term.id A⋆) ⨟ binconcat A) ⨟ homT f) :=
          PEq.compL _ (PEq.prepend_def A)
      _ ≡ₜ (prodF (pureT A) (Term.id A⋆) ⨟ (binconcat A ⨟ homT f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (pureT A) (Term.id A⋆) ⨟ (prodF (homT f) (homT f) ⨟ binconcat B)) :=
          PEq.compR _ (homT_binconcat f)
      _ ≡ₜ ((prodF (pureT A) (Term.id A⋆) ⨟ prodF (homT f) (homT f)) ⨟ binconcat B) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (pureT A ⨟ homT f) (Term.id A⋆ ⨟ homT f) ⨟ binconcat B) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF f (homT f) ⨟ binconcat B) :=
          PEq.compL _ (PEq.congr_prodF (homT_pure f) (PEq.id_comp _))
  calc (cons A ⨟ homT f) ≡ₜ (either (nilT A) (prepend A) ⨟ homT f) := PEq.compL _ hc
    _ ≡ₜ either (nilT A ⨟ homT f) (prepend A ⨟ homT f) := either_comp _ _ _
    _ ≡ₜ either (nilT B) (f ⊙ homT f) := either_congr (homT_nil f) hp

/-- A homomorphism on a list built by `snoc`. -/
theorem homT_snoc {A : Ty} (f : Term A B⋆) :
    (snoc A ⨟ homT f) ≡ₜ either (nilT B) (homT f ⊙ f) := by
  have hc : snoc A ≡ₜ either (nilT A) (append A) := by
    calc snoc A ≡ₜ (Term.id (Ty.unit ⊕' (A⋆ ⊗ A)) ⨟ snoc A) := PEq.symm (PEq.id_comp _)
      _ ≡ₜ (either (inl Ty.unit (A⋆ ⊗ A)) (inr Ty.unit (A⋆ ⊗ A)) ⨟ snoc A) :=
          PEq.compL _ (PEq.symm (either_inl_inr _ _))
      _ ≡ₜ either (inl Ty.unit (A⋆ ⊗ A) ⨟ snoc A) (inr Ty.unit (A⋆ ⊗ A) ⨟ snoc A) :=
          either_comp _ _ _
      _ ≡ₜ either (nilT A) (append A) := either_congr (PEq.inl_snoc_cons A) (PEq.refl _)
  have hp : (append A ⨟ homT f) ≡ₜ (homT f ⊙ f) := by
    calc (append A ⨟ homT f)
        ≡ₜ ((prodF (Term.id A⋆) (pureT A) ⨟ binconcat A) ⨟ homT f) :=
          PEq.compL _ (PEq.append_def A)
      _ ≡ₜ (prodF (Term.id A⋆) (pureT A) ⨟ (binconcat A ⨟ homT f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (prodF (Term.id A⋆) (pureT A) ⨟ (prodF (homT f) (homT f) ⨟ binconcat B)) :=
          PEq.compR _ (homT_binconcat f)
      _ ≡ₜ ((prodF (Term.id A⋆) (pureT A) ⨟ prodF (homT f) (homT f)) ⨟ binconcat B) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (prodF (Term.id A⋆ ⨟ homT f) (pureT A ⨟ homT f) ⨟ binconcat B) :=
          PEq.compL _ (PEq.prod_comp _ _ _ _)
      _ ≡ₜ (prodF (homT f) f ⨟ binconcat B) :=
          PEq.compL _ (PEq.congr_prodF (PEq.id_comp _) (homT_pure f))
  calc (snoc A ⨟ homT f) ≡ₜ (either (nilT A) (append A) ⨟ homT f) := PEq.compL _ hc
    _ ≡ₜ either (nilT A ⨟ homT f) (append A ⨟ homT f) := either_comp _ _ _
    _ ≡ₜ either (nilT B) (homT f ⊙ f) := either_congr (homT_nil f) hp

end Term

/-! ### The two peeling isomorphisms -/

variable {B : Ty}

/-- The empty constant on a type. -/
abbrev nilconst (B A : Ty) : Term A B⋆ := Term.toUnit A ⨟ Term.nilT B

/-- A *left block*: a run of elements of `E`, which contributes nothing, followed by one
element of `N`. -/
def blockL (B E : Ty) {N : Ty} (F : Term N B⋆) : Term (E⋆ ⊗ N) B⋆ := nilconst B E⋆ ⊙ F

/-- A *right block*: one element of `N` followed by a run of elements of `E`. -/
def blockR (B E : Ty) {N : Ty} (F : Term N B⋆) : Term (N ⊗ E⋆) B⋆ := F ⊙ nilconst B E⋆

/-- The term on `E + N` all of whose elements of `E` are erased. -/
abbrev nilCase (B E : Ty) {N : Ty} (F : Term N B⋆) : Term (E ⊕' N) B⋆ :=
  Term.either (nilconst B E) F

/-- Composing the inverse of `block` with the homomorphism of a term that erases `E`. -/
theorem unblock_homT_nilCase {E N : Ty} (F : Term N B⋆) :
    (Term.unblock E N ⨟ homT (nilCase B E F)) ≡ₜ
      (nilconst B E⋆ ⊙ homT (blockR B E F)) := by
  have hE : (Term.inl E N ⨟ nilCase B E F) ≡ₜ nilconst B E :=
    Term.inl_either _ _
  have hN : (Term.inr E N ⨟ nilCase B E F) ≡ₜ F := Term.inr_either _ _
  have hEh : homT (Term.inl E N ⨟ nilCase B E F) ≡ₜ nilconst B E⋆ :=
    (Term.homT_congr hE).trans (Term.homT_nilconst E B)
  calc (Term.unblock E N ⨟ homT (nilCase B E F))
      ≡ₜ (homT (Term.inl E N ⨟ nilCase B E F) ⊙
          homT ((Term.inr E N ⨟ nilCase B E F) ⊙ homT (Term.inl E N ⨟ nilCase B E F))) :=
        Term.unblock_comp_homT _
    _ ≡ₜ (nilconst B E⋆ ⊙ homT (F ⊙ nilconst B E⋆)) :=
        Term.fdot_congr hEh (Term.homT_congr (Term.fdot_congr hN hEh))

/-- **Peeling one block off on the left.**  A list over `E + N` is either a list over `E`, or
a list over `E` followed by one element of `N` followed by a list over `E + N`. -/
def unpeelL (E N : Ty) :
    Term (E⋆ ⊕' ((E⋆ ⊗ N) ⊗ (E ⊕' N)⋆)) ((E ⊕' N)⋆) :=
  Term.sumF (Term.unitR E⋆)
      (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
        (Term.assocR E⋆ N (E⋆ ⊗ (N ⊗ E⋆)⋆) ⨟
          Term.prodF (Term.id E⋆) (Term.assocL N E⋆ ((N ⊗ E⋆)⋆)))) ⨟
    Term.undistR E⋆ Ty.unit ((N ⊗ E⋆) ⊗ (N ⊗ E⋆)⋆) ⨟
      Term.prodF (Term.id E⋆) (Term.cons (N ⊗ E⋆)) ⨟ Term.unblock E N

/-- **Peeling one block off on the right.** -/
def unpeelR (E N : Ty) :
    Term (E⋆ ⊕' ((E ⊕' N)⋆ ⊗ (N ⊗ E⋆))) ((E ⊕' N)⋆) :=
  Term.sumF (Term.unitR E⋆)
      (Term.prodF (Term.block E N) (Term.id (N ⊗ E⋆)) ⨟
        Term.assocR E⋆ ((N ⊗ E⋆)⋆) (N ⊗ E⋆)) ⨟
    Term.undistR E⋆ Ty.unit (((N ⊗ E⋆)⋆) ⊗ (N ⊗ E⋆)) ⨟
      Term.prodF (Term.id E⋆) (Term.snoc (N ⊗ E⋆)) ⨟ Term.unblock E N

theorem provableIso_unpeelL (E N : Ty) : ProvableIso (unpeelL E N) := by
  refine ProvableIso.comp (ProvableIso.comp (ProvableIso.comp ?_ (ProvableIso.undistR _ _ _))
    (ProvableIso.prodF (ProvableIso.id _) (ProvableIso.cons _))) (ProvableIso.unblock E N)
  exact ProvableIso.sumF (ProvableIso.unitR _)
    (ProvableIso.comp (ProvableIso.prodF (ProvableIso.id _) (ProvableIso.block E N))
      (ProvableIso.comp (ProvableIso.assocR _ _ _)
        (ProvableIso.prodF (ProvableIso.id _) (ProvableIso.assocL _ _ _))))

theorem provableIso_unpeelR (E N : Ty) : ProvableIso (unpeelR E N) := by
  refine ProvableIso.comp (ProvableIso.comp (ProvableIso.comp ?_ (ProvableIso.undistR _ _ _))
    (ProvableIso.prodF (ProvableIso.id _) (ProvableIso.snoc _))) (ProvableIso.unblock E N)
  exact ProvableIso.sumF (ProvableIso.unitR _)
    (ProvableIso.comp (ProvableIso.prodF (ProvableIso.block E N) (ProvableIso.id _))
      (ProvableIso.assocR _ _ _))

/-- **The effect of peeling one block off on the left.** -/
theorem unpeelL_homT {E N : Ty} (F : Term N B⋆) :
    (unpeelL E N ⨟ homT (nilCase B E F)) ≡ₜ
      Term.either (nilconst B E⋆) (blockL B E F ⊙ homT (nilCase B E F)) := by
  set h : Term (E ⊕' N) B⋆ := nilCase B E F with hh
  set nE : Term (E⋆) B⋆ := nilconst B E⋆ with hnE
  set M : Ty := N ⊗ E⋆ with hM
  set G : Term M B⋆ := blockR B E F with hG
  -- the four stages of the isomorphism
  have h1 : (Term.unblock E N ⨟ homT h) ≡ₜ (nE ⊙ homT G) := unblock_homT_nilCase F
  have h2 : (Term.prodF (Term.id E⋆) (Term.cons M) ⨟ (nE ⊙ homT G)) ≡ₜ
      (nE ⊙ Term.either (Term.nilT B) (G ⊙ homT G)) :=
    (Term.fdot_comp_both _ _ _ _).trans
      (Term.fdot_congr (PEq.id_comp _) (Term.homT_cons G))
  have h3 : (Term.undistR E⋆ Ty.unit (M ⊗ M⋆) ⨟
        (nE ⊙ Term.either (Term.nilT B) (G ⊙ homT G))) ≡ₜ
      Term.either (nE ⊙ Term.nilT B) (nE ⊙ (G ⊙ homT G)) := by
    calc (Term.undistR E⋆ Ty.unit (M ⊗ M⋆) ⨟
          (nE ⊙ Term.either (Term.nilT B) (G ⊙ homT G)))
        ≡ₜ (Term.undistR E⋆ Ty.unit (M ⊗ M⋆) ⨟
            (Term.distR E⋆ Ty.unit (M ⊗ M⋆) ⨟
              Term.either (nE ⊙ Term.nilT B) (nE ⊙ (G ⊙ homT G)))) :=
          PEq.compR _ (Term.fdot_either_distR _ _ _)
      _ ≡ₜ ((Term.undistR E⋆ Ty.unit (M ⊗ M⋆) ⨟ Term.distR E⋆ Ty.unit (M ⊗ M⋆)) ⨟
            Term.either (nE ⊙ Term.nilT B) (nE ⊙ (G ⊙ homT G))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id _ ⨟ Term.either (nE ⊙ Term.nilT B) (nE ⊙ (G ⊙ homT G))) :=
          PEq.compL _ (PEq.undistR_distR _ _ _)
      _ ≡ₜ _ := PEq.id_comp _
  -- the left summand
  have hleft : (Term.unitR E⋆ ⨟ (nE ⊙ Term.nilT B)) ≡ₜ nE := by
    calc (Term.unitR E⋆ ⨟ (nE ⊙ Term.nilT B))
        ≡ₜ (Term.unitR E⋆ ⨟ (Term.fst E⋆ Ty.unit ⨟ nE)) :=
          PEq.compR _ (Term.fdot_nil_right nE)
      _ ≡ₜ ((Term.unitR E⋆ ⨟ Term.fst E⋆ Ty.unit) ⨟ nE) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id E⋆ ⨟ nE) := PEq.compL _ (PEq.unitR_fst E⋆)
      _ ≡ₜ nE := PEq.id_comp _
  -- the right summand
  have hright : ((Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
        (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
          Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))) ⨟ (nE ⊙ (G ⊙ homT G))) ≡ₜ
      (blockL B E F ⊙ homT h) := by
    have e1 : (Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)) ⨟ (nE ⊙ (G ⊙ homT G))) ≡ₜ
        (nE ⊙ (F ⊙ (nE ⊙ homT G))) := by
      refine (Term.fdot_comp_both _ _ _ _).trans ?_
      refine Term.fdot_congr (PEq.id_comp _) ?_
      calc (Term.assocL N E⋆ (M⋆) ⨟ (G ⊙ homT G))
          ≡ₜ (Term.assocL N E⋆ (M⋆) ⨟ (Term.assocR N E⋆ (M⋆) ⨟ (F ⊙ (nE ⊙ homT G)))) :=
            PEq.compR _ (Term.fdot_assoc F nE (homT G))
        _ ≡ₜ ((Term.assocL N E⋆ (M⋆) ⨟ Term.assocR N E⋆ (M⋆)) ⨟ (F ⊙ (nE ⊙ homT G))) :=
            PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id _ ⨟ (F ⊙ (nE ⊙ homT G))) := PEq.compL _ (PEq.assocL_assocR _ _ _)
        _ ≡ₜ _ := PEq.id_comp _
    have e2 : (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟ (nE ⊙ (F ⊙ (nE ⊙ homT G)))) ≡ₜ
        (blockL B E F ⊙ (nE ⊙ homT G)) :=
      PEq.symm (Term.fdot_assoc nE F (nE ⊙ homT G))
    have e3 : (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
        (blockL B E F ⊙ (nE ⊙ homT G))) ≡ₜ (blockL B E F ⊙ homT h) := by
      refine (Term.fdot_comp_both _ _ _ _).trans ?_
      refine Term.fdot_congr (PEq.id_comp _) ?_
      calc (Term.block E N ⨟ (nE ⊙ homT G))
          ≡ₜ (Term.block E N ⨟ (Term.unblock E N ⨟ homT h)) := PEq.compR _ (PEq.symm h1)
        _ ≡ₜ ((Term.block E N ⨟ Term.unblock E N) ⨟ homT h) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id _ ⨟ homT h) := PEq.compL _ (PEq.block_unblock E N)
        _ ≡ₜ homT h := PEq.id_comp _
    calc ((Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
            (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
              Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))) ⨟ (nE ⊙ (G ⊙ homT G)))
        ≡ₜ (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
            ((Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
              Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆))) ⨟ (nE ⊙ (G ⊙ homT G)))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
            (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
              (Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)) ⨟ (nE ⊙ (G ⊙ homT G))))) :=
          PEq.compR _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
            (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟ (nE ⊙ (F ⊙ (nE ⊙ homT G))))) :=
          PEq.compR _ (PEq.compR _ e1)
      _ ≡ₜ (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
            (blockL B E F ⊙ (nE ⊙ homT G))) := PEq.compR _ e2
      _ ≡ₜ (blockL B E F ⊙ homT h) := e3
  -- putting the stages together
  calc (unpeelL E N ⨟ homT h)
      ≡ₜ (Term.sumF (Term.unitR E⋆)
            (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
              (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
                Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))) ⨟
          (Term.undistR E⋆ Ty.unit (M ⊗ M⋆) ⨟
            (Term.prodF (Term.id E⋆) (Term.cons M) ⨟ (Term.unblock E N ⨟ homT h)))) :=
        (PEq.comp_assoc
            ((Term.sumF (Term.unitR E⋆)
                (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
                  (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
                    Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))) ⨟
              Term.undistR E⋆ Ty.unit (M ⊗ M⋆)) ⨟
              Term.prodF (Term.id E⋆) (Term.cons M))
            (Term.unblock E N) (homT h)).trans
          ((PEq.comp_assoc
              (Term.sumF (Term.unitR E⋆)
                  (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
                    (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
                      Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))) ⨟
                Term.undistR E⋆ Ty.unit (M ⊗ M⋆))
              (Term.prodF (Term.id E⋆) (Term.cons M))
              (Term.unblock E N ⨟ homT h)).trans
            (PEq.comp_assoc
              (Term.sumF (Term.unitR E⋆)
                (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
                  (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
                    Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))))
              (Term.undistR E⋆ Ty.unit (M ⊗ M⋆))
              (Term.prodF (Term.id E⋆) (Term.cons M) ⨟ (Term.unblock E N ⨟ homT h))))
    _ ≡ₜ (Term.sumF (Term.unitR E⋆)
            (Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
              (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
                Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))) ⨟
          Term.either (nE ⊙ Term.nilT B) (nE ⊙ (G ⊙ homT G))) :=
        PEq.compR _ ((PEq.compR _ ((PEq.compR _ h1).trans h2)).trans h3)
    _ ≡ₜ Term.either (Term.unitR E⋆ ⨟ (nE ⊙ Term.nilT B))
          ((Term.prodF (Term.id (E⋆ ⊗ N)) (Term.block E N) ⨟
            (Term.assocR E⋆ N (E⋆ ⊗ M⋆) ⨟
              Term.prodF (Term.id E⋆) (Term.assocL N E⋆ (M⋆)))) ⨟ (nE ⊙ (G ⊙ homT G))) :=
        Term.sumF_either _ _ _ _
    _ ≡ₜ Term.either nE (blockL B E F ⊙ homT h) := Term.either_congr hleft hright

/-- **The effect of peeling one block off on the right.** -/
theorem unpeelR_homT {E N : Ty} (F : Term N B⋆) :
    (unpeelR E N ⨟ homT (nilCase B E F)) ≡ₜ
      Term.either (nilconst B E⋆) (homT (nilCase B E F) ⊙ blockR B E F) := by
  set h : Term (E ⊕' N) B⋆ := nilCase B E F with hh
  set nE : Term (E⋆) B⋆ := nilconst B E⋆ with hnE
  set M : Ty := N ⊗ E⋆ with hM
  set G : Term M B⋆ := blockR B E F with hG
  have h1 : (Term.unblock E N ⨟ homT h) ≡ₜ (nE ⊙ homT G) := unblock_homT_nilCase F
  have h2 : (Term.prodF (Term.id E⋆) (Term.snoc M) ⨟ (nE ⊙ homT G)) ≡ₜ
      (nE ⊙ Term.either (Term.nilT B) (homT G ⊙ G)) :=
    (Term.fdot_comp_both _ _ _ _).trans
      (Term.fdot_congr (PEq.id_comp _) (Term.homT_snoc G))
  have h3 : (Term.undistR E⋆ Ty.unit (M⋆ ⊗ M) ⨟
        (nE ⊙ Term.either (Term.nilT B) (homT G ⊙ G))) ≡ₜ
      Term.either (nE ⊙ Term.nilT B) (nE ⊙ (homT G ⊙ G)) := by
    calc (Term.undistR E⋆ Ty.unit (M⋆ ⊗ M) ⨟
          (nE ⊙ Term.either (Term.nilT B) (homT G ⊙ G)))
        ≡ₜ (Term.undistR E⋆ Ty.unit (M⋆ ⊗ M) ⨟
            (Term.distR E⋆ Ty.unit (M⋆ ⊗ M) ⨟
              Term.either (nE ⊙ Term.nilT B) (nE ⊙ (homT G ⊙ G)))) :=
          PEq.compR _ (Term.fdot_either_distR _ _ _)
      _ ≡ₜ ((Term.undistR E⋆ Ty.unit (M⋆ ⊗ M) ⨟ Term.distR E⋆ Ty.unit (M⋆ ⊗ M)) ⨟
            Term.either (nE ⊙ Term.nilT B) (nE ⊙ (homT G ⊙ G))) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id _ ⨟ Term.either (nE ⊙ Term.nilT B) (nE ⊙ (homT G ⊙ G))) :=
          PEq.compL _ (PEq.undistR_distR _ _ _)
      _ ≡ₜ _ := PEq.id_comp _
  have hleft : (Term.unitR E⋆ ⨟ (nE ⊙ Term.nilT B)) ≡ₜ nE := by
    calc (Term.unitR E⋆ ⨟ (nE ⊙ Term.nilT B))
        ≡ₜ (Term.unitR E⋆ ⨟ (Term.fst E⋆ Ty.unit ⨟ nE)) :=
          PEq.compR _ (Term.fdot_nil_right nE)
      _ ≡ₜ ((Term.unitR E⋆ ⨟ Term.fst E⋆ Ty.unit) ⨟ nE) := PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.id E⋆ ⨟ nE) := PEq.compL _ (PEq.unitR_fst E⋆)
      _ ≡ₜ nE := PEq.id_comp _
  have hright : ((Term.prodF (Term.block E N) (Term.id M) ⨟ Term.assocR E⋆ (M⋆) M) ⨟
      (nE ⊙ (homT G ⊙ G))) ≡ₜ (homT h ⊙ G) := by
    have e2 : (Term.assocR E⋆ (M⋆) M ⨟ (nE ⊙ (homT G ⊙ G))) ≡ₜ ((nE ⊙ homT G) ⊙ G) :=
      PEq.symm (Term.fdot_assoc nE (homT G) G)
    have e3 : (Term.prodF (Term.block E N) (Term.id M) ⨟ ((nE ⊙ homT G) ⊙ G)) ≡ₜ
        (homT h ⊙ G) := by
      refine (Term.fdot_comp_both _ _ _ _).trans ?_
      refine Term.fdot_congr ?_ (PEq.id_comp _)
      calc (Term.block E N ⨟ (nE ⊙ homT G))
          ≡ₜ (Term.block E N ⨟ (Term.unblock E N ⨟ homT h)) := PEq.compR _ (PEq.symm h1)
        _ ≡ₜ ((Term.block E N ⨟ Term.unblock E N) ⨟ homT h) := PEq.symm (PEq.comp_assoc _ _ _)
        _ ≡ₜ (Term.id _ ⨟ homT h) := PEq.compL _ (PEq.block_unblock E N)
        _ ≡ₜ homT h := PEq.id_comp _
    exact (PEq.comp_assoc _ _ _).trans ((PEq.compR _ e2).trans e3)
  calc (unpeelR E N ⨟ homT h)
      ≡ₜ (Term.sumF (Term.unitR E⋆)
            (Term.prodF (Term.block E N) (Term.id M) ⨟ Term.assocR E⋆ (M⋆) M) ⨟
          (Term.undistR E⋆ Ty.unit (M⋆ ⊗ M) ⨟
            (Term.prodF (Term.id E⋆) (Term.snoc M) ⨟ (Term.unblock E N ⨟ homT h)))) :=
        (PEq.comp_assoc
            ((Term.sumF (Term.unitR E⋆)
                (Term.prodF (Term.block E N) (Term.id M) ⨟ Term.assocR E⋆ (M⋆) M) ⨟
              Term.undistR E⋆ Ty.unit (M⋆ ⊗ M)) ⨟
              Term.prodF (Term.id E⋆) (Term.snoc M))
            (Term.unblock E N) (homT h)).trans
          ((PEq.comp_assoc
              (Term.sumF (Term.unitR E⋆)
                  (Term.prodF (Term.block E N) (Term.id M) ⨟ Term.assocR E⋆ (M⋆) M) ⨟
                Term.undistR E⋆ Ty.unit (M⋆ ⊗ M))
              (Term.prodF (Term.id E⋆) (Term.snoc M))
              (Term.unblock E N ⨟ homT h)).trans
            (PEq.comp_assoc
              (Term.sumF (Term.unitR E⋆)
                (Term.prodF (Term.block E N) (Term.id M) ⨟ Term.assocR E⋆ (M⋆) M))
              (Term.undistR E⋆ Ty.unit (M⋆ ⊗ M))
              (Term.prodF (Term.id E⋆) (Term.snoc M) ⨟ (Term.unblock E N ⨟ homT h))))
    _ ≡ₜ (Term.sumF (Term.unitR E⋆)
            (Term.prodF (Term.block E N) (Term.id M) ⨟ Term.assocR E⋆ (M⋆) M) ⨟
          Term.either (nE ⊙ Term.nilT B) (nE ⊙ (homT G ⊙ G))) :=
        PEq.compR _ ((PEq.compR _ ((PEq.compR _ h1).trans h2)).trans h3)
    _ ≡ₜ Term.either (Term.unitR E⋆ ⨟ (nE ⊙ Term.nilT B))
          ((Term.prodF (Term.block E N) (Term.id M) ⨟ Term.assocR E⋆ (M⋆) M) ⨟
            (nE ⊙ (homT G ⊙ G))) := Term.sumF_either _ _ _ _
    _ ≡ₜ Term.either nE (homT h ⊙ G) := Term.either_congr hleft hright

end Lax149335Proofs

bridge_export Lax149335Proofs
