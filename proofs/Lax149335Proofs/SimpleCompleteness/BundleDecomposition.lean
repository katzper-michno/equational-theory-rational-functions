import Lax149335Proofs.Terms.Semantics
import Mathlib.Logic.Function.Basic
import Mathlib.Order.MinMax

/-!
# The bundle decomposition of a list (semantic side of the bundle lemma)

Lemma 6.7 of the paper (`Lax149335Proofs.concatMap_bundle_iso_arbitrarily_large'`) states that the
concatenation map

`(A^{k+1})* × A^{<k+1} ↣ A*`

is a *provable* isomorphism.  This file proves the corresponding *semantic* statement: the
function denoted by that concatenation map is a bijection, i.e. every list over `A`
decomposes uniquely into a sequence of blocks of length `k+1` followed by a remainder of
length at most `k`.

The surjectivity half of this bijection is what makes Axiom 16 (`Lax149335Proofs.PEq.window`)
sound, which is why the file comes before `Lax149335Proofs.EquationalTheory.Soundness`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Tuples of a fixed length -/

/-- The list of the `k` entries of a tuple in `Aᵏ`, i.e. the denotation of the concatenation
map of `Aᵏ`. -/
def powDen (A : Ty) (k : ℕ) (x : ⟦(TyF.pow k).app A⟧) : List ⟦A⟧ :=
  ((TyF.pow k).concatMap A).den x

/-- The list of the entries of a tuple in `A^{<k+1}`, i.e. the denotation of the
concatenation map of `A^{<k+1}`. -/
def ltDen (A : Ty) (k : ℕ) (x : ⟦(TyF.lt k).app A⟧) : List ⟦A⟧ :=
  ((TyF.lt k).concatMap A).den x

@[simp] theorem powDen_zero (A : Ty) (x : ⟦(TyF.pow 0).app A⟧) : powDen A 0 x = [] := rfl

@[simp] theorem powDen_succ (A : Ty) (k : ℕ) (a : ⟦A⟧) (y : ⟦(TyF.pow k).app A⟧) :
    powDen A (k + 1) (a, y) = a :: powDen A k y := by
  show (((pureT A) ⊙ ((TyF.pow k).concatMap A)).den (a, y) : List ⟦A⟧) = _
  rw [den_fdot, den_pureT]
  rfl

@[simp] theorem ltDen_zero (A : Ty) (x : ⟦(TyF.lt 0).app A⟧) : ltDen A 0 x = [] := rfl

@[simp] theorem ltDen_inl (A : Ty) (k : ℕ) (y : ⟦(TyF.lt k).app A⟧) :
    ltDen A (k + 1) (Sum.inl y) = ltDen A k y := rfl

@[simp] theorem ltDen_inr (A : Ty) (k : ℕ) (z : ⟦(TyF.pow (k + 1)).app A⟧) :
    ltDen A (k + 1) (Sum.inr z) = powDen A (k + 1) z := rfl

/-! ### The bundle decomposition -/

/-- The function denoted by the bundle concatenation map: the blocks and the remainder are
concatenated. -/
theorem den_bundle (A : Ty) (k : ℕ)
    (x : ⟦((TyF.list (TyF.pow (k + 1))).prod (TyF.lt k)).app A⟧) :
    ((TyF.concatMap ((TyF.list (TyF.pow (k + 1))).prod (TyF.lt k)) A).den x : List ⟦A⟧)
      = (x.1.map (powDen A (k + 1))).flatten ++ ltDen A k x.2 := by
  show ((((TyF.list (TyF.pow (k + 1))).concatMap A) ⊙ ((TyF.lt k).concatMap A)).den x :
      List ⟦A⟧) = _
  rw [den_fdot]
  rfl

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
