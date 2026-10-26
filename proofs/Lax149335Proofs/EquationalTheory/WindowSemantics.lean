import Lax149335Proofs.Terms.Derived
import Lax149335Proofs.SimpleCompleteness.BundleDecomposition

/-!
# The bundle term splits a list into bundles of two (semantic side of Axiom 16)

This file computes the denotation of the bundle term `Lax149335Proofs.Term.bundle` of Definition H.5
(`Lax149335Proofs.EquationalTheory.Window`) and proves that it is a one-sided inverse of the
concatenation map

`(A × A)* × (1 + A) ↣ A*`

for *every* type `A` and every value `w : 1 → A`: a list is split into consecutive pairs,
followed by a remainder of at most one element, and concatenating the result gives the list
back (`Lax149335Proofs.Term.bundle_concatMap_den`).  This is the semantic content of Axiom 16, the
window axiom, and it is what makes that axiom sound; the paper only postulates the equation
for `A = 2*` and `w = []`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

variable {A : Ty}

/-! ### The first three steps: the alternating annotation -/

/-- The function computed by `Lax149335Proofs.Term.bundleTag`: an element annotated with the
generator `Right` goes to the left copy of `A`, and an element annotated with the identity
`Left` goes to the right copy. -/
def tagFun (A : Ty) (p : ⟦A⟧ × ⟦Ty.finAlph 1⟧) : ⟦A⟧ ⊕ ⟦A⟧ :=
  match p.2 with
  | Sum.inl _ => Sum.inr p.1
  | Sum.inr _ => Sum.inl p.1

theorem den_bundleTag (p : ⟦A⟧ × ⟦Ty.finAlph 1⟧) : (bundleTag A).den p = tagFun A p := by
  obtain ⟨a, g | g⟩ := p <;> rfl

/-- The alternating annotation of a list, as produced by the first three steps of the bundle
term: starting from the accumulated group element `acc`, the elements are annotated with
`acc·g, acc·g², …`, and an element annotated with the generator goes to the left copy of `A`.
Starting from the group identity, the elements at odd positions go to the left copy and the
elements at even positions go to the right copy. -/
def tagAlt (A : Ty) : ⟦Ty.finAlph 1⟧ → List ⟦A⟧ → List (⟦A⟧ ⊕ ⟦A⟧)
  | _, [] => []
  | Sum.inl _, a :: t => Sum.inl a :: tagAlt A (Sum.inr ()) t
  | Sum.inr _, a :: t => Sum.inr a :: tagAlt A (Sum.inl ()) t

/-- The first two steps of the bundle term, followed by the tagging, produce the alternating
annotation. -/
theorem prefixMul_tagFun (acc : ⟦Ty.finAlph 1⟧) (l : List ⟦A⟧) :
    letI := cyclicTwo
    ((prefixMul acc (l.map (fun a => (a, cyclicTwoGen)))).map (tagFun A)) = tagAlt A acc l := by
  letI := cyclicTwo
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
      rcases acc with u | u
      · rw [List.map_cons,
          show prefixMul (α := ⟦A⟧) (G := ⟦Ty.finAlph 1⟧) (Sum.inl u)
              ((a, cyclicTwoGen) :: t.map (fun a => (a, cyclicTwoGen)))
            = (a, (Sum.inr () : ⟦Ty.finAlph 1⟧)) ::
                prefixMul (α := ⟦A⟧) (G := ⟦Ty.finAlph 1⟧) (Sum.inr ())
                  (t.map (fun a => (a, cyclicTwoGen)))
            from rfl,
          List.map_cons, ih (Sum.inr ())]
        rfl
      · rw [List.map_cons,
          show prefixMul (α := ⟦A⟧) (G := ⟦Ty.finAlph 1⟧) (Sum.inr u)
              ((a, cyclicTwoGen) :: t.map (fun a => (a, cyclicTwoGen)))
            = (a, (Sum.inl () : ⟦Ty.finAlph 1⟧)) ::
                prefixMul (α := ⟦A⟧) (G := ⟦Ty.finAlph 1⟧) (Sum.inl ())
                  (t.map (fun a => (a, cyclicTwoGen)))
            from rfl,
          List.map_cons, ih (Sum.inl ())]
        rfl

/-! ### Steps four and five: `block ; shiftL`, and the coercion into pairs -/

/-- The blocks produced by `block ; shiftL` on the alternating annotation of a list: a list
of blocks `([a₂ᵢ₋₁], a₂ᵢ)`, followed by a tail that is empty for a list of even length and the
singleton of the last element for a list of odd length. -/
def blocksOf (A : Ty) : List ⟦A⟧ → List (List ⟦A⟧ × ⟦A⟧) × List ⟦A⟧
  | [] => ([], [])
  | [a] => ([], [a])
  | a :: b :: t => (([a], b) :: (blocksOf A t).1, (blocksOf A t).2)

/-- `block` cuts the alternating annotation of a list of length at least two after its first
two elements. -/
theorem blockDen_tagAlt_cons_cons (a b : ⟦A⟧) (t : List ⟦A⟧) :
    blockDen (tagAlt A (Sum.inl ()) (a :: b :: t))
      = ([a], (b, (blockDen (tagAlt A (Sum.inl ()) t)).1) ::
          (blockDen (tagAlt A (Sum.inl ()) t)).2) := rfl

/-- **`block ; shiftL` cuts the alternating annotation of a list into its blocks.** -/
theorem shiftLDen_blockDen_tagAlt : ∀ l : List ⟦A⟧,
    shiftLDen (blockDen (tagAlt A (Sum.inl ()) l)).1 (blockDen (tagAlt A (Sum.inl ()) l)).2
      = blocksOf A l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      have ih := shiftLDen_blockDen_tagAlt t
      rw [blockDen_tagAlt_cons_cons]
      show (([a], b) :: (shiftLDen (blockDen (tagAlt A (Sum.inl ()) t)).1
          (blockDen (tagAlt A (Sum.inl ()) t)).2).1,
        (shiftLDen (blockDen (tagAlt A (Sum.inl ()) t)).1
          (blockDen (tagAlt A (Sum.inl ()) t)).2).2) = _
      rw [ih]
      rfl

/-- **The first four steps of the bundle term cut a list into its blocks.** -/
theorem den_bundle_blocks (w : Value A) (l : List ⟦A⟧) :
    (bundle A w).den l
      = (prodF (listF (prodF (headT w) (id A))) (uncons A ⨟ sumF (id Ty.unit) (fst A A⋆))).den
          (blocksOf A l) := by
  letI := cyclicTwo
  have h1 : (listF (unitR A ⨟ prodF (id A) (inr Ty.unit (Ty.finAlph 0))) ⨟
      pref A cyclicTwo).den l = prefixMul (1 : ⟦Ty.finAlph 1⟧)
        (l.map (fun a => (a, cyclicTwoGen))) := rfl
  have h2 : ∀ m : List (⟦A⟧ × ⟦Ty.finAlph 1⟧),
      (listF (bundleTag A)).den m = m.map (tagFun A) := fun m =>
    List.map_congr_left (fun p _ => den_bundleTag p)
  have h3 : (1 : ⟦Ty.finAlph 1⟧) = Sum.inl () := rfl
  show (prodF (listF (prodF (headT w) (id A))) (uncons A ⨟ sumF (id Ty.unit) (fst A A⋆))).den
      ((shiftL A⋆ A).den ((block A A).den ((listF (bundleTag A)).den
        ((listF (unitR A ⨟ prodF (id A) (inr Ty.unit (Ty.finAlph 0))) ⨟
          pref A cyclicTwo).den l)))) = _
  rw [h1, h2, h3, prefixMul_tagFun]
  exact congrArg _ (shiftLDen_blockDen_tagAlt l)

/-! ### The concatenation map of the window axiom -/

/-- The concatenation map `(A × A)* × (1 + A) ↣ A*`, semantically. -/
theorem den_concatMap_window (x : ⟦TyF.window.app A⟧) :
    (TyF.concatMap TyF.window A).den x
      = (x.1.map (fun p => [p.1, p.2])).flatten ++
          (match x.2 with | Sum.inl _ => [] | Sum.inr a => [a]) := by
  obtain ⟨ps, r⟩ := x
  rcases r with u | a <;> rfl

/-- The coercion of the blocks into pairs, followed by the concatenation map, gives the list
back. -/
theorem concat_blocksOf (w : Value A) : ∀ l : List ⟦A⟧,
    (TyF.concatMap TyF.window A).den
      ((prodF (listF (prodF (headT w) (id A))) (uncons A ⨟ sumF (id Ty.unit) (fst A A⋆))).den
        (blocksOf A l)) = l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      have ih := concat_blocksOf w t
      have hF :
          (prodF (listF (prodF (headT w) (id A))) (uncons A ⨟ sumF (id Ty.unit) (fst A A⋆))).den
            (blocksOf A (a :: b :: t))
          = ((a, b) :: ((prodF (listF (prodF (headT w) (id A)))
                (uncons A ⨟ sumF (id Ty.unit) (fst A A⋆))).den (blocksOf A t)).1,
              ((prodF (listF (prodF (headT w) (id A)))
                (uncons A ⨟ sumF (id Ty.unit) (fst A A⋆))).den (blocksOf A t)).2) := rfl
      rw [den_concatMap_window] at ih
      rw [hF, den_concatMap_window, List.map_cons, List.flatten_cons, List.append_assoc, ih]
      rfl

/-- **The bundle term is a one-sided inverse of the concatenation map** (the semantic content
of Axiom 16, for an arbitrary type `A` and an arbitrary value `w`): splitting a list into
bundles of two consecutive entries, followed by a remainder of at most one entry, and
concatenating the result gives the list back. -/
theorem bundle_concatMap_den (A : Ty) (w : Value A) :
    (bundle A w ⨟ TyF.concatMap TyF.window A).den = (Term.id A⋆).den := by
  funext l
  show (TyF.concatMap TyF.window A).den ((bundle A w).den l) = l
  rw [den_bundle_blocks]
  exact concat_blocksOf w l

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
