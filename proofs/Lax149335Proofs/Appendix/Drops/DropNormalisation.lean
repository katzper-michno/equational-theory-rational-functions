import Lax149335Proofs.Appendix.Drops.InjectiveTypes
import Lax149335Proofs.Appendix.Drops.SumProdNormalisation

/-!
# Properties of drop and lift functions (appendix, *Properties of drop and lift functions*)

This file records the results of the appendix section whose goal is to prove the exchange
lemma (Lemma 7.5) and the joint simplification of drops (Lemma 7.3):

* the three normalisation lemmas (sum, product and list codomain);
* the shift exchange lemma, which is what the list normalisation lemma needs in order to
  handle `shift`;
* the drop simplification lemma.

The composition rank and the normal forms are defined in
`Lax149335Proofs.Appendix.Drops.DropRank`, and the sum and product normalisation lemmas are proved
in `Lax149335Proofs.Appendix.Drops.SumProdNormalisation`; the product one is restated here in the
form in which the appendix uses it (`Lax149335Proofs.drops_with_prod_codomain`), and the sum one is
discussed below.

Lemma 7.5 itself (`Lax149335Proofs.exchange`) and Lemma 7.3 (`Lax149335Proofs.drops_to_simple`) are stated
in `Lax149335Proofs.GeneralCompleteness.Statements`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The sum normalisation lemma

**Lemma (Sum normalisation)** (appendix).  Every drop with a co-product codomain is provably
equal to a lift followed by an `n`-ary co-pairing, associated to the right, of components of
the form `gᵢ ; Left` or `gᵢ ; Right` whose `gᵢ` have at most the rank of the original drop.

It is proved in `Lax149335Proofs.Appendix.Drops.SumProdNormalisation`, as
`Lax149335Proofs.drops_with_sum_codomain`; the co-pairing shape of the statement is
`Lax149335Proofs.IsNormalSumVec`.  The re-association of the co-product that the appendix uses is
available because `sumAssocL` and `sumAssocR` are prime lift functions. -/

/-- **Lemma (Product normalisation)** (appendix).  Every drop with a product codomain is
provably equivalent to a lift followed by a drop in normal form, whose components have at
most the rank of the original drop.

(As for the previous lemma, the rank condition is the paper's one, on the components of the
normal form: each of the cases of the `n`-ary co-pairing raises the rank of the whole normal
form by one.) -/
theorem drops_with_prod_codomain {A B₁ B₂ : Ty} (f : Term A (B₁ ⊗ B₂)) (hf : IsDrop f) :
    ∃ (D : Ty) (alpha : Term A D) (g : Term D (B₁ ⊗ B₂)),
      IsLift alpha ∧ IsDrop g ∧ IsNormalProdLe (rank f) g ∧ f ≡ₜ (alpha ⨟ g) := by
  obtain ⟨D, alpha, g, halpha, hg, he⟩ := (sumProd_normalisable (rank f)).2 f hf le_rfl
  exact ⟨D, alpha, g, halpha, hg.isDrop, hg, he⟩

/-! ### The list normalisation and drop simplification lemmas

**Lemma (List normalisation)** (appendix).  Every drop with a list codomain is provably equal
to a lift followed by a normal list shape whose leaves have at most the rank of the original
drop.  It is stated and proved as `Lax149335Proofs.drops_with_list_codomain` in
`Lax149335Proofs.Appendix.Drops.ListNormalisation`, where the normal shapes
(`Lax149335Proofs.IsNormalListLeaf`, `Lax149335Proofs.normalListShape`) are also explained.

**Lemma (Drop simplification)** (appendix).  A drop into the lists over a finite alphabet is
provably equal to a lift into a shape all of whose leaves are values.  It is stated and
proved as `Lax149335Proofs.drop_simplification` in
`Lax149335Proofs.Appendix.Drops.DropSimplification`, and it is what the joint simplification
of two drops (Lemma 7.3) is built from. -/

end Lax149335Proofs

bridge_export Lax149335Proofs
