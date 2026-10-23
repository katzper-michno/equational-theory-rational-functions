import Lax149335Proofs.EquationalTheory.Soundness

/-!
# Section 4: the main theorem

Soundness of the axioms is proved directly. Completeness follows from the provable
simplification theorem of Section 7 and completeness for simple rational terms
(Lemma 6.1), after reducing to binary string outputs with Lemma 5.6 and cancelling the
injective encoding and the surjective simplifying term with Lemma 5.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs.Results

open Term

/--
---
conclusion: Lax149335.FiniteAxiomatisation.finite_axiomatisation
---
Soundness is checked axiom by axiom against the denotational semantics. For completeness,
let `f, g : A → B` have the same denotation. Postcomposing with the injective binary
encoding `enc : B → 2*` of Lemma 5.6, the provable simplification theorem gives a surjective
term `π` such that `π ; f ; enc` and `π ; g ; enc` are provably equivalent to simple
rational terms. These have the same denotation, so they are provably equivalent by
Lemma 6.1, and `π` and `enc` are cancelled with Lemma 5.5.
-/
theorem finite_axiomatisation :
    type_of% @Lax149335.FiniteAxiomatisation.finite_axiomatisation := by
  intro A B f g
  refine ⟨fun h => ?_, PEq.sound⟩
  obtain ⟨enc, -, henc⟩ := Lax149335.StringRepresentations.exists_injective_binary_encoding B
  refine ((Lax149335.Cancellation.cancel f g).1 _ enc henc).2 ?_
  obtain ⟨C, π, hπ, ⟨f', hf's, hf'⟩, ⟨g', hg's, hg'⟩⟩ :=
    Lax149335.ProvableSimplification.provable_simplification ⟨1, rfl⟩ (f ⨟ enc) (g ⨟ enc)
  refine ((Lax149335.Cancellation.cancel (f ⨟ enc) (g ⨟ enc)).2 _ π hπ).2 ?_
  have hden : f'.den = g'.den := by
    rw [← PEq.sound hf', ← PEq.sound hg']
    funext x
    simp [h]
  have hs := (Lax149335.SimpleCompleteness.completeness_simple ⟨1, rfl⟩ f' g' hf's hg's
    (Term.nilT _)).1 hden
  exact hf'.trans (hs.trans (PEq.symm hg'))

end Lax149335Proofs.Results
