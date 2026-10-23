import Lax149335Proofs.RationalFunctions.Decidability
import Lax149335Proofs.SimpleCompleteness.Bridge
import Lax149335Proofs.EquationalTheory.Soundness

/-!
# Section 2: rational functions and simple rational terms

The proofs of Theorem 2.6, Claim 2.7, Corollary 2.8 and Theorem 2.9. As the paper explains,
Theorem 2.9 is a consequence of Theorem 7.7 (provable simplification).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs.Results

open Term

/--
---
conclusion: Lax149335.ConjugacyCompleteness.conjugacy_completeness
---
Soundness of the rules is checked rule by rule. Completeness is proved by induction on the
input type: the rules for moving constants bring a term into a normal form determined by the
input type, and the induction steps for products and lists use Levi's lemma, the latter
together with the conjugacy rule.
-/
theorem conjugacy_completeness :
    type_of% @Lax149335.ConjugacyCompleteness.conjugacy_completeness :=
  @Lax149335Proofs.SimpleTerm.conjugacy_completeness

/--
---
conclusion: Lax149335.SynchronisedLengths.claim_same_lengths
---
Compare the outputs on inputs that differ by one element in a single list component.
-/
theorem claim_same_lengths : type_of% @Lax149335.SynchronisedLengths.claim_same_lengths :=
  @Lax149335Proofs.SimpleTerm.claim_same_lengths

/--
---
conclusion: Lax149335.DecidableEquivalence.decidable_equivalence
---
By induction on the input type: over a co-product the two summands are compared, over a
product each component is compared with the other one fixed, and over a list type the empty
list and the singleton lists are compared; the last two cases are applications of Levi's
lemma.
-/
theorem decidable_equivalence :
    type_of% @Lax149335.DecidableEquivalence.decidable_equivalence :=
  @Lax149335Proofs.SimpleTerm.den_eq_iff_testInputs

/--
---
conclusion: Lax149335.Simplification.simplification_of_rational_terms
---
By Theorem 7.7 (provable simplification), there is a surjective term `π` after which both
terms are provably equivalent to simple rational terms of the compositional syntax. By
soundness, the denotation of `π` is surjective, and the denotations of the two compositions
are those of simple rational terms, which are simple rational functions.
-/
theorem simplification_of_rational_terms :
    type_of% @Lax149335.Simplification.simplification_of_rational_terms := by
  intro N M _ hM f g
  obtain ⟨B, π, ⟨ρ, hρ⟩, ⟨f', hf's, hf'⟩, ⟨g', hg's, hg'⟩⟩ :=
    Lax149335.ProvableSimplification.provable_simplification hM f g
  refine ⟨B, π, fun y => ⟨ρ.den y, ?_⟩, ?_, ?_⟩
  · have := congrFun (PEq.sound hρ) y
    simpa using this
  · obtain ⟨t, ht⟩ := SimpleTerm.exists_interp hf's
    exact ⟨t, by rw [← SimpleTerm.den_interp t, PEq.sound ht, PEq.sound hf']⟩
  · obtain ⟨t, ht⟩ := SimpleTerm.exists_interp hg's
    exact ⟨t, by rw [← SimpleTerm.den_interp t, PEq.sound ht, PEq.sound hg']⟩

end Lax149335Proofs.Results
