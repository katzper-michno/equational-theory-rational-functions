import Lax149335Proofs.SimpleCompleteness.Proof
import Lax149335Proofs.SimpleCompleteness.ValueExtractionProof

/-!
# Section 6: completeness for simple rational terms

The proofs of Lemma 6.1, Lemma 6.2, Lemma 6.4, Lemma 6.5, Claim 6.6 and Lemma 6.7. The proof
of Lemma 6.1 uses Lemmas 5.5, 6.2, 6.4, 6.5 and 6.7; the proof of Lemma 6.5 uses Claim 6.6;
and the proof of Lemma 6.7 uses the binary encodings of Lemma 5.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs.Results

/--
---
conclusion: Lax149335.SimpleCompleteness.completeness_simple
---
The completeness rule and the conjugacy rule are proved together by induction on the nesting
depth of lists in the input type. The completeness rule follows the proof of Theorem 2.6.
For the conjugacy rule with a nonempty value `w` of length `k`, Lemmas 6.4 and 6.5 reduce to
co-pairings of `k`-guarded nonempty terms. After grouping the list into bundles of size at
least `k` with the bundle lemma (Lemma 6.7), the bundled terms become syntactically
`w`-conjugate, by the induction hypothesis, and Lemma 6.2 applies. The bundle isomorphism is
cancelled with Lemma 5.5.
-/
theorem completeness_simple :
    type_of% @Lax149335.SimpleCompleteness.completeness_simple :=
  @Lax149335Proofs.completeness_simple_of Lax149335.Cancellation.cancel
    Lax149335.ConjugacyRule.conjugacy_of_syntactic Lax149335.GuardedReduction.wlog_kguarded
    Lax149335.NonemptyReduction.wlog_nonempty
    Lax149335.BundleLemma.concatMap_bundle_iso_arbitrarily_large'

/--
---
conclusion: Lax149335.ConjugacyRule.conjugacy_of_syntactic
---
Both sides factor through the list of pairs `(h(a), w)`; the two factorisations are related
by shifting the brackets of a list of pairs whose first components are values (the *shift
ones* lemma) and naturality of `shiftL`.
-/
theorem conjugacy_of_syntactic :
    type_of% @Lax149335.ConjugacyRule.conjugacy_of_syntactic :=
  @Lax149335Proofs.conjugacy_of_syntactic

/--
---
conclusion: Lax149335.GuardedReduction.wlog_kguarded
---
By value extraction, there is an isomorphism after which both terms are co-pairings of
`k`-guarded terms; the conclusion is transported back along this isomorphism.
-/
theorem wlog_kguarded : type_of% @Lax149335.GuardedReduction.wlog_kguarded :=
  @Lax149335Proofs.wlog_kguarded

/--
---
conclusion: Lax149335.NonemptyReduction.wlog_nonempty
---
The input type is split into the summands on which both terms produce the empty list and the
remaining ones; the former are removed with Claim 6.6.
-/
theorem wlog_nonempty : type_of% @Lax149335.NonemptyReduction.wlog_nonempty :=
  @Lax149335Proofs.wlog_nonempty_of Lax149335.EmptySummands.hom_factors

/--
---
conclusion: Lax149335.EmptySummands.hom_factors
---
The empty case contributes nothing to the homomorphism, by the axioms about empty lists
(Axioms 10 and 14).
-/
theorem hom_factors : type_of% @Lax149335.EmptySummands.hom_factors :=
  @Lax149335Proofs.hom_factors

/--
---
conclusion: Lax149335.BundleLemma.concatMap_bundle_iso_arbitrarily_large'
---
For binary strings and bundles of size two, the window axiom provides the inverse of the
concatenation map. Every type is a retract of the binary strings, by Lemma 5.6, and
concatenation maps are natural, which gives bundles of size two for every type. Bundles of
bundles multiply the bundle sizes, which gives all powers of two.
-/
theorem concatMap_bundle_iso_arbitrarily_large' :
    type_of% @Lax149335.BundleLemma.concatMap_bundle_iso_arbitrarily_large' :=
  @Lax149335Proofs.concatMap_bundle_iso_arbitrarily_large'_of
    Lax149335.StringRepresentations.exists_injective_binary_encoding

end Lax149335Proofs.Results
