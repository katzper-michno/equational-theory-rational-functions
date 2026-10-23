import Lax149335Proofs.GeneralCompleteness.Groups

/-!
# Section 7: completeness for all rational terms

The proofs of Lemmas 7.2–7.5, Corollary 7.6 and the provable simplification theorem. The
proof of Lemma 7.4 uses Lemma 7.5; Corollary 7.6 uses Lemmas 5.5, 5.6, 6.1, 7.2, 7.3 and
7.4; and the provable simplification theorem uses Lemma 7.3, together with the
grouplift-drop factorisation of the appendix.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs.Results

open Term

/--
---
conclusion: Lax149335.LiftInverses.lift_iso
---
By induction on the lift. The combinators are handled by functoriality, and each atomic lift
has a drop inverse by the isomorphism axioms; for `split` the inverse is the concatenation
map `unsplit`, and for `shift` it is `⟨[], unshift⟩`.
-/
theorem lift_iso : type_of% @Lax149335.LiftInverses.lift_iso :=
  @Lax149335Proofs.lift_iso

/--
---
conclusion: Lax149335.JointSimplification.drops_to_simple
---
By a syntactic analysis of drops: drops with co-product, product and list codomains are
normalised, the normal forms of two drops are brought to a common shape by a common lift,
and a drop of that shape into the lists over a finite alphabet is provably equivalent to a
simple rational term.
-/
theorem drops_to_simple : type_of% @Lax149335.JointSimplification.drops_to_simple :=
  @Lax149335Proofs.drops_to_simple

/--
---
conclusion: Lax149335.LiftDropFactorisation.lift_drop_factorisation
---
By induction on the term. The atomic terms are factorised directly, the functoriality
combinators preserve factorisations, and for a composition the inner drop-lift is turned
into a lift-drop by the exchange lemma.
-/
theorem lift_drop_factorisation :
    type_of% @Lax149335.LiftDropFactorisation.lift_drop_factorisation := by
  intro A B f hf
  exact Lax149335Proofs.isLiftDrop_of_aperiodic_of Lax149335.Exchange.exchange f hf

/--
---
conclusion: Lax149335.Exchange.exchange
---
By induction on the lift. The combinators and all atomic lifts except `shift` and `split`
are straightforward; the cases of `shift` and `split` are the shift exchange and the split
exchange lemmas of the appendix.
-/
theorem exchange : type_of% @Lax149335.Exchange.exchange :=
  @Lax149335Proofs.exchange

/--
---
conclusion: Lax149335.AperiodicCompleteness.completeness_aperiodic
---
Reduce to binary string outputs with the encoding of Lemma 5.6 and Lemma 5.5. Factorise the
two terms as a common lift followed by drops (Lemmas 7.4 and 7.2). The two drops have the
same denotation, so they are provably equivalent by Lemma 7.3 and Lemma 6.1, and the common
lift is cancelled with Lemma 5.5.
-/
theorem completeness_aperiodic :
    type_of% @Lax149335.AperiodicCompleteness.completeness_aperiodic :=
  @Lax149335Proofs.completeness_aperiodic_of Lax149335.Cancellation.cancel
    Lax149335.StringRepresentations.exists_injective_binary_encoding
    Lax149335.SimpleCompleteness.completeness_simple Lax149335.LiftInverses.lift_iso
    Lax149335.JointSimplification.drops_to_simple
    Lax149335.LiftDropFactorisation.lift_drop_factorisation

/--
---
conclusion: Lax149335.ProvableSimplification.provable_simplification
---
The grouplift-drop factorisation of the appendix gives a group-lift `α : A → C` with a
one-sided inverse `α⁻¹`, i.e. `α ; α⁻¹ ≡ id`, such that `α⁻¹ ; f` and `α⁻¹ ; g` are provably
equivalent to drops. By Lemma 7.3 there is a lift `σ : C → B` with inverse `σ⁻¹` such that
`σ⁻¹` composed with these drops gives simple rational terms. The term `π = σ⁻¹ ; α⁻¹` is
surjective, since `(α ; σ) ; π ≡ id`.
-/
theorem provable_simplification :
    type_of% @Lax149335.ProvableSimplification.provable_simplification := by
  intro A N hN f g
  obtain ⟨n, rfl⟩ := hN
  obtain ⟨D, mu, pi, d₁, d₂, hmupi, hd₁, hd₂, hf, hg⟩ :=
    Lax149335Proofs.common_grouplift_drop_normalisation f g
  obtain ⟨C, l, π, -, -, hlπ, -, ⟨f', hf's, hf'⟩, ⟨g', hg's, hg'⟩⟩ :=
    Lax149335.JointSimplification.drops_to_simple ⟨n, rfl⟩ d₁ d₂ hd₁ hd₂
  refine ⟨C, π ⨟ pi, ⟨mu ⨟ l, ?_⟩, ⟨f', hf's, ?_⟩, ⟨g', hg's, ?_⟩⟩
  · calc ((mu ⨟ l) ⨟ (π ⨟ pi)) ≡ₜ (mu ⨟ (l ⨟ (π ⨟ pi))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (mu ⨟ ((l ⨟ π) ⨟ pi)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ (mu ⨟ (Term.id D ⨟ pi)) := PEq.compR _ (PEq.compL _ hlπ)
      _ ≡ₜ (mu ⨟ pi) := PEq.compR _ (PEq.id_comp _)
      _ ≡ₜ Term.id A := hmupi
  · calc ((π ⨟ pi) ⨟ f) ≡ₜ (π ⨟ (pi ⨟ f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (π ⨟ d₁) := PEq.compR _ hf
      _ ≡ₜ f' := hf'
  · calc ((π ⨟ pi) ⨟ g) ≡ₜ (π ⨟ (pi ⨟ g)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (π ⨟ d₂) := PEq.compR _ hg
      _ ≡ₜ g' := hg'

end Lax149335Proofs.Results
