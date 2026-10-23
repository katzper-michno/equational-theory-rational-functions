import Lax149335Proofs.Appendix.Groups.ExchangeProof

/-!
# Completeness in the presence of groups: the proof

This file finishes the appendix section *Completeness in the presence of groups*:

* `Lax149335Proofs.isGLiftInvDrop_of_term` — the **grouplift-drop factorisation** in its inverted
  form: every term `f : A → B` fits in a provably commuting triangle

  ```
        f
   A ------→ B
   ↑        ↗
   π      drop
   |     /
   C ---
  ```

  where `π` is the one-sided inverse of a group-lift `μ : A ⊸ C`;
* `Lax149335Proofs.common_grouplift_inverse_drop_normalisation` — the same, jointly for two terms
  with a common group-lift;
* `Lax149335Proofs.common_grouplift_drop_normalisation_appendix` — the form of the above in
  which the inverted group-lift is followed by drops, which is what the provable
  simplification theorem (`Lax149335Proofs.Results.provable_simplification`) uses.

The inversion is what makes the completeness proof work: `π` is provably surjective (it has
the group-lift `μ` as a one-sided inverse on the other side), so it can be cancelled on the
left-hand side of an equational proof, which a group-lift itself could not be.

Everything here is proved.  The prefix exchange lemma, which the group exchange lemma rests
on, is proved as well (`Lax149335Proofs.prefix_exchange_group`, in
`Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`).  The bundle lemma (Lemma 6.7,
`Lax149335Proofs.concatMap_bundle_iso_arbitrarily_large'`), which enters through completeness for
aperiodic terms, is proved from Axiom 16 in `Lax149335Proofs.Appendix.Bundles.Window`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The inverted grouplift-drop factorisation of every term -/

namespace IsGLiftInvDrop

/-- Terms with an inverted grouplift-drop factorisation are closed under composition: this is
where the (inverted) group exchange lemma is used. -/
theorem comp {A B C : Ty} {f : Term A B} {g : Term B C} (hf : IsGLiftInvDrop f)
    (hg : IsGLiftInvDrop g) : IsGLiftInvDrop (f ⨟ g) := by
  obtain ⟨C₁, mu₁, pi₁, d₁, hmu₁, hd₁, he₁⟩ := hf
  obtain ⟨C₂, mu₂, pi₂, d₂, hmu₂, hd₂, he₂⟩ := hg
  obtain ⟨C₃, nu, rho, k, hnu, hk, hex⟩ := group_exchange_inv hmu₂ d₁ hd₁
  refine ⟨C₃, mu₁ ⨟ nu, rho ⨟ pi₁, k ⨟ d₂, hmu₁.comp hnu, IsDrop.comp hk hd₂, ?_⟩
  calc ((rho ⨟ pi₁) ⨟ (f ⨟ g)) ≡ₜ (rho ⨟ (pi₁ ⨟ (f ⨟ g))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (rho ⨟ ((pi₁ ⨟ f) ⨟ g)) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (rho ⨟ (d₁ ⨟ g)) := PEq.compR _ (PEq.compL _ he₁)
    _ ≡ₜ ((rho ⨟ d₁) ⨟ g) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((k ⨟ pi₂) ⨟ g) := PEq.compL _ hex
    _ ≡ₜ (k ⨟ (pi₂ ⨟ g)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (k ⨟ d₂) := PEq.compR _ he₂

end IsGLiftInvDrop

/-- The group prefix multiplication, in the co-product presentation, has an inverted
grouplift-drop factorisation.  This is the case `ρ = id` of the Simon lift lemma, i.e. the
Simon lift for `H` the whole group: it is a group-lift whose one-sided inverse `γ`, composed
with `spref`, is the drop `δ` of the lemma. -/
theorem isGLiftInvDrop_spref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    IsGLiftInvDrop (Term.spref A G) := by
  obtain ⟨S, simon, gamma, delta, hpair, hdelta, hsq⟩ :=
    isGLiftPair_simon_H A G (hm := fun g : ⟦Ty.finAlph n⟧ => g) Function.injective_id
  refine ⟨S, simon, gamma, delta, hpair, hdelta, ?_⟩
  calc (gamma ⨟ Term.spref A G)
      ≡ₜ (gamma ⨟ (Term.id ((Term.sigmaTy A n)⋆) ⨟ Term.spref A G)) :=
        PEq.compR _ (PEq.symm (PEq.id_comp _))
    _ ≡ₜ (gamma ⨟ (Term.listF (Term.rhoInj A (fun g : ⟦Ty.finAlph n⟧ => g)) ⨟
          Term.spref A G)) :=
        PEq.compR _ (PEq.compL _ (PEq.symm (Term.listF_rhoInj_id A)))
    _ ≡ₜ delta := hsq

/-- The group prefix multiplication has an inverted grouplift-drop factorisation. -/
theorem isGLiftInvDrop_pref (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    IsGLiftInvDrop (Term.pref A G) := by
  refine IsGLiftInvDrop.congr (Term.pref_eq_spref A G) ?_
  refine IsGLiftInvDrop.comp
    (IsGLiftInvDrop.comp (IsGLiftInvDrop.comp ?_ (isGLiftInvDrop_spref A G)) ?_) ?_
  · exact IsGLiftInvDrop.of_isAperiodic _ (by simp [IsAperiodic, Term.usesPref])
  · exact IsGLiftInvDrop.of_isAperiodic _ (by simp [IsAperiodic])
  · exact IsGLiftInvDrop.of_isAperiodic _ (by simp [IsAperiodic, Term.usesPref])

/-- **Lemma (Grouplift-drop factorisation)** (appendix, *Proof of
completeness*).  Every rational term `f : A → B` becomes provably equal to a drop after
precomposition with the one-sided inverse of a suitable group-lift. -/
theorem isGLiftInvDrop_of_term : ∀ {A B : Ty} (f : Term A B), IsGLiftInvDrop f := by
  intro A B f
  induction f with
  | comp f g ihf ihg => exact ihf.comp ihg
  | prodF f g ihf ihg => exact ihf.prodF ihg
  | sumF f g ihf ihg => exact ihf.sumF ihg
  | listF f ihf => exact ihf.listF
  | pref A G => exact isGLiftInvDrop_pref A G
  | _ =>
      exact IsGLiftInvDrop.of_isAperiodic _ (by simp [IsAperiodic, Term.usesPref])

/-- **A common group-lift inverse.**  Two rational terms with the same domain become provably
equal to drops after precomposition with the one-sided inverse `π` of one and the same
group-lift `μ`. -/
theorem common_grouplift_inverse_drop_normalisation {A B : Ty} (f g : Term A B) :
    ∃ (D : Ty) (mu : Term A D) (pi : Term D A) (d₁ d₂ : Term D B),
      (mu ⨟ pi) ≡ₜ Term.id A ∧ IsDrop d₁ ∧ IsDrop d₂ ∧
        (pi ⨟ f) ≡ₜ d₁ ∧ (pi ⨟ g) ≡ₜ d₂ := by
  obtain ⟨C₁, mu₁, pi₁, d₁, hmu₁, hd₁, he₁⟩ := isGLiftInvDrop_of_term f
  obtain ⟨C₂, mu₂, pi₂, d₂, hmu₂, hd₂, he₂⟩ := isGLiftInvDrop_of_term (pi₁ ⨟ g)
  refine ⟨C₂, mu₁ ⨟ mu₂, pi₂ ⨟ pi₁, pi₂ ⨟ d₁, d₂, (hmu₁.comp hmu₂).retract,
    IsDrop.comp hmu₂.isDrop hd₁, hd₂, ?_, ?_⟩
  · calc ((pi₂ ⨟ pi₁) ⨟ f) ≡ₜ (pi₂ ⨟ (pi₁ ⨟ f)) := PEq.comp_assoc _ _ _
      _ ≡ₜ (pi₂ ⨟ d₁) := PEq.compR _ he₁
  · exact (PEq.comp_assoc _ _ _).trans he₂

/-! ### Completeness -/

/-- **The statement that the main part imports from the appendix.**  The completeness half
of Theorem 4.1 quotes the appendix through
`Lax149335Proofs.common_grouplift_drop_normalisation`, in
`Lax149335Proofs.GeneralCompleteness.Groups`; that statement is this instance of
`Lax149335Proofs.common_grouplift_inverse_drop_normalisation`. -/
theorem common_grouplift_drop_normalisation_appendix {A : Ty} {n : ℕ}
    (f g : Term A (Ty.finAlph n)⋆) :
    ∃ (D : Ty) (mu : Term A D) (pi : Term D A) (d₁ d₂ : Term D (Ty.finAlph n)⋆),
      (mu ⨟ pi) ≡ₜ Term.id A ∧ IsDrop d₁ ∧ IsDrop d₂ ∧
        (pi ⨟ f) ≡ₜ d₁ ∧ (pi ⨟ g) ≡ₜ d₂ :=
  common_grouplift_inverse_drop_normalisation f g

end Lax149335Proofs

bridge_export Lax149335Proofs
