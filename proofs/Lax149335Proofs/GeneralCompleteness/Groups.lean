import Lax149335Proofs.Appendix.Groups.Completeness

/-!
# Completeness in the presence of groups

Section 7 of the paper finishes the completeness proof for *aperiodic* terms
(`Lax149335Proofs.completeness_aperiodic`); the remaining case, of terms that use the group prefix
multiplication `pref`, is treated in the appendix (Section "Completeness in the presence of
groups").  There, lifts are generalised to *grouplifts* — lifts, group injections and Simon
lifts — which are provably injective with drop one-sided inverses, and the group version of
the exchange lemma gives every rational term a grouplift-drop factorisation, with the
grouplift shared by two given terms.

The statement `Lax149335Proofs.common_grouplift_drop_normalisation` below records what that
appendix argument provides.  It is the only input from the appendix that the provable
simplification theorem (`Lax149335Proofs.Results.provable_simplification`), and through it
the completeness half of Theorem 4.1, needs.  It is discharged by the appendix section that
this file imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- **Appendix (completeness in the presence of groups).**  Given two rational terms
`f, g : A → Ā*` with outputs over a finite alphabet, the group version of the exchange lemma
provides a common grouplift `μ : A ⊸ D` together with its drop one-sided inverse
`π : D ⇒ A`, so that `μ; π ≡ id`, and both `π; f` and `π; g` are provably equivalent to
drops.

(For a grouplift `μ` with one-sided inverse `π`, each atomic factor of `μ` is either an
isomorphism whose inverse cancels the factor, or a group injection, whose inverse composed
with it is again a drop; so `π; μ` is provably equivalent to a drop, and precomposing the
grouplift-drop factorisations of `f` and of `g` with `π` gives the two drops above.)

This is proved in the appendix, as
`Lax149335Proofs.common_grouplift_drop_normalisation_appendix` in
`Lax149335Proofs.Appendix.Groups.Completeness`, from
`Lax149335Proofs.common_grouplift_inverse_drop_normalisation`. -/
theorem common_grouplift_drop_normalisation {A : Ty} {n : ℕ}
    (f g : Term A (Ty.finAlph n)⋆) :
    ∃ (D : Ty) (mu : Term A D) (pi : Term D A) (d₁ d₂ : Term D (Ty.finAlph n)⋆),
      (mu ⨟ pi) ≡ₜ Term.id A ∧ IsDrop d₁ ∧ IsDrop d₂ ∧
        (pi ⨟ f) ≡ₜ d₁ ∧ (pi ⨟ g) ≡ₜ d₂ :=
  common_grouplift_drop_normalisation_appendix f g

end Lax149335Proofs

bridge_export Lax149335Proofs
