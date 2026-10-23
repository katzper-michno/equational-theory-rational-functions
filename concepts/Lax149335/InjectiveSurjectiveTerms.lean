import Lax149335.EquationalTheory

/-!
---
title: Injective, surjective and isomorphic terms
type: definition
---
**Definition 5.4.** A rational term $f : A \to B$ is

- *injective* if $f \mathbin{;} f^{-1} \equiv \mathrm{id}$ for some term $f^{-1} : B \to A$;
- *surjective* if $f^{-1} \mathbin{;} f \equiv \mathrm{id}$ for some term
  $f^{-1} : B \to A$;
- an *isomorphism* if both hold for the same term $f^{-1}$.

In categorical terms, an injective term is a section and a surjective term is a retraction
in the category of rational terms modulo $\equiv$.

# Formalization notes

The notions are called `ProvablyInjective`, `ProvablySurjective` and `ProvableIso`, to
distinguish them from injectivity and surjectivity of the denotation.
-/

namespace Lax149335.InjectiveSurjectiveTerms

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory

/-- `f : A → B` is injective if `f ; f' ≡ id` for some `f' : B → A`. -/
def ProvablyInjective {A B : Ty} (f : Term A B) : Prop :=
  ∃ f' : Term B A, (f ⨟ f') ≡ₜ Term.id A

/-- `f : A → B` is surjective if `f' ; f ≡ id` for some `f' : B → A`. -/
def ProvablySurjective {A B : Ty} (f : Term A B) : Prop :=
  ∃ f' : Term B A, (f' ⨟ f) ≡ₜ Term.id B

/-- `f : A → B` is an isomorphism if `f ; f' ≡ id` and `f' ; f ≡ id` for some
`f' : B → A`. -/
def ProvableIso {A B : Ty} (f : Term A B) : Prop :=
  ∃ f' : Term B A, (f ⨟ f') ≡ₜ Term.id A ∧ (f' ⨟ f) ≡ₜ Term.id B

end Lax149335.InjectiveSurjectiveTerms
