import Lax149335.LiftsAndDrops
import Lax149335.SimpleRationalTerms

/-!
---
title: Provable simplification of drops
type: lemma
---
**Lemma 7.3 (Provable simplification of drops).** Let $N$ be a finite alphabet, and let
$f, g : A \to N^*$ be drops. There is a lift $\pi : A \to C$ and its inverse $\pi^{-1}$ such
that $\pi^{-1} \mathbin{;} f$ and $\pi^{-1} \mathbin{;} g$ are both equivalent to simple
rational terms.

# Formalization notes

The statement records that $\pi^{-1}$ is a drop and that $\pi$ and $\pi^{-1}$ are mutually
inverse.
-/

namespace Lax149335.JointSimplification

open Lax149335.Types Lax149335.Terms Lax149335.EquationalTheory Lax149335.LiftsAndDrops
  Lax149335.SimpleRationalTerms

/-- **Lemma 7.3.** Two drops `A → N*` into the lists over a finite alphabet become provably
equivalent to simple rational terms after precomposing with the inverse of a common lift. -/
axiom drops_to_simple {A B : Ty} (hB : Ty.IsFinAlph B) (f g : Term A B⋆)
    (hf : IsDrop f) (hg : IsDrop g) :
    ∃ (C : Ty) (l : Term A C) (π : Term C A),
      IsLift l ∧ IsDrop π ∧ (l ⨟ π) ≡ₜ Term.id A ∧ (π ⨟ l) ≡ₜ Term.id C ∧
      (∃ f' : Term C B⋆, IsSimple B f' ∧ (π ⨟ f) ≡ₜ f') ∧
      (∃ g' : Term C B⋆, IsSimple B g' ∧ (π ⨟ g) ≡ₜ g')

end Lax149335.JointSimplification
