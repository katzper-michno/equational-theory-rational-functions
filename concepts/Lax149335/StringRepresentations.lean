import Lax149335.InjectiveSurjectiveTerms

/-!
---
title: Injective string representations
type: lemma
---
**Lemma 5.6.** For every type $A$ there is an injective aperiodic term
$\mathsf{enc}_A : A \to 2^*$, where $2 = 1 + 1$ is the binary alphabet.
-/

namespace Lax149335.StringRepresentations

open Lax149335.Types Lax149335.Terms Lax149335.InjectiveSurjectiveTerms

/-- **Lemma 5.6.** Every type has an injective aperiodic encoding into binary strings. -/
axiom exists_injective_binary_encoding (A : Ty) :
    ∃ enc : Term A (Ty.finAlph 1)⋆, IsAperiodic enc ∧ ProvablyInjective enc

end Lax149335.StringRepresentations
