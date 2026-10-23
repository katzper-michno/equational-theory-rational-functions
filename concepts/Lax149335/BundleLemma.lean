import Lax149335.InjectiveTerms

/-!
---
title: The bundle lemma
type: lemma
---
**Lemma 6.7 (Bundles).** For every type $A$, there are arbitrarily large numbers $k$ such
that the concatenation map
$$
(A^k)^* \times A^{<k} \rightarrowtail A^*
$$
is an isomorphism. Here $A^i$ is the $i$-fold product of $A$ with itself, with
$A^0 = 1$, and $A^{<k}$ is the co-product of all $A^i$ with $0 \le i < k$.

# Formalization notes

The bundle size is written $k + 1$, so that $A^{<k+1} = A^0 + \cdots + A^k$ is the type
constructor `TyF.lt k`. The formal statement is stronger than the paper's: the bundle
sizes $k + 1$ can be chosen independently of the type $A$.
-/

namespace Lax149335.BundleLemma

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.InjectiveTerms

/-- **Lemma 6.7.** For every `N` there is a `k ≥ N` such that, for every type `A`, the
concatenation map `(A^{k+1})* × A^{<k+1} ↣ A*` is an isomorphism. -/
axiom concatMap_bundle_iso_arbitrarily_large' (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ ∀ A : Ty,
      ProvableIso (TyF.concatMap (.prod (.list (TyF.pow (k + 1))) (TyF.lt k)) A)

end Lax149335.BundleLemma
