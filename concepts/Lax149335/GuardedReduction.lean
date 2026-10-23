import Lax149335.GuardedTerms

/-!
---
title: Reduction to co-pairings of guarded terms
type: lemma
---
In the proof of the conjugacy rule for simple rational terms, let $k \geq 1$ be the length
of $w$. Without loss of generality, $f$ and $g$ are co-pairings
$$
\langle f_1, \ldots, f_n \rangle \quad\text{and}\quad \langle g_1, \ldots, g_n \rangle
\qquad\text{for some $k$-guarded terms } f_i, g_i : A_i \to B^*.
$$

# Formalization notes

The "without loss of generality" is formalised as a reduction: if the conjugacy rule
$f \cdot w \equiv w \cdot g \Rightarrow (\mathrm{hom}\, f) \cdot w \equiv w \cdot
(\mathrm{hom}\, g)$ holds for all such co-pairings, then it holds for all simple rational
terms $f, g : A \to B^*$. The proof of completeness for simple rational terms is an induction on the nesting depth of
lists in the input type, so the reduction is stated with the additional guarantee that the
co-pairings have an input type whose nesting depth is at most that of $A$. The assumption
that $B$ is a finite alphabet is not needed.
-/

namespace Lax149335.GuardedReduction

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.EquationalTheory Lax149335.SimpleRationalTerms Lax149335.GuardedTerms

/-- The conjugacy rule for simple rational terms follows from the conjugacy
rule for co-pairings of `k`-guarded terms, where `k > 0` is the length of `w`. -/
axiom wlog_kguarded {B : Ty} (w : Value B⋆) (hw : 0 < valLength w) {A : Ty}
    (H : ∀ (A₀ : Ty) (As : List Ty) (f₀ g₀ : Term A₀ B⋆) (fs gs : Cases B⋆ As),
      Ty.listDepth (sumTyOf A₀ As) ≤ Ty.listDepth A →
      KGuarded (valLength w) B f₀ → KGuarded (valLength w) B g₀ →
      fs.All (fun _ f => KGuarded (valLength w) B f) →
      gs.All (fun _ g => KGuarded (valLength w) B g) →
      dotR (copair f₀ fs) w ≡ₜ dotL w (copair g₀ gs) →
      dotR (homT (copair f₀ fs)) w ≡ₜ dotL w (homT (copair g₀ gs)))
    (f g : Term A B⋆) (hf : IsSimple B f) (hg : IsSimple B g)
    (hfg : dotR f w ≡ₜ dotL w g) :
    dotR (homT f) w ≡ₜ dotL w (homT g)

end Lax149335.GuardedReduction
