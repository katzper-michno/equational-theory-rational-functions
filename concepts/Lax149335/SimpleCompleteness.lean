import Lax149335.SimpleRationalTerms

/-!
---
title: Completeness for simple rational terms
type: lemma
---
**Lemma 6.1 (Completeness for simple rational terms).** For all simple rational terms
$f, g : A \to B^*$, where $B$ is a finite alphabet, and every value $w : 1 \to B^*$,
$$
\begin{aligned}
[\![ f ]\!] = [\![ g ]\!] &\quad\text{implies}\quad f \equiv g, \\
f \cdot w \equiv w \cdot g &\quad\text{implies}\quad
  (\mathrm{hom}\, f) \cdot w \equiv w \cdot (\mathrm{hom}\, g).
\end{aligned}
$$
-/

namespace Lax149335.SimpleCompleteness

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.EquationalTheory Lax149335.SimpleRationalTerms

/-- **Lemma 6.1.** The completeness rule and the conjugacy rule for simple rational terms. -/
axiom completeness_simple {A B : Ty} (hB : Ty.IsFinAlph B) (f g : Term A B⋆)
    (hf : IsSimple B f) (hg : IsSimple B g) (w : Value B⋆) :
    (f.den = g.den → f ≡ₜ g) ∧
    (dotR f w ≡ₜ dotL w g → dotR (homT f) w ≡ₜ dotL w (homT g))

end Lax149335.SimpleCompleteness
