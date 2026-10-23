import Lax149335.EquationalTheory

/-!
---
title: Concatenation with values
type: lemma
---
**Lemma 5.2 (Concatenation with values).** For terms $f : A \to B^*$ and
$g : A' \to B^*$ and list values $w, v : 1 \to B^*$,
$$
\begin{aligned}
(f \cdot w) \cdot v &\equiv f \cdot (w \cdot v), &
w \cdot (v \cdot f) &\equiv (w \cdot v) \cdot f, &
f \cdot [\,] &\equiv f \equiv [\,] \cdot f, \\
(w \cdot f) \cdot v &\equiv w \cdot (f \cdot v), &
(f \cdot w) \odot g &\equiv f \odot (w \cdot g).
\end{aligned}
$$
-/

namespace Lax149335.ValueConcatenation

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.EquationalTheory

/-- **Lemma 5.2.** The associativity and unit laws for concatenation with values. -/
axiom value_assoc {A A' B : Ty} (f : Term A B⋆) (g : Term A' B⋆) (w v : Value B⋆) :
    (dotR (dotR f w) v ≡ₜ dotR f (dotL w v)) ∧
    (dotL w (dotL v f) ≡ₜ dotL (dotL w v) f) ∧
    (dotR f (nilT B) ≡ₜ f) ∧
    (dotL (nilT B) f ≡ₜ f) ∧
    (dotR (dotL w f) v ≡ₜ dotL w (dotR f v)) ∧
    (fdot (dotR f w) g ≡ₜ fdot f (dotL w g))

end Lax149335.ValueConcatenation
