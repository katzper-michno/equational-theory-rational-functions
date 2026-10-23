import Lax149335.SimpleRationalFunctions

/-!
---
title: Equivalence of simple rational terms is decidable
type: corollary
---
**Corollary 2.8.** Equivalence for simple rational terms is decidable in polynomial time.

# Formalization notes

Running time is not expressible here. The corollary is formalised by a decision procedure
that is explicit enough to make the polynomial bound evident: two simple rational terms
$f, g : A \to B^*$ define the same function if and only if they agree on a fixed finite set
$T(A)$ of *test inputs*, defined by induction on the type $A$:
$$
\begin{aligned}
T(1) &= \{()\}, &
T(A_1 + A_2) &= \mathsf{Left}\, T(A_1) \cup \mathsf{Right}\, T(A_2), \\
T(A^*) &= \{[\,]\} \cup \{[a] : a \in T(A)\}, &
T(A_1 \times A_2) &= T(A_1) \times \{e_2\} \;\cup\; \{e_1\} \times T(A_2),
\end{aligned}
$$
where $e_i$ is a fixed element of $A_i$ (`Ty.someElem`). The number of test inputs is at
most the size of $A$, every test input has size at most the size of $A$, and a simple
rational term is evaluated on an input in polynomial time.
-/

namespace Lax149335.DecidableEquivalence

open Lax149335.Types Lax149335.SimpleRationalFunctions

/-- The test inputs `T(A)` of a type. -/
def testInputs : (A : Ty) → List ⟦A⟧
  | .unit => [()]
  | .sum A₁ A₂ => (testInputs A₁).map Sum.inl ++ (testInputs A₂).map Sum.inr
  | .prod A₁ A₂ =>
      (testInputs A₁).map (fun a => (a, Ty.someElem A₂)) ++
        (testInputs A₂).map (fun b => (Ty.someElem A₁, b))
  | .list A => [] :: (testInputs A).map (fun a => [a])

/-- **Corollary 2.8.** Two simple rational terms define the same function if and only if they
agree on all test inputs. -/
axiom decidable_equivalence {Bs : Type} {A : Ty} (f g : SimpleTerm Bs A) :
    f.den = g.den ↔ ∀ x ∈ testInputs A, f.den x = g.den x

end Lax149335.DecidableEquivalence
