import Lax149335.Types

/-!
---
title: Simple rational functions
type: definition
---
**Definition (Simple rational functions).** Let $B$ be a finite alphabet. The *simple
rational terms* with outputs in $B^*$ are the terms generated from the term
$[] : 1 \to B^*$, which produces the empty string, by the following combinators:

- *co-pairing*: for $f_1 : A_1 \to B^*$ and $f_2 : A_2 \to B^*$, the term
  $\langle f_1, f_2 \rangle : A_1 + A_2 \to B^*$ that applies $f_1$ or $f_2$ depending on
  the summand;
- *concatenation*: for $f_1 : A_1 \to B^*$ and $f_2 : A_2 \to B^*$, the term
  $f_1 \odot f_2 : A_1 \times A_2 \to B^*$ that maps $(a_1, a_2)$ to $f_1(a_1)\,f_2(a_2)$;
- *homomorphism*: for $f : A \to B^*$, the term $\mathrm{hom}\, f : A^* \to B^*$ that maps
  $[a_1, \ldots, a_n]$ to $f(a_1) \cdots f(a_n)$;
- *constants*: for $f : A \to B^*$ and a string $w \in B^*$, the terms $w \cdot f$ and
  $f \cdot w$, which prepend or append $w$ to the output.

A *simple rational function* is a function that is defined by a simple rational term.

# Formalization notes

The output alphabet is an arbitrary Lean type `Bs`; the statements that need it to be
finite say so.
-/

namespace Lax149335.SimpleRationalFunctions

open Lax149335.Types

/-- Simple rational terms `A → Bs*`. -/
inductive SimpleTerm (Bs : Type) : Ty → Type
  /-- The term `[] : 1 → Bs*` with empty output. -/
  | empty : SimpleTerm Bs Ty.unit
  /-- Co-pairing `⟨f₁, f₂⟩ : A₁ + A₂ → Bs*`. -/
  | either {A₁ A₂ : Ty} : SimpleTerm Bs A₁ → SimpleTerm Bs A₂ → SimpleTerm Bs (A₁ ⊕' A₂)
  /-- Concatenation `f₁ ⊙ f₂ : A₁ × A₂ → Bs*`. -/
  | conc {A₁ A₂ : Ty} : SimpleTerm Bs A₁ → SimpleTerm Bs A₂ → SimpleTerm Bs (A₁ ⊗ A₂)
  /-- Homomorphism `hom f : A* → Bs*`. -/
  | hom {A : Ty} : SimpleTerm Bs A → SimpleTerm Bs A⋆
  /-- Prepending a string constant, `w · f`. -/
  | pre {A : Ty} : List Bs → SimpleTerm Bs A → SimpleTerm Bs A
  /-- Appending a string constant, `f · w`. -/
  | post {A : Ty} : SimpleTerm Bs A → List Bs → SimpleTerm Bs A

namespace SimpleTerm

variable {Bs : Type}

/-- The function defined by a simple rational term. -/
def den : {A : Ty} → SimpleTerm Bs A → ⟦A⟧ → List Bs
  | _, .empty, _ => []
  | _, .either f _, .inl a => den f a
  | _, .either _ g, .inr b => den g b
  | _, .conc f g, (a, b) => den f a ++ den g b
  | _, .hom f, l => (l.map (den f)).flatten
  | _, .pre w f, a => w ++ den f a
  | _, .post f w, a => den f a ++ w

/-- A function is a simple rational function if it is defined by a simple rational term. -/
def IsSimpleFun {A : Ty} (f : ⟦A⟧ → List Bs) : Prop := ∃ t : SimpleTerm Bs A, t.den = f

end SimpleTerm

end Lax149335.SimpleRationalFunctions
