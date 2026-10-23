import Lax149335.SimpleRationalTerms

/-!
---
title: Guarded terms
type: definition
---
Let $k \in \{1, 2, \ldots\}$. A term $f : A \to B^*$ is *$k$-guarded*
if it is either

1. *constant*: the composition of the unique term $A \to 1$ with a value; or
2. *long*: of the form $u \cdot h \cdot v$ for values $u, v$ of length $k$ and a simple
   rational term $h$.

A term $f : A \to B^*$ is *nonempty* if it never produces the empty list.

The reductions to guarded and to nonempty terms are about $n$-ary co-pairings
$\langle f_1, \ldots, f_n \rangle : A_1 + \cdots + A_n \to B^*$ of such terms, and about the
*nesting depth* of the list constructor in a type, on which the proof of completeness for simple
rational terms is an induction.

# Formalization notes

An $n$-ary co-pairing, for $n \geq 1$, is given by its first term
$f_1 : A_1 \to B^*$ and the list of the remaining terms (`Cases`); its input type
$A_1 + (A_2 + \cdots + A_n)$ is `sumTyOf A₁ [A₂, …, Aₙ]`.
-/

namespace Lax149335.GuardedTerms

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term
  Lax149335.SimpleRationalTerms

/-- `f : A → B*` is `k`-guarded if it is constant, or of the form
`u · h · v` for values `u`, `v` of length `k` and a simple rational term `h`. -/
def KGuarded (k : ℕ) (B : Ty) {A : Ty} (f : Term A B⋆) : Prop :=
  (∃ v : Value B⋆, f = toUnit A ⨟ v) ∨
  (∃ (u v : Value B⋆) (h : Term A B⋆),
      IsSimple B h ∧ valLength u = k ∧ valLength v = k ∧ f = dotR (dotL u h) v)

/-- A term with list outputs is nonempty if it never produces the empty list. -/
def NonemptyOutput {A B : Ty} (f : Term A B⋆) : Prop := ∀ a : ⟦A⟧, f.den a ≠ []

/-- The co-product `A₀ + (A₁ + ⋯ + Aₙ)` of a nonempty list of types. -/
def sumTyOf : Ty → List Ty → Ty
  | A, [] => A
  | A, (A' :: As) => A ⊕' sumTyOf A' As

/-- A list of terms `Aᵢ → B`, one for each type in a list of types. -/
inductive Cases (B : Ty) : List Ty → Type
  /-- The empty list of terms. -/
  | nil : Cases B []
  /-- One more term. -/
  | cons {A : Ty} {As : List Ty} : Term A B → Cases B As → Cases B (A :: As)

/-- The `n`-ary co-pairing `⟨f₀, f₁, …, fₙ⟩ : A₀ + (A₁ + ⋯ + Aₙ) → B`. -/
def copair {B : Ty} : {A : Ty} → {As : List Ty} → Term A B → Cases B As →
    Term (sumTyOf A As) B
  | _, [], f, _ => f
  | _, _ :: _, f, .cons g rest => Term.either f (copair g rest)

/-- A property holds for all terms in a list of terms. -/
def Cases.All {B : Ty} (P : (A : Ty) → Term A B → Prop) :
    {As : List Ty} → Cases B As → Prop
  | [], _ => True
  | _ :: _, .cons f rest => P _ f ∧ Cases.All P rest

/-- The nesting depth of the list constructor in a type. -/
def Ty.listDepth : Ty → ℕ
  | .unit => 0
  | .prod A B => max (Ty.listDepth A) (Ty.listDepth B)
  | .sum A B => max (Ty.listDepth A) (Ty.listDepth B)
  | .list A => Ty.listDepth A + 1

end Lax149335.GuardedTerms
