import Lax149335.DerivedTerms

/-!
---
title: Lifts and drops
type: definition
---
**Definition (Lifts and drops).** *Lift* terms (respectively, *drop* terms) are those
which can be obtained from the atomic lift (respectively, atomic drop) terms in the following table by
applying composition, as well as the functoriality combinators for co-products, products and
lists.

The atomic lift terms are
$$
\begin{gathered}
A \xrightarrow{\mathrm{id}} A \qquad A + B \xrightarrow{\mathsf{comm}} B + A \qquad
A \to A \times 1 \qquad A \to 1 \times A \\
A \times (B \times C) \xrightarrow{\mathsf{assocL}} (A \times B) \times C \qquad
(A \times B) \times C \xrightarrow{\mathsf{assocR}} A \times (B \times C) \\
A + (B + C) \to (A + B) + C \qquad (A + B) + C \to A + (B + C) \\
(A + B) \times C \xrightarrow{\mathsf{distL}} A \times C + B \times C \qquad
A \times (B + C) \xrightarrow{\mathsf{distR}} A \times B + A \times C \\
(A + B)^* \xrightarrow{\mathsf{split}} A^* \times (B \times A^*)^* \qquad
(A \times B)^* \xrightarrow{\mathsf{shift}} 1 + A \times (B \times A)^* \times B
\end{gathered}
$$
and the atomic drop terms are
$$
\begin{gathered}
A \xrightarrow{\mathrm{id}} A \qquad A \xrightarrow{1 \,;\, v} B \qquad
A \times B \xrightarrow{\mathsf{fst}} A \qquad A \times B \xrightarrow{\mathsf{snd}} B
\qquad A \xrightarrow{\mathsf{Left}} A + B \qquad B \xrightarrow{\mathsf{Right}} A + B \\
\mathsf{assocL} \qquad \mathsf{assocR} \qquad A + A \xrightarrow{\mathsf{codiag}} A
\qquad A \xrightarrow{\mathsf{pure}} A^* \qquad A^{**} \xrightarrow{\mathsf{concat}} A^*
\qquad A^* \times A^* \xrightarrow{\mathsf{binconcat}} A^* \\
A \times (B \times A)^* \times B \xrightarrow{\mathsf{unshift}} (A \times B)^*
\end{gathered}
$$
where $1 \,;\, v$ is the unique term $A \to 1$ followed by an arbitrary value
$v : 1 \to B$.
-/

namespace Lax149335.LiftsAndDrops

open Lax149335.Types Lax149335.Terms Lax149335.DerivedTerms Lax149335.DerivedTerms.Term

/-- **Lifts.** The terms obtained from the atomic lift terms by
composition and the functoriality combinators of products, co-products and lists. -/
inductive IsLift : {A B : Ty} → Term A B → Prop
  /-- Lifts are closed under composition. -/
  | comp {A B C : Ty} {f : Term A B} {g : Term B C} : IsLift f → IsLift g → IsLift (f ⨟ g)
  /-- Lifts are closed under functoriality of products. -/
  | prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsLift f → IsLift g → IsLift (Term.prodF f g)
  /-- Lifts are closed under functoriality of co-products. -/
  | sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsLift f → IsLift g → IsLift (Term.sumF f g)
  /-- Lifts are closed under functoriality of lists. -/
  | listF {A B : Ty} {f : Term A B} : IsLift f → IsLift (Term.listF f)
  /-- The identity is a prime lift. -/
  | id (A : Ty) : IsLift (Term.id A)
  /-- `(id,1)` is a prime lift. -/
  | unitR (A : Ty) : IsLift (Term.unitR A)
  /-- `(1,id)` is a prime lift. -/
  | unitL (A : Ty) : IsLift (Term.unitL A)
  /-- `assocL` is a prime lift. -/
  | assocL (A B C : Ty) : IsLift (Term.assocL A B C)
  /-- `assocR` is a prime lift. -/
  | assocR (A B C : Ty) : IsLift (Term.assocR A B C)
  /-- Associativity of the co-product, from right to left, is a prime lift. -/
  | sumAssocL (A B C : Ty) : IsLift (Term.sumAssocL A B C)
  /-- Associativity of the co-product, from left to right, is a prime lift. -/
  | sumAssocR (A B C : Ty) : IsLift (Term.sumAssocR A B C)
  /-- Commutativity of the co-product is a prime lift. -/
  | comm (A B : Ty) : IsLift (Term.comm A B)
  /-- `distL` is a prime lift. -/
  | distL (A B C : Ty) : IsLift (Term.distL A B C)
  /-- `distR` is a prime lift. -/
  | distR (A B C : Ty) : IsLift (Term.distR A B C)
  /-- `split` is a prime lift. -/
  | split (A B : Ty) : IsLift (Term.split A B)
  /-- `shift` is a prime lift. -/
  | shift (A B : Ty) : IsLift (Term.shift A B)

/-- **Drops.** The terms obtained from the atomic drop terms by
composition and the functoriality combinators of products, co-products and lists. -/
inductive IsDrop : {A B : Ty} → Term A B → Prop
  /-- Drops are closed under composition. -/
  | comp {A B C : Ty} {f : Term A B} {g : Term B C} : IsDrop f → IsDrop g → IsDrop (f ⨟ g)
  /-- Drops are closed under functoriality of products. -/
  | prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsDrop f → IsDrop g → IsDrop (Term.prodF f g)
  /-- Drops are closed under functoriality of co-products. -/
  | sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂} :
      IsDrop f → IsDrop g → IsDrop (Term.sumF f g)
  /-- Drops are closed under functoriality of lists. -/
  | listF {A B : Ty} {f : Term A B} : IsDrop f → IsDrop (Term.listF f)
  /-- The identity is a prime drop. -/
  | id (A : Ty) : IsDrop (Term.id A)
  /-- A constant function `1 ; v`, for an arbitrary value `v`, is a prime drop. -/
  | bangV (A : Ty) {B : Ty} (v : Value B) : IsDrop (Term.toUnit A ⨟ v)
  /-- `assocL` is a prime drop. -/
  | assocL (A B C : Ty) : IsDrop (Term.assocL A B C)
  /-- `assocR` is a prime drop. -/
  | assocR (A B C : Ty) : IsDrop (Term.assocR A B C)
  /-- `fst` is a prime drop. -/
  | fst (A B : Ty) : IsDrop (Term.fst A B)
  /-- `snd` is a prime drop. -/
  | snd (A B : Ty) : IsDrop (Term.snd A B)
  /-- `Left` is a prime drop. -/
  | inl (A B : Ty) : IsDrop (Term.inl A B)
  /-- `Right` is a prime drop. -/
  | inr (A B : Ty) : IsDrop (Term.inr A B)
  /-- The co-diagonal is a prime drop. -/
  | codiag (A : Ty) : IsDrop (Term.codiag A)
  /-- `pure` is a prime drop. -/
  | pureT (A : Ty) : IsDrop (Term.pureT A)
  /-- `binconcat` is a prime drop. -/
  | binconcat (A : Ty) : IsDrop (Term.binconcat A)
  /-- `concat` is a prime drop. -/
  | concat (A : Ty) : IsDrop (Term.concat A)
  /-- `unshift` is a prime drop. -/
  | unshift (A B : Ty) : IsDrop (Term.unshift A B)

end Lax149335.LiftsAndDrops
