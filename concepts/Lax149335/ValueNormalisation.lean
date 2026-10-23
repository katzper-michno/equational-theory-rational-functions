import Lax149335.EquationalTheory

/-!
---
title: Normalisation of values
type: lemma
---
**Lemma (Normalisation of values).** Every value $1 \to A$ is provably equivalent to a
value built from the identity on $1$ using the following constructors: $v \mathbin{;}
\mathsf{Left}$ and $v \mathbin{;} \mathsf{Right}$ for values of co-products, $(v, w)$ for
values of products, and $v \cdot w$, $[v]$ and $[\,]$ for values of list types.
-/

namespace Lax149335.ValueNormalisation

open Lax149335.Types Lax149335.Terms Lax149335.Terms.Term Lax149335.DerivedTerms
  Lax149335.DerivedTerms.Term Lax149335.EquationalTheory

/-- Values in normal form. -/
inductive NormalValue : {A : Ty} → Value A → Prop
  /-- The identity on the unit type. -/
  | id : NormalValue (Term.id Ty.unit)
  /-- A co-product value `v; Left`. -/
  | inl {A B : Ty} {v : Value A} : NormalValue v → NormalValue (v ⨟ Term.inl A B)
  /-- A co-product value `v; Right`. -/
  | inr {A B : Ty} {v : Value B} : NormalValue v → NormalValue (v ⨟ Term.inr A B)
  /-- A product value `(v, w)`. -/
  | pair {A B : Ty} {v : Value A} {w : Value B} :
      NormalValue v → NormalValue w → NormalValue (pairR v w)
  /-- The concatenation `v · w` of two list values. -/
  | dot {A : Ty} {v w : Value A⋆} : NormalValue v → NormalValue w → NormalValue (dotL v w)
  /-- A singleton list value `[v]`. -/
  | sing {A : Ty} {v : Value A} : NormalValue v → NormalValue (sing v)
  /-- The empty list value `[]`. -/
  | nil {A : Ty} : NormalValue (nilT A)

/-- Every value is provably equivalent to a value in normal form. -/
axiom normalisation_of_values {A : Ty} (v : Value A) : ∃ u : Value A, NormalValue u ∧ v ≡ₜ u

end Lax149335.ValueNormalisation
