import Lax149335.SimpleRationalTerms

/-!
---
title: Synchronised output lengths
type: claim
---
**Claim 2.7.** This claim arises in the induction step for products in the proof of
Theorem 2.6. Consider two simple rational terms with input type
$A_1^* \times \cdots \times A_n^*$ of the form
$$
f = w_0 \cdot (\mathrm{hom}\, f_1 \cdot w_1) \odot \cdots \odot (\mathrm{hom}\, f_n \cdot w_n)
\qquad
g = v_0 \cdot (\mathrm{hom}\, g_1 \cdot v_1) \odot \cdots \odot (\mathrm{hom}\, g_n \cdot v_n)
$$
that define the same function. Then for every $i \in \{1, \ldots, n\}$ and every
$a \in A_i$, the strings $f_i(a)$ and $g_i(a)$ have the same length.

# Formalization notes

The input type is $A_1^* \times (A_2^* \times \cdots \times (A_n^* \times 1))$, and the
components $(f_i, w_i)$ are given as a list (`HomList`).
-/

namespace Lax149335.SynchronisedLengths

open Lax149335.Types Lax149335.SimpleRationalTerms

namespace SimpleTerm

variable {Bs : Type}

/-- The type `A₁* × (A₂* × ⋯ × (Aₙ* × 1))`. -/
def prodListTy : List Ty → Ty
  | [] => Ty.unit
  | A :: As => Ty.prod A⋆ (prodListTy As)

/-- A list of pairs `(fᵢ, wᵢ)` of a simple rational term `fᵢ : Aᵢ → Bs*` and a string `wᵢ`. -/
inductive HomList (Bs : Type) : List Ty → Type
  | nil : HomList Bs []
  | cons {A : Ty} {As : List Ty} : SimpleTerm Bs A → List Bs → HomList Bs As →
      HomList Bs (A :: As)

/-- The term `(hom f₁ · w₁) ⊙ ⋯ ⊙ (hom fₙ · wₙ)` of a list of pairs. -/
def HomList.term : {As : List Ty} → HomList Bs As → SimpleTerm Bs (prodListTy As)
  | _, .nil => .empty
  | _, .cons f w rest => .conc (.post (.hom f) w) rest.term

/-- Two lists of pairs whose terms `fᵢ` and `gᵢ` produce outputs of the same length on every
input. -/
def HomList.SameLengths : {As : List Ty} → HomList Bs As → HomList Bs As → Prop
  | _, .nil, .nil => True
  | _, .cons f _ F, .cons g _ G =>
      (∀ a, (f.den a).length = (g.den a).length) ∧ HomList.SameLengths F G

end SimpleTerm

open SimpleTerm

/-- **Claim 2.7.** If `w₀ · (hom f₁ · w₁) ⊙ ⋯ ⊙ (hom fₙ · wₙ)` and
`v₀ · (hom g₁ · v₁) ⊙ ⋯ ⊙ (hom gₙ · vₙ)` define the same function, then `fᵢ` and `gᵢ` produce
outputs of the same length on every input. -/
axiom claim_same_lengths {Bs : Type} {As : List Ty} (F G : HomList Bs As) (w₀ v₀ : List Bs) :
    (SimpleRationalTerms.SimpleTerm.pre w₀ F.term).den =
      (SimpleRationalTerms.SimpleTerm.pre v₀ G.term).den →
    F.SameLengths G

end Lax149335.SynchronisedLengths
