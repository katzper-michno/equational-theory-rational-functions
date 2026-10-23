import Lax149335Proofs.Preliminaries.StringRepresentation
import Lax149335Proofs.Appendix.Naturality
import Lax149335Proofs.Appendix.ValueAlgebra
import Lax149335Proofs.Appendix.ValueNormalisation

/-!
# Preliminaries for the completeness proof (Section 5)

Concatenation maps and their naturality (Section 5.1), values and their normalisation
(Section 5.2), and provably injective / surjective terms (Section 5.3).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! Lemma 5.2 (`Lax149335Proofs.value_assoc`) is proved in `Lax149335Proofs.Appendix.ValueAlgebra`. -/

/-- The value representing an element of a type is in normal form. -/
theorem encV_normal : (A : Ty) → (x : ⟦A⟧) → NormalValue (encV A x)
  | .unit => fun _ => NormalValue.id
  | .prod A B => fun x => NormalValue.pair (encV_normal A x.1) (encV_normal B x.2)
  | .sum A B => fun x =>
      match x with
      | .inl a => NormalValue.inl (encV_normal A a)
      | .inr b => NormalValue.inr (encV_normal B b)
  | .list A => fun l => by
      induction l with
      | nil => exact NormalValue.nil
      | cons a t ih => exact NormalValue.dot (NormalValue.sing (encV_normal A a)) ih

/-- **Lemma 5.3 (Normalisation of values).**  Every value is provably equivalent to one
constructed using the constructors of `NormalValue`.

The proof is the one of the appendix, organised through the value `encV A x` representing an
element `x` of a type: every term composed with such a value again gives such a value
(`Lax149335Proofs.computes`), and the lemma is the special case where the term is the value itself
and the element is the unique element of the unit type. -/
theorem normalisation_of_values {A : Ty} (v : Value A) :
    ∃ u : Value A, NormalValue u ∧ v ≡ₜ u :=
  ⟨encV A (v.den ()), encV_normal A _, (PEq.symm (PEq.id_comp v)).trans (computes v ())⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
