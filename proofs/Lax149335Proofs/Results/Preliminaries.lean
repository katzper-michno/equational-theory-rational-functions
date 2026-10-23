import Lax149335Proofs.Preliminaries.Overview
import Lax149335Proofs.Appendix.Bundles.Window

/-!
# Preliminaries for the completeness proof

The proofs of the laws for concatenation with values, the normalisation of values, the
cancellation of injective and surjective terms, and the injective string representations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs.Results

/--
---
conclusion: Lax149335.ValueConcatenation.value_assoc
---
Each law is derived from the monoid axioms for `binconcat` and the coherence laws
for products, which in turn follow from Mac Lane's pentagon and triangle.
-/
theorem value_assoc : type_of% @Lax149335.ValueConcatenation.value_assoc :=
  @Lax149335Proofs.value_assoc

/--
---
conclusion: Lax149335.ValueNormalisation.normalisation_of_values
---
Every term composed with the value representing an element of a type is provably equivalent
to the value representing the image of that element; the lemma is the special case of a
value applied to the unique element of `1`.
-/
theorem normalisation_of_values :
    type_of% @Lax149335.ValueNormalisation.normalisation_of_values :=
  @Lax149335Proofs.normalisation_of_values

/--
---
conclusion: Lax149335.Cancellation.cancel
---
Compose with the one-sided inverse and use the category axioms.
-/
theorem cancel : type_of% @Lax149335.Cancellation.cancel :=
  @Lax149335Proofs.cancel

/--
---
conclusion: Lax149335.StringRepresentations.exists_injective_binary_encoding
---
A type is first encoded injectively into strings over a finite alphabet, by induction on the
type, and the finite alphabet is then encoded into binary strings by blocks of a fixed
length that is a power of two, using the injectivity half of the bundle lemma.
-/
theorem exists_injective_binary_encoding :
    type_of% @Lax149335.StringRepresentations.exists_injective_binary_encoding :=
  @Lax149335Proofs.exists_injective_binary_encoding

end Lax149335Proofs.Results
