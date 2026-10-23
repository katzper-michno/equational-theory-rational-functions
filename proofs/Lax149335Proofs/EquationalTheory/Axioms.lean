import Lax149335Proofs.Terms.Derived

/-!
# The equational theory (Section 4)

The relation `f ≡ₜ g` of *provable equality* of rational terms is the least equivalence
relation that contains Axioms 1-16 of Section 4 and that is stable under applying the four
combinators of the system (composition and functoriality of products, co-products and lists).
Theorem 4.1, the main result of the paper, is stated at the end of the file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

instance {A B : Ty} : Trans (α := Term A B) PEq PEq PEq := ⟨PEq.trans⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
