import Lax149335Proofs.Appendix.Groups.Unprefixing

/-!
# The denotation of unprefixing

The equational proofs that distribute the unprefixing operation over concatenation
(`Lax149335Proofs.Term.unpref_concat` and `Lax149335Proofs.Term.unpref_commutes_with_concat`) are carried
out on the denotational side wherever the equational theory allows it, which is what this
file prepares.

The key combinatorial fact is `Lax149335Proofs.Term.unprefDen_append`: unprefixing a concatenation
is the concatenation of the unprefixings, provided that the second one starts from the group
element carried by the last entry of the first list.  The file also records the denotation of
`unpref` itself and of the injection `ι_g` in the point-free form that `simp` wants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Unprefixing a concatenation -/

/-- The group element that the unprefixing operation has accumulated after reading a list:
the group element of its last entry, or the initial accumulator if the list is empty. -/
def lastAcc {α G : Type} : G → List (α × G) → G
  | acc, [] => acc
  | _, (_, g) :: t => lastAcc g t

@[simp] theorem lastAcc_nil {α G : Type} (acc : G) : lastAcc acc ([] : List (α × G)) = acc :=
  rfl

@[simp] theorem lastAcc_cons {α G : Type} (acc : G) (a : α) (g : G) (t : List (α × G)) :
    lastAcc acc ((a, g) :: t) = lastAcc g t := rfl

theorem lastAcc_append {α G : Type} (acc : G) (l₁ l₂ : List (α × G)) :
    lastAcc acc (l₁ ++ l₂) = lastAcc (lastAcc acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons p t ih => obtain ⟨a, g⟩ := p; simpa using ih g

theorem lastAcc_append_singleton {α G : Type} (acc : G) (l : List (α × G)) (a : α) (g : G) :
    lastAcc acc (l ++ [(a, g)]) = g := by
  rw [lastAcc_append]
  rfl

/-- Unprefixing distributes over concatenation, with the accumulator of the second part
given by the last group element of the first part. -/
theorem unprefDen_append {α G : Type} [Group G] (acc : G) (l₁ l₂ : List (α × G)) :
    unprefDen acc (l₁ ++ l₂) = unprefDen acc l₁ ++ unprefDen (lastAcc acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨a, g⟩ := p
      simpa using ih g

/-! ### The denotations of `unpref` and of the injection -/

/-- The denotation of `unpref`, as a function. -/
@[simp] theorem den_unpref_fun (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (unpref A G).den = letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧) := by
  funext l
  exact den_unpref A G l

/-- The denotation of the injection `ι_g`. -/
@[simp] theorem den_iotaG (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧)
    (u : List (⟦A⟧ × ⟦Ty.finAlph n⟧)) (a : ⟦A⟧) (t : Unit) :
    (iotaG A g).den (u, (a, t)) = u ++ [(a, g)] := by
  obtain ⟨⟩ := t
  simp [iotaG]

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
