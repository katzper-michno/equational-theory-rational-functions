import Lax149335Proofs.SimpleCompleteness.JointCasesDepth

/-!
# Shuffling co-products

The proof of value extraction has to combine two decompositions of the input type into an
"empty" and a "nonempty" part into a single such decomposition of the co-product of the two
input types.  This file collects the provable isomorphisms of co-products that are needed for
this, together with their action on co-pairings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace ProvableIso

theorem sumAssocR (A B C : Ty) : ProvableIso (Term.sumAssocR A B C) :=
  ⟨Term.sumAssocL A B C, Term.sumAssocR_sumAssocL A B C, Term.sumAssocL_sumAssocR A B C⟩

theorem sumAssocL (A B C : Ty) : ProvableIso (Term.sumAssocL A B C) :=
  ⟨Term.sumAssocR A B C, Term.sumAssocL_sumAssocR A B C, Term.sumAssocR_sumAssocL A B C⟩

theorem sumRot (A E N : Ty) : ProvableIso (Term.sumRot A E N) :=
  ⟨Term.sumRot E A N, Term.sumRot_sumRot A E N, Term.sumRot_sumRot E A N⟩

theorem comm (A B : Ty) : ProvableIso (Term.comm A B) :=
  ⟨Term.comm B A, Term.comm_comm A B, Term.comm_comm B A⟩

end ProvableIso

namespace Term

/-- Composing a co-projection into the left summand with a co-pairing. -/
theorem comp_inl_either {X A₁ A₂ C : Ty} (p : Term X A₁) (f : Term A₁ C) (g : Term A₂ C) :
    ((p ⨟ inl A₁ A₂) ⨟ either f g) ≡ₜ (p ⨟ f) :=
  (PEq.comp_assoc _ _ _).trans (PEq.compR _ (inl_either f g))

/-- Composing a co-projection into the right summand with a co-pairing. -/
theorem comp_inr_either {X A₁ A₂ C : Ty} (p : Term X A₂) (f : Term A₁ C) (g : Term A₂ C) :
    ((p ⨟ inr A₁ A₂) ⨟ either f g) ≡ₜ (p ⨟ g) :=
  (PEq.comp_assoc _ _ _).trans (PEq.compR _ (inr_either f g))

/-- Swapping the two summands of a co-product before a co-pairing. -/
theorem comm_either {A B C : Ty} (x : Term B C) (y : Term A C) :
    (Term.comm A B ⨟ either x y) ≡ₜ either y x :=
  (either_comp _ _ _).trans (either_congr (inr_either x y) (inl_either x y))

/-- **The four-fold shuffle of co-products**, `(E₁ + E₂) + (N₁ + N₂) → (E₁ + N₁) + (E₂ + N₂)`. -/
def sumShuffle (E₁ N₁ E₂ N₂ : Ty) :
    Term ((E₁ ⊕' E₂) ⊕' (N₁ ⊕' N₂)) ((E₁ ⊕' N₁) ⊕' (E₂ ⊕' N₂)) :=
  either
    (either (inl E₁ N₁ ⨟ inl (E₁ ⊕' N₁) (E₂ ⊕' N₂)) (inl E₂ N₂ ⨟ inr (E₁ ⊕' N₁) (E₂ ⊕' N₂)))
    (either (inr E₁ N₁ ⨟ inl (E₁ ⊕' N₁) (E₂ ⊕' N₂)) (inr E₂ N₂ ⨟ inr (E₁ ⊕' N₁) (E₂ ⊕' N₂)))

/-- The action of the four-fold shuffle on a co-pairing. -/
theorem sumShuffle_either {E₁ N₁ E₂ N₂ C : Ty} (a : Term E₁ C) (b : Term N₁ C)
    (c : Term E₂ C) (d : Term N₂ C) :
    (sumShuffle E₁ N₁ E₂ N₂ ⨟ either (either a b) (either c d)) ≡ₜ
      either (either a c) (either b d) := by
  refine (either_comp _ _ _).trans (either_congr ?_ ?_)
  · refine (either_comp _ _ _).trans (either_congr ?_ ?_)
    · exact (comp_inl_either _ _ _).trans (inl_either a b)
    · exact (comp_inr_either _ _ _).trans (inl_either c d)
  · refine (either_comp _ _ _).trans (either_congr ?_ ?_)
    · exact (comp_inl_either _ _ _).trans (inr_either a b)
    · exact (comp_inr_either _ _ _).trans (inr_either c d)

/-- The four-fold shuffle is its own inverse, up to a permutation of its arguments. -/
theorem sumShuffle_sumShuffle (E₁ N₁ E₂ N₂ : Ty) :
    (sumShuffle E₁ N₁ E₂ N₂ ⨟ sumShuffle E₁ E₂ N₁ N₂) ≡ₜ Term.id ((E₁ ⊕' E₂) ⊕' (N₁ ⊕' N₂)) := by
  have h : sumShuffle E₁ E₂ N₁ N₂ =
      either
        (either (inl E₁ E₂ ⨟ inl (E₁ ⊕' E₂) (N₁ ⊕' N₂))
          (inl N₁ N₂ ⨟ inr (E₁ ⊕' E₂) (N₁ ⊕' N₂)))
        (either (inr E₁ E₂ ⨟ inl (E₁ ⊕' E₂) (N₁ ⊕' N₂))
          (inr N₁ N₂ ⨟ inr (E₁ ⊕' E₂) (N₁ ⊕' N₂))) := rfl
  rw [h]
  refine (sumShuffle_either _ _ _ _).trans ?_
  calc either
        (either (inl E₁ E₂ ⨟ inl (E₁ ⊕' E₂) (N₁ ⊕' N₂)) (inr E₁ E₂ ⨟ inl (E₁ ⊕' E₂) (N₁ ⊕' N₂)))
        (either (inl N₁ N₂ ⨟ inr (E₁ ⊕' E₂) (N₁ ⊕' N₂)) (inr N₁ N₂ ⨟ inr (E₁ ⊕' E₂) (N₁ ⊕' N₂)))
      ≡ₜ either (either (inl E₁ E₂) (inr E₁ E₂) ⨟ inl (E₁ ⊕' E₂) (N₁ ⊕' N₂))
          (either (inl N₁ N₂) (inr N₁ N₂) ⨟ inr (E₁ ⊕' E₂) (N₁ ⊕' N₂)) :=
        either_congr (PEq.symm (either_comp _ _ _)) (PEq.symm (either_comp _ _ _))
    _ ≡ₜ either (Term.id (E₁ ⊕' E₂) ⨟ inl (E₁ ⊕' E₂) (N₁ ⊕' N₂))
          (Term.id (N₁ ⊕' N₂) ⨟ inr (E₁ ⊕' E₂) (N₁ ⊕' N₂)) :=
        either_congr (PEq.compL _ (either_inl_inr _ _)) (PEq.compL _ (either_inl_inr _ _))
    _ ≡ₜ either (inl (E₁ ⊕' E₂) (N₁ ⊕' N₂)) (inr (E₁ ⊕' E₂) (N₁ ⊕' N₂)) :=
        either_congr (PEq.id_comp _) (PEq.id_comp _)
    _ ≡ₜ Term.id ((E₁ ⊕' E₂) ⊕' (N₁ ⊕' N₂)) := either_inl_inr _ _

end Term

theorem ProvableIso.sumShuffle (E₁ N₁ E₂ N₂ : Ty) :
    ProvableIso (Term.sumShuffle E₁ N₁ E₂ N₂) :=
  ⟨Term.sumShuffle E₁ E₂ N₁ N₂, Term.sumShuffle_sumShuffle E₁ N₁ E₂ N₂,
    Term.sumShuffle_sumShuffle E₁ E₂ N₁ N₂⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
