import Lax149335Proofs.Appendix.ShiftOnes
import Lax149335Proofs.Appendix.BasicFacts
import Lax149335Proofs.Appendix.ValueAlgebra
import Lax149335Proofs.EquationalTheory.Soundness

/-!
# Multivariate list-polynomial functors (appendix, *Concatenation maps*)

The appendix section on concatenation maps works with type constructors that have several
parameters.  This file introduces them, together with their functorial action, and proves the
one distributivity law of the section that the later files use.

A multivariate functor is represented by the inductive type `Lax149335Proofs.Term.TyFn`, whose
parameters are indexed by natural numbers; the parameters are instantiated by an environment
`As : ℕ → Ty`.

The two consequences of the section that the development uses, the lemmas *shift ones* and
*shift unsplit*, are proved in `Lax149335Proofs.Appendix.ShiftOnes`
(`Lax149335Proofs.Term.shift_ones` and `Lax149335Proofs.Term.splitLT_iso`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

namespace Term

/-! ### Multivariate list-polynomial functors -/

/-- **Multivariate list-polynomial functors** (appendix, *Concatenation maps*): type
constructors with arbitrarily many parameters, built from the parameters and the unit type
using products, co-products and lists. -/
inductive TyFn : Type
  /-- The `i`-th parameter. -/
  | param : ℕ → TyFn
  /-- The unit type. -/
  | unit : TyFn
  /-- Product of two type constructors. -/
  | prod : TyFn → TyFn → TyFn
  /-- Co-product of two type constructors. -/
  | sum : TyFn → TyFn → TyFn
  /-- List of a type constructor. -/
  | list : TyFn → TyFn

/-- The type `F(A₀, A₁, …)` obtained by substituting the types of the environment `As` for
the parameters of `F`. -/
def TyFn.app : TyFn → (ℕ → Ty) → Ty
  | .param i, As => As i
  | .unit, _ => Ty.unit
  | .prod F G, As => (F.app As) ⊗ (G.app As)
  | .sum F G, As => (F.app As) ⊕' (G.app As)
  | .list F, As => (F.app As)⋆

/-- The functorial action of a multivariate type constructor on a family of terms. -/
def TyFn.mapN : (F : TyFn) → {As Bs : ℕ → Ty} → ((i : ℕ) → Term (As i) (Bs i)) →
    Term (F.app As) (F.app Bs)
  | .param i, _, _, f => f i
  | .unit, _, _, _ => Term.id Ty.unit
  | .prod F G, _, _, f => prodF (F.mapN f) (G.mapN f)
  | .sum F G, _, _, f => sumF (F.mapN f) (G.mapN f)
  | .list F, _, _, f => listF (F.mapN f)

/-! ### Distributivity of concatenation over a co-pairing -/

/-- Co-pairing distributes over concatenation of terms with list outputs, on the right. -/
theorem fdot_either_distR {A₁ A₂ C B : Ty} (f : Term C B⋆) (f₁ : Term A₁ B⋆)
    (f₂ : Term A₂ B⋆) :
    (f ⊙ either f₁ f₂) ≡ₜ (distR C A₁ A₂ ⨟ either (f ⊙ f₁) (f ⊙ f₂)) := by
  calc (prodF f (either f₁ f₂) ⨟ binconcat B)
      ≡ₜ ((distR C A₁ A₂ ⨟ either (prodF f f₁) (prodF f f₂)) ⨟ binconcat B) :=
        PEq.compL _ (prodF_either_distR f₁ f₂ f)
    _ ≡ₜ (distR C A₁ A₂ ⨟ (either (prodF f f₁) (prodF f f₂) ⨟ binconcat B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (distR C A₁ A₂ ⨟ either (prodF f f₁ ⨟ binconcat B) (prodF f f₂ ⨟ binconcat B)) :=
        PEq.compR _ (either_comp _ _ _)

end Term

end Lax149335Proofs

bridge_export Lax149335Proofs
