import Lax149335Proofs.Appendix.Groups.SimonLift
import Lax149335Proofs.GeneralCompleteness.Statements
import Lax149335Proofs.Appendix.Drops.FunctorTools
import Lax149335Proofs.Appendix.Drops.DropNormalisation
import Lax149335Proofs.Appendix.Drops.ListNormalisation
import Lax149335Proofs.Appendix.Groups.Aperiodicity
import Lax149335Proofs.Appendix.Groups.SigmaTypes
import Lax149335Proofs.Appendix.Groups.AnyTermDrop
import Lax149335Proofs.Appendix.Groups.AperiodicDrops
import Mathlib.Tactic.Choose

/-!
# The group exchange lemma, in its inverted form

This file formalises the *Group Exchange Lemma* of the appendix section
*Completeness in the presence of groups*: the predicate `Lax149335Proofs.IsGExch` that expresses
the inverted exchange square, its closure properties, and the functorial cases of the
induction.  The induction itself, which needs the prefix exchange lemma, is in
`Lax149335Proofs.Appendix.Groups.ExchangeProof`.

The statement is the inverted one: for a drop `f : A ⇒ B` and a group-lift `μ : B ⊸ D` with
one-sided inverse `π : D ⇒ B`, there are a group-lift `ν : A ⊸ C` with one-sided inverse
`ρ : C ⇒ A` and a drop `k : C ⇒ D` such that

```
ρ ; f  ≡  k ; π
```

commutes provably.  This is the predicate `Lax149335Proofs.IsGExch f π`.  Since the group-lift is
inverted, the square is *not* the same as the usual exchange square; it is strictly stronger,
and it is what makes the completeness proof go through.

The functorial cases proved here — `Lax149335Proofs.gexch_normalProd`,
`Lax149335Proofs.gexch_normalSumTree` and `Lax149335Proofs.gexch_normalListLeaf` — handle drops with a
product, a co-product and a list codomain, exactly as in the aperiodic case, by way of the
normalisation lemmas for drops.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### The conclusion of the inverted exchange square -/

/-- **The conclusion of the (inverted) group exchange lemma.**  `IsGExch f pi` says that the
drop `f : A ⇒ B`, precomposed with the inverse `ρ` of a suitable group-lift, factors through
the given group-lift inverse `pi : D ⇒ B` by a drop. -/
def IsGExch {A B D : Ty} (f : Term A B) (pi : Term D B) : Prop :=
  ∃ (C : Ty) (nu : Term A C) (rho : Term C A) (k : Term C D),
    IsGLiftPair nu rho ∧ IsDrop k ∧ (rho ⨟ f) ≡ₜ (k ⨟ pi)

namespace IsGExch

theorem congr {A B D : Ty} {f f' : Term A B} {pi : Term D B} (h : f ≡ₜ f')
    (hf : IsGExch f' pi) : IsGExch f pi := by
  obtain ⟨C, nu, rho, k, hnu, hk, he⟩ := hf
  exact ⟨C, nu, rho, k, hnu, hk, (PEq.compR _ h).trans he⟩

/-- A lift in front of the drop is absorbed into the group-lift. -/
theorem of_lift_comp {A E B D : Ty} {alpha : Term A E} {g : Term E B} {pi : Term D B}
    (hl : IsLift alpha) (hg : IsGExch g pi) : IsGExch (alpha ⨟ g) pi := by
  obtain ⟨C, nu, rho, k, hnu, hk, he⟩ := hg
  obtain ⟨alpha', halpha', h₁, h₂⟩ := lift_iso alpha hl
  refine ⟨C, alpha ⨟ nu, rho ⨟ alpha', k, .comp (.ofLift hl halpha' h₁) hnu, hk, ?_⟩
  calc ((rho ⨟ alpha') ⨟ (alpha ⨟ g)) ≡ₜ (rho ⨟ g) := comp_cancel_mid h₂
    _ ≡ₜ (k ⨟ pi) := he

/-- Post-composition with a map that commutes with the group-lift inverse up to a drop. -/
theorem post {A B B' D D' : Ty} {f : Term A B} {pi : Term D B} {u : Term B B'}
    {v : Term D D'} {pi' : Term D' B'} (hf : IsGExch f pi) (hv : IsDrop v)
    (hsq : (pi ⨟ u) ≡ₜ (v ⨟ pi')) : IsGExch (f ⨟ u) pi' := by
  obtain ⟨C, nu, rho, k, hnu, hk, he⟩ := hf
  refine ⟨C, nu, rho, k ⨟ v, hnu, IsDrop.comp hk hv, ?_⟩
  calc (rho ⨟ (f ⨟ u)) ≡ₜ ((rho ⨟ f) ⨟ u) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((k ⨟ pi) ⨟ u) := PEq.compL _ he
    _ ≡ₜ (k ⨟ (pi ⨟ u)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (k ⨟ (v ⨟ pi')) := PEq.compR _ hsq
    _ ≡ₜ ((k ⨟ v) ⨟ pi') := PEq.symm (PEq.comp_assoc _ _ _)

theorem prodF {A₁ A₂ B₁ B₂ D₁ D₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    {pi₁ : Term D₁ B₁} {pi₂ : Term D₂ B₂} (hf : IsGExch f pi₁) (hg : IsGExch g pi₂) :
    IsGExch (Term.prodF f g) (Term.prodF pi₁ pi₂) := by
  obtain ⟨C₁, nu₁, rho₁, k₁, hnu₁, hk₁, he₁⟩ := hf
  obtain ⟨C₂, nu₂, rho₂, k₂, hnu₂, hk₂, he₂⟩ := hg
  refine ⟨C₁ ⊗ C₂, Term.prodF nu₁ nu₂, Term.prodF rho₁ rho₂, Term.prodF k₁ k₂,
    hnu₁.prodF hnu₂, IsDrop.prodF hk₁ hk₂, ?_⟩
  calc (Term.prodF rho₁ rho₂ ⨟ Term.prodF f g) ≡ₜ Term.prodF (rho₁ ⨟ f) (rho₂ ⨟ g) :=
        PEq.prod_comp _ _ _ _
    _ ≡ₜ Term.prodF (k₁ ⨟ pi₁) (k₂ ⨟ pi₂) := PEq.congr_prodF he₁ he₂
    _ ≡ₜ (Term.prodF k₁ k₂ ⨟ Term.prodF pi₁ pi₂) := PEq.symm (PEq.prod_comp _ _ _ _)

theorem sumF {A₁ A₂ B₁ B₂ D₁ D₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    {pi₁ : Term D₁ B₁} {pi₂ : Term D₂ B₂} (hf : IsGExch f pi₁) (hg : IsGExch g pi₂) :
    IsGExch (Term.sumF f g) (Term.sumF pi₁ pi₂) := by
  obtain ⟨C₁, nu₁, rho₁, k₁, hnu₁, hk₁, he₁⟩ := hf
  obtain ⟨C₂, nu₂, rho₂, k₂, hnu₂, hk₂, he₂⟩ := hg
  refine ⟨C₁ ⊕' C₂, Term.sumF nu₁ nu₂, Term.sumF rho₁ rho₂, Term.sumF k₁ k₂,
    hnu₁.sumF hnu₂, IsDrop.sumF hk₁ hk₂, ?_⟩
  calc (Term.sumF rho₁ rho₂ ⨟ Term.sumF f g) ≡ₜ Term.sumF (rho₁ ⨟ f) (rho₂ ⨟ g) :=
        PEq.sum_comp _ _ _ _
    _ ≡ₜ Term.sumF (k₁ ⨟ pi₁) (k₂ ⨟ pi₂) := PEq.congr_sumF he₁ he₂
    _ ≡ₜ (Term.sumF k₁ k₂ ⨟ Term.sumF pi₁ pi₂) := PEq.symm (PEq.sum_comp _ _ _ _)

theorem listF {A B D : Ty} {f : Term A B} {pi : Term D B} (hf : IsGExch f pi) :
    IsGExch (Term.listF f) (Term.listF pi) := by
  obtain ⟨C, nu, rho, k, hnu, hk, he⟩ := hf
  refine ⟨C⋆, Term.listF nu, Term.listF rho, Term.listF k, hnu.listF, IsDrop.listF hk, ?_⟩
  calc (Term.listF rho ⨟ Term.listF f) ≡ₜ Term.listF (rho ⨟ f) := PEq.list_comp _ _
    _ ≡ₜ Term.listF (k ⨟ pi) := PEq.congr_listF he
    _ ≡ₜ (Term.listF k ⨟ Term.listF pi) := PEq.symm (PEq.list_comp _ _)

theorem either {A₁ A₂ B D : Ty} {f : Term A₁ B} {g : Term A₂ B} {pi : Term D B}
    (hf : IsGExch f pi) (hg : IsGExch g pi) : IsGExch (Term.either f g) pi := by
  obtain ⟨C₁, nu₁, rho₁, k₁, hnu₁, hk₁, he₁⟩ := hf
  obtain ⟨C₂, nu₂, rho₂, k₂, hnu₂, hk₂, he₂⟩ := hg
  refine ⟨C₁ ⊕' C₂, Term.sumF nu₁ nu₂, Term.sumF rho₁ rho₂, Term.either k₁ k₂,
    hnu₁.sumF hnu₂, IsDrop.comp (IsDrop.sumF hk₁ hk₂) (IsDrop.codiag D), ?_⟩
  calc (Term.sumF rho₁ rho₂ ⨟ Term.either f g) ≡ₜ Term.either (rho₁ ⨟ f) (rho₂ ⨟ g) :=
        Term.sumF_either _ _ _ _
    _ ≡ₜ Term.either (k₁ ⨟ pi) (k₂ ⨟ pi) := Term.either_congr he₁ he₂
    _ ≡ₜ (Term.either k₁ k₂ ⨟ pi) := PEq.symm (Term.either_comp _ _ _)

end IsGExch

/-! ### The functorial cases of the induction -/

/-- The case of a product: a normal drop with a product codomain. -/
theorem gexch_normalProd {B₁ B₂ D₁ D₂ : Ty} {pi₁ : Term D₁ B₁} {pi₂ : Term D₂ B₂}
    (ihf : ∀ {A : Ty} {d : Term A B₁}, IsDrop d → IsGExch d pi₁)
    (ihg : ∀ {A : Ty} {d : Term A B₂}, IsDrop d → IsGExch d pi₂) :
    ∀ {A : Ty} {g₀ : Term A (B₁ ⊗ B₂)}, IsNormalProd g₀ →
      IsGExch g₀ (Term.prodF pi₁ pi₂) := by
  intro A g₀ hg₀
  induction hg₀ with
  | @prodF X Y _ _ x y hx hy => exact (ihf hx).prodF (ihg hy)
  | either _ _ ih₁ ih₂ => exact (ih₁ ihf ihg).either (ih₂ ihf ihg)

/-- The case of a co-product: a normal drop with a co-product codomain. -/
theorem gexch_normalSumTree {r : ℕ} {B₁ B₂ D₁ D₂ : Ty} {pi₁ : Term D₁ B₁} {pi₂ : Term D₂ B₂}
    (ihf : ∀ {A : Ty} {d : Term A B₁}, IsDrop d → IsGExch d pi₁)
    (ihg : ∀ {A : Ty} {d : Term A B₂}, IsDrop d → IsGExch d pi₂) :
    ∀ {A : Ty} {g₀ : Term A (B₁ ⊕' B₂)}, IsNormalSumTree r g₀ →
      IsGExch g₀ (Term.sumF pi₁ pi₂) := by
  intro A g₀ hg₀
  induction hg₀ with
  | @inl A₀ _ _ g₁ hg₁ _ =>
      exact (ihf hg₁).post (IsDrop.inl D₁ D₂) (PEq.symm (PEq.nat_inl pi₁ pi₂))
  | @inr A₀ _ _ g₂ hg₂ _ =>
      exact (ihg hg₂).post (IsDrop.inr D₁ D₂) (PEq.symm (PEq.nat_inr pi₁ pi₂))
  | @sumF A₁ A₂ _ _ g₁ g₂ hg₁ hg₂ _ _ => exact (ihf hg₁).sumF (ihg hg₂)
  | either _ _ ih₁ ih₂ => exact (ih₁ ihf ihg).either (ih₂ ihf ihg)

/-- The case of a list: a leaf of a normal drop with a list codomain.  The constant leaf is
the reason why the group-lift `mu` itself — and not only its inverse — is needed: the
constant value is transported along `mu`. -/
theorem gexch_normalListLeaf {B D : Ty} {mu : Term B D} {pi : Term D B}
    (hret : (mu ⨟ pi) ≡ₜ Term.id B)
    (ihf : ∀ {A : Ty} {d : Term A B}, IsDrop d → IsGExch d pi)
    {A : Ty} {u : Term A B⋆} (hu : IsNormalListLeaf B u) :
    IsGExch u (Term.listF pi) := by
  induction hu with
  | @const A₀ v =>
      refine ⟨A₀, Term.id A₀, Term.id A₀, Term.toUnit A₀ ⨟ (v ⨟ Term.listF mu),
        IsGLiftPair.id A₀, IsDrop.bangV A₀ (v ⨟ Term.listF mu), ?_⟩
      calc (Term.id A₀ ⨟ (Term.toUnit A₀ ⨟ v)) ≡ₜ (Term.toUnit A₀ ⨟ v) := PEq.id_comp _
        _ ≡ₜ (Term.toUnit A₀ ⨟ (v ⨟ Term.id B⋆)) := PEq.compR _ (PEq.symm (PEq.comp_id _))
        _ ≡ₜ (Term.toUnit A₀ ⨟ (v ⨟ Term.listF (Term.id B))) :=
            PEq.compR _ (PEq.compR _ (PEq.symm (PEq.list_id _)))
        _ ≡ₜ (Term.toUnit A₀ ⨟ (v ⨟ Term.listF (mu ⨟ pi))) :=
            PEq.compR _ (PEq.compR _ (PEq.congr_listF (PEq.symm hret)))
        _ ≡ₜ (Term.toUnit A₀ ⨟ (v ⨟ (Term.listF mu ⨟ Term.listF pi))) :=
            PEq.compR _ (PEq.compR _ (PEq.symm (PEq.list_comp _ _)))
        _ ≡ₜ (Term.toUnit A₀ ⨟ ((v ⨟ Term.listF mu) ⨟ Term.listF pi)) :=
            PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ ((Term.toUnit A₀ ⨟ (v ⨟ Term.listF mu)) ⨟ Term.listF pi) :=
            PEq.symm (PEq.comp_assoc _ _ _)
  | @sing A₀ g hg => exact (ihf hg).post (IsDrop.pureT D) (Term.pureT_natural pi)
  | @map A₀ g hg => exact (ihf hg).listF

end Lax149335Proofs

bridge_export Lax149335Proofs
