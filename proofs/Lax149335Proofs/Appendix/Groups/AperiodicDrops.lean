import Lax149335Proofs.GeneralCompleteness.LiftsAndDrops
import Lax149335Proofs.Appendix.Groups.SprefInverse
import Lax149335Proofs.Appendix.Groups.AnyTermDrop
import Lax149335Proofs.Appendix.Groups.ToTSemantics
import Mathlib.Tactic.Set
import Lax149335Proofs.Appendix.Groups.AperiodicEquations
import Lax149335Proofs.Appendix.Groups.ProductConsolidation

/-!
# Substitution of functors, and aperiodic drops

Two ingredients of the group part of the appendix that are of general use:

* substitution of list-polynomial functors (`Lax149335Proofs.Term.TyF.subst`) and its effect on the
  type `F(A)` (`Lax149335Proofs.Term.TyF.subst_app`);
* every drop is provably equal to an *aperiodic* drop
  (`Lax149335Proofs.IsDrop.aperiodic_normal`): the only way a drop can use the group prefix
  multiplication is inside a constant `1 ; v`, and replacing `v` by the value that represents
  its denotation removes it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-- Substituting a list-polynomial functor for the parameter of another one. -/
def TyF.subst : TyF → TyF → TyF
  | .param, H => H
  | .unit, _ => .unit
  | .prod F₁ F₂, H => .prod (TyF.subst F₁ H) (TyF.subst F₂ H)
  | .sum F₁ F₂, H => .sum (TyF.subst F₁ H) (TyF.subst F₂ H)
  | .list F, H => .list (TyF.subst F H)

bridge_export Lax149335Proofs

theorem TyF.subst_app : (F H : TyF) → (A : Ty) → (F.subst H).app A = F.app (H.app A)
  | .param, _, _ => rfl
  | .unit, _, _ => rfl
  | .prod F₁ F₂, H, A => by
      simp [TyF.subst, TyF.app, TyF.subst_app F₁ H A, TyF.subst_app F₂ H A]
  | .sum F₁ F₂, H, A => by
      simp [TyF.subst, TyF.app, TyF.subst_app F₁ H A, TyF.subst_app F₂ H A]
  | .list F, H, A => by
      simp [TyF.subst, TyF.app, TyF.subst_app F H A]

end Term

/-! ### Every drop is provably equal to an aperiodic drop

The only way in which a drop can use the group prefix multiplication is inside a constant
`1 ; v`; replacing `v` by the value that represents its denotation removes it. -/

/-- Every drop is provably equal to an *aperiodic* drop. -/
theorem IsDrop.aperiodic_normal {A B : Ty} {f : Term A B} (hf : IsDrop f) :
    ∃ f' : Term A B, IsDrop f' ∧ IsAperiodic f' ∧ f ≡ₜ f' := by
  induction hf with
  | @comp A B C f g _ _ ihf ihg =>
      obtain ⟨f', hf', haf', hef⟩ := ihf
      obtain ⟨g', hg', hag', heg⟩ := ihg
      exact ⟨f' ⨟ g', IsDrop.comp hf' hg', by
        simp [IsAperiodic, Term.usesPref] at haf' hag' ⊢
        exact ⟨haf', hag'⟩, (PEq.compL _ hef).trans (PEq.compR _ heg)⟩
  | @prodF A₁ A₂ B₁ B₂ f g _ _ ihf ihg =>
      obtain ⟨f', hf', haf', hef⟩ := ihf
      obtain ⟨g', hg', hag', heg⟩ := ihg
      exact ⟨Term.prodF f' g', IsDrop.prodF hf' hg', by
        simp [IsAperiodic, Term.usesPref] at haf' hag' ⊢
        exact ⟨haf', hag'⟩, PEq.congr_prodF hef heg⟩
  | @sumF A₁ A₂ B₁ B₂ f g _ _ ihf ihg =>
      obtain ⟨f', hf', haf', hef⟩ := ihf
      obtain ⟨g', hg', hag', heg⟩ := ihg
      exact ⟨Term.sumF f' g', IsDrop.sumF hf' hg', by
        simp [IsAperiodic, Term.usesPref] at haf' hag' ⊢
        exact ⟨haf', hag'⟩, PEq.congr_sumF hef heg⟩
  | @listF A B f _ ih =>
      obtain ⟨f', hf', haf', hef⟩ := ih
      exact ⟨Term.listF f', IsDrop.listF hf', by
        simpa [IsAperiodic, Term.usesPref] using haf', PEq.congr_listF hef⟩
  | bangV A v =>
      refine ⟨Term.toUnit A ⨟ encV _ (v.den ()), IsDrop.bangV A _, ?_, PEq.compR _ ?_⟩
      · have h := aperiodic_encV _ (v.den ())
        simp [IsAperiodic, Term.usesPref, Term.toUnit] at h ⊢
        exact h
      · exact (PEq.symm (PEq.id_comp v)).trans (computes v ())
  | id A => exact ⟨_, IsDrop.id A, rfl, PEq.refl _⟩
  | assocL A B C => exact ⟨_, IsDrop.assocL A B C, rfl, PEq.refl _⟩
  | assocR A B C => exact ⟨_, IsDrop.assocR A B C, rfl, PEq.refl _⟩
  | fst A B => exact ⟨_, IsDrop.fst A B, rfl, PEq.refl _⟩
  | snd A B => exact ⟨_, IsDrop.snd A B, rfl, PEq.refl _⟩
  | inl A B => exact ⟨_, IsDrop.inl A B, rfl, PEq.refl _⟩
  | inr A B => exact ⟨_, IsDrop.inr A B, rfl, PEq.refl _⟩
  | codiag A => exact ⟨_, IsDrop.codiag A, rfl, PEq.refl _⟩
  | concat A => exact ⟨_, IsDrop.concat A, rfl, PEq.refl _⟩
  | pureT A =>
      exact ⟨_, IsDrop.pureT A, by simp [IsAperiodic, Term.usesPref, Term.pureT, Term.nilT],
        PEq.refl _⟩
  | binconcat A =>
      exact ⟨_, IsDrop.binconcat A, by
        simp [IsAperiodic, Term.usesPref, Term.binconcat, Term.pureT, Term.nilT, Term.prepend],
        PEq.refl _⟩
  | unshift A B =>
      exact ⟨_, IsDrop.unshift A B, by simp [IsAperiodic, Term.usesPref, Term.unshift],
        PEq.refl _⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
