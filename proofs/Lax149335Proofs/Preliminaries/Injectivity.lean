import Lax149335Proofs.EquationalTheory.DerivedRules

/-!
# Provably injective and provably surjective terms (Definition 5.4, Lemma 5.5)

This file contains Definition 5.4 and Lemma 5.5 of the paper, together with the basic
closure properties of provably injective terms that are established in the appendix
(the claim at the beginning of the appendix section "Provably injective string
representations"): the co-projections are provably injective, and provably injective terms
are closed under composition and under the functorial combinators for `+`, `×` and `*`.

A few derived equational rules that are used there are proved as well.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-- **Lemma 5.5.**  Provably injective and provably surjective terms can be cancelled out in
equivalence proofs. -/
theorem cancel {A B : Ty} (g₁ g₂ : Term A B) :
    (∀ (C : Ty) (f : Term B C), ProvablyInjective f → (g₁ ≡ₜ g₂ ↔ (g₁ ⨟ f) ≡ₜ (g₂ ⨟ f))) ∧
    (∀ (C : Ty) (f : Term C A), ProvablySurjective f → (g₁ ≡ₜ g₂ ↔ (f ⨟ g₁) ≡ₜ (f ⨟ g₂))) := by
  constructor
  · intro C f hf
    obtain ⟨f', hf'⟩ := hf
    constructor
    · intro h
      exact PEq.congr_comp h (PEq.refl f)
    · intro h
      have e₁ : g₁ ≡ₜ (g₁ ⨟ f) ⨟ f' :=
        PEq.symm (PEq.trans (PEq.comp_assoc g₁ f f')
          (PEq.trans (PEq.congr_comp (PEq.refl g₁) hf') (PEq.comp_id g₁)))
      have e₂ : (g₂ ⨟ f) ⨟ f' ≡ₜ g₂ :=
        PEq.trans (PEq.comp_assoc g₂ f f')
          (PEq.trans (PEq.congr_comp (PEq.refl g₂) hf') (PEq.comp_id g₂))
      exact PEq.trans e₁ (PEq.trans (PEq.congr_comp h (PEq.refl f')) e₂)
  · intro C f hf
    obtain ⟨f', hf'⟩ := hf
    constructor
    · intro h
      exact PEq.congr_comp (PEq.refl f) h
    · intro h
      have e₁ : g₁ ≡ₜ f' ⨟ (f ⨟ g₁) :=
        PEq.symm (PEq.trans (PEq.symm (PEq.comp_assoc f' f g₁))
          (PEq.trans (PEq.congr_comp hf' (PEq.refl g₁)) (PEq.id_comp g₁)))
      have e₂ : f' ⨟ (f ⨟ g₂) ≡ₜ g₂ :=
        PEq.trans (PEq.symm (PEq.comp_assoc f' f g₂))
          (PEq.trans (PEq.congr_comp hf' (PEq.refl g₂)) (PEq.id_comp g₂))
      exact PEq.trans e₁ (PEq.trans (PEq.congr_comp (PEq.refl f') h) e₂)

namespace Term

/-! ### A few derived equational rules -/

/-- The first projection recovers the first component of a right pairing with a value. -/
theorem pairR_fst {A B C : Ty} (f : Term A B) (v : Value C) :
    (pairR f v ⨟ fst B C) ≡ₜ f := by
  calc ((unitR A ⨟ prodF f v) ⨟ fst B C) ≡ₜ (unitR A ⨟ (prodF f v ⨟ fst B C)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR A ⨟ (fst A Ty.unit ⨟ f)) := PEq.compR _ (PEq.nat_fst f v)
    _ ≡ₜ ((unitR A ⨟ fst A Ty.unit) ⨟ f) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id A ⨟ f) := PEq.compL _ (PEq.unitR_fst A)
    _ ≡ₜ f := PEq.id_comp f

/-- The second projection recovers the second component of a left pairing with a value. -/
theorem pairL_snd {A B C : Ty} (v : Value C) (f : Term A B) :
    (pairL v f ⨟ snd C B) ≡ₜ f := by
  calc ((unitL A ⨟ prodF v f) ⨟ snd C B) ≡ₜ (unitL A ⨟ (prodF v f ⨟ snd C B)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (unitL A ⨟ (snd Ty.unit A ⨟ f)) := PEq.compR _ (PEq.nat_snd v f)
    _ ≡ₜ ((unitL A ⨟ snd Ty.unit A) ⨟ f) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id A ⨟ f) := PEq.compL _ (PEq.unitL_snd A)
    _ ≡ₜ f := PEq.id_comp f

/-- Composing a right pairing with a product of two terms. -/
theorem pairR_prodF {A B C B' C' : Ty} (f : Term A B) (v : Value C)
    (g : Term B B') (h : Term C C') :
    (pairR f v ⨟ prodF g h) ≡ₜ pairR (f ⨟ g) (v ⨟ h) := by
  calc ((unitR A ⨟ prodF f v) ⨟ prodF g h) ≡ₜ (unitR A ⨟ (prodF f v ⨟ prodF g h)) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (unitR A ⨟ prodF (f ⨟ g) (v ⨟ h)) := PEq.compR _ (PEq.prod_comp _ _ _ _)

/-- Congruence for right pairing. -/
theorem pairR_congr {A B C : Ty} {f f' : Term A B} {v v' : Value C}
    (hf : f ≡ₜ f') (hv : v ≡ₜ v') : pairR f v ≡ₜ pairR f' v' :=
  PEq.compR _ (PEq.congr_prodF hf hv)

/-- Distributivity on the right undoes the left co-projection. -/
theorem prodF_inl_distR (A B C : Ty) :
    (prodF (Term.id A) (inl B C) ⨟ distR A B C) ≡ₜ inl (A ⊗ B) (A ⊗ C) := by
  calc (prodF (Term.id A) (inl B C) ⨟ distR A B C)
      ≡ₜ ((inl (A ⊗ B) (A ⊗ C) ⨟ undistR A B C) ⨟ distR A B C) :=
        PEq.compL _ (PEq.symm (inl_either _ _))
    _ ≡ₜ (inl (A ⊗ B) (A ⊗ C) ⨟ (undistR A B C ⨟ distR A B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inl (A ⊗ B) (A ⊗ C) ⨟ Term.id ((A ⊗ B) ⊕' (A ⊗ C))) :=
        PEq.compR _ (PEq.undistR_distR A B C)
    _ ≡ₜ inl (A ⊗ B) (A ⊗ C) := PEq.comp_id _

/-- Distributivity on the right undoes the right co-projection. -/
theorem prodF_inr_distR (A B C : Ty) :
    (prodF (Term.id A) (inr B C) ⨟ distR A B C) ≡ₜ inr (A ⊗ B) (A ⊗ C) := by
  calc (prodF (Term.id A) (inr B C) ⨟ distR A B C)
      ≡ₜ ((inr (A ⊗ B) (A ⊗ C) ⨟ undistR A B C) ⨟ distR A B C) :=
        PEq.compL _ (PEq.symm (inr_either _ _))
    _ ≡ₜ (inr (A ⊗ B) (A ⊗ C) ⨟ (undistR A B C ⨟ distR A B C)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (inr (A ⊗ B) (A ⊗ C) ⨟ Term.id ((A ⊗ B) ⊕' (A ⊗ C))) :=
        PEq.compR _ (PEq.undistR_distR A B C)
    _ ≡ₜ inr (A ⊗ B) (A ⊗ C) := PEq.comp_id _

/-! ### Every type is inhabited by a value -/

-- (the value `Term.defaultValue A` of an arbitrary type `A` is defined in
-- `Lax149335Proofs.Terms.Derived`)

/-- A canonical term `A → B` between arbitrary types, obtained by composing the unique term
into the unit type with a value of the target type. -/
def anyTerm (A B : Ty) : Term A B := toUnit A ⨟ defaultValue B

theorem aperiodic_defaultValue (A : Ty) : IsAperiodic (defaultValue A) := by
  induction A with
  | unit => rfl
  | prod A B ihA ihB => simp [IsAperiodic, defaultValue, usesPref] at ihA ihB ⊢; simp [ihA, ihB]
  | sum A B ihA _ => simp [IsAperiodic, defaultValue, usesPref] at ihA ⊢; simp [ihA]
  | list A _ => rfl

end Term

/-! ### Closure properties of provably injective terms -/

namespace ProvablyInjective

/-- The identity is provably injective. -/
theorem id (A : Ty) : ProvablyInjective (Term.id A) := ⟨Term.id A, PEq.id_comp _⟩

/-- Provably injective terms are closed under composition. -/
theorem comp {A B C : Ty} {f : Term A B} {g : Term B C}
    (hf : ProvablyInjective f) (hg : ProvablyInjective g) : ProvablyInjective (f ⨟ g) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  refine ⟨g' ⨟ f', ?_⟩
  calc ((f ⨟ g) ⨟ (g' ⨟ f')) ≡ₜ (f ⨟ (g ⨟ (g' ⨟ f'))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (f ⨟ ((g ⨟ g') ⨟ f')) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (f ⨟ (Term.id B ⨟ f')) := PEq.compR _ (PEq.compL _ hg')
    _ ≡ₜ (f ⨟ f') := PEq.compR _ (PEq.id_comp _)
    _ ≡ₜ Term.id A := hf'

/-- Provably injective terms are closed under the product combinator. -/
theorem prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : ProvablyInjective f) (hg : ProvablyInjective g) :
    ProvablyInjective (Term.prodF f g) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨Term.prodF f' g',
    (PEq.prod_comp _ _ _ _).trans ((PEq.congr_prodF hf' hg').trans (PEq.prod_id _ _))⟩

/-- Provably injective terms are closed under the co-product combinator. -/
theorem sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : ProvablyInjective f) (hg : ProvablyInjective g) :
    ProvablyInjective (Term.sumF f g) := by
  obtain ⟨f', hf'⟩ := hf
  obtain ⟨g', hg'⟩ := hg
  exact ⟨Term.sumF f' g',
    (PEq.sum_comp _ _ _ _).trans ((PEq.congr_sumF hf' hg').trans (PEq.sum_id _ _))⟩

/-- Provably injective terms are closed under the list combinator. -/
theorem listF {A B : Ty} {f : Term A B} (hf : ProvablyInjective f) :
    ProvablyInjective (Term.listF f) := by
  obtain ⟨f', hf'⟩ := hf
  exact ⟨Term.listF f', (PEq.list_comp _ _).trans ((PEq.congr_listF hf').trans (PEq.list_id _))⟩

/-- The left co-projection is provably injective. -/
theorem inl (A B : Ty) : ProvablyInjective (Term.inl A B) :=
  ⟨Term.either (Term.id A) (Term.anyTerm B A), Term.inl_either _ _⟩

/-- The right co-projection is provably injective. -/
theorem inr (A B : Ty) : ProvablyInjective (Term.inr A B) :=
  ⟨Term.either (Term.anyTerm A B) (Term.id B), Term.inr_either _ _⟩

/-- A term that becomes provably injective after composing with something is itself provably
injective. -/
theorem of_comp {A B C : Ty} {h : Term A B} (p : Term B C) {f : Term A C}
    (hpf : (h ⨟ p) ≡ₜ f) (hf : ProvablyInjective f) : ProvablyInjective h := by
  obtain ⟨f', hf'⟩ := hf
  refine ⟨p ⨟ f', ?_⟩
  calc (h ⨟ (p ⨟ f')) ≡ₜ ((h ⨟ p) ⨟ f') := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (f ⨟ f') := PEq.compL _ hpf
    _ ≡ₜ Term.id A := hf'

/-- Provable injectivity only depends on the provable equivalence class of a term. -/
theorem of_peq {A B : Ty} {f g : Term A B} (h : f ≡ₜ g) (hg : ProvablyInjective g) :
    ProvablyInjective f := by
  obtain ⟨g', hg'⟩ := hg
  exact ⟨g', (PEq.compL _ h).trans hg'⟩

/-- Pairing with a value on the right preserves provable injectivity. -/
theorem pairR {A B C : Ty} (f : Term A B) (v : Value C) (hf : ProvablyInjective f) :
    ProvablyInjective (Term.pairR f v) :=
  of_comp (Term.fst B C) (Term.pairR_fst f v) hf

/-- Pairing with a value on the left preserves provable injectivity. -/
theorem pairL {A B C : Ty} (v : Value C) (f : Term A B) (hf : ProvablyInjective f) :
    ProvablyInjective (Term.pairL v f) :=
  of_comp (Term.snd C B) (Term.pairL_snd v f) hf

/-- `(1,id)` is provably injective. -/
theorem unitL (A : Ty) : ProvablyInjective (Term.unitL A) :=
  ⟨Term.snd Ty.unit A, PEq.unitL_snd A⟩

/-- The inverse of `split` is provably injective. -/
theorem unsplit (A B : Ty) : ProvablyInjective (Term.unsplit A B) :=
  ⟨Term.split A B, PEq.unsplit_split A B⟩

end ProvablyInjective

end Lax149335Proofs

bridge_export Lax149335Proofs
