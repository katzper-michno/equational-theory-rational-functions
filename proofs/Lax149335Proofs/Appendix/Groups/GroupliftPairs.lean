import Lax149335Proofs.Appendix.Groups.PrefAsSpref

/-!
# Completeness in the presence of groups: group-lifts and their one-sided inverses

This file starts the formalisation of the appendix section *Completeness in the presence of
groups*.  Group-lifts are not surjective, so they cannot be cancelled on the left-hand side
of an equational proof; the factorisation statements are therefore stated for a **one-sided
inverse** of the group-lift instead of for the group-lift itself.  Those inverses *are*
provably surjective, by definition, so they can be cancelled, which is what makes the last
step of the completeness proof go through.

The `Σ`-encoding that the section works with is set up in
`Lax149335Proofs.Appendix.Groups.SigmaTypes` and
`Lax149335Proofs.Appendix.Groups.PrefAsSpref`.

## What is in this file

* `Lax149335Proofs.IsGLiftPair mu pi`: `mu` is a group-lift and `pi` is the drop one-sided inverse
  that comes with it.  Following the definition of the appendix, the prime group-lifts are the prime
  lifts (with their inverse, which exists by Lemma 7.2), the *group injections* — which are
  aperiodic terms with a drop one-sided inverse — and the *Simon lifts*, which are
  compositions of a drop, the group prefix multiplication and a lift, and which come with a
  drop one-sided inverse.  The class is closed under composition and the three
  functoriality combinators, and the inverse is carried along.
* `Lax149335Proofs.IsGLiftInvDrop f`: the conclusion of the grouplift-drop factorisation —
  there is a group-lift `mu : A ⊸ C` with one-sided inverse `pi : C ⇒ A` such that `pi ⨟ f`
  is provably equal to a drop.
* the closure properties of both notions that do not need the group exchange lemma.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Group-lifts, together with their one-sided inverse -/

/-- **Definition (Group-lifts).**  `IsGLiftPair mu pi` says that `mu` is a
group-lift with the distinguished drop one-sided inverse `pi`, i.e. `mu ⨟ pi ≡ id`.

Group-lifts are defined like lifts, except that two new kinds of prime lifts are allowed:

* *group injections* (`groupInj`), which are aperiodic terms with a drop one-sided inverse;
* *Simon lifts* (`simon`), which are compositions of a drop, the group prefix multiplication
  and a lift, and which are provably injective with a drop one-sided inverse.

The Simon lift constructor below asks exactly for the two properties that the Simon
lift lemma provides and that the group exchange lemma uses: the shape "a drop, then the
group prefix multiplication (in the co-product presentation `spref`), then a lift", and a
drop one-sided inverse.  The Simon lift lemma itself — which constructs such a term for
every subset `H` of the group, together with the second drop `δ` of its statement — is
`Lax149335Proofs.simon_lift_H` in `Lax149335Proofs.Appendix.Groups.SimonLiftProof`. -/
inductive IsGLiftPair : {A B : Ty} → Term A B → Term B A → Prop
  /-- A lift, with the drop inverse provided by Lemma 7.2. -/
  | ofLift {A B : Ty} {l : Term A B} {d : Term B A} :
      IsLift l → IsDrop d → (l ⨟ d) ≡ₜ Term.id A → IsGLiftPair l d
  /-- A group injection: an aperiodic term with a drop one-sided inverse. -/
  | groupInj {A B : Ty} {f : Term A B} {g : Term B A} :
      IsAperiodic f → IsDrop g → (f ⨟ g) ≡ₜ Term.id A → IsGLiftPair f g
  /-- A Simon lift: a drop, then the group prefix multiplication, then a lift; it comes with
  a drop one-sided inverse. -/
  | simon {X S A : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
      {s : Term X S} {gamma : Term S X}
      (d₀ : Term X ((Term.sigmaTy A n)⋆)) (l : Term (Term.tTy A n) S) :
      IsDrop d₀ → IsLift l → s ≡ₜ (d₀ ⨟ (Term.spref A G ⨟ l)) →
      IsDrop gamma → (s ⨟ gamma) ≡ₜ Term.id X → IsGLiftPair s gamma
  /-- Group-lifts are closed under composition; the inverses are composed in the other
  order. -/
  | comp {A B C : Ty} {f : Term A B} {f' : Term B A} {g : Term B C} {g' : Term C B} :
      IsGLiftPair f f' → IsGLiftPair g g' → IsGLiftPair (f ⨟ g) (g' ⨟ f')
  /-- Group-lifts are closed under functoriality of products. -/
  | prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {f' : Term B₁ A₁}
      {g : Term A₂ B₂} {g' : Term B₂ A₂} :
      IsGLiftPair f f' → IsGLiftPair g g' →
      IsGLiftPair (Term.prodF f g) (Term.prodF f' g')
  /-- Group-lifts are closed under functoriality of co-products. -/
  | sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {f' : Term B₁ A₁}
      {g : Term A₂ B₂} {g' : Term B₂ A₂} :
      IsGLiftPair f f' → IsGLiftPair g g' →
      IsGLiftPair (Term.sumF f g) (Term.sumF f' g')
  /-- Group-lifts are closed under functoriality of lists. -/
  | listF {A B : Ty} {f : Term A B} {f' : Term B A} :
      IsGLiftPair f f' → IsGLiftPair (Term.listF f) (Term.listF f')

namespace IsGLiftPair

/-- The one-sided inverse of a group-lift is a drop. -/
theorem isDrop : ∀ {A B : Ty} {mu : Term A B} {pi : Term B A}, IsGLiftPair mu pi → IsDrop pi
  | _, _, _, _, .ofLift _ hd _ => hd
  | _, _, _, _, .groupInj _ hg _ => hg
  | _, _, _, _, .simon _ _ _ _ _ _ hgamma _ => hgamma
  | _, _, _, _, .comp hf hg => IsDrop.comp hg.isDrop hf.isDrop
  | _, _, _, _, .prodF hf hg => IsDrop.prodF hf.isDrop hg.isDrop
  | _, _, _, _, .sumF hf hg => IsDrop.sumF hf.isDrop hg.isDrop
  | _, _, _, _, .listF hf => IsDrop.listF hf.isDrop

/-- A group-lift is provably injective: composed with its inverse it is the identity. -/
theorem retract : ∀ {A B : Ty} {mu : Term A B} {pi : Term B A}, IsGLiftPair mu pi →
    (mu ⨟ pi) ≡ₜ Term.id A
  | _, _, _, _, .ofLift _ _ h => h
  | _, _, _, _, .groupInj _ _ h => h
  | _, _, _, _, .simon _ _ _ _ _ _ _ h => h
  | _, _, _, _, @IsGLiftPair.comp A B C f f' g g' hf hg => by
      calc ((f ⨟ g) ⨟ (g' ⨟ f')) ≡ₜ (f ⨟ (g ⨟ (g' ⨟ f'))) := PEq.comp_assoc _ _ _
        _ ≡ₜ (f ⨟ ((g ⨟ g') ⨟ f')) := PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
        _ ≡ₜ (f ⨟ (Term.id B ⨟ f')) := PEq.compR _ (PEq.compL _ hg.retract)
        _ ≡ₜ (f ⨟ f') := PEq.compR _ (PEq.id_comp _)
        _ ≡ₜ Term.id A := hf.retract
  | _, _, _, _, .prodF hf hg =>
      (PEq.prod_comp _ _ _ _).trans
        ((PEq.congr_prodF hf.retract hg.retract).trans (PEq.prod_id _ _))
  | _, _, _, _, .sumF hf hg =>
      (PEq.sum_comp _ _ _ _).trans
        ((PEq.congr_sumF hf.retract hg.retract).trans (PEq.sum_id _ _))
  | _, _, _, _, .listF hf =>
      (PEq.list_comp _ _).trans ((PEq.congr_listF hf.retract).trans (PEq.list_id _))

/-- The identity, with itself as inverse. -/
theorem id (A : Ty) : IsGLiftPair (Term.id A) (Term.id A) :=
  .ofLift (IsLift.id A) (IsDrop.id A) (PEq.id_comp _)

/-- Every lift is a group-lift, with the inverse of Lemma 7.2. -/
theorem of_isLift {A B : Ty} {l : Term A B} (hl : IsLift l) :
    ∃ d : Term B A, IsGLiftPair l d ∧ (d ⨟ l) ≡ₜ Term.id B := by
  obtain ⟨d, hd, h₁, h₂⟩ := lift_iso l hl
  exact ⟨d, .ofLift hl hd h₁, h₂⟩

/-- Group-lifts, with their inverses, are closed under the functorial action of a
multivariate list-polynomial functor. -/
theorem mapN : (F : TyFn) → {As Bs : ℕ → Ty} →
    {f : (i : ℕ) → Term (As i) (Bs i)} → {f' : (i : ℕ) → Term (Bs i) (As i)} →
    (∀ i, IsGLiftPair (f i) (f' i)) → IsGLiftPair (F.mapN f) (F.mapN f')
  | .param i, _, _, _, _, h => h i
  | .unit, _, _, _, _, _ => IsGLiftPair.id _
  | .prod F G, _, _, _, _, h => .prodF (mapN F h) (mapN G h)
  | .sum F G, _, _, _, _, h => .sumF (mapN F h) (mapN G h)
  | .list F, _, _, _, _, h => .listF (mapN F h)

end IsGLiftPair

/-! ### The grouplift-drop factorisation -/

/-- **The conclusion of the grouplift-drop factorisation.**  There is a group-lift
`mu : A ⊸ C` with one-sided inverse `pi : C ⇒ A` such that `pi ⨟ f` is provably equal to a
drop.  Since `mu ⨟ pi ≡ id`, the term `pi` is provably surjective, which is what allows it
to be cancelled in the completeness proof. -/
def IsGLiftInvDrop {A B : Ty} (f : Term A B) : Prop :=
  ∃ (C : Ty) (mu : Term A C) (pi : Term C A) (d : Term C B),
    IsGLiftPair mu pi ∧ IsDrop d ∧ (pi ⨟ f) ≡ₜ d

namespace IsGLiftInvDrop

theorem congr {A B : Ty} {f g : Term A B} (h : f ≡ₜ g) (hg : IsGLiftInvDrop g) :
    IsGLiftInvDrop f := by
  obtain ⟨C, mu, pi, d, hmu, hd, he⟩ := hg
  exact ⟨C, mu, pi, d, hmu, hd, (PEq.compR _ h).trans he⟩

/-- Every term with a lift-drop factorisation — in particular every aperiodic term — has a
grouplift-drop factorisation: the inverse of the lift is a group-lift inverse. -/
theorem of_isLiftDrop {A B : Ty} {f : Term A B} (h : IsLiftDrop f) : IsGLiftInvDrop f := by
  obtain ⟨C, l, d, hl, hd, he⟩ := h
  obtain ⟨l', hl', hll'⟩ := IsGLiftPair.of_isLift hl
  refine ⟨C, l, l', d, hl', hd, ?_⟩
  calc (l' ⨟ f) ≡ₜ (l' ⨟ (l ⨟ d)) := PEq.compR _ he
    _ ≡ₜ ((l' ⨟ l) ⨟ d) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id C ⨟ d) := PEq.compL _ hll'
    _ ≡ₜ d := PEq.id_comp _

theorem of_isAperiodic {A B : Ty} (f : Term A B) (h : IsAperiodic f) : IsGLiftInvDrop f :=
  of_isLiftDrop (isLiftDrop_of_aperiodic f h)

theorem prodF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : IsGLiftInvDrop f) (hg : IsGLiftInvDrop g) : IsGLiftInvDrop (Term.prodF f g) := by
  obtain ⟨C₁, mu₁, pi₁, d₁, hmu₁, hd₁, he₁⟩ := hf
  obtain ⟨C₂, mu₂, pi₂, d₂, hmu₂, hd₂, he₂⟩ := hg
  refine ⟨C₁ ⊗ C₂, Term.prodF mu₁ mu₂, Term.prodF pi₁ pi₂, Term.prodF d₁ d₂,
    hmu₁.prodF hmu₂, IsDrop.prodF hd₁ hd₂, ?_⟩
  exact (PEq.prod_comp _ _ _ _).trans (PEq.congr_prodF he₁ he₂)

theorem sumF {A₁ A₂ B₁ B₂ : Ty} {f : Term A₁ B₁} {g : Term A₂ B₂}
    (hf : IsGLiftInvDrop f) (hg : IsGLiftInvDrop g) : IsGLiftInvDrop (Term.sumF f g) := by
  obtain ⟨C₁, mu₁, pi₁, d₁, hmu₁, hd₁, he₁⟩ := hf
  obtain ⟨C₂, mu₂, pi₂, d₂, hmu₂, hd₂, he₂⟩ := hg
  refine ⟨C₁ ⊕' C₂, Term.sumF mu₁ mu₂, Term.sumF pi₁ pi₂, Term.sumF d₁ d₂,
    hmu₁.sumF hmu₂, IsDrop.sumF hd₁ hd₂, ?_⟩
  exact (PEq.sum_comp _ _ _ _).trans (PEq.congr_sumF he₁ he₂)

theorem listF {A B : Ty} {f : Term A B} (hf : IsGLiftInvDrop f) :
    IsGLiftInvDrop (Term.listF f) := by
  obtain ⟨C, mu, pi, d, hmu, hd, he⟩ := hf
  refine ⟨C⋆, Term.listF mu, Term.listF pi, Term.listF d, hmu.listF, IsDrop.listF hd, ?_⟩
  exact (PEq.list_comp _ _).trans (PEq.congr_listF he)

end IsGLiftInvDrop

end Lax149335Proofs

bridge_export Lax149335Proofs
