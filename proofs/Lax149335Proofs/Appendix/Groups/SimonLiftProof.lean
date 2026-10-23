import Lax149335Proofs.Appendix.Groups.SimonLift
import Lax149335Proofs.Appendix.Groups.SprefInverse
import Lax149335Proofs.Appendix.Groups.AnyTermDrop
import Lax149335Proofs.Appendix.Groups.ToTSemantics
import Mathlib.Tactic.Set
import Lax149335Proofs.Appendix.Groups.AperiodicEquations

/-!
# The Simon lift lemma of the appendix section: the proof

This file states and proves the Simon lift lemma, `Lax149335Proofs.simon_lift_H`, with the
terms of `Lax149335Proofs.Appendix.Groups.SimonLift`.

The appendix proof applies the lift-drop factorisation of aperiodic terms (Lemma 7.4) to
`check_H`, and then uses the loop of partial prefix multiplication
(`Lax149335Proofs.partial_prefix_multiplication`).  One thing has to be said about it.

* The factorisation is applied to *two* terms — `check_H` itself and `check_H` followed by
  the unprefixing of both variants — and the appendix uses **one** lift `λ` for both.  That
  is legitimate: `Lax149335Proofs.common_liftDrop` proves that any two aperiodic terms with the
  same domain admit a lift-drop factorisation with a common lift, because lifts are
  isomorphisms (Lemma 7.2), so two factorisations can be compared and their lifts refined.
  The two terms are packaged here as `Lax149335Proofs.Term.simonDeltaTerm` (which produces the
  input again when the check succeeds, and the empty word otherwise) and
  `Lax149335Proofs.Term.simonGammaTerm` (which unprefixes and projects back to `Σ_H A` when the
  check succeeds, and returns the empty list otherwise); the drops that the factorisation
  produces for them are exactly the `δ` and the `γ` of the lemma.

The lemma is proved unconditionally.  It is the form that the definition of a group-lift
consumes (`Lax149335Proofs.IsGLiftPair.simon`), and `Lax149335Proofs.isGLiftPair_simon_H` records that.

The factorisation itself is also packaged, as `Lax149335Proofs.SimonHData`, because the
component-wise exchange lemma of the appendix
(`Lax149335Proofs.simon_exchange_component_wise`, in
`Lax149335Proofs.Appendix.Groups.ComponentWiseExchange`) has to relate the `γ` of two types,
and therefore needs the two factorisations, not only their conclusions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### A common lift for two lift-drop factorisations -/

/-- **A common lift-drop factorisation.**  Two aperiodic terms with the same domain admit
lift-drop factorisations with the *same* lift.

The proof compares the two factorisations `u₁ ≡ l₁ ; f₁` and `u₂ ≡ l₂ ; f₂` given by Lemma
7.4: the term `l₁⁻¹ ; l₂` is again aperiodic, so it factors as `l ; d`, and `l₁ ; l` is a
lift through which both terms factor by a drop. -/
theorem common_liftDrop {X Y₁ Y₂ : Ty} (u₁ : Term X Y₁) (u₂ : Term X Y₂)
    (h₁ : IsLiftDrop u₁) (h₂ : IsLiftDrop u₂) :
    ∃ (Z : Ty) (lam : Term X Z) (d₁ : Term Z Y₁) (d₂ : Term Z Y₂),
      IsLift lam ∧ IsDrop d₁ ∧ IsDrop d₂ ∧ u₁ ≡ₜ (lam ⨟ d₁) ∧ u₂ ≡ₜ (lam ⨟ d₂) := by
  obtain ⟨S₁, l₁, f₁, hl₁, hf₁, he₁⟩ := h₁
  obtain ⟨S₂, l₂, f₂, hl₂, hf₂, he₂⟩ := h₂
  obtain ⟨i₁, hi₁, hl₁i₁, hi₁l₁⟩ := lift_iso l₁ hl₁
  obtain ⟨Z, l, d, hl, hd, hek⟩ :=
    (IsLiftDrop.of_isDrop hi₁).comp (IsLiftDrop.of_isLift hl₂)
  obtain ⟨l', hl', hll', hl'l⟩ := lift_iso l hl
  refine ⟨Z, l₁ ⨟ l, l' ⨟ f₁, d ⨟ f₂, IsLift.comp hl₁ hl, IsDrop.comp hl' hf₁,
    IsDrop.comp hd hf₂, ?_, ?_⟩
  · exact he₁.trans (PEq.symm (comp_cancel_mid hll'))
  · calc u₂ ≡ₜ (l₂ ⨟ f₂) := he₂
      _ ≡ₜ ((Term.id X ⨟ l₂) ⨟ f₂) := PEq.compL _ (PEq.symm (PEq.id_comp _))
      _ ≡ₜ (((l₁ ⨟ i₁) ⨟ l₂) ⨟ f₂) := PEq.compL _ (PEq.compL _ (PEq.symm hl₁i₁))
      _ ≡ₜ ((l₁ ⨟ (i₁ ⨟ l₂)) ⨟ f₂) := PEq.compL _ (PEq.comp_assoc _ _ _)
      _ ≡ₜ ((l₁ ⨟ (l ⨟ d)) ⨟ f₂) := PEq.compL _ (PEq.compR _ hek)
      _ ≡ₜ (((l₁ ⨟ l) ⨟ d) ⨟ f₂) := PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
      _ ≡ₜ ((l₁ ⨟ l) ⨟ (d ⨟ f₂)) := PEq.comp_assoc _ _ _

/-! ### The two terms that the factorisation is applied to -/

namespace Term

/-- The empty word, as a value of the type `T A`. -/
def emptyTValue (A : Ty) (n : ℕ) : Value (tTy A n) :=
  inl Ty.unit (sigmaTy (((sigmaTy A n)⋆) ⊗ A) n)

@[simp] theorem usesPref_emptyTValue (A : Ty) (n : ℕ) :
    usesPref (emptyTValue A n) = false := rfl

@[simp] theorem usesPref_rhoInv (A : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) :
    usesPref (rhoInv A hm) = false :=
  usesPref_sigmaCase _ (fun _ => usesPref_injSigma A _)

/-- The term of which `δ` is the drop part: if the input passes the test `check_H` it is
returned unchanged, and otherwise the empty word is returned. -/
def simonDeltaTerm (A : Ty) {n : ℕ}
    (t : Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆))) :
    Term (tTy A n) (tTy A n) :=
  fromT A n ⨟ (t ⨟ either (toT A n) (toUnit ((sigmaTy A n)⋆) ⨟ emptyTValue A n))

/-- The term of which `γ` is the drop part: if the input passes the test `check_H` it is
unprefixed and projected back to `Σ_H A`, and otherwise the empty list is returned. -/
noncomputable def simonGammaTerm (A : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (t : Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆))) :
    Term (tTy A n) ((sigmaTy A m)⋆) :=
  fromT A n ⨟ (t ⨟ either (unsprefS A G ⨟ listF (rhoInv A hm))
    (toUnit ((sigmaTy A n)⋆) ⨟ nilT (sigmaTy A m)))

theorem isAperiodic_simonDeltaTerm (A : Ty) {n : ℕ}
    {t : Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆))} (ht : IsAperiodic t) :
    IsAperiodic (simonDeltaTerm A t) := by
  simp [IsAperiodic, simonDeltaTerm, usesPref, show usesPref t = false from ht]

theorem isAperiodic_simonGammaTerm (A : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    {t : Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆))} (ht : IsAperiodic t) :
    IsAperiodic (simonGammaTerm A G hm t) := by
  simp [IsAperiodic, simonGammaTerm, usesPref, show usesPref t = false from ht]

/-! ### Three denotational facts -/

/-- On a letter whose annotation lies in `H`, the drop inverse of `ρ` is undone by `ρ`. -/
theorem rhoInj_rhoInv_den {A : Ty} {m n : ℕ} {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧}
    (x : ⟦sigmaTy A n⟧) (hx : ∃ i, hm i = annOfSigma A x) :
    (rhoInj A hm).den ((rhoInv A hm).den x) = x := by
  classical
  obtain ⟨a, g, rfl⟩ := sigma_cases A x
  have hg : ∃ i, hm i = g := by simpa using hx
  have hden : (rhoInv A hm).den ((injSigma A g).den a)
      = (injSigma A (if h : ∃ i, hm i = g then h.choose else firstAlph m)).den a :=
    den_sigmaCase _ g a
  rw [hden, dif_pos hg]
  have : (rhoInj A hm).den ((injSigma A hg.choose).den a)
      = (injSigma A (hm hg.choose)).den a := den_sigmaCase _ _ a
  rw [this, hg.choose_spec]

@[simp] theorem den_fromT_emptyTValue (A : Ty) (n : ℕ) :
    (fromT A n).den ((emptyTValue A n).den ()) = [] := rfl

@[simp] theorem den_unsprefS_nil (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (unsprefS A G).den [] = [] := rfl

end Term

/-! ### The two equations of the Simon lift, before the factorisation -/

/-- **The loop of the Simon lift.**  The partial prefix multiplication, followed by the term
of which `γ` is the drop part, is provably the identity.  This is
`Lax149335Proofs.partial_prefix_multiplication`, rearranged. -/
theorem simonGammaTerm_loop {A : Ty} {m n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} (hinj : Function.Injective hm)
    {t p : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))}
    (ht : IsCheckH G (fun g => ∃ i, hm i = g) t)
    (hp : IsPrecheckH (fun g => ∃ i, hm i = g) p) :
    ((Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G) ⨟ Term.simonGammaTerm A G hm t) ≡ₜ
      Term.id ((Term.sigmaTy A m)⋆) := by
  classical
  have hE : Term.either (Term.unsprefS A G ⨟ Term.listF (Term.rhoInv A hm))
      (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A m)) ≡ₜ
      (Term.either (Term.unsprefS A G)
        (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n)) ⨟
        Term.listF (Term.rhoInv A hm)) := by
    refine PEq.symm ((Term.either_comp _ _ _).trans (Term.either_congr (PEq.refl _) ?_))
    calc ((Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n)) ⨟
          Term.listF (Term.rhoInv A hm))
        ≡ₜ (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ (Term.nilT (Term.sigmaTy A n) ⨟
            Term.listF (Term.rhoInv A hm))) := PEq.comp_assoc _ _ _
      _ ≡ₜ (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A m)) :=
          PEq.compR _ (Term.nilT_natural _)
  calc ((Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G) ⨟ Term.simonGammaTerm A G hm t)
      ≡ₜ (((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ Term.toT A n) ⨟
          (Term.fromT A n ⨟ (t ⨟ _))) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ (t ⨟ _)) :=
        comp_cancel_mid (Term.toT_fromT A n)
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟
        (t ⨟ (Term.either (Term.unsprefS A G)
          (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n)) ⨟
          Term.listF (Term.rhoInv A hm)))) := PEq.compR _ (PEq.compR _ hE)
    _ ≡ₜ (((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟
        (t ⨟ Term.either (Term.unsprefS A G)
          (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n)))) ⨟
        Term.listF (Term.rhoInv A hm)) := by
        refine PEq.trans (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))) ?_
        exact PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ t) ⨟
        Term.either (Term.unsprefS A G)
          (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n))) ⨟
        Term.listF (Term.rhoInv A hm)) :=
        PEq.compL _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ Term.id ((Term.sigmaTy A m)⋆) := partial_prefix_multiplication hinj ht hp

/-- **The square of the Simon lift.**  The term of which `γ` is the drop part, followed by
the partial prefix multiplication, is provably the term of which `δ` is the drop part.  Both
sides become aperiodic once the prefix multiplication is inverted, so the equation is checked
denotationally (Corollary 7.6). -/
theorem simonGammaTerm_square {A : Ty} {m n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧}
    {t : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))}
    (ht : IsCheckH G (fun g => ∃ i, hm i = g) t) :
    (Term.simonGammaTerm A G hm t ⨟
        (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)) ≡ₜ Term.simonDeltaTerm A t := by
  classical
  have htA : Term.usesPref t = false := ht.1
  have hunspref : ∀ y : ⟦Term.tTy A n⟧,
      (Term.unspref A G).den y = (Term.unsprefS A G).den ((Term.fromT A n).den y) := by
    intro y
    exact congrFun (PEq.sound (Term.unspref_eq_unsprefS A G)) y
  have hfromT_toT : ∀ w : List ⟦Term.sigmaTy A n⟧,
      (Term.fromT A n).den ((Term.toT A n).den w) = w := by
    intro w
    exact congrFun (PEq.sound (Term.toT_fromT A n)) w
  refine PEq.trans (PEq.symm (PEq.comp_assoc _ _ _)) ?_
  refine peq_comp_spref _ _ ?_ ?_ ?_
  · simp [IsAperiodic, Term.simonGammaTerm, Term.usesPref, htA]
  · simp [IsAperiodic, Term.simonDeltaTerm, Term.usesPref, htA]
  · intro x
    set w : List ⟦Term.sigmaTy A n⟧ := (Term.fromT A n).den x with hw
    have hgamma : (Term.simonGammaTerm A G hm t).den x =
        (Term.either (Term.unsprefS A G ⨟ Term.listF (Term.rhoInv A hm))
          (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A m))).den (t.den w) :=
      rfl
    have hdelta : (Term.simonDeltaTerm A t).den x =
        (Term.either (Term.toT A n)
          (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.emptyTValue A n)).den (t.den w) := rfl
    have hden : (Term.listF (Term.rhoInj A hm)).den ((Term.simonGammaTerm A G hm t).den x) =
        (Term.unspref A G).den ((Term.simonDeltaTerm A t).den x) := by
      rw [hgamma, hdelta, hunspref, ht.2 w]
      by_cases hgood : ∀ y ∈ (show List ⟦Term.sigmaTy A n⟧ from (Term.unsprefS A G).den w),
          ∃ i, hm i = Term.annOfSigma A y
      · rw [if_pos hgood]
        have hleft : (Term.either (Term.unsprefS A G ⨟ Term.listF (Term.rhoInv A hm))
            (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A m))).den (Sum.inl w)
            = ((Term.unsprefS A G).den w).map (Term.rhoInv A hm).den := rfl
        have hright : (Term.either (Term.toT A n)
            (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.emptyTValue A n)).den (Sum.inl w)
            = (Term.toT A n).den w := rfl
        rw [hleft, hright, hfromT_toT w, Term.den_listF, List.map_map]
        refine (List.map_congr_left ?_).trans (List.map_id _)
        intro y hy
        exact Term.rhoInj_rhoInv_den y (hgood y hy)
      · rw [if_neg hgood]
        rfl
    exact hden

/-! ### The lift-drop factorisation the proof goes through -/

/-- **The lift-drop factorisation of `check_H`.**  This is the data that the appendix proof
of the Simon lift lemma produces at a type `A`: a term `check_H`, a lift `λ` and the drop
parts `γ` and `δ` of the factorisations, along `λ`, of the two terms
`Lax149335Proofs.Term.simonGammaTerm` and `Lax149335Proofs.Term.simonDeltaTerm`.

It exists unconditionally (`Lax149335Proofs.exists_simonHData`), and it is what
`Lax149335Proofs.simon_lift_H` is read off; the component-wise exchange lemma needs it in this
unpacked form, because it relates the `γ` of two different types. -/
structure SimonHData {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (A : Ty) where
  /-- The intermediate type of the factorisation. -/
  S : Ty
  /-- The term `check_H`. -/
  check : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))
  /-- It is a `check_H`. -/
  check_spec : IsCheckH G (fun g => ∃ i, hm i = g) check
  /-- The lift of the factorisation. -/
  lam : Term (Term.tTy A n) S
  /-- It is a lift. -/
  lam_isLift : IsLift lam
  /-- The drop part of the factorisation of `simonGammaTerm`. -/
  gamma : Term S ((Term.sigmaTy A m)⋆)
  /-- It is a drop. -/
  gamma_isDrop : IsDrop gamma
  /-- It is the drop part of the factorisation. -/
  gamma_factor : (lam ⨟ gamma) ≡ₜ Term.simonGammaTerm A G hm check
  /-- The drop part of the factorisation of `simonDeltaTerm`. -/
  delta : Term S (Term.tTy A n)
  /-- It is a drop. -/
  delta_isDrop : IsDrop delta
  /-- It is the drop part of the factorisation. -/
  delta_factor : (lam ⨟ delta) ≡ₜ Term.simonDeltaTerm A check

namespace SimonHData

variable {m n : ℕ} {G : Group ⟦Ty.finAlph n⟧} {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} {A : Ty}

/-- The Simon lift built from the data: the injection `ρ*`, the group prefix multiplication
and the lift of the factorisation. -/
def simonT (D : SimonHData G hm A) : Term ((Term.sigmaTy A m)⋆) D.S :=
  Term.listF (Term.rhoInj A hm) ⨟ (Term.spref A G ⨟ D.lam)

/-- **The loop of the Simon lift.**  The Simon lift followed by `γ` is provably the
identity; this is `Lax149335Proofs.simonGammaTerm_loop`, transported along the factorisation. -/
theorem loop (hinj : Function.Injective hm) (D : SimonHData G hm A) :
    (D.simonT ⨟ D.gamma) ≡ₜ Term.id ((Term.sigmaTy A m)⋆) := by
  classical
  obtain ⟨p, hp⟩ := exists_precheckH A (fun g => ∃ i, hm i = g)
  calc ((Term.listF (Term.rhoInj A hm) ⨟ (Term.spref A G ⨟ D.lam)) ⨟ D.gamma)
      ≡ₜ (Term.listF (Term.rhoInj A hm) ⨟ (Term.spref A G ⨟ (D.lam ⨟ D.gamma))) :=
        (PEq.comp_assoc _ _ _).trans (PEq.compR _ (PEq.comp_assoc _ _ _))
    _ ≡ₜ (Term.listF (Term.rhoInj A hm) ⨟
          (Term.spref A G ⨟ Term.simonGammaTerm A G hm D.check)) :=
        PEq.compR _ (PEq.compR _ D.gamma_factor)
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G) ⨟
          Term.simonGammaTerm A G hm D.check) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ Term.id ((Term.sigmaTy A m)⋆) := simonGammaTerm_loop hinj D.check_spec hp

/-- **The square of the Simon lift.**  The drop `γ`, followed by the injection `ρ*` and the
group prefix multiplication, is provably the drop `δ`; this is
`Lax149335Proofs.simonGammaTerm_square`, transported along the factorisation. -/
theorem square (D : SimonHData G hm A) :
    (D.gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)) ≡ₜ D.delta := by
  obtain ⟨lam', hlam', -, hl'l⟩ := lift_iso D.lam D.lam_isLift
  have key : (D.lam ⨟ (D.gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G))) ≡ₜ
      (D.lam ⨟ D.delta) := by
    calc (D.lam ⨟ (D.gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)))
        ≡ₜ ((D.lam ⨟ D.gamma) ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)) :=
          PEq.symm (PEq.comp_assoc _ _ _)
      _ ≡ₜ (Term.simonGammaTerm A G hm D.check ⨟
            (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)) := PEq.compL _ D.gamma_factor
      _ ≡ₜ Term.simonDeltaTerm A D.check := simonGammaTerm_square D.check_spec
      _ ≡ₜ (D.lam ⨟ D.delta) := PEq.symm D.delta_factor
  calc (D.gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G))
      ≡ₜ ((lam' ⨟ D.lam) ⨟ (D.gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G))) :=
        (PEq.symm (PEq.id_comp _)).trans (PEq.compL _ (PEq.symm hl'l))
    _ ≡ₜ (lam' ⨟ (D.lam ⨟ (D.gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (lam' ⨟ (D.lam ⨟ D.delta)) := PEq.compR _ key
    _ ≡ₜ ((lam' ⨟ D.lam) ⨟ D.delta) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ D.delta := (PEq.compL _ hl'l).trans (PEq.id_comp _)

/-- The Simon lift built from the data is a group-lift, with `γ` as its drop one-sided
inverse. -/
theorem isGLiftPair (hinj : Function.Injective hm) (D : SimonHData G hm A) :
    IsGLiftPair D.simonT D.gamma :=
  IsGLiftPair.simon G (Term.listF (Term.rhoInj A hm)) D.lam
    (IsDrop.listF (Term.isDrop_rhoInj A hm)) D.lam_isLift (PEq.refl _)
    D.gamma_isDrop (D.loop hinj)

end SimonHData

/-- **The lift-drop factorisation exists.**  This is the appendix proof of the Simon lift
lemma: the factorisation of Lemma 7.4 is applied to `Lax149335Proofs.Term.simonDeltaTerm` and
`Lax149335Proofs.Term.simonGammaTerm` with a common lift (`Lax149335Proofs.common_liftDrop`). -/
theorem exists_simonHData (A : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} : Nonempty (SimonHData G hm A) := by
  classical
  obtain ⟨t, ht⟩ := exists_checkH A G (fun g => ∃ i, hm i = g)
  obtain ⟨Z, lam, dd, dg, hlam, hdd, hdg, hedd, hedg⟩ :=
    common_liftDrop (Term.simonDeltaTerm A t) (Term.simonGammaTerm A G hm t)
      (isLiftDrop_of_aperiodic _ (Term.isAperiodic_simonDeltaTerm A ht.1))
      (isLiftDrop_of_aperiodic _ (Term.isAperiodic_simonGammaTerm A G hm ht.1))
  exact ⟨⟨Z, t, ht, lam, hlam, dg, hdg, PEq.symm hedg, dd, hdd, PEq.symm hedd⟩⟩

/-! ### The Simon lift lemma -/

/-- **Lemma (Simon lift)** (appendix, *Group-lifts*).  For every subset `H` of the group —
presented as the image of an injective map `hm` — and every type `A` there is a term
`(Σ_H A)* → S`, the *Simon lift*, which

1. is a composition of a drop, the group prefix multiplication and a lift;
2. is provably injective, with a drop one-sided inverse `γ`;
3. comes with a drop `δ` making the square `γ ; ρ* ; spref ≡ δ` commute provably — the
   square is stated for `γ`, not for the Simon lift itself.

The proof is the one of the appendix: the lift-drop factorisation of Lemma
7.4 is applied to the two aperiodic terms `Lax149335Proofs.Term.simonDeltaTerm` and
`Lax149335Proofs.Term.simonGammaTerm` with a common lift (`Lax149335Proofs.common_liftDrop`), and the two
equations are `Lax149335Proofs.simonGammaTerm_loop` and `Lax149335Proofs.simonGammaTerm_square`. -/
theorem simon_lift_H (A : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} (hinj : Function.Injective hm) :
    ∃ (S : Ty) (simon : Term ((Term.sigmaTy A m)⋆) S)
      (gamma : Term S ((Term.sigmaTy A m)⋆)) (delta : Term S (Term.tTy A n)),
      (∃ (d₀ : Term ((Term.sigmaTy A m)⋆) ((Term.sigmaTy A n)⋆))
         (l : Term (Term.tTy A n) S),
          IsDrop d₀ ∧ IsLift l ∧ simon ≡ₜ (d₀ ⨟ (Term.spref A G ⨟ l))) ∧
      IsDrop gamma ∧ (simon ⨟ gamma) ≡ₜ Term.id ((Term.sigmaTy A m)⋆) ∧
      IsDrop delta ∧
      (gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)) ≡ₜ delta := by
  obtain ⟨D⟩ := exists_simonHData A G (hm := hm)
  exact ⟨D.S, D.simonT, D.gamma, D.delta,
    ⟨Term.listF (Term.rhoInj A hm), D.lam, IsDrop.listF (Term.isDrop_rhoInj A hm),
      D.lam_isLift, PEq.refl _⟩,
    D.gamma_isDrop, D.loop hinj, D.delta_isDrop, D.square⟩

/-- **The Simon lift is a group-lift.**  The term produced by `Lax149335Proofs.simon_lift_H` is
a group-lift, with `γ` as its drop one-sided inverse; this is the way the Simon lift lemma
enters the completeness proof. -/
theorem isGLiftPair_simon_H (A : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} (hinj : Function.Injective hm) :
    ∃ (S : Ty) (simon : Term ((Term.sigmaTy A m)⋆) S)
      (gamma : Term S ((Term.sigmaTy A m)⋆)) (delta : Term S (Term.tTy A n)),
      IsGLiftPair simon gamma ∧ IsDrop delta ∧
        (gamma ⨟ (Term.listF (Term.rhoInj A hm) ⨟ Term.spref A G)) ≡ₜ delta := by
  obtain ⟨S, simon, gamma, delta, ⟨d₀, l, hd₀, hl, hshape⟩, hgamma, hloop, hdelta, hsquare⟩ :=
    simon_lift_H A G hinj
  exact ⟨S, simon, gamma, delta,
    IsGLiftPair.simon G d₀ l hd₀ hl hshape hgamma hloop, hdelta, hsquare⟩

end Lax149335Proofs

bridge_export Lax149335Proofs
