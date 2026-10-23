import Lax149335Proofs.Appendix.Groups.SimonLiftProof
import Lax149335Proofs.Appendix.Groups.StarConsolidation
import Lax149335Proofs.Appendix.Groups.AperiodicDrops

/-!
# The component-wise exchange lemma for a Simon lift

This file proves the lemma of the appendix that exchanges a Simon lift with a drop of the
special shape `(Σ_{h ∈ H} f_h)*` — a collection of drops `A ⇒ B` applied component-wise to
a list over `Σ_H A` — and the two consequences the appendix draws from it: the map case of
the prefix exchange lemma, and the prefix exchange lemma itself.

`Lax149335Proofs.simon_exchange_component_wise` is the lemma: it is the group exchange lemma
(`Lax149335Proofs.IsGExch`) for the drop `(Σ_H f_h)*` and the one-sided inverse `γ` of the Simon
lift at the codomain.  The construction is the one of the appendix: a Simon lift is applied
to the domain as well, and the two `γ`s are connected by the aperiodic term
`λ_T⁻¹ ; g ; λ_S`, where `g` is `Lax149335Proofs.Term.depMapT`, the term that applies `f_i` to the
payload of a letter, the index `i` being read off the *unprefixed* annotation of that
letter.  That is an aperiodic operation, built exactly like the term `check_H` of the
appendix (duplicate the annotation, unprefix the copy, act on the letter according to it),
and the square it has to satisfy,

  `simonGammaTerm X ; (Σ_H f_i)*  ≡  depMapT ; simonGammaTerm Y`,

relates two aperiodic terms, so it follows from `Lax149335Proofs.completeness_aperiodic`.

The lemma needs no hypothesis beyond the lift-drop factorisations of `check_H` at the two
types (`Lax149335Proofs.SimonHData`), which exist unconditionally; the appendix reads it off the
proof of the Simon lift lemma in the same way.

The consequences:

* `Lax149335Proofs.prefixExchangeMapCase_group`: the map case of the prefix exchange lemma — a
  group injection followed by the component-wise exchange lemma;
* `Lax149335Proofs.prefix_exchange_group`: with the star consolidation square, which is proved in
  `Lax149335Proofs.Appendix.Groups.StarConsolidation`, the prefix exchange lemma, and hence the
  group exchange lemma, hold unconditionally.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

/-! ### Unprefixing a list whose letters have been transformed according to their unprefixed
annotation -/

/-- The combinatorial heart of the per-component naturality square.  Duplicating every
annotation, unprefixing, transforming each payload by `F d`, where `d` is the unprefixed
annotation, and unprefixing again gives the same list as unprefixing once and then
transforming each payload by `F d`. -/
theorem unprefDen_dep {E E' Gt : Type} [Group Gt] (F : Gt → E → E') :
    ∀ (acc : Gt) (l : List (E × Gt)),
      unprefDen acc ((unprefDen acc (l.map (fun p => (p, p.2)))).map
          (fun q => (F q.2 q.1.1, q.1.2)))
        = (unprefDen acc l).map (fun q => (F q.2 q.1, q.2))
  | _, [] => rfl
  | acc, p :: t => by
      obtain ⟨a, g⟩ := p
      simp only [List.map_cons, unprefDen_cons, List.map_cons]
      rw [unprefDen_dep F g t]

namespace Term

/-! ### The terms -/

open Classical in
/-- The index of `Σ_H A` that `Lax149335Proofs.Term.rhoInv` assigns to a group element. -/
noncomputable def rhoIdx {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (g : ⟦Ty.finAlph n⟧) : ⟦Ty.finAlph m⟧ :=
  if h : ∃ i, hm i = g then h.choose else firstAlph m

theorem rhoInv_eq_sigmaCase (A : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) :
    rhoInv A hm = sigmaCase (fun g => injSigma A (rhoIdx hm g)) := rfl

/-- `Lax149335Proofs.unprefDen_dep` for the family of denotations used below, in beta-normal
form. -/
theorem unprefDen_dep_fs {X Y : Ty} {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (fs : ⟦Ty.finAlph m⟧ → Term X Y)
    (l : List (⟦X⟧ × ⟦Ty.finAlph n⟧)) :
    (letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧)
        ((unprefDen (1 : ⟦Ty.finAlph n⟧) (l.map (fun p => (p, p.2)))).map
          (fun q => ((fs (rhoIdx hm q.2)).den q.1.1, q.1.2))))
      = (letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧) l).map
          (fun q => ((fs (rhoIdx hm q.2)).den q.1, q.2)) :=
  letI := G; unprefDen_dep (fun d a => (fs (rhoIdx hm d)).den a) 1 l

/-- The letter map of `Lax149335Proofs.Term.depMapS`: the letter keeps its annotation `g`, and its
payload is transformed by the member `f_i` of the family selected by the *unprefixed*
annotation `d`, which the term receives as its second component. -/
noncomputable def depLetter (X Y : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (fs : ⟦Ty.finAlph m⟧ → Term X Y) :
    Term ((X ⊗ Ty.finAlph n) ⊗ Ty.finAlph n) (sigmaTy Y n) :=
  caseR (fun d => prodF (fs (rhoIdx hm d)) (Term.id (Ty.finAlph n)) ⨟ sigmaEnc Y n)

/-- The per-component map on lists over `Σ A`: every letter keeps its annotation and has its
payload transformed by the member of the family selected by its unprefixed annotation.  It is
built like the term `check_H` of the appendix: the annotation of every letter is duplicated,
the copy is unprefixed, and the letter is transformed according to it. -/
noncomputable def depMapS (X Y : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (fs : ⟦Ty.finAlph m⟧ → Term X Y) :
    Term ((sigmaTy X n)⋆) ((sigmaTy Y n)⋆) :=
  (listF (sigmaDec X n ⨟ dupAnn X n) ⨟ unpref (X ⊗ Ty.finAlph n) G) ⨟
    listF (depLetter X Y hm fs)

/-- The same map, on the more lifted type `T A`. -/
noncomputable def depMapT (X Y : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (fs : ⟦Ty.finAlph m⟧ → Term X Y) :
    Term (tTy X n) (tTy Y n) :=
  fromT X n ⨟ (depMapS X Y G hm fs ⨟ toT Y n)

theorem usesPref_depLetter (X Y : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    {fs : ⟦Ty.finAlph m⟧ → Term X Y} (h : ∀ i, usesPref (fs i) = false) :
    usesPref (depLetter X Y hm fs) = false :=
  usesPref_caseR _ (fun d => by simp [usesPref, h (rhoIdx hm d)])

theorem isAperiodic_depMapT (X Y : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) {fs : ⟦Ty.finAlph m⟧ → Term X Y}
    (h : ∀ i, IsAperiodic (fs i)) : IsAperiodic (depMapT X Y G hm fs) := by
  have hl : usesPref (depLetter X Y hm fs) = false :=
    usesPref_depLetter X Y hm (fun i => h i)
  simp [IsAperiodic, depMapT, depMapS, usesPref, hl]

/-! ### The letter map, denotationally -/

/-- The denotation of the letter map of `Lax149335Proofs.Term.depMapS`, as a map on the letters of
the *unprefixed* list. -/
noncomputable def depLetterDen (X Y : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (fs : ⟦Ty.finAlph m⟧ → Term X Y) (x : ⟦sigmaTy X n⟧) : ⟦sigmaTy Y n⟧ :=
  (injSigma Y (annOfSigma X x)).den
    ((fs (rhoIdx hm (annOfSigma X x))).den ((sigmaDec X n).den x).1)

@[simp] theorem depLetterDen_injSigma (X Y : Ty) {m n : ℕ}
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (fs : ⟦Ty.finAlph m⟧ → Term X Y)
    (g : ⟦Ty.finAlph n⟧) (a : ⟦X⟧) :
    depLetterDen X Y hm fs ((injSigma X g).den a)
      = (injSigma Y g).den ((fs (rhoIdx hm g)).den a) := by
  simp [depLetterDen, annOfSigma]

@[simp] theorem annOfSigma_depLetterDen (X Y : Ty) {m n : ℕ}
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (fs : ⟦Ty.finAlph m⟧ → Term X Y)
    (x : ⟦sigmaTy X n⟧) :
    annOfSigma Y (depLetterDen X Y hm fs x) = annOfSigma X x := by
  simp [depLetterDen, annOfSigma]

/-- The letter map commutes with the projections back to `Σ_H`: this is the per-component
naturality, one letter at a time. -/
theorem rhoInv_depLetterDen (X Y : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (fs : ⟦Ty.finAlph m⟧ → Term X Y) (x : ⟦sigmaTy X n⟧) :
    (rhoInv Y hm).den (depLetterDen X Y hm fs x)
      = (sigmaCase (fun i => fs i ⨟ injSigma Y i)).den ((rhoInv X hm).den x) := by
  obtain ⟨a, g, rfl⟩ := sigma_cases X x
  rw [depLetterDen_injSigma, rhoInv_eq_sigmaCase, rhoInv_eq_sigmaCase]
  simp

/-! ### The list map, denotationally -/

theorem den_unsprefS (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (w : List ⟦sigmaTy A n⟧) :
    (unsprefS A G).den w
      = (letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧) (w.map (sigmaDec A n).den)).map
          (sigmaEnc A n).den := by
  show ((unpref A G).den (w.map (sigmaDec A n).den)).map (sigmaEnc A n).den = _
  rw [den_unpref]

theorem den_depLetter (X Y : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (fs : ⟦Ty.finAlph m⟧ → Term X Y) (p : ⟦X⟧ × ⟦Ty.finAlph n⟧) (d : ⟦Ty.finAlph n⟧) :
    (depLetter X Y hm fs).den (p, d)
      = (injSigma Y p.2).den ((fs (rhoIdx hm d)).den p.1) := by
  obtain ⟨a, g⟩ := p
  simp [depLetter]

theorem den_depMapS (X Y : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (fs : ⟦Ty.finAlph m⟧ → Term X Y)
    (v : List ⟦sigmaTy X n⟧) :
    (depMapS X Y G hm fs).den v
      = (letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧)
            ((v.map (sigmaDec X n).den).map (fun p => (p, p.2)))).map
          (fun q => (injSigma Y q.1.2).den ((fs (rhoIdx hm q.2)).den q.1.1)) := by
  show ((unpref (X ⊗ Ty.finAlph n) G).den
      ((listF (sigmaDec X n ⨟ dupAnn X n)).den v)).map (depLetter X Y hm fs).den = _
  have hstep : (listF (sigmaDec X n ⨟ dupAnn X n)).den v
      = (v.map (sigmaDec X n).den).map (fun p => (p, p.2)) := by
    simp [List.map_map, Function.comp_def]
  rw [hstep, den_unpref]
  refine List.map_congr_left (fun q _ => ?_)
  exact den_depLetter X Y hm fs q.1 q.2

/-- **The key semantic fact.**  Unprefixing after the per-component map is the same as the
per-component map on letters after unprefixing. -/
theorem den_unsprefS_depMapS (X Y : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (fs : ⟦Ty.finAlph m⟧ → Term X Y)
    (v : List ⟦sigmaTy X n⟧) :
    (unsprefS Y G).den ((depMapS X Y G hm fs).den v)
      = ((unsprefS X G).den v).map (depLetterDen X Y hm fs) := by
  classical
  rw [den_unsprefS, den_unsprefS, den_depMapS]
  have hdec : ((letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧)
        ((v.map (sigmaDec X n).den).map (fun p => (p, p.2)))).map
        (fun q => (injSigma Y q.1.2).den ((fs (rhoIdx hm q.2)).den q.1.1))).map
        (sigmaDec Y n).den
      = (letI := G; unprefDen (1 : ⟦Ty.finAlph n⟧)
          ((v.map (sigmaDec X n).den).map (fun p => (p, p.2)))).map
          (fun q => ((fs (rhoIdx hm q.2)).den q.1.1, q.1.2)) := by
    rw [List.map_map]
    refine List.map_congr_left (fun q _ => ?_)
    simp
  rw [hdec]
  refine Eq.trans (congrArg (List.map (sigmaEnc Y n).den)
    (unprefDen_dep_fs G hm fs (v.map (sigmaDec X n).den))) ?_
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun q _ => ?_)
  obtain ⟨a, d⟩ := q
  simp

/-! ### The two branches of the term of which `γ` is the drop part -/

theorem den_simonGammaTerm_inl (A : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    {t : Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆))} {z : ⟦tTy A n⟧}
    {u : List ⟦sigmaTy A n⟧} (h : t.den ((fromT A n).den z) = Sum.inl u) :
    (simonGammaTerm A G hm t).den z = ((unsprefS A G).den u).map (rhoInv A hm).den := by
  simp [simonGammaTerm, den_comp, h]

theorem den_simonGammaTerm_inr (A : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    {t : Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆))} {z : ⟦tTy A n⟧}
    {u : List ⟦sigmaTy A n⟧} (h : t.den ((fromT A n).den z) = Sum.inr u) :
    (simonGammaTerm A G hm t).den z = ([] : List ⟦sigmaTy A m⟧) := by
  simp [simonGammaTerm, den_comp, h]

/-! ### The per-component naturality square -/

/-- **The term of which `γ` is the drop part is per-component natural.**  Both sides are
aperiodic and have the same denotation, so they are provably equal. -/
theorem simonGammaTerm_depMapT (X Y : Ty) {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) {fs : ⟦Ty.finAlph m⟧ → Term X Y}
    (hfs : ∀ i, IsAperiodic (fs i))
    {tX : Term ((sigmaTy X n)⋆) (((sigmaTy X n)⋆) ⊕' ((sigmaTy X n)⋆))}
    {tY : Term ((sigmaTy Y n)⋆) (((sigmaTy Y n)⋆) ⊕' ((sigmaTy Y n)⋆))}
    (htX : IsCheckH G (fun g => ∃ i, hm i = g) tX)
    (htY : IsCheckH G (fun g => ∃ i, hm i = g) tY) :
    (simonGammaTerm X G hm tX ⨟ listF (sigmaCase (fun i => fs i ⨟ injSigma Y i))) ≡ₜ
      (depMapT X Y G hm fs ⨟ simonGammaTerm Y G hm tY) := by
  classical
  have hw : IsAperiodic (sigmaCase (fun i => fs i ⨟ injSigma Y i)) :=
    usesPref_sigmaCase _ (fun i => by
      simp [usesPref, usesPref_injSigma, show usesPref (fs i) = false from hfs i])
  refine completeness_aperiodic _ _ ?_ ?_ ?_
  · exact (isAperiodic_comp _ _).mpr ⟨isAperiodic_simonGammaTerm X G hm htX.1,
      (isAperiodic_listF _).mpr hw⟩
  · exact (isAperiodic_comp _ _).mpr ⟨isAperiodic_depMapT X Y G hm hfs,
      isAperiodic_simonGammaTerm Y G hm htY.1⟩
  · funext z
    have hround : ∀ u : List ⟦sigmaTy Y n⟧, (fromT Y n).den ((toT Y n).den u) = u := by
      intro u
      have h := congrFun (PEq.sound (toT_fromT Y n)) u
      simpa using h
    have hRHS : (depMapT X Y G hm fs ⨟ simonGammaTerm Y G hm tY).den z
        = (simonGammaTerm Y G hm tY).den ((toT Y n).den
            ((depMapS X Y G hm fs).den ((fromT X n).den z))) := by
      simp only [depMapT, den_comp]
    have hLHS : (simonGammaTerm X G hm tX ⨟
          listF (sigmaCase (fun i => fs i ⨟ injSigma Y i))).den z
        = ((simonGammaTerm X G hm tX).den z).map
            (sigmaCase (fun i => fs i ⨟ injSigma Y i)).den := by
      simp only [den_comp, den_listF]
    have hun : (unsprefS Y G).den ((depMapS X Y G hm fs).den ((fromT X n).den z))
        = ((unsprefS X G).den ((fromT X n).den z)).map (depLetterDen X Y hm fs) :=
      den_unsprefS_depMapS X Y G hm fs _
    have hcond : (∀ x ∈ (show List ⟦sigmaTy Y n⟧ from
          (unsprefS Y G).den ((depMapS X Y G hm fs).den ((fromT X n).den z))),
            ∃ i, hm i = annOfSigma Y x)
        ↔ (∀ x ∈ (show List ⟦sigmaTy X n⟧ from
            (unsprefS X G).den ((fromT X n).den z)),
            ∃ i, hm i = annOfSigma X x) := by
      rw [hun]
      constructor
      · intro h x hx
        simpa using h _ (List.mem_map_of_mem hx)
      · intro h y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        simpa using h x hx
    rw [hLHS, hRHS]
    by_cases hP : ∀ x ∈ (show List ⟦sigmaTy X n⟧ from
        (unsprefS X G).den ((fromT X n).den z)), ∃ i, hm i = annOfSigma X x
    · have hX : tX.den ((fromT X n).den z) = Sum.inl ((fromT X n).den z) := by
        rw [htX.2 _, if_pos hP]
      have hY : tY.den ((fromT Y n).den ((toT Y n).den
            ((depMapS X Y G hm fs).den ((fromT X n).den z))))
          = Sum.inl ((depMapS X Y G hm fs).den ((fromT X n).den z)) := by
        rw [hround, htY.2 _, if_pos (hcond.mpr hP)]
      rw [den_simonGammaTerm_inl (m := m) X G hm hX, den_simonGammaTerm_inl Y G hm hY, hun]
      simp only [List.map_map, Function.comp_def]
      exact List.map_congr_left (fun x _ => (rhoInv_depLetterDen X Y hm fs x).symm)
    · have hX : tX.den ((fromT X n).den z) = Sum.inr ((fromT X n).den z) := by
        rw [htX.2 _, if_neg hP]
      have hY : tY.den ((fromT Y n).den ((toT Y n).den
            ((depMapS X Y G hm fs).den ((fromT X n).den z))))
          = Sum.inr ((depMapS X Y G hm fs).den ((fromT X n).den z)) := by
        rw [hround, htY.2 _, if_neg (fun h => hP (hcond.mp h))]
      rw [den_simonGammaTerm_inr (m := m) X G hm hX, den_simonGammaTerm_inr Y G hm hY]
      rfl

end Term

/-! ### Per-component naturality of the one-sided inverse of the Simon lift -/

/-- **The one-sided inverse `γ` of the Simon lift is natural per component.**  For every
family `f_i` of drops `X ⇒ Y` indexed by `H`, the square relating `γ` at `X` and `γ` at `Y`
over the induced map `Σ_H X → Σ_H Y` commutes provably, up to a lift-drop factorisation on
the `S`-side.

This is the naturality that the appendix uses in the map case of the prefix exchange lemma.
It needs no assumption beyond the lift-drop factorisations at the two types: the connecting
term is `λ_X⁻¹ ; depMapT ; λ_Y`, and the square for `depMapT` is
`Lax149335Proofs.Term.simonGammaTerm_depMapT`. -/
theorem SimonHData.perComponent {m n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} {X Y : Ty}
    (DX : SimonHData G hm X) (DY : SimonHData G hm Y)
    (fs : ⟦Ty.finAlph m⟧ → Term X Y) (hfs : ∀ i, IsDrop (fs i)) :
    ∃ t : Term DX.S DY.S, IsLiftDrop t ∧
      (DX.gamma ⨟ Term.listF (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y i))) ≡ₜ
        (t ⨟ DY.gamma) := by
  classical
  choose fs' hfs'drop hfs'ap hfs'eq using fun i => (hfs i).aperiodic_normal
  obtain ⟨lamInv, hlamInv, -, hlamInvL⟩ := lift_iso DX.lam DX.lam_isLift
  refine ⟨lamInv ⨟ (Term.depMapT X Y G hm fs' ⨟ DY.lam), ?_, ?_⟩
  · exact (IsLiftDrop.of_isDrop hlamInv).comp
      ((isLiftDrop_of_aperiodic _ (Term.isAperiodic_depMapT X Y G hm hfs'ap)).comp
        (IsLiftDrop.of_isLift DY.lam_isLift))
  · have hcase : Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y i) ≡ₜ
        Term.sigmaCase (fun i => fs' i ⨟ Term.injSigma Y i) :=
      Term.sigmaCase_congr (fun i => PEq.compL _ (hfs'eq i))
    have hsq := Term.simonGammaTerm_depMapT X Y G hm hfs'ap DX.check_spec DY.check_spec
    calc (DX.gamma ⨟ Term.listF (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y i)))
        ≡ₜ (DX.gamma ⨟ Term.listF (Term.sigmaCase (fun i => fs' i ⨟ Term.injSigma Y i))) :=
          PEq.compR _ (PEq.congr_listF hcase)
      _ ≡ₜ ((lamInv ⨟ DX.lam) ⨟
            (DX.gamma ⨟
              Term.listF (Term.sigmaCase (fun i => fs' i ⨟ Term.injSigma Y i)))) :=
          (PEq.symm (PEq.id_comp _)).trans (PEq.compL _ (PEq.symm hlamInvL))
      _ ≡ₜ (lamInv ⨟ ((DX.lam ⨟ DX.gamma) ⨟
            Term.listF (Term.sigmaCase (fun i => fs' i ⨟ Term.injSigma Y i)))) :=
          (PEq.comp_assoc _ _ _).trans (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _)))
      _ ≡ₜ (lamInv ⨟ (Term.simonGammaTerm X G hm DX.check ⨟
            Term.listF (Term.sigmaCase (fun i => fs' i ⨟ Term.injSigma Y i)))) :=
          PEq.compR _ (PEq.compL _ DX.gamma_factor)
      _ ≡ₜ (lamInv ⨟ (Term.depMapT X Y G hm fs' ⨟
            Term.simonGammaTerm Y G hm DY.check)) := PEq.compR _ hsq
      _ ≡ₜ (lamInv ⨟ (Term.depMapT X Y G hm fs' ⨟ (DY.lam ⨟ DY.gamma))) :=
          PEq.compR _ (PEq.compR _ (PEq.symm DY.gamma_factor))
      _ ≡ₜ ((lamInv ⨟ (Term.depMapT X Y G hm fs' ⨟ DY.lam)) ⨟ DY.gamma) :=
          (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))).trans
            (PEq.symm (PEq.comp_assoc _ _ _))

/-! ### The component-wise exchange lemma -/

/-- **Lemma (component-wise exchange for a Simon lift)** (appendix, *Proof of the Group
Exchange Lemma*).  Consider a collection `f_h` of drops `A ⇒ B` indexed by a subset `H` of
the group.  Then the drop `(Σ_{h ∈ H} f_h)* : (Σ_H A)* ⇒ (Σ_H B)*`, followed by a Simon lift
of `(Σ_H B)*`, satisfies the (inverted) group exchange square: there are a group-lift with
one-sided inverse `C ⇒ (Σ_H A)*` and a drop `C ⇒ S` making the square commute provably,
where `S` is the codomain of the Simon lift and `γ` its one-sided inverse.

The Simon lift of `(Σ_H B)*` is produced along with its data, as in
`Lax149335Proofs.simon_lift_H`: it is a group-lift with one-sided inverse `γ`, and `δ` is the drop
closing the square `γ ; ρ* ; spref ≡ δ`.

The construction is the one of the appendix: a Simon lift is applied to the domain
`(Σ_H A)*` as well, and the two one-sided inverses are connected by the aperiodic term
`λ_T⁻¹ ; depMapT ; λ_S`, which is `Lax149335Proofs.SimonHData.perComponent`. -/
theorem simon_exchange_component_wise {m n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} (hinj : Function.Injective hm) {A B : Ty}
    (fs : ⟦Ty.finAlph m⟧ → Term A B) (hfs : ∀ i, IsDrop (fs i)) :
    ∃ (S : Ty) (simon : Term ((Term.sigmaTy B m)⋆) S)
      (gamma : Term S ((Term.sigmaTy B m)⋆)) (delta : Term S (Term.tTy B n)),
      IsGLiftPair simon gamma ∧ IsDrop delta ∧
        (gamma ⨟ (Term.listF (Term.rhoInj B hm) ⨟ Term.spref B G)) ≡ₜ delta ∧
        IsGExch (Term.listF (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma B i))) gamma := by
  obtain ⟨DA⟩ := exists_simonHData A G (hm := hm)
  obtain ⟨DB⟩ := exists_simonHData B G (hm := hm)
  obtain ⟨t, ht, hnat⟩ := DA.perComponent DB fs hfs
  exact ⟨DB.S, DB.simonT, DB.gamma, DB.delta, DB.isGLiftPair hinj, DB.delta_isDrop,
    DB.square,
    IsGExch.of_gliftPair_liftDrop (DA.isGLiftPair hinj) ht hnat⟩

/-! ### The map case, and the prefix exchange lemma -/

/-- The one-sided inverse `γ` of the Simon lift, followed by the injection `ρ*`, is the drop
`δ` followed by `unspref`: this is the square of the Simon lift lemma, with the group prefix
multiplication moved to the other side. -/
theorem gamma_rhoInj_unspref {Y S : Ty} {m n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} {gamma : Term S ((Term.sigmaTy Y m)⋆)}
    {delta : Term S (Term.tTy Y n)}
    (hsq : (gamma ⨟ (Term.listF (Term.rhoInj Y hm) ⨟ Term.spref Y G)) ≡ₜ delta) :
    (gamma ⨟ Term.listF (Term.rhoInj Y hm)) ≡ₜ (delta ⨟ Term.unspref Y G) := by
  calc (gamma ⨟ Term.listF (Term.rhoInj Y hm))
      ≡ₜ (gamma ⨟ (Term.listF (Term.rhoInj Y hm) ⨟ Term.id ((Term.sigmaTy Y n)⋆))) :=
        PEq.compR _ (PEq.symm (PEq.comp_id _))
    _ ≡ₜ (gamma ⨟ (Term.listF (Term.rhoInj Y hm) ⨟
          (Term.spref Y G ⨟ Term.unspref Y G))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm (Term.spref_unspref Y G)))
    _ ≡ₜ ((gamma ⨟ (Term.listF (Term.rhoInj Y hm) ⨟ Term.spref Y G)) ⨟
          Term.unspref Y G) :=
        (PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))).trans
          (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (delta ⨟ Term.unspref Y G) := PEq.compL _ hsq

/-- **The map case of the prefix exchange lemma** (appendix, proof of the prefix exchange
lemma, leaf case `g*`), proved: for every drop `g : A ⇒ Σ Y` the homomorphic image `g*`
satisfies the inverted exchange square over `unspref`.

This is the argument of the appendix: the group injection (`Lax149335Proofs.group_injection`) makes
`g` component-wise over a subset `H` of the group, after which the component-wise exchange
lemma (`Lax149335Proofs.simon_exchange_component_wise`) applies, and the resulting square is
transported along `ρ*` by the square of the Simon lift. -/
theorem prefixExchangeMapCase_group {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    PrefixExchangeMapCase G := by
  classical
  intro Y A g hg
  obtain ⟨m, hm, C, iota, sigma, fs, hinj, hap, hsig, hret, hfsdrop, heq⟩ :=
    group_injection g hg
  -- a group injection is a prime group-lift: it is aperiodic and has a drop one-sided inverse
  have hpair : IsGLiftPair iota sigma := .groupInj hap hsig hret
  obtain ⟨S, simon, gamma, delta, hpairY, hdelta, hsq, hexch⟩ :=
    simon_exchange_component_wise G hinj (A := C) (B := Y) fs hfsdrop
  obtain ⟨D, nu, rho, k, hnu, hk, he⟩ := hexch
  refine ⟨D, Term.listF iota ⨟ nu, rho ⨟ Term.listF sigma, k ⨟ delta,
    hpair.listF.comp hnu, IsDrop.comp hk hdelta, ?_⟩
  calc ((rho ⨟ Term.listF sigma) ⨟ Term.listF g)
      ≡ₜ (rho ⨟ (Term.listF sigma ⨟ Term.listF g)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (rho ⨟ Term.listF (sigma ⨟ g)) := PEq.compR _ (PEq.list_comp _ _)
    _ ≡ₜ (rho ⨟ Term.listF (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y (hm i)))) :=
        PEq.compR _ (PEq.congr_listF heq)
    _ ≡ₜ (rho ⨟ Term.listF (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y i) ⨟
          Term.rhoInj Y hm)) := PEq.compR _ (PEq.congr_listF (sigmaCase_rhoInj hm fs))
    _ ≡ₜ ((rho ⨟ Term.listF (Term.sigmaCase (fun i => fs i ⨟ Term.injSigma Y i))) ⨟
          Term.listF (Term.rhoInj Y hm)) :=
        (PEq.compR _ (PEq.symm (PEq.list_comp _ _))).trans
          (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ ((k ⨟ gamma) ⨟ Term.listF (Term.rhoInj Y hm)) := PEq.compL _ he
    _ ≡ₜ (k ⨟ (gamma ⨟ Term.listF (Term.rhoInj Y hm))) := PEq.comp_assoc _ _ _
    _ ≡ₜ (k ⨟ (delta ⨟ Term.unspref Y G)) := PEq.compR _ (gamma_rhoInj_unspref hsq)
    _ ≡ₜ ((k ⨟ delta) ⨟ Term.unspref Y G) := PEq.symm (PEq.comp_assoc _ _ _)

/-- **Lemma (Prefix exchange)** (appendix, *Proof of the group exchange lemma*),
proved.  Every drop `f : A ⇒ (Σ B)*` fits in an inverted exchange square over the inverse
`unspref` of the group prefix multiplication.

Its proof needs the whole of this part of
the appendix: the induction on the normal form of a drop with a list codomain
(`Lax149335Proofs.prefix_exchange_of_claims`), the map case (`Lax149335Proofs.prefixExchangeMapCase_group`)
and the star consolidation square (`Lax149335Proofs.starConsolidation`). -/
theorem prefix_exchange_group {A B : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (f : Term A ((Term.sigmaTy B n)⋆)) (hf : IsDrop f) :
    IsGExch f (Term.unspref B G) :=
  prefix_exchange_of_claims (prefixExchangeMapCase_group G) (starConsolidation G) f hf

end Lax149335Proofs

bridge_export Lax149335Proofs
