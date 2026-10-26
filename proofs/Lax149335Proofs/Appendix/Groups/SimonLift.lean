import Lax149335Proofs.Appendix.Groups.GroupInjection
import Lax149335Proofs.Appendix.Groups.GroupliftPairs

/-!
# Partial prefix multiplication, Simon lifts and group injections

This file formalises the statements of the first half of the appendix section
*Completeness in the presence of groups*:

* the partial prefix multiplication for a subset `H ⊆ G` of the group: the injection
  `ρ : Σ_H A ↣ Σ A` (`Lax149335Proofs.Term.rhoInj`) and its drop one-sided inverse
  (`Lax149335Proofs.Term.rhoInv`), the term `check_H` and the term `precheck_H`, the lemma that
  `check_H` may be replaced by `left` (`Lax149335Proofs.checkH_left`), and the lemma that the whole
  loop of partial prefix multiplication is provably the identity
  (`Lax149335Proofs.partial_prefix_multiplication`);
* the terms of the **Simon lift**; the lemma itself
  (`Lax149335Proofs.simon_lift_H`) is stated and proved in
  `Lax149335Proofs.Appendix.Groups.SimonLiftProof`: the Simon lift is a composition of a drop,
  the group prefix multiplication and a lift, it is provably injective with a drop
  one-sided inverse `γ`, and there is a drop `δ` making the square `γ ; ρ* ; pref ≡ δ`
  commute (the square is stated for `γ`, not for the Simon lift itself);
* **group injections** (`Lax149335Proofs.group_injection`): a drop function into `Σ B` becomes
  annotation-diagonal after the domain is injected into a co-product `Σ_H C` indexed by a
  subset of the group.

The subset `H ⊆ G` is presented as an injective map `hm` from a smaller alphabet
`⟦finAlph m⟧` into the alphabet `⟦finAlph n⟧` carrying the group; `Σ_H A` is then
`Σ_m A = sigmaTy A m`.

The group injection lemma is stated here and proved in
`Lax149335Proofs.Appendix.Groups.GroupInjection`; see its docstring.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lax149335Proofs

open Term

namespace Term

/-! ### The group prefix multiplication on `(Σ A)*`

`Lax149335Proofs.Term.spref` has the more lifted codomain `T A`; composing it with the isomorphism
`T A ≃ (Σ A)*` gives the operation `(Σ A)* → (Σ A)*` that the appendix writes `pref`. -/

/-- The group prefix multiplication in the co-product presentation, `(Σ A)* → (Σ A)*`. -/
def sprefS (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term ((sigmaTy A n)⋆) ((sigmaTy A n)⋆) :=
  (listF (sigmaDec A n) ⨟ pref A G) ⨟ listF (sigmaEnc A n)

/-- Its inverse, `(Σ A)* → (Σ A)*`. -/
def unsprefS (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    Term ((sigmaTy A n)⋆) ((sigmaTy A n)⋆) :=
  (listF (sigmaDec A n) ⨟ unpref A G) ⨟ listF (sigmaEnc A n)

theorem unspref_eq_unsprefS (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    unspref A G ≡ₜ (fromT A n ⨟ unsprefS A G) :=
  PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))

@[simp] theorem usesPref_unsprefS (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    usesPref (unsprefS A G) = false := by
  simp [unsprefS, usesPref]

/-- `sprefS` and `unsprefS` are mutually inverse. -/
theorem sprefS_unsprefS (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (sprefS A G ⨟ unsprefS A G) ≡ₜ Term.id ((sigmaTy A n)⋆) := by
  have hED : (listF (sigmaEnc A n) ⨟ listF (sigmaDec A n)) ≡ₜ Term.id ((A ⊗ Ty.finAlph n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaEnc_sigmaDec A n)).trans (PEq.list_id _))
  have hDE : (listF (sigmaDec A n) ⨟ listF (sigmaEnc A n)) ≡ₜ Term.id ((sigmaTy A n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaDec_sigmaEnc A n)).trans (PEq.list_id _))
  calc (sprefS A G ⨟ unsprefS A G)
      ≡ₜ (((listF (sigmaDec A n) ⨟ pref A G) ⨟ listF (sigmaEnc A n)) ⨟
          (listF (sigmaDec A n) ⨟ (unpref A G ⨟ listF (sigmaEnc A n)))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((listF (sigmaDec A n) ⨟ pref A G) ⨟ (unpref A G ⨟ listF (sigmaEnc A n))) :=
        comp_cancel_mid hED
    _ ≡ₜ (listF (sigmaDec A n) ⨟ listF (sigmaEnc A n)) :=
        comp_cancel_mid (PEq.pref_unpref A G)
    _ ≡ₜ Term.id ((sigmaTy A n)⋆) := hDE

theorem unsprefS_sprefS (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) :
    (unsprefS A G ⨟ sprefS A G) ≡ₜ Term.id ((sigmaTy A n)⋆) := by
  have hED : (listF (sigmaEnc A n) ⨟ listF (sigmaDec A n)) ≡ₜ Term.id ((A ⊗ Ty.finAlph n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaEnc_sigmaDec A n)).trans (PEq.list_id _))
  have hDE : (listF (sigmaDec A n) ⨟ listF (sigmaEnc A n)) ≡ₜ Term.id ((sigmaTy A n)⋆) :=
    (PEq.list_comp _ _).trans
      ((PEq.congr_listF (sigmaDec_sigmaEnc A n)).trans (PEq.list_id _))
  calc (unsprefS A G ⨟ sprefS A G)
      ≡ₜ (((listF (sigmaDec A n) ⨟ unpref A G) ⨟ listF (sigmaEnc A n)) ⨟
          (listF (sigmaDec A n) ⨟ (pref A G ⨟ listF (sigmaEnc A n)))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((listF (sigmaDec A n) ⨟ unpref A G) ⨟ (pref A G ⨟ listF (sigmaEnc A n))) :=
        comp_cancel_mid hED
    _ ≡ₜ (listF (sigmaDec A n) ⨟ listF (sigmaEnc A n)) :=
        comp_cancel_mid (PEq.unpref_pref A G)
    _ ≡ₜ Term.id ((sigmaTy A n)⋆) := hDE

/-- The annotation carried by a letter of `Σ A`. -/
def annOfSigma (A : Ty) {n : ℕ} (x : ⟦sigmaTy A n⟧) : ⟦Ty.finAlph n⟧ :=
  ((sigmaDec A n).den x).2

/-! ### The injection `ρ : Σ_H A ↣ Σ A` -/

/-- A distinguished letter of the alphabet `⟦finAlph m⟧`, which is never empty. -/
def firstAlph : (m : ℕ) → ⟦Ty.finAlph m⟧
  | 0 => ()
  | (_ + 1) => .inl ()

/-- The injection `ρ : Σ_H A ↣ Σ A` of the co-product indexed by the subset `H` — presented
as the image of the injective map `hm` — into the co-product indexed by the whole group. -/
def rhoInj (A : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) :
    Term (sigmaTy A m) (sigmaTy A n) :=
  sigmaCase (fun i => injSigma A (hm i))

open Classical in
/-- A (non-natural) drop one-sided inverse of `ρ`: a variant outside the image of `hm` is
sent to the first variant of `Σ_H A`. -/
noncomputable def rhoInv (A : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) :
    Term (sigmaTy A n) (sigmaTy A m) :=
  sigmaCase (fun g => injSigma A (if h : ∃ i, hm i = g then h.choose else firstAlph m))

theorem isDrop_rhoInj (A : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) :
    IsDrop (rhoInj A hm) :=
  isDrop_sigmaCase (fun i => isDrop_injSigma A (hm i))

/-- `ρ` is provably injective, with `rhoInv` as its one-sided inverse. -/
theorem rhoInj_rhoInv (A : Ty) {m n : ℕ} {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧}
    (hinj : Function.Injective hm) :
    (rhoInj A hm ⨟ rhoInv A hm) ≡ₜ Term.id (sigmaTy A m) := by
  classical
  refine (sigmaCase_comp _ _).trans ?_
  refine PEq.trans (sigmaCase_congr (fun i => ?_)) (sigmaCase_injSigma A m)
  have hex : ∃ j, hm j = hm i := ⟨i, rfl⟩
  have hchoose : hex.choose = i := hinj hex.choose_spec
  calc (injSigma A (hm i) ⨟ rhoInv A hm)
      ≡ₜ injSigma A (if h : ∃ j, hm j = hm i then h.choose else firstAlph m) :=
        injSigma_sigmaCase _ _
    _ ≡ₜ injSigma A i := by rw [dif_pos hex, hchoose]; exact PEq.refl _

/-- For `H` the whole group, i.e. `hm` the identity, the injection `ρ` is provably the
identity.  This is the case `ρ = id` of the appendix, which the grouplift-drop factorisation
uses for the prime `pref`. -/
theorem rhoInj_id (A : Ty) {n : ℕ} :
    rhoInj A (fun g : ⟦Ty.finAlph n⟧ => g) ≡ₜ Term.id (sigmaTy A n) :=
  sigmaCase_injSigma A n

/-- The same, after the list functor. -/
theorem listF_rhoInj_id (A : Ty) {n : ℕ} :
    listF (rhoInj A (fun g : ⟦Ty.finAlph n⟧ => g)) ≡ₜ Term.id ((sigmaTy A n)⋆) :=
  (PEq.congr_listF (rhoInj_id A)).trans (PEq.list_id _)

end Term

/-! ### An aperiodic test: are all the letters of a list left variants?

The two terms `precheck_H` and `check_H` below both flag every letter of their input as good
or bad and then check that no letter was flagged bad, returning the (unchanged) input in the
left variant if the check succeeds.  The second half of that procedure is the term
`Lax149335Proofs.Term.allLeftTest`, which is built from `block`: a list over `X + X` is split into
an initial run of left variants followed by a list of blocks, each starting with a right
variant, and the input consists only of left variants exactly when the list of blocks is
empty.  In either case the input can be rebuilt from the output of `block`. -/

namespace Term

/-- Rebuilds the input of `block X X` from its output. -/
def rebuildBlock (X : Ty) : Term ((X⋆) ⊗ (X ⊗ X⋆)⋆) (X⋆) :=
  prodF (id (X⋆)) (listF (inr Ty.unit (X ⊗ X⋆) ⨟ cons X) ⨟ concat X) ⨟ binconcat X

@[simp] theorem den_cons_inr_pair (X : Ty) (x : ⟦X⟧ × List ⟦X⟧) :
    (cons X).den (Sum.inr x) = x.1 :: x.2 := rfl

@[simp] theorem den_rebuildBlock (X : Ty) (g : List ⟦X⟧) (r : List (⟦X⟧ × List ⟦X⟧)) :
    (rebuildBlock X).den (g, r) = g ++ (r.map (fun p => p.1 :: p.2)).flatten := by
  simp only [rebuildBlock, den_comp, den_prodF, den_id, den_listF, den_concat, den_binconcat]
  rfl

@[simp] theorem usesPref_rebuildBlock (X : Ty) : usesPref (rebuildBlock X) = false := by
  simp [rebuildBlock, usesPref, binconcat, prepend, pureT, nilT]

/-- The collapse of a co-product of a type with itself. -/
def unSum {X : Ty} : ⟦X⟧ ⊕ ⟦X⟧ → ⟦X⟧ := Sum.elim _root_.id _root_.id

/-- Rebuilding the input of `block X X` from its output really does give the input back
(after the two variants have been collapsed). -/
theorem blockDen_rebuild {X : Ty} (l : List (⟦X⟧ ⊕ ⟦X⟧)) :
    (blockDen l).1 ++ ((blockDen l).2.map (fun p => p.1 :: p.2)).flatten = l.map unSum := by
  induction l with
  | nil => rfl
  | cons y t ih =>
      cases y with
      | inl a => simpa [blockDen, unSum] using ih
      | inr b => simpa [blockDen, unSum] using ih

/-- `block X X` produces no block exactly when all the letters are left variants. -/
theorem blockDen_snd_nil {X : Ty} (l : List (⟦X⟧ ⊕ ⟦X⟧)) :
    (blockDen l).2 = [] ↔ ∀ y ∈ l, y.isLeft = true := by
  induction l with
  | nil => simp [blockDen]
  | cons y t ih =>
      cases y with
      | inl a => simpa [blockDen] using ih
      | inr b => simp [blockDen]

/-- The aperiodic test: the input list is returned unchanged, in the left variant exactly
when all its letters are left variants. -/
def allLeftFinish (X : Ty) : Term ((X⋆) ⊗ (X ⊗ X⋆)⋆) ((X⋆) ⊕' (X⋆)) :=
  (prodF (id (X⋆)) (uncons (X ⊗ X⋆)) ⨟ distR (X⋆) Ty.unit ((X ⊗ X⋆) ⊗ (X ⊗ X⋆)⋆)) ⨟
    either (fst (X⋆) Ty.unit ⨟ inl (X⋆) (X⋆))
      ((prodF (id (X⋆)) (inr Ty.unit ((X ⊗ X⋆) ⊗ (X ⊗ X⋆)⋆) ⨟ cons (X ⊗ X⋆)) ⨟
          rebuildBlock X) ⨟ inr (X⋆) (X⋆))

def allLeftTest (X : Ty) : Term ((X ⊕' X)⋆) ((X⋆) ⊕' (X⋆)) :=
  block X X ⨟ allLeftFinish X

theorem den_allLeftFinish_nil (X : Ty) (g : List ⟦X⟧) :
    (allLeftFinish X).den (g, []) = Sum.inl g := rfl

theorem den_allLeftFinish_cons (X : Ty) (g : List ⟦X⟧) (z : ⟦X⟧ × List ⟦X⟧)
    (zs : List (⟦X⟧ × List ⟦X⟧)) :
    (allLeftFinish X).den (g, z :: zs) =
      Sum.inr (g ++ ((z :: zs).map (fun p => p.1 :: p.2)).flatten) := by
  show Sum.inr ((rebuildBlock X).den (g, z :: zs)) = _
  rw [den_rebuildBlock]

@[simp] theorem usesPref_allLeftTest (X : Ty) : usesPref (allLeftTest X) = false := by
  simp [allLeftTest, allLeftFinish, either, usesPref]

theorem den_allLeftTest (X : Ty) (l : List (⟦X⟧ ⊕ ⟦X⟧)) :
    (allLeftTest X).den l =
      if ∀ y ∈ l, y.isLeft = true then Sum.inl (l.map unSum) else Sum.inr (l.map unSum) := by
  have hrb := blockDen_rebuild l
  have hnil := blockDen_snd_nil l
  have hden : (allLeftTest X).den l = (allLeftFinish X).den (blockDen l) := rfl
  rcases hs : blockDen l with ⟨g, r⟩
  rw [hs] at hrb hnil
  rw [hden, hs]
  cases r with
  | nil =>
      rw [if_pos (hnil.mp rfl), den_allLeftFinish_nil]
      exact congrArg Sum.inl (by simpa using hrb)
  | cons z zs =>
      have hfalse : ¬ ∀ y ∈ l, y.isLeft = true := fun h => by
        simpa using hnil.mpr h
      rw [if_neg hfalse, den_allLeftFinish_cons]
      exact congrArg Sum.inr hrb

end Term

/-! ### `check_H` and `precheck_H`

`precheck_H` tests whether all the letters of the input list carry an annotation in `H`, and
`check_H` tests whether all the letters of the *unprefixed* input list do, i.e. whether the
input has been obtained by prefix multiplication from a list of elements of `Σ_H A`.  Both
put the (unchanged) input in the left variant if the test succeeds and in the right variant
otherwise.  The appendix leaves the construction of these two aperiodic terms to the reader;
the predicate below is the specification, and `Lax149335Proofs.exists_precheckH` /
`Lax149335Proofs.exists_checkH` are the two existence statements. -/

open Classical in
/-- The specification of `precheck_H`: the input is unchanged, and it is put in the left
variant exactly when all its letters carry an annotation in `H`. -/
def IsPrecheckH {A : Ty} {n : ℕ} (H : ⟦Ty.finAlph n⟧ → Prop)
    (t : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))) :
    Prop :=
  IsAperiodic t ∧
    ∀ w : List ⟦Term.sigmaTy A n⟧,
      t.den w = if ∀ x ∈ w, H (Term.annOfSigma A x) then .inl w else .inr w

open Classical in
/-- The specification of `check_H`: the input is unchanged, and it is put in the left variant
exactly when the list obtained from it by *unprefixing* has all its annotations in `H`, i.e.
exactly when the input is the prefix multiplication of a list over `Σ_H A`. -/
def IsCheckH {A : Ty} {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (H : ⟦Ty.finAlph n⟧ → Prop)
    (t : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))) :
    Prop :=
  IsAperiodic t ∧
    ∀ w : List ⟦Term.sigmaTy A n⟧,
      t.den w =
        if ∀ x ∈ (show List ⟦Term.sigmaTy A n⟧ from (Term.unsprefS A G).den w),
            H (Term.annOfSigma A x) then .inl w else .inr w

/-! ### The existence of `check_H` and `precheck_H`

Both terms are aperiodic, and the appendix leaves their construction to the reader.  They are
built here from `Lax149335Proofs.Term.allLeftTest`: every letter of the input is flagged good or bad
— for `precheck_H` according to its own annotation, for `check_H` according to the annotation
it gets after unprefixing, which is obtained by applying the (aperiodic) term `unpref` to a
copy of the annotation — and then `allLeftTest` checks that no letter was flagged bad. -/

namespace Term

/-- Duplicates the annotation of a letter of `A × G`, so that the copy can be unprefixed
while the letter itself is kept. -/
def dupAnn (A : Ty) (n : ℕ) : Term (A ⊗ Ty.finAlph n) ((A ⊗ Ty.finAlph n) ⊗ Ty.finAlph n) :=
  caseR (fun g => pairR (pairR (id A) (constFin g)) (constFin g))

@[simp] theorem den_dupAnn (A : Ty) (n : ℕ) (a : ⟦A⟧) (g : ⟦Ty.finAlph n⟧) :
    (dupAnn A n).den (a, g) = ((a, g), g) := by
  simp [dupAnn]

@[simp] theorem den_dupAnn_pair (A : Ty) (n : ℕ) (p : ⟦A⟧ × ⟦Ty.finAlph n⟧) :
    (dupAnn A n).den p = (p, p.2) := by
  obtain ⟨a, g⟩ := p
  simp

@[simp] theorem usesPref_dupAnn (A : Ty) (n : ℕ) : usesPref (dupAnn A n) = false :=
  usesPref_caseR _ (fun _ => by simp [usesPref, usesPref_constFin])

/-- Flags a letter of `Σ A`, presented as a payload together with a group element `h`, by
whether `h` lies in `H`; the letter itself is rebuilt from its payload. -/
def flagBy (A : Ty) {n : ℕ} (Hb : ⟦Ty.finAlph n⟧ → Bool) :
    Term ((A ⊗ Ty.finAlph n) ⊗ Ty.finAlph n) ((sigmaTy A n) ⊕' (sigmaTy A n)) :=
  caseR (fun h => sigmaEnc A n ⨟
    (if Hb h then inl (sigmaTy A n) (sigmaTy A n) else inr (sigmaTy A n) (sigmaTy A n)))

@[simp] theorem den_flagBy (A : Ty) {n : ℕ} (Hb : ⟦Ty.finAlph n⟧ → Bool)
    (p : ⟦A⟧ × ⟦Ty.finAlph n⟧) (h : ⟦Ty.finAlph n⟧) :
    (flagBy A Hb).den (p, h) =
      if Hb h then Sum.inl ((sigmaEnc A n).den p) else Sum.inr ((sigmaEnc A n).den p) := by
  simp only [flagBy, den_caseR, den_comp]
  by_cases hh : Hb h <;> simp [hh]

@[simp] theorem usesPref_flagBy (A : Ty) {n : ℕ} (Hb : ⟦Ty.finAlph n⟧ → Bool) :
    usesPref (flagBy A Hb) = false :=
  usesPref_caseR _ (fun h => by by_cases hh : Hb h <;> simp [usesPref, hh])

@[simp] theorem den_sigmaEnc_sigmaDec (A : Ty) (n : ℕ) (x : ⟦sigmaTy A n⟧) :
    (sigmaEnc A n).den ((sigmaDec A n).den x) = x := by
  have h := congrFun (PEq.sound (sigmaDec_sigmaEnc A n)) x
  simpa using h

@[simp] theorem annOfSigma_sigmaEnc (A : Ty) {n : ℕ} (p : ⟦A⟧ × ⟦Ty.finAlph n⟧) :
    annOfSigma A ((sigmaEnc A n).den p) = p.2 := by
  obtain ⟨a, g⟩ := p
  simp [annOfSigma]

/-- The term `precheck_H`. -/
def precheckTerm (A : Ty) {n : ℕ} (Hb : ⟦Ty.finAlph n⟧ → Bool) :
    Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆)) :=
  listF (sigmaDec A n ⨟ (dupAnn A n ⨟ flagBy A Hb)) ⨟ allLeftTest (sigmaTy A n)

/-- The term `check_H`. -/
def checkTerm (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧) (Hb : ⟦Ty.finAlph n⟧ → Bool) :
    Term ((sigmaTy A n)⋆) (((sigmaTy A n)⋆) ⊕' ((sigmaTy A n)⋆)) :=
  ((listF (sigmaDec A n ⨟ dupAnn A n) ⨟ unpref (A ⊗ Ty.finAlph n) G) ⨟
      listF (flagBy A Hb)) ⨟ allLeftTest (sigmaTy A n)

/-! Two elementary facts about lists of flagged values. -/

theorem flagged_isLeft {X : Ty} {E : Type} (P : E → Bool) (val : E → ⟦X⟧) (L : List E) :
    ((∀ y ∈ L.map (fun z => if P z then Sum.inl (val z) else Sum.inr (val z)),
        Sum.isLeft y = true) ↔ ∀ z ∈ L, P z = true) := by
  constructor
  · intro h z hz
    have hy := h _ (List.mem_map_of_mem hz)
    by_cases hp : P z
    · exact hp
    · simp [hp] at hy
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    simp [h z hz]

theorem flagged_unSum {X : Ty} {E : Type} (P : E → Bool) (val : E → ⟦X⟧) (L : List E) :
    (L.map (fun z => if P z then Sum.inl (val z) else Sum.inr (val z))).map unSum
      = L.map val := by
  induction L with
  | nil => rfl
  | cons z t ih =>
      rw [List.map_cons, List.map_cons, List.map_cons, ih]
      by_cases hp : P z <;> simp [hp, unSum]

theorem flagged_isLeft_self {X : Ty} (P : ⟦X⟧ → Bool) (w : List ⟦X⟧) :
    ((∀ y ∈ w.map (fun x => if P x then Sum.inl x else Sum.inr x), Sum.isLeft y = true)
      ↔ ∀ x ∈ w, P x = true) :=
  flagged_isLeft P (fun x => x) w

theorem flagged_unSum_self {X : Ty} (P : ⟦X⟧ → Bool) (w : List ⟦X⟧) :
    (w.map (fun x => if P x then Sum.inl x else Sum.inr x)).map unSum = w := by
  have h := flagged_unSum P (fun x => x) w
  simpa using h

end Term

/-! Unprefixing a list in which every annotation has been duplicated: the payloads are the
letters of the original list, and the new annotations are those of its unprefixing. -/

theorem unprefDen_dup_fst {E Gt : Type} [Group Gt] :
    (acc : Gt) → (l : List (E × Gt)) →
      ((unprefDen acc (l.map (fun p => (p, p.2)))).map Prod.fst) = l
  | _, [] => rfl
  | acc, p :: t => by
      obtain ⟨a, g⟩ := p
      simp only [List.map_cons, unprefDen_cons, List.map_cons]
      rw [unprefDen_dup_fst g t]

theorem unprefDen_dup_snd {E Gt : Type} [Group Gt] :
    (acc : Gt) → (l : List (E × Gt)) →
      ((unprefDen acc (l.map (fun p => (p, p.2)))).map Prod.snd)
        = (unprefDen acc l).map Prod.snd
  | _, [] => rfl
  | acc, p :: t => by
      obtain ⟨a, g⟩ := p
      simp only [List.map_cons, unprefDen_cons, List.map_cons]
      rw [unprefDen_dup_snd g t]

theorem unprefDen_dup_forall_snd {E Gt : Type} [Group Gt] (P : Gt → Bool) (acc : Gt)
    (l : List (E × Gt)) :
    (∀ z ∈ unprefDen acc (l.map (fun p => (p, p.2))), P z.2 = true)
      ↔ ∀ z ∈ unprefDen acc l, P z.2 = true := by
  constructor
  · intro h z hz
    have hm : z.2 ∈ (unprefDen acc l).map Prod.snd := List.mem_map_of_mem hz
    rw [← unprefDen_dup_snd acc l] at hm
    obtain ⟨y, hy, hy2⟩ := List.mem_map.mp hm
    have hPy := h y hy
    rwa [hy2] at hPy
  · intro h z hz
    have hm : z.2 ∈ (unprefDen acc (l.map (fun p => (p, p.2)))).map Prod.snd :=
      List.mem_map_of_mem hz
    rw [unprefDen_dup_snd acc l] at hm
    obtain ⟨y, hy, hy2⟩ := List.mem_map.mp hm
    have hPy := h y hy
    rwa [hy2] at hPy

/-- **The term `precheck_H`** (appendix, proof of the lemma "`check_H` may be replaced by
`left`").  An aperiodic term that leaves its input unchanged and puts it in the left variant
exactly when all its letters carry an annotation in `H`. -/
theorem exists_precheckH (A : Ty) {n : ℕ} (H : ⟦Ty.finAlph n⟧ → Prop) :
    ∃ t, IsPrecheckH (A := A) H t := by
  classical
  refine ⟨Term.precheckTerm A (fun g => decide (H g)), ?_, ?_⟩
  · simp [IsAperiodic, Term.precheckTerm, Term.usesPref]
  · intro w
    have hstep : ∀ x : ⟦Term.sigmaTy A n⟧,
        (Term.sigmaDec A n ⨟ (Term.dupAnn A n ⨟ Term.flagBy A (fun g => decide (H g)))).den x
          = if decide (H (Term.annOfSigma A x)) then Sum.inl x else Sum.inr x := by
      intro x
      show (Term.flagBy A (fun g => decide (H g))).den
          ((Term.dupAnn A n).den ((Term.sigmaDec A n).den x)) = _
      rw [Term.den_dupAnn_pair, Term.den_flagBy, Term.den_sigmaEnc_sigmaDec]
      rfl
    show (Term.allLeftTest (Term.sigmaTy A n)).den
        ((Term.listF (Term.sigmaDec A n ⨟
          (Term.dupAnn A n ⨟ Term.flagBy A (fun g => decide (H g))))).den w) = _
    rw [Term.den_listF, List.map_congr_left (fun x _ => hstep x), Term.den_allLeftTest,
      Term.flagged_unSum_self]
    have hfull := (Term.flagged_isLeft_self (fun x => decide (H (Term.annOfSigma A x))) w).trans
      (by simp : (∀ x ∈ w, decide (H (Term.annOfSigma A x)) = true)
        ↔ ∀ x ∈ w, H (Term.annOfSigma A x))
    by_cases hc : ∀ x ∈ w, H (Term.annOfSigma A x)
    · rw [if_pos (hfull.mpr hc), if_pos hc]
    · rw [if_neg (fun h => hc (hfull.mp h)), if_neg hc]

/-- **The term `check_H`** (appendix, *Partial prefix multiplication*).  An aperiodic term
that leaves its input unchanged and puts it in the left variant exactly when the input has
been obtained by prefix multiplication from a list over `Σ_H A`. -/
theorem exists_checkH (A : Ty) {n : ℕ} (G : Group ⟦Ty.finAlph n⟧)
    (H : ⟦Ty.finAlph n⟧ → Prop) :
    ∃ t, IsCheckH (A := A) G H t := by
  classical
  letI := G
  refine ⟨Term.checkTerm A G (fun g => decide (H g)), ?_, ?_⟩
  · simp [IsAperiodic, Term.checkTerm, Term.usesPref]
  · intro w
    have hstep1 : (Term.listF (Term.sigmaDec A n ⨟ Term.dupAnn A n)).den w
        = (w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2)) := by
      simp [List.map_map, Function.comp_def]
    have hunspref : (show List ⟦Term.sigmaTy A n⟧ from (Term.unsprefS A G).den w)
        = (unprefDen (1 : ⟦Ty.finAlph n⟧) (w.map (Term.sigmaDec A n).den)).map
            (Term.sigmaEnc A n).den := by
      show ((Term.unpref A G).den (w.map (Term.sigmaDec A n).den)).map
        (Term.sigmaEnc A n).den = _
      rw [show (Term.unpref A G).den (w.map (Term.sigmaDec A n).den)
          = unprefDen (1 : ⟦Ty.finAlph n⟧) (w.map (Term.sigmaDec A n).den) from
        Term.den_unpref _ _ _]
    have hval : (unprefDen (1 : ⟦Ty.finAlph n⟧)
          ((w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2)))).map
          (fun z => (Term.sigmaEnc A n).den z.1) = w := by
      have hsplitmap : (unprefDen (1 : ⟦Ty.finAlph n⟧)
            ((w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2)))).map
            (fun z => (Term.sigmaEnc A n).den z.1)
          = ((unprefDen (1 : ⟦Ty.finAlph n⟧)
              ((w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2)))).map Prod.fst).map
              (Term.sigmaEnc A n).den := List.map_map.symm
      refine hsplitmap.trans ?_
      refine (congrArg (List.map (Term.sigmaEnc A n).den)
        (unprefDen_dup_fst (E := ⟦A⟧) (Gt := ⟦Ty.finAlph n⟧) (1 : ⟦Ty.finAlph n⟧)
          (w.map (Term.sigmaDec A n).den))).trans ?_
      simp [List.map_map, Function.comp_def]
    have hiff : (∀ z ∈ unprefDen (1 : ⟦Ty.finAlph n⟧) (w.map (Term.sigmaDec A n).den),
          decide (H z.2) = true)
        ↔ (∀ x ∈ (unprefDen (1 : ⟦Ty.finAlph n⟧) (w.map (Term.sigmaDec A n).den)).map
              (Term.sigmaEnc A n).den, H (Term.annOfSigma A x)) := by
      constructor
      · intro h x hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
        rw [Term.annOfSigma_sigmaEnc]
        exact of_decide_eq_true (h z hz)
      · intro h z hz
        have hz' := h _ (List.mem_map_of_mem (f := (Term.sigmaEnc A n).den) hz)
        rw [Term.annOfSigma_sigmaEnc] at hz'
        exact decide_eq_true hz'
    have hfull : (∀ y ∈ (unprefDen (1 : ⟦Ty.finAlph n⟧)
            ((w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2)))).map
            (fun z => if decide (H z.2) then Sum.inl ((Term.sigmaEnc A n).den z.1)
              else Sum.inr ((Term.sigmaEnc A n).den z.1)), Sum.isLeft y = true)
        ↔ (∀ x ∈ (show List ⟦Term.sigmaTy A n⟧ from (Term.unsprefS A G).den w),
            H (Term.annOfSigma A x)) := by
      refine (Term.flagged_isLeft
        (fun z : (⟦A⟧ × ⟦Ty.finAlph n⟧) × ⟦Ty.finAlph n⟧ => decide (H z.2))
        (fun z : (⟦A⟧ × ⟦Ty.finAlph n⟧) × ⟦Ty.finAlph n⟧ =>
          (Term.sigmaEnc A n).den z.1) _).trans ?_
      refine (unprefDen_dup_forall_snd (E := ⟦A⟧) (Gt := ⟦Ty.finAlph n⟧)
        (fun g => decide (H g)) (1 : ⟦Ty.finAlph n⟧)
        (w.map (Term.sigmaDec A n).den)).trans ?_
      rw [hunspref]
      exact hiff
    show (Term.allLeftTest (Term.sigmaTy A n)).den
        ((Term.listF (Term.flagBy A (fun g => decide (H g)))).den
          ((Term.unpref (A ⊗ Ty.finAlph n) G).den
            ((Term.listF (Term.sigmaDec A n ⨟ Term.dupAnn A n)).den w))) = _
    rw [hstep1,
      show (Term.unpref (A ⊗ Ty.finAlph n) G).den
            ((w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2)))
          = unprefDen (1 : ⟦Ty.finAlph n⟧)
            ((w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2))) from
        Term.den_unpref _ _ _,
      Term.den_listF,
      List.map_congr_left (fun z _ => Term.den_flagBy A (fun g => decide (H g)) z.1 z.2),
      Term.den_allLeftTest]
    have hval2 : List.map Term.unSum
        (List.map (fun z : (⟦A⟧ × ⟦Ty.finAlph n⟧) × ⟦Ty.finAlph n⟧ =>
            if decide (H z.2) then Sum.inl ((Term.sigmaEnc A n).den z.1)
              else Sum.inr ((Term.sigmaEnc A n).den z.1))
          (unprefDen (1 : ⟦Ty.finAlph n⟧)
            ((w.map (Term.sigmaDec A n).den).map (fun p => (p, p.2))))) = w :=
      (Term.flagged_unSum _ _ _).trans hval
    exact if_congr hfull (congrArg Sum.inl hval2) (congrArg Sum.inr hval2)

/-! ### The annotations of the image of `ρ` -/

namespace Term

@[simp] theorem usesPref_rhoInj (A : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) :
    usesPref (rhoInj A hm) = false :=
  usesPref_sigmaCase _ (fun i => usesPref_injSigma A (hm i))

@[simp] theorem annOfSigma_injSigma (A : Ty) {n : ℕ} (g : ⟦Ty.finAlph n⟧) (a : ⟦A⟧) :
    annOfSigma A ((injSigma A g).den a) = g := by
  simp [annOfSigma]

/-- Every letter in the image of `ρ` carries an annotation in `H`. -/
theorem ann_mem_of_rhoInj (A : Ty) {m n : ℕ} (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧)
    (x : ⟦sigmaTy A m⟧) : ∃ i, hm i = annOfSigma A ((rhoInj A hm).den x) := by
  obtain ⟨a, i, rfl⟩ := sigma_cases A x
  refine ⟨i, ?_⟩
  simp [rhoInj]

end Term

/-! ### `check_H` may be replaced by `left` -/

/-- The square of the appendix that commutes `check_H` past the prefix multiplication: it is
an aperiodic equation once both occurrences of the prefix multiplication are inverted. -/
theorem sprefS_checkH {A : Ty} {n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {H : ⟦Ty.finAlph n⟧ → Prop}
    {t p : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))}
    (ht : IsCheckH G H t) (hp : IsPrecheckH H p) :
    (Term.sprefS A G ⨟ t) ≡ₜ (p ⨟ Term.sumF (Term.sprefS A G) (Term.sprefS A G)) := by
  classical
  have htA : Term.usesPref t = false := ht.1
  have hpA : Term.usesPref p = false := hp.1
  have hap : (Term.unsprefS A G ⨟ p) ≡ₜ
      (t ⨟ Term.sumF (Term.unsprefS A G) (Term.unsprefS A G)) := by
    refine peq_of_den (by simp [IsAperiodic, Term.usesPref, hpA]) ?_ ?_
    · simp [IsAperiodic, Term.usesPref, htA]
    · intro w
      show p.den ((Term.unsprefS A G).den w) =
        (Term.sumF (Term.unsprefS A G) (Term.unsprefS A G)).den (t.den w)
      rw [hp.2 ((Term.unsprefS A G).den w), ht.2 w]
      by_cases hcond : ∀ x ∈ (show List ⟦Term.sigmaTy A n⟧ from (Term.unsprefS A G).den w),
          H (Term.annOfSigma A x)
      · rw [if_pos hcond, if_pos hcond]
        rfl
      · rw [if_neg hcond, if_neg hcond]
        rfl
  have hiso : (Term.sumF (Term.unsprefS A G) (Term.unsprefS A G) ⨟
      Term.sumF (Term.sprefS A G) (Term.sprefS A G)) ≡ₜ
        Term.id (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆)) :=
    (PEq.sum_comp _ _ _ _).trans
      ((PEq.congr_sumF (Term.unsprefS_sprefS A G) (Term.unsprefS_sprefS A G)).trans
        (PEq.sum_id _ _))
  calc (Term.sprefS A G ⨟ t) ≡ₜ (Term.sprefS A G ⨟ (t ⨟ Term.id _)) :=
        PEq.compR _ (PEq.symm (PEq.comp_id _))
    _ ≡ₜ (Term.sprefS A G ⨟ (t ⨟ (Term.sumF (Term.unsprefS A G) (Term.unsprefS A G) ⨟
          Term.sumF (Term.sprefS A G) (Term.sprefS A G)))) :=
        PEq.compR _ (PEq.compR _ (PEq.symm hiso))
    _ ≡ₜ (Term.sprefS A G ⨟ ((t ⨟ Term.sumF (Term.unsprefS A G) (Term.unsprefS A G)) ⨟
          Term.sumF (Term.sprefS A G) (Term.sprefS A G))) :=
        PEq.compR _ (PEq.symm (PEq.comp_assoc _ _ _))
    _ ≡ₜ (Term.sprefS A G ⨟ ((Term.unsprefS A G ⨟ p) ⨟
          Term.sumF (Term.sprefS A G) (Term.sprefS A G))) :=
        PEq.compR _ (PEq.compL _ (PEq.symm hap))
    _ ≡ₜ (Term.sprefS A G ⨟ (Term.unsprefS A G ⨟
          (p ⨟ Term.sumF (Term.sprefS A G) (Term.sprefS A G)))) :=
        PEq.compR _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.sprefS A G ⨟ Term.unsprefS A G) ⨟
          (p ⨟ Term.sumF (Term.sprefS A G) (Term.sprefS A G))) :=
        PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ (Term.id ((Term.sigmaTy A n)⋆) ⨟
          (p ⨟ Term.sumF (Term.sprefS A G) (Term.sprefS A G))) :=
        PEq.compL _ (Term.sprefS_unsprefS A G)
    _ ≡ₜ (p ⨟ Term.sumF (Term.sprefS A G) (Term.sprefS A G)) := PEq.id_comp _

/-- On the image of `ρ*`, the term `precheck_H` is the left injection. -/
theorem rhoInj_precheckH {A : Ty} {m n : ℕ} {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧}
    {p : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))}
    (hp : IsPrecheckH (fun g => ∃ i, hm i = g) p) :
    (Term.listF (Term.rhoInj A hm) ⨟ p) ≡ₜ
      (Term.listF (Term.rhoInj A hm) ⨟ Term.inl _ _) := by
  classical
  have hpA : Term.usesPref p = false := hp.1
  refine peq_of_den (by simp [IsAperiodic, Term.usesPref, hpA]) (by simp [IsAperiodic,
    Term.usesPref]) ?_
  intro w
  show p.den ((Term.listF (Term.rhoInj A hm)).den w) =
    Sum.inl ((Term.listF (Term.rhoInj A hm)).den w)
  rw [hp.2]
  refine if_pos ?_
  intro x hx
  simp only [Term.den_listF, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact Term.ann_mem_of_rhoInj A hm y

/-- **Lemma (`check_H` may be replaced by `left`)** (appendix, *Partial prefix
multiplication*).  After the injection `ρ*` and the prefix multiplication, the test `check_H`
always succeeds, so it is provably the left injection. -/
theorem checkH_left {A : Ty} {m n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧}
    {t p : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))}
    (ht : IsCheckH G (fun g => ∃ i, hm i = g) t) (hp : IsPrecheckH (fun g => ∃ i, hm i = g) p) :
    ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ t) ≡ₜ
      ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ Term.inl _ _) := by
  calc ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ t)
      ≡ₜ (Term.listF (Term.rhoInj A hm) ⨟ (Term.sprefS A G ⨟ t)) := PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.listF (Term.rhoInj A hm) ⨟
          (p ⨟ Term.sumF (Term.sprefS A G) (Term.sprefS A G))) :=
        PEq.compR _ (sprefS_checkH ht hp)
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ p) ⨟
          Term.sumF (Term.sprefS A G) (Term.sprefS A G)) := PEq.symm (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.inl _ _) ⨟
          Term.sumF (Term.sprefS A G) (Term.sprefS A G)) :=
        PEq.compL _ (rhoInj_precheckH hp)
    _ ≡ₜ (Term.listF (Term.rhoInj A hm) ⨟
          (Term.inl _ _ ⨟ Term.sumF (Term.sprefS A G) (Term.sprefS A G))) :=
        PEq.comp_assoc _ _ _
    _ ≡ₜ (Term.listF (Term.rhoInj A hm) ⨟ (Term.sprefS A G ⨟ Term.inl _ _)) :=
        PEq.compR _ (PEq.nat_inl _ _)
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ Term.inl _ _) :=
        PEq.symm (PEq.comp_assoc _ _ _)

/-- **Lemma (Partial prefix multiplication)** (appendix, *Partial prefix multiplication*).
Injecting a list over `Σ_H A` into `(Σ A)*`, multiplying prefixes, testing with `check_H`,
undoing the multiplication on the left variant (and returning the empty list on the right
one) and projecting back is provably the identity. -/
theorem partial_prefix_multiplication {A : Ty} {m n : ℕ} {G : Group ⟦Ty.finAlph n⟧}
    {hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧} (hinj : Function.Injective hm)
    {t p : Term ((Term.sigmaTy A n)⋆) (((Term.sigmaTy A n)⋆) ⊕' ((Term.sigmaTy A n)⋆))}
    (ht : IsCheckH G (fun g => ∃ i, hm i = g) t)
    (hp : IsPrecheckH (fun g => ∃ i, hm i = g) p) :
    ((((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ t) ⨟
        Term.either (Term.unsprefS A G)
          (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n))) ⨟
      Term.listF (Term.rhoInv A hm)) ≡ₜ Term.id ((Term.sigmaTy A m)⋆) := by
  classical
  have hleft := checkH_left (A := A) ht hp
  have hstep : ((((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ t) ⨟
      Term.either (Term.unsprefS A G)
        (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n)))) ≡ₜ
      ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ Term.unsprefS A G) := by
    calc ((((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ t) ⨟
        Term.either (Term.unsprefS A G)
          (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n))))
        ≡ₜ (((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ Term.inl _ _) ⨟
            Term.either (Term.unsprefS A G)
              (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n))) :=
          PEq.compL _ hleft
      _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ (Term.inl _ _ ⨟
            Term.either (Term.unsprefS A G)
              (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n)))) :=
          PEq.comp_assoc _ _ _
      _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ Term.unsprefS A G) :=
          PEq.compR _ (Term.inl_either _ _)
  calc ((((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ t) ⨟
      Term.either (Term.unsprefS A G)
        (Term.toUnit ((Term.sigmaTy A n)⋆) ⨟ Term.nilT (Term.sigmaTy A n))) ⨟
      Term.listF (Term.rhoInv A hm))
      ≡ₜ (((Term.listF (Term.rhoInj A hm) ⨟ Term.sprefS A G) ⨟ Term.unsprefS A G) ⨟
          Term.listF (Term.rhoInv A hm)) := PEq.compL _ hstep
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ (Term.sprefS A G ⨟ Term.unsprefS A G)) ⨟
          Term.listF (Term.rhoInv A hm)) := PEq.compL _ (PEq.comp_assoc _ _ _)
    _ ≡ₜ ((Term.listF (Term.rhoInj A hm) ⨟ Term.id ((Term.sigmaTy A n)⋆)) ⨟
          Term.listF (Term.rhoInv A hm)) :=
        PEq.compL _ (PEq.compR _ (Term.sprefS_unsprefS A G))
    _ ≡ₜ (Term.listF (Term.rhoInj A hm) ⨟ Term.listF (Term.rhoInv A hm)) :=
        PEq.compL _ (PEq.comp_id _)
    _ ≡ₜ Term.listF (Term.rhoInj A hm ⨟ Term.rhoInv A hm) := PEq.list_comp _ _
    _ ≡ₜ Term.listF (Term.id (Term.sigmaTy A m)) :=
        PEq.congr_listF (Term.rhoInj_rhoInv A hinj)
    _ ≡ₜ Term.id ((Term.sigmaTy A m)⋆) := PEq.list_id _

/-! ### Group injections

The lemma below is the group injection lemma of the appendix.  Property (1) of the appendix
— the group injection is an *aperiodic* term — is `IsAperiodic iota` below: the injection
constructed by the proof is `α ; ε`, where `ε` is a co-projection into a variant of `Σ_H`
and `α` is the lift produced by the co-product normalisation of drops, and both are
aperiodic.  (The injection is in general *not* a drop, because that normalisation genuinely
needs lifts, already for the projection `fst : (B₁ + B₂) × C ⇒ B₁ + B₂`, whose case
distinction is exposed by the prime lift `distR`.)  Property (2) is the provable injectivity
with the drop one-sided inverse `σ`, and property (3) is the last equation.
 -/

/-- **Lemma (Group injection)** (appendix, *Group-lifts*).  Every drop `f : A ⇒ Σ B` becomes
annotation-diagonal after `A` has been injected into a co-product `Σ_H C` indexed by a subset
of the group: the injection is an aperiodic term which is provably injective with a drop
one-sided inverse `σ`, and `σ ; f` is provably the case tree that sends the `h`-th variant to
the `h`-th variant, by a drop.

The proof is the one of the appendix — a repeated application of the normalisation of drops
with a co-product codomain, followed by a grouping of the summands — and is carried out in
`Lax149335Proofs.Appendix.Groups.GroupInjection`. -/
theorem group_injection {A B : Ty} {n : ℕ} (f : Term A (Term.sigmaTy B n)) (hf : IsDrop f) :
    ∃ (m : ℕ) (hm : ⟦Ty.finAlph m⟧ → ⟦Ty.finAlph n⟧) (C : Ty)
      (iota : Term A (Term.sigmaTy C m)) (sigma : Term (Term.sigmaTy C m) A)
      (fs : ⟦Ty.finAlph m⟧ → Term C B),
      Function.Injective hm ∧ IsAperiodic iota ∧ IsDrop sigma ∧
        (iota ⨟ sigma) ≡ₜ Term.id A ∧ (∀ i, IsDrop (fs i)) ∧
        (sigma ⨟ f) ≡ₜ Term.sigmaCase (fun i => fs i ⨟ Term.injSigma B (hm i)) :=
  hasGroupInjection_of_isDrop n f hf

end Lax149335Proofs

bridge_export Lax149335Proofs
